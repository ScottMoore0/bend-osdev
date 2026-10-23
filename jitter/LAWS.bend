# The laws of the jitter core, over its public interface. The core laws
# hold for every conditioning hash (the template arguments of crypto's hash
# interface), every parameter set and every state; the core_ laws for every
# conditioner (any block step).
#
# The stuck test: a zero delta is stuck, and so is a delta equal to the one
# before it, after any deltas; so a constant source is stuck from its
# second delta on.
#
# The SP 800-90B health tests: C identical samples trip the Repetition
# Count Test with cutoff C (C >= 2), and C - 1 do not; C identical samples
# trip the Adaptive Proportion Test with cutoff C in a window of at least C
# samples; a failure of either is never forgotten, by the test or by the
# generator.
#
# The generator: the same deltas give the same state however they arrive
# (absorbing a, then b, is absorbing a ++ b); a stuck source never lets a
# block be taken, after any number of deltas, under any parameters that
# need two or more counted deltas per block; a block that cannot be taken
# is refused with the reason; a generator whose health test has failed
# refuses every read of one or more bytes; and a read that succeeds gives
# exactly the bytes asked for.
#
# Vectors: the stuck test on small deltas, the APT's window restarting, the
# default parameters and the deltas they need per block.
#
# The XDRBG option: SHAKE256 reads give the bytes asked for and are one
# stream, with NIST's example for the empty message; XDRBG-256 over SHAKE256
# gives the same state and block for the same deltas however they arrive,
# 32-byte blocks, reads of the length asked for, and refuses reads once a
# health test has failed.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./stuck.bend as Sk
import ./health.bend as Ht
import ./jitter.bend as J
import ./shake.bend as S
import ./xdrbg.bend as X
import ./xdrbg256.bend as JX

# The stuck test

law stuck_zero:
  for s: Sk.JitStuckState
  {Sk.JitStuck.is_stuck(s, W.W64.zero()) == True{} : Bool}

law stuck_repeat:
  for s: Sk.JitStuckState
  for +t: W.W64
  {Sk.JitStuck.is_stuck(Sk.JitStuck.next(s, t), t) == True{} : Bool}

# 5, 7, 9: the second derivative is 0, so 9 is stuck
law stuck_vec_second:
  {Sk.JitStuck.is_stuck(Sk.JitStuck.next(Sk.JitStuck.next(Sk.JitStuck.new(), W.W64.from_u32(5)), W.W64.from_u32(7)), W.W64.from_u32(9)) == True{} : Bool}

# 5, 7, 10: no derivative is 0, so 10 is not stuck
law stuck_vec_moving:
  {Sk.JitStuck.is_stuck(Sk.JitStuck.next(Sk.JitStuck.next(Sk.JitStuck.new(), W.W64.from_u32(5)), W.W64.from_u32(7)), W.W64.from_u32(10)) == False{} : Bool}

# The Repetition Count Test

law rct_trips:
  for +x: W.W64
  for +k: Nat
  {Ht.JitRct.failed(Ht.JitRct.run(2n+k, Ht.JitRct.new(), List.replicate(W.W64, 2n+k, x))) == True{} : Bool}

law rct_below_cutoff:
  for +x: W.W64
  for +k: Nat
  {Ht.JitRct.failed(Ht.JitRct.run(2n+k, Ht.JitRct.new(), List.replicate(W.W64, 1n+k, x))) == False{} : Bool}

law rct_latch:
  for +c: Nat
  for r: Ht.JitRct
  for +x: W.W64
  for h: {Ht.JitRct.failed(r) == True{} : Bool}
  {Ht.JitRct.failed(Ht.JitRct.feed(c, r, x)) == True{} : Bool}

# The Adaptive Proportion Test

law apt_trips:
  for +x: W.W64
  for +k: Nat
  for +w: Nat
  for h: {Nat.is_le(2n+k, w) == True{} : Bool}
  {Ht.JitApt.failed(Ht.JitApt.run(w, 2n+k, Ht.JitApt.new(), List.replicate(W.W64, 2n+k, x))) == True{} : Bool}

law apt_latch:
  for +w: Nat
  for +c: Nat
  for t: Ht.JitApt
  for +x: W.W64
  for h: {Ht.JitApt.failed(t) == True{} : Bool}
  {Ht.JitApt.failed(Ht.JitApt.feed(w, c, t, x)) == True{} : Bool}

# window 4, cutoff 3: 1, 1, 2, 1 has three 1s in a window; 1, 1, 2, 2, 1, 1
# has four, but the window restarts after the fourth sample
law apt_vec_window:
  {Ht.JitApt.failed(Ht.JitApt.run(4n, 3n, Ht.JitApt.new(), [W.W64.from_u32(1), W.W64.from_u32(1), W.W64.from_u32(2), W.W64.from_u32(1)])) == True{} : Bool}

law apt_vec_restart:
  {Ht.JitApt.failed(Ht.JitApt.run(4n, 3n, Ht.JitApt.new(), [W.W64.from_u32(1), W.W64.from_u32(1), W.W64.from_u32(2), W.W64.from_u32(2), W.W64.from_u32(1), W.W64.from_u32(1)])) == False{} : Bool}

# The generator

law absorb_all_append:
  for ~H: Data
  for ~bsize: Nat
  for ~update: H -> B.Octets -> H
  for ~digest: B.Octets -> B.Octets
  for +p: J.JitParams
  for st: J.JitState<H>
  for a: List<&2, W.W64>
  for b: List<&2, W.W64>
  {J.Jitter.absorb_all(~H, ~bsize, ~update, ~digest, p, J.Jitter.absorb_all(~H, ~bsize, ~update, ~digest, p, st, a), b) == J.Jitter.absorb_all(~H, ~bsize, ~update, ~digest, p, st, List.append(&2, W.W64, a, b)) : J.JitState<H>}

law absorb_failed:
  for ~H: Data
  for ~bsize: Nat
  for ~update: H -> B.Octets -> H
  for ~digest: B.Octets -> B.Octets
  for +p: J.JitParams
  for st: J.JitState<H>
  for +d: W.W64
  for h: {J.Jitter.failed(~H, st) == True{} : Bool}
  {J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)) == True{} : Bool}

law stuck_source:
  for ~H: Data
  for ~bsize: Nat
  for ~init: H
  for ~update: H -> B.Octets -> H
  for ~digest: B.Octets -> B.Octets
  for +p: J.JitParams
  for h: {Nat.is_lt(1n, J.JitParams.need(p)) == True{} : Bool}
  for +d: W.W64
  for n: Nat
  {J.Jitter.can_block(~H, p, J.Jitter.absorb_all(~H, ~bsize, ~update, ~digest, p, J.Jitter.init(~H, ~init, p), List.replicate(W.W64, n, d))) == False{} : Bool}

law block_refused:
  for ~H: Data
  for ~init: H
  for ~update: H -> B.Octets -> H
  for ~final: H -> B.Octets
  for +p: J.JitParams
  for +st: J.JitState<H>
  for h: {J.Jitter.can_block(~H, p, st) == False{} : Bool}
  {J.Jitter.block(~H, ~init, ~update, ~final, p, st) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitBlock<H>>}

law read_failed:
  for ~H: Data
  for ~bsize: Nat
  for ~init: H
  for ~update: H -> B.Octets -> H
  for ~final: H -> B.Octets
  for ~digest: B.Octets -> B.Octets
  for +p: J.JitParams
  for +st: J.JitState<H>
  for ds: List<&2, W.W64>
  for +n: Nat
  for h: {J.Jitter.failed(~H, st) == True{} : Bool}
  {J.Jitter.read(~H, ~bsize, ~init, ~update, ~final, ~digest, p, st, ds, 1n+n) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitOut<H>>}

law read_length:
  for ~H: Data
  for ~bsize: Nat
  for ~init: H
  for ~update: H -> B.Octets -> H
  for ~final: H -> B.Octets
  for ~digest: B.Octets -> B.Octets
  for +p: J.JitParams
  for +st: J.JitState<H>
  for ds: List<&2, W.W64>
  for +n: Nat
  {Result.map(&2, &2, J.JitError, J.JitOut<H>, Nat, o => B.Octets.len(J.JitOut.out(~H, o)), J.Jitter.read(~H, ~bsize, ~init, ~update, ~final, ~digest, p, st, ds, n)) == Result.map(&2, &2, J.JitError, J.JitOut<H>, Nat, o => n, J.Jitter.read(~H, ~bsize, ~init, ~update, ~final, ~digest, p, st, ds, n)) : Result<&2, &2, J.JitError, Nat>}

# The default parameters: osr 3, safety factor 65, RCT cutoff 91, APT
# window 512 and cutoff 459, the hash loop's domain separator, one block
# discarded; (256 + 65) * 3 = 963 counted deltas per block
law params_default:
  {J.JitParams.default() == J.JitParams{3n, 65n, 91n, 512n, 459n, 2, 1n} : J.JitParams}

law need_default:
  {J.JitParams.need(J.JitParams.default()) == 963n : Nat}

# The core, for every conditioner (any ~take, jitter.bend's JitCore): the
# generator laws above hold whatever the block step is

law core_block_refused:
  for ~H: Data
  for ~take: H -> J.JitTaken<H>
  for +p: J.JitParams
  for +st: J.JitState<H>
  for h: {J.Jitter.can_block(~H, p, st) == False{} : Bool}
  {J.JitCore.block(~H, ~take, p, st) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitBlock<H>>}

law core_read_failed:
  for ~H: Data
  for ~bsize: Nat
  for ~update: H -> B.Octets -> H
  for ~digest: B.Octets -> B.Octets
  for ~take: H -> J.JitTaken<H>
  for +p: J.JitParams
  for +st: J.JitState<H>
  for ds: List<&2, W.W64>
  for +n: Nat
  for h: {J.Jitter.failed(~H, st) == True{} : Bool}
  {J.JitCore.read(~H, ~bsize, ~update, ~digest, ~take, p, st, ds, 1n+n) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitOut<H>>}

law core_read_length:
  for ~H: Data
  for ~bsize: Nat
  for ~update: H -> B.Octets -> H
  for ~digest: B.Octets -> B.Octets
  for ~take: H -> J.JitTaken<H>
  for +p: J.JitParams
  for +st: J.JitState<H>
  for ds: List<&2, W.W64>
  for +n: Nat
  {Result.map(&2, &2, J.JitError, J.JitOut<H>, Nat, o => B.Octets.len(J.JitOut.out(~H, o)), J.JitCore.read(~H, ~bsize, ~update, ~digest, ~take, p, st, ds, n)) == Result.map(&2, &2, J.JitError, J.JitOut<H>, Nat, o => n, J.JitCore.read(~H, ~bsize, ~update, ~digest, ~take, p, st, ds, n)) : Result<&2, &2, J.JitError, Nat>}

# SHAKE256 (shake.bend), for every state: a read gives exactly the bytes
# asked for, and the output is one stream (a + b bytes from offset i are
# the a bytes there followed by the b bytes at offset i + a, so XDRBG's two
# reads of T are T split)

law shake_read_length:
  for s: S.JitShakeState
  for +i: Nat
  for +n: Nat
  {B.Octets.len(S.JitShake.read(s, i, n)) == n : Nat}

law shake_read_split:
  for +s: S.JitShakeState
  for +i: Nat
  for +a: Nat
  for +b: Nat
  {S.JitShake.read(s, i, Nat.add(a, b)) == B.Octets.append(S.JitShake.read(s, i, a), S.JitShake.read(s, Nat.add(i, a), b)) : B.Octets}

# SHAKE256 of the empty message, its first 32 bytes (NIST's SHA-3 examples,
# SHAKE256_Msg0)
law shake256_empty:
  {S.JitShake.shake256(B.Octets.empty(), 32n) == B.Octets.of_list([70, 185, 221, 43, 11, 168, 141, 19, 35, 59, 63, 235, 116, 62, 235, 36, 63, 205, 82, 234, 98, 184, 27, 130, 181, 12, 39, 100, 110, 213, 118, 47]) : B.Octets}

# the same output's bytes 136 to 143, from the second block squeezed
law shake256_empty_second_block:
  {S.JitShake.read(S.JitShake.update(S.JitShake.init(), B.Octets.empty()), 136n, 8n) == B.Octets.of_list([148, 59, 106, 236, 70, 138, 45, 98]) : B.Octets}

# XDRBG-256 over SHAKE256 (xdrbg256.bend), for every parameter set, state
# and delta list: the same deltas give the same state and the same block
# however they arrive; a block is l = 32 bytes; a read that succeeds gives
# exactly the bytes asked for; a failed generator refuses every read

law xdrbg_absorb_append:
  for +p: J.JitParams
  for st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>
  for a: List<&2, W.W64>
  for b: List<&2, W.W64>
  {JX.JitXdrbg256.absorb_all(p, JX.JitXdrbg256.absorb_all(p, st, a), b) == JX.JitXdrbg256.absorb_all(p, st, List.append(&2, W.W64, a, b)) : J.JitState<X.JitXdrbgPool<S.JitShakeState>>}

law xdrbg_block_append:
  for +p: J.JitParams
  for st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>
  for a: List<&2, W.W64>
  for b: List<&2, W.W64>
  {JX.JitXdrbg256.block(p, JX.JitXdrbg256.absorb_all(p, JX.JitXdrbg256.absorb_all(p, st, a), b)) == JX.JitXdrbg256.block(p, JX.JitXdrbg256.absorb_all(p, st, List.append(&2, W.W64, a, b))) : Result<&2, &2, J.JitError, J.JitBlock<X.JitXdrbgPool<S.JitShakeState>>>}

law xdrbg_block_length:
  for +p: J.JitParams
  for +st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>
  {Result.map(&2, &2, J.JitError, J.JitBlock<X.JitXdrbgPool<S.JitShakeState>>, Nat, k => B.Octets.len(J.JitBlock.out(~X.JitXdrbgPool<S.JitShakeState>, k)), JX.JitXdrbg256.block(p, st)) == Result.map(&2, &2, J.JitError, J.JitBlock<X.JitXdrbgPool<S.JitShakeState>>, Nat, k => 32n, JX.JitXdrbg256.block(p, st)) : Result<&2, &2, J.JitError, Nat>}

law xdrbg_read_length:
  for +p: J.JitParams
  for +st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>
  for ds: List<&2, W.W64>
  for +n: Nat
  {Result.map(&2, &2, J.JitError, J.JitOut<X.JitXdrbgPool<S.JitShakeState>>, Nat, o => B.Octets.len(J.JitOut.out(~X.JitXdrbgPool<S.JitShakeState>, o)), JX.JitXdrbg256.read(p, st, ds, n)) == Result.map(&2, &2, J.JitError, J.JitOut<X.JitXdrbgPool<S.JitShakeState>>, Nat, o => n, JX.JitXdrbg256.read(p, st, ds, n)) : Result<&2, &2, J.JitError, Nat>}

law xdrbg_read_failed:
  for +p: J.JitParams
  for +st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>
  for ds: List<&2, W.W64>
  for +n: Nat
  for h: {J.Jitter.failed(~X.JitXdrbgPool<S.JitShakeState>, st) == True{} : Bool}
  {JX.JitXdrbg256.read(p, st, ds, 1n+n) == Fail{J.Jitter.why(~X.JitXdrbgPool<S.JitShakeState>, p, st)} : Result<&2, &2, J.JitError, J.JitOut<X.JitXdrbgPool<S.JitShakeState>>>}
