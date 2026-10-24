# A constant source makes the generator fail its Repetition Count Test,
# rather than run out of deltas: for every conditioner, every parameter set
# under which a block needs two or more counted deltas and the RCT's cutoff
# C is at least 2 and no more than the APT's window and cutoff, and every
# delta d, reading one or more bytes from a new generator given C or more
# copies of d fails with JitRctFailure. A constant source's deltas after the
# first are stuck (stuck_source), so no block comes; the RCT then trips at
# the C-th delta (rct_trips), before the APT can.
#
# Under the default parameters (C = 91, an APT window of 512 and cutoff of
# 459, 963 deltas a block) that is any 91 or more copies.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./jitter.bend as J

law core_constant_fails:
  for ~H: Data
  for ~bsize: Nat
  for ~init: H
  for ~update: H -> B.Octets -> H
  for ~digest: B.Octets -> B.Octets
  for ~take: H -> J.JitTaken<H>
  for +p: J.JitParams
  for +d: W.W64
  for +m: Nat
  for +n: Nat
  for h1: {Nat.is_lt(1n, J.JitParams.need(p)) == True{} : Bool}
  for h2: {Nat.is_le(2n, J.JitParams.rct_cutoff(p)) == True{} : Bool}
  for h3: {Nat.is_le(J.JitParams.rct_cutoff(p), J.JitParams.apt_window(p)) == True{} : Bool}
  for h4: {Nat.is_le(J.JitParams.rct_cutoff(p), J.JitParams.apt_cutoff(p)) == True{} : Bool}
  for h5: {Nat.is_le(J.JitParams.rct_cutoff(p), m) == True{} : Bool}
  {J.JitCore.generate(~H, ~bsize, ~init, ~update, ~digest, ~take, p, List.replicate(W.W64, m, d), 1n+n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<H>>}

law constant_fails:
  for ~H: Data
  for ~bsize: Nat
  for ~init: H
  for ~update: H -> B.Octets -> H
  for ~final: H -> B.Octets
  for ~digest: B.Octets -> B.Octets
  for +p: J.JitParams
  for +d: W.W64
  for +m: Nat
  for +n: Nat
  for h1: {Nat.is_lt(1n, J.JitParams.need(p)) == True{} : Bool}
  for h2: {Nat.is_le(2n, J.JitParams.rct_cutoff(p)) == True{} : Bool}
  for h3: {Nat.is_le(J.JitParams.rct_cutoff(p), J.JitParams.apt_window(p)) == True{} : Bool}
  for h4: {Nat.is_le(J.JitParams.rct_cutoff(p), J.JitParams.apt_cutoff(p)) == True{} : Bool}
  for h5: {Nat.is_le(J.JitParams.rct_cutoff(p), m) == True{} : Bool}
  {J.Jitter.generate(~H, ~bsize, ~init, ~update, ~final, ~digest, p, List.replicate(W.W64, m, d), 1n+n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<H>>}

law constant_fails_default:
  for ~H: Data
  for ~bsize: Nat
  for ~init: H
  for ~update: H -> B.Octets -> H
  for ~final: H -> B.Octets
  for ~digest: B.Octets -> B.Octets
  for +d: W.W64
  for +m: Nat
  for +n: Nat
  for h: {Nat.is_le(91n, m) == True{} : Bool}
  {J.Jitter.generate(~H, ~bsize, ~init, ~update, ~final, ~digest, J.JitParams.default(), List.replicate(W.W64, m, d), 1n+n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<H>>}
