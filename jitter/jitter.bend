# bend-osdev-jitter: the pure core of a CPU Jitter random number generator
# (Stephan Müller's jitterentropy): it takes time deltas, measured
# elsewhere (jitterclock reads a clock), and holds the noise processing,
# the health tests and the conditioning.
#
# For each delta (Müller, "CPU Time Jitter Based Non-Physical True Random
# Number Generator", 4 May 2026, sections 3.1.4 to 3.1.7):
#   * the stuck test (stuck.bend) decides whether it counts;
#   * the SP 800-90B Repetition Count and Adaptive Proportion Tests
#     (health.bend) see it;
#   * it is inserted into the entropy pool, a hash state, as one buffer of
#     the hash's block size, so that every insertion runs the permutation:
#     the delta (8 bytes, little-endian), a domain separator byte, the
#     digest of the health tests' status (the auxiliary data), and zeros.
# A block is the pool's digest once enough deltas have counted, (256 +
# safety) * osr of them; the pool then starts again from the block (section
# 3.1.4: the pool's previous contents are reused). Bytes are blocks
# concatenated, the last cut (section 3.2).
#
# The conditioning is a hash through the crypto package's hash interface
# (template arguments ~H, ~bsize, ~init, ~update, ~final, ~digest), SHA3-256
# (crypto's inst_sha3.bend) by default: the 2022 design's conditioner
# (jitterentropy 3.0 to 3.6). The 2026 design replaces it with an XDRBG
# over SHAKE-256 (section 3.1.1); see README.md for what this means for
# compatibility.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./stuck.bend as Sk
import ./health.bend as Ht

# ---------------------------------------------------------------- parameters

# osr: the oversampling rate (each counted delta is taken to hold 1/osr
# bits of entropy); safety: the deltas beyond 256 * osr (the safety factor,
# times osr); the health tests' cutoffs and the APT's window; domain: the
# separator byte (1: memory access loop only, 2: hash loop only, 3: both);
# prime: blocks generated and discarded before the first output
type JitParams is Data:
  JitParams{osr: Nat, safety: Nat, rct_cutoff: Nat, apt_window: Nat, apt_cutoff: Nat, domain: U32, prime: Nat}

# the APT cutoffs Müller's table gives for a window of 512 and a false
# positive probability of 2^-30, by osr (section 3.1.6)
def JitParams.apt_cutoff_for(osr: Nat) -> Nat:
  match osr:
    case 0n:
      512n
    case 1n:
      325n
    case 2n:
      422n
    case 3n:
      459n
    case 4n:
      477n
    case 5n:
      488n
    case 6n:
      494n
    case 7n:
      499n
    case 8n:
      502n
    case 9n:
      505n
    case 10n:
      507n
    case 11n:
      508n
    case 12n:
      509n
    case 13n:
      510n
    case 14n:
      511n
    case 15n+r:
      512n

# the parameters for an oversampling rate: the RCT cutoff C = 1 + 30 * osr
# (SP 800-90B's formula for alpha = 2^-30 and H = 1/osr), the APT's window
# of 512 and its cutoff from Müller's table, a safety factor of 65, the
# hash loop's domain separator, and one block discarded
def JitParams.for_osr(+osr: Nat) -> JitParams:
  JitParams{osr, 65n, 1n+Nat.mul(30n, osr), 512n, JitParams.apt_cutoff_for(osr), 2, 1n}

# osr 3, the lowest the jitterentropy library allows (JENT_MIN_OSR)
def JitParams.default() -> JitParams:
  JitParams.for_osr(3n)

def JitParams.rct_cutoff(p: JitParams) -> Nat:
  match p:
    case JitParams{o, s, rc, aw, ac, d, pr}:
      rc

def JitParams.apt_window(p: JitParams) -> Nat:
  match p:
    case JitParams{o, s, rc, aw, ac, d, pr}:
      aw

def JitParams.apt_cutoff(p: JitParams) -> Nat:
  match p:
    case JitParams{o, s, rc, aw, ac, d, pr}:
      ac

def JitParams.domain(p: JitParams) -> U32:
  match p:
    case JitParams{o, s, rc, aw, ac, d, pr}:
      d

def JitParams.prime(p: JitParams) -> Nat:
  match p:
    case JitParams{o, s, rc, aw, ac, d, pr}:
      pr

# the deltas that must count before a block: (256 + safety) * osr
def JitParams.need(p: JitParams) -> Nat:
  match p:
    case JitParams{+o, +s, rc, aw, ac, d, pr}:
      Nat.mul(Nat.add(256n, s), o)

# ---------------------------------------------------------------- state

# the pool (a hash state), the stuck test, the two health tests, the
# deltas counted towards the next block, and the blocks still to discard
type JitState<-H: Data> is Data:
  JitState{pool: H, stuck: Sk.JitStuckState, rct: Ht.JitRct, apt: Ht.JitApt, count: Nat, discard: Nat}

type JitError is Data:
  JitRctFailure{}
  JitAptFailure{}
  JitNotEnough{have: Nat, need: Nat}
  JitNeedMore{have: Nat}

# a block, and the state after it
type JitBlock<-H: Data> is Data:
  JitBlock{out: B.Octets, state: JitState<H>}

# bytes read, the state after them, and the deltas not used
type JitOut<-H: Data> is Data:
  JitOut{out: B.Octets, state: JitState<H>, rest: List<&2, W.W64>}

def JitBlock.out(~H: Data, b: JitBlock<H>) -> B.Octets:
  match b:
    case JitBlock{o, s}:
      o

def JitBlock.state(~H: Data, b: JitBlock<H>) -> JitState<H>:
  match b:
    case JitBlock{o, s}:
      s

def JitOut.out(~H: Data, r: JitOut<H>) -> B.Octets:
  match r:
    case JitOut{o, s, d}:
      o

def JitOut.state(~H: Data, r: JitOut<H>) -> JitState<H>:
  match r:
    case JitOut{o, s, d}:
      s

def JitOut.rest(~H: Data, r: JitOut<H>) -> List<&2, W.W64>:
  match r:
    case JitOut{o, s, d}:
      d

# a new state: an empty pool, the tests before any sample, p.prime blocks
# to discard
def Jitter.init(~H: Data, ~init: H, +p: JitParams) -> JitState<H>:
  JitState{init, Sk.JitStuck.new(), Ht.JitRct.new(), Ht.JitApt.new(), 0n, JitParams.prime(p)}

def Jitter.count(~H: Data, st: JitState<H>) -> Nat:
  match st:
    case JitState{pool, s, r, a, c, d}:
      c

# whether a health test has failed (for good)
def Jitter.failed(~H: Data, st: JitState<H>) -> Bool:
  match st:
    case JitState{pool, s, r, a, c, d}:
      Bool.or(Ht.JitRct.failed(r), Ht.JitApt.failed(a))

# whether a block can be taken: no health test has failed, and enough
# deltas have counted
def Jitter.can_block(~H: Data, +p: JitParams, +st: JitState<H>) -> Bool:
  Bool.and(Bool.not(Jitter.failed(~H, st)), Nat.is_le(JitParams.need(p), Jitter.count(~H, st)))

def jit.why.go(rf: Bool, af: Bool, +c: Nat, +n: Nat) -> JitError:
  match rf:
    case True{}:
      JitRctFailure{}
    case False{}:
      match af:
        case True{}:
          JitAptFailure{}
        case False{}:
          JitNotEnough{c, n}

# why a block cannot be taken
def Jitter.why(~H: Data, +p: JitParams, st: JitState<H>) -> JitError:
  match st:
    case JitState{pool, s, r, a, c, d}:
      jit.why.go(Ht.JitRct.failed(r), Ht.JitApt.failed(a), c, JitParams.need(p))

# ---------------------------------------------------------------- one delta

# the auxiliary data: the RCT's count, the APT's count, cutoff and window
# (four little-endian 32-bit words) and the APT's base (64 bits)
def jit.aux(+p: JitParams, r: Ht.JitRct, a: Ht.JitApt) -> B.Octets:
  +a2 = a
  B.Octets.of_list(B.append(B.le32(U32.from_nat(Ht.JitRct.count(r))), B.append(B.le32(U32.from_nat(Ht.JitApt.count(a2))), B.append(B.le32(U32.from_nat(JitParams.apt_cutoff(p))), B.append(B.le32(U32.from_nat(JitParams.apt_window(p))), B.le64(Ht.JitApt.base(a2)))))))

# the buffer one delta inserts: the delta, the domain separator, the
# digest of the auxiliary data, zeros to the hash's block size
def jit.buf(~bsize: Nat, ~digest: B.Octets -> B.Octets, +p: JitParams, +d: W.W64, aux: B.Octets) -> B.Octets:
  +dig = digest(aux)
  B.Octets.append(B.Octets.of_list(B.append(B.le64(d), [JitParams.domain(p)])), B.Octets.append(dig, B.Octets.zeros(Nat.sub(bsize, Nat.add(9n, B.Octets.len(dig))))))

def jit.count(stuck: Bool, c: Nat) -> Nat:
  match stuck:
    case True{}:
      c
    case False{}:
      1n+c

# the state after one delta
def Jitter.absorb(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, +p: JitParams, st: JitState<H>, +d: W.W64) -> JitState<H>:
  match st:
    case JitState{pool, +s, r, a, c, dis}:
      +r2 = Ht.JitRct.feed(JitParams.rct_cutoff(p), r, d)
      +a2 = Ht.JitApt.feed(JitParams.apt_window(p), JitParams.apt_cutoff(p), a, d)
      JitState{update(pool, jit.buf(~bsize, ~digest, p, d, jit.aux(p, r2, a2))), Sk.JitStuck.next(s, d), r2, a2, jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}

def jit.absorb_all(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, ds: List<&2, W.W64>, +p: JitParams, st: JitState<H>) -> JitState<H>:
  match ds:
    case Nil{}:
      st
    case Con{d, rest}:
      jit.absorb_all(~H, ~bsize, ~update, ~digest, rest, p, Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d))

# the state after deltas in order
def Jitter.absorb_all(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, +p: JitParams, st: JitState<H>, ds: List<&2, W.W64>) -> JitState<H>:
  jit.absorb_all(~H, ~bsize, ~update, ~digest, ds, p, st)

# ---------------------------------------------------------------- blocks

# the block, and the state after it: the pool starts again from the block
def jit.take(~H: Data, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, st: JitState<H>) -> JitBlock<H>:
  match st:
    case JitState{pool, s, r, a, c, dis}:
      +out = final(pool)
      JitBlock{out, JitState{update(init, out), s, r, a, 0n, dis}}

def jit.block.go(~H: Data, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ok: Bool, +p: JitParams, st: JitState<H>) -> Result<&2, &2, JitError, JitBlock<H>>:
  match ok:
    case True{}:
      Done{jit.take(~H, ~init, ~update, ~final, st)}
    case False{}:
      Fail{Jitter.why(~H, p, st)}

# a block, if one can be taken
def Jitter.block(~H: Data, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, +p: JitParams, +st: JitState<H>) -> Result<&2, &2, JitError, JitBlock<H>>:
  jit.block.go(~H, ~init, ~update, ~final, Jitter.can_block(~H, p, st), p, st)

# ---------------------------------------------------------------- reading bytes

# n bytes of a byte string, zeros past its end
def jit.pad(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match xs:
        case Nil{}:
          Con{0, jit.pad(m, Nil{})}
        case Con{x, t}:
          Con{x, jit.pad(m, t)}

def jit.fit(n: Nat, acc: B.Octets) -> B.Octets:
  B.Octets.of_list(jit.pad(n, B.Octets.to_list(acc)))

# bytes so far, and the state
type JitAcc<-H: Data> is Data:
  JitAcc{state: JitState<H>, acc: B.Octets}

def JitAcc.state(~H: Data, r: JitAcc<H>) -> JitState<H>:
  match r:
    case JitAcc{s, a}:
      s

def JitAcc.acc(~H: Data, r: JitAcc<H>) -> B.Octets:
  match r:
    case JitAcc{s, a}:
      a

def jit.keep(~H: Data, b: JitBlock<H>, acc: B.Octets) -> JitAcc<H>:
  match b:
    case JitBlock{out, st}:
      match st:
        case JitState{pool, s, r, a, c, dis}:
          match dis:
            case 0n:
              JitAcc{JitState{pool, s, r, a, c, 0n}, B.Octets.append(acc, out)}
            case 1n+k:
              JitAcc{JitState{pool, s, r, a, c, k}, acc}

# after a delta: a block when one can be taken, kept or discarded
def jit.emit(~H: Data, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ready: Bool, st: JitState<H>, acc: B.Octets) -> JitAcc<H>:
  match ready:
    case True{}:
      jit.keep(~H, jit.take(~H, ~init, ~update, ~final, st), acc)
    case False{}:
      JitAcc{st, acc}

def jit.end(~H: Data, done: Bool, failed: Bool, +p: JitParams, st: JitState<H>, acc: B.Octets, +n: Nat) -> Result<&2, &2, JitError, JitOut<H>>:
  match done:
    case True{}:
      Done{JitOut{jit.fit(n, acc), st, Nil{}}}
    case False{}:
      match failed:
        case True{}:
          Fail{Jitter.why(~H, p, st)}
        case False{}:
          Fail{JitNeedMore{B.Octets.len(acc)}}

def jit.go(~H: Data, ~bsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, ds: List<&2, W.W64>, done: Bool, failed: Bool, +p: JitParams, st: JitState<H>, acc: B.Octets, +n: Nat) -> Result<&2, &2, JitError, JitOut<H>>:
  match ds:
    case Nil{}:
      jit.end(~H, done, failed, p, st, acc, n)
    case Con{d, rest}:
      match done:
        case True{}:
          Done{JitOut{jit.fit(n, acc), st, Con{d, rest}}}
        case False{}:
          match failed:
            case True{}:
              Fail{Jitter.why(~H, p, st)}
            case False{}:
              +st1 = Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)
              +r = jit.emit(~H, ~init, ~update, ~final, Jitter.can_block(~H, p, st1), st1, acc)
              jit.go(~H, ~bsize, ~init, ~update, ~final, ~digest, rest, Nat.is_le(n, B.Octets.len(JitAcc.acc(~H, r))), Jitter.failed(~H, JitAcc.state(~H, r)), p, JitAcc.state(~H, r), JitAcc.acc(~H, r), n)

# n bytes from the deltas: blocks are taken as the deltas allow (the first
# p.prime of them discarded), and the bytes are their concatenation, cut to
# n; answers the bytes, the state, and the deltas left over. Fails with
# JitRctFailure or JitAptFailure when a health test fails, and with
# JitNeedMore when the deltas run out first.
def Jitter.read(~H: Data, ~bsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, +p: JitParams, +st: JitState<H>, ds: List<&2, W.W64>, +n: Nat) -> Result<&2, &2, JitError, JitOut<H>>:
  jit.go(~H, ~bsize, ~init, ~update, ~final, ~digest, ds, Nat.is_le(n, 0n), Jitter.failed(~H, st), p, st, B.Octets.empty(), n)

# n bytes from a new state
def Jitter.generate(~H: Data, ~bsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, +p: JitParams, ds: List<&2, W.W64>, +n: Nat) -> Result<&2, &2, JitError, JitOut<H>>:
  Jitter.read(~H, ~bsize, ~init, ~update, ~final, ~digest, p, Jitter.init(~H, ~init, p), ds, n)
