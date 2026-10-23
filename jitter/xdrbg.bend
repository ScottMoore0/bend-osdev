# The XDRBG conditioner over any XOF: the 2026 design of jitterentropy
# (Müller, "CPU Time Jitter Based Non-Physical True Random Number
# Generator", 4 May 2026, section 3.1.1), on the XDRBG of Kelsey, Lucks and
# Müller ("XDRBG: A Proposed Deterministic Random Bit Generator Based on Any
# XOF", IACR ToSC 2024(1), 5-34, Algorithm 2 and appendix B).
#
# The pool collects the seed: each delta's buffer (jitter.bend's jit.buf) is
# fed to the XOF as it arrives. A block then
#   (re)seeds:  V <- XOF(encode(seed, alpha, 0), |V|) for the first block,
#               V <- XOF(encode(V' || seed, alpha, 1), |V|) after it, V' the
#               state the block before left;
#   generates:  T <- XOF(encode(V, alpha, 2), l + |V|), the new state V the
#               first |V| bytes of T, the block the last l bytes;
# and the next pool starts from the new V, ready to reseed. encode(S, alpha,
# n) is S || alpha || (n * 85 + |alpha|) as one byte (ToSC appendix B,
# |alpha| at most 84 bytes). The first |V| and the last l bytes of T are read
# as two reads of the same XOF output (shake.bend's XOF interface).
#
# As a conditioner for the core (jitter.bend's JitCore.*), over an XOF
# (~X, ~xinit, ~xupdate, ~xread) and parameters ~xp:
#   ~JitXdrbgPool<X>, ~JitXdrbg.init(~X, ~xinit),
#   ~JitXdrbg.update(~X, ~xupdate), ~JitXdrbg.take(~X, ~xinit, ~xupdate,
#   ~xread, ~xp)
# xdrbg256.bend fills in SHAKE256 and the default parameters.
import Base
import ../bytes/bytes.bend as B
import ./jitter.bend as J

# |V| and l in bytes, and the additional input alpha (open)
type JitXdrbgParams is Data:
  JitXdrbgParams{vsize: Nat, outsize: Nat, alpha: B.Octets}

# XDRBG-256 as jitterentropy 3.7.0 uses it (section 3.1.1): |V| = 512 bits,
# l = 256 bits, alpha empty (a NULL buffer)
def JitXdrbgParams.default() -> JitXdrbgParams:
  JitXdrbgParams{64n, 32n, B.Octets.empty()}

def JitXdrbgParams.vsize(xp: JitXdrbgParams) -> Nat:
  match xp:
    case JitXdrbgParams{v, o, a}:
      v

def JitXdrbgParams.outsize(xp: JitXdrbgParams) -> Nat:
  match xp:
    case JitXdrbgParams{v, o, a}:
      o

def JitXdrbgParams.alpha(xp: JitXdrbgParams) -> B.Octets:
  match xp:
    case JitXdrbgParams{v, o, a}:
      a

# The pool (opaque): the XOF's state, and whether the next block reseeds
# (the XOF has absorbed the state V' before the seed) or instantiates
type JitXdrbgPool<-X: Data> is Data:
  JitXdrbgPool{xof: X, reseed: Bool}

def JitXdrbg.init(~X: Data, ~xinit: X) -> JitXdrbgPool<X>:
  JitXdrbgPool{xinit, False{}}

# the pool after more seed bytes
def JitXdrbg.update(~X: Data, ~xupdate: X -> B.Octets -> X, pool: JitXdrbgPool<X>, o: B.Octets) -> JitXdrbgPool<X>:
  match pool:
    case JitXdrbgPool{x, r}:
      JitXdrbgPool{xupdate(x, o), r}

# what encode appends to S: alpha, and n * 85 + |alpha| as one byte
def jit.xdrbg.encode(+alpha: B.Octets, n: Nat) -> B.Octets:
  B.Octets.append(alpha, B.Octets.of_list([U32.from_nat(Nat.add(Nat.mul(n, 85n), B.Octets.len(alpha)))]))

# encode's n for a (re)seed: 0 to instantiate, 1 to reseed
def jit.xdrbg.seed_n(r: Bool) -> Nat:
  match r:
    case False{}:
      0n
    case True{}:
      1n

# the block step: (re)seed, generate, and start the next pool from V
def JitXdrbg.take(~X: Data, ~xinit: X, ~xupdate: X -> B.Octets -> X, ~xread: X -> Nat -> Nat -> B.Octets, ~xp: JitXdrbgParams, pool: JitXdrbgPool<X>) -> J.JitTaken<JitXdrbgPool<X>>:
  match pool:
    case JitXdrbgPool{x, r}:
      +vs = JitXdrbgParams.vsize(xp)
      +al = JitXdrbgParams.alpha(xp)
      +v = xread(xupdate(x, jit.xdrbg.encode(al, jit.xdrbg.seed_n(r))), 0n, vs)
      +g = xupdate(xupdate(xinit, v), jit.xdrbg.encode(al, 2n))
      J.JitTaken{xread(g, vs, JitXdrbgParams.outsize(xp)), JitXdrbgPool{xupdate(xinit, xread(g, 0n, vs)), True{}}}
