# CAST-256 (RFC 2612, The CAST-256 Encryption Algorithm, 1999), also called
# CAST6: a 128-bit block cipher with keys of 128, 160, 192, 224 or 256 bits,
# as a cipher for the 128-bit modes (~LcCast6Key, ~LcCast6.encrypt,
# ~LcCast6.decrypt).
#
# The block is four big-endian words A, B, C, D (a CmBlock). The forward
# quad-round Q(i) is
#   C ^= f1(D), B ^= f2(C), A ^= f3(B), D ^= f1(A)
# with key set i's masking and rotation keys, and QBAR(i) is the same four
# steps in reverse order; encryption is Q(0) .. Q(5), then QBAR(6) ..
# QBAR(11). f1, f2, f3 are CAST-128's round functions of types 1, 2, 3 over
# its S1 .. S4 (cast5.bend). The key schedule pads the key with zeros to
# eight words A .. H and runs 24 forward octaves W(i) on them, with the masks
# Tm (from 2^30 sqrt 2, stepping by 2^30 sqrt 3) and rotations Tr (from 19,
# stepping by 17 mod 32); after octaves 2i and 2i + 1, Kr(i) is the low 5
# bits of A, C, E, G and Km(i) is H, F, D, B.
#
# Each step XORs a function of one word into another, so it is undone by
# itself, and QBAR(i) undoes Q(i): decryption (the quad-rounds undone last
# to first, RFC 2612's decryption) undoes encryption for every key and block,
# whatever the S-boxes hold.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ../cipher-core/cipher-core.bend as L
import ../cast5/cast5.bend as C5

# A quad-round's key set (internal)
type LcCast6Ks is Data:
  LcCast6Ks{m0: U32, m1: U32, m2: U32, m3: U32, r0: U32, r1: U32, r2: U32, r3: U32, t: C5.LcCastTabs}

# the four steps of Q, each undone by itself
def c6.sc(k: LcCast6Ks, s: M.CmBlock) -> M.CmBlock:
  match k:
    case LcCast6Ks{m0, m1, m2, m3, r0, r1, r2, r3, t}:
      match s:
        case M.CmBlock{a, b, c, +d}:
          M.CmBlock{a, b, U32.xor(c, C5.cast.f(C5.LcCastF1{}, t, d, m0, r0)), d}

def c6.sb(k: LcCast6Ks, s: M.CmBlock) -> M.CmBlock:
  match k:
    case LcCast6Ks{m0, m1, m2, m3, r0, r1, r2, r3, t}:
      match s:
        case M.CmBlock{a, b, +c, d}:
          M.CmBlock{a, U32.xor(b, C5.cast.f(C5.LcCastF2{}, t, c, m1, r1)), c, d}

def c6.sa(k: LcCast6Ks, s: M.CmBlock) -> M.CmBlock:
  match k:
    case LcCast6Ks{m0, m1, m2, m3, r0, r1, r2, r3, t}:
      match s:
        case M.CmBlock{a, +b, c, d}:
          M.CmBlock{U32.xor(a, C5.cast.f(C5.LcCastF3{}, t, b, m2, r2)), b, c, d}

def c6.sd(k: LcCast6Ks, s: M.CmBlock) -> M.CmBlock:
  match k:
    case LcCast6Ks{m0, m1, m2, m3, r0, r1, r2, r3, t}:
      match s:
        case M.CmBlock{+a, b, c, d}:
          M.CmBlock{a, b, c, U32.xor(d, C5.cast.f(C5.LcCastF1{}, t, a, m3, r3))}

# Q and QBAR
def c6.q(+k: LcCast6Ks, s: M.CmBlock) -> M.CmBlock:
  c6.sd(k, c6.sa(k, c6.sb(k, c6.sc(k, s))))

def c6.qbar(+k: LcCast6Ks, s: M.CmBlock) -> M.CmBlock:
  c6.sc(k, c6.sb(k, c6.sa(k, c6.sd(k, s))))

# The steps of the cipher (internal): Q (fwd True) or QBAR with a key set
type LcCast6Op is Data:
  LcCast6Op{fwd: Bool, k: LcCast6Ks}

def c6.op(o: LcCast6Op, s: M.CmBlock) -> M.CmBlock:
  match o:
    case LcCast6Op{fwd, k}:
      match fwd:
        case True{}:
          c6.q(k, s)
        case False{}:
          c6.qbar(k, s)

def c6.unop(o: LcCast6Op, s: M.CmBlock) -> M.CmBlock:
  match o:
    case LcCast6Op{fwd, k}:
      match fwd:
        case True{}:
          c6.qbar(k, s)
        case False{}:
          c6.q(k, s)

def c6.run(os: List<&2, LcCast6Op>, s: M.CmBlock) -> M.CmBlock:
  match os:
    case Nil{}:
      s
    case Con{o, t}:
      c6.run(t, c6.op(o, s))

def c6.unrun(os: List<&2, LcCast6Op>, s: M.CmBlock) -> M.CmBlock:
  match os:
    case Nil{}:
      s
    case Con{o, t}:
      c6.unop(o, c6.unrun(t, s))

# The key schedule (RFC 2612, 2.4)

# word i of xs replaced by v
def c6.set(xs: List<&2, U32>, i: Nat, v: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match i:
        case 0n:
          Con{v, t}
        case 1n+j:
          Con{x, c6.set(t, j, v)}

# KAPPA (the eight words A .. H) and the next Tm and Tr
type LcCast6Kst is Data:
  LcCast6Kst{k: List<&2, U32>, cm: U32, cr: U32}

# one step of an octave: word dst ^= f_ty(word src), with the next Tm, Tr
def c6.w(+t: C5.LcCastTabs, ty: C5.LcCastTy, +dst: Nat, src: Nat, st: LcCast6Kst) -> LcCast6Kst:
  match st:
    case LcCast6Kst{+k, +cm, +cr}:
      LcCast6Kst{c6.set(k, dst, U32.xor(L.lc.at(k, dst), C5.cast.f(ty, t, L.lc.at(k, src), cm, cr))), U32.add(cm, 1859775393), U32.and(31, U32.add(cr, 17))}

# the forward octave W
def c6.octave(+t: C5.LcCastTabs, st: LcCast6Kst) -> LcCast6Kst:
  +s1 = c6.w(t, C5.LcCastF1{}, 6n, 7n, st)
  +s2 = c6.w(t, C5.LcCastF2{}, 5n, 6n, s1)
  +s3 = c6.w(t, C5.LcCastF3{}, 4n, 5n, s2)
  +s4 = c6.w(t, C5.LcCastF1{}, 3n, 4n, s3)
  +s5 = c6.w(t, C5.LcCastF2{}, 2n, 3n, s4)
  +s6 = c6.w(t, C5.LcCastF3{}, 1n, 2n, s5)
  +s7 = c6.w(t, C5.LcCastF1{}, 0n, 1n, s6)
  c6.w(t, C5.LcCastF2{}, 7n, 0n, s7)

# the key set read from KAPPA: Km = H, F, D, B and Kr = A, C, E, G (low 5 bits)
def c6.ks(+t: C5.LcCastTabs, +k: List<&2, U32>) -> LcCast6Ks:
  LcCast6Ks{L.lc.at(k, 7n), L.lc.at(k, 5n), L.lc.at(k, 3n), L.lc.at(k, 1n), U32.and(31, L.lc.at(k, 0n)), U32.and(31, L.lc.at(k, 2n)), U32.and(31, L.lc.at(k, 4n)), U32.and(31, L.lc.at(k, 6n)), t}

# the key set read from KAPPA after an octave pair
def c6.ks.of(+t: C5.LcCastTabs, st: LcCast6Kst) -> LcCast6Ks:
  match st:
    case LcCast6Kst{+k, cm, cr}:
      c6.ks(t, k)

# the steps from quad-round i on: Q up to i = 5, then QBAR
def c6.ops(n: Nat, +i: Nat, +t: C5.LcCastTabs, st: LcCast6Kst) -> List<&2, LcCast6Op>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +st2 = c6.octave(t, c6.octave(t, st))
      Con{LcCast6Op{Nat.is_lt(i, 6n), c6.ks.of(t, st2)}, c6.ops(p, Nat.add(i, 1n), t, st2)}

# A CAST-256 key: the steps of the cipher (opaque; built by LcCast6.key)
type LcCast6Key is Data:
  LcCast6Key{ops: List<&2, LcCast6Op>}

# the eight key words of a key padded to 32 bytes
def c6.words(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Con{L.lc.be(a, b, c, d), c6.words(t)}
    case _:
      Nil{}

def c6.key.pick(ok: Bool, +n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcCast6Key>:
  match ok:
    case True{}:
      Done{LcCast6Key{c6.ops(12n, 0n, C5.cast.tables(), LcCast6Kst{c6.words(B.append(xs, B.zeros(Nat.sub(32n, n)))), 1518500249, 19})}}
    case False{}:
      Fail{L.LcBadKeyLength{n}}

# The cipher

# a key of 16, 20, 24, 28 or 32 bytes
def LcCast6.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcCast6Key>:
  +xs = B.Octets.to_list(o)
  +n = B.len(xs)
  c6.key.pick(Bool.and(Bool.and(Nat.is_le(16n, n), Nat.is_le(n, 32n)), Nat.is_eq(Nat.mod(n, 4n), 0n)), n, xs)

def LcCast6.encrypt(k: LcCast6Key, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcCast6Key{ops}:
      c6.run(ops, b)

def LcCast6.decrypt(k: LcCast6Key, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcCast6Key{ops}:
      c6.unrun(ops, b)
