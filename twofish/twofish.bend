# Twofish (B. Schneier, J. Kelsey, D. Whiting, D. Wagner, C. Hall, N.
# Ferguson, "Twofish: A 128-Bit Block Cipher", AES submission, 1998): a
# 128-bit block cipher with 128-, 192- or 256-bit keys, as a cipher for
# the 128-bit modes (~LcTwofishKey, ~LcTwofish.encrypt, ~LcTwofish.decrypt).
#
# Twofish reads the block as four little-endian words; a CmBlock holds
# big-endian words, so the cipher swaps each word's bytes on the way in and
# out. The key schedule turns the key into a list of steps, each one
# invertible: the byte swap, the whitening XORs, the sixteen rounds
#   (R0, R1, R2, R3) -> ((R2 xor F0) >>> 1, (R3 <<< 1) xor F1, R0, R1)
# with (F0, F1) = F(R0, R1, r), and the swap that undoes the last round's
# exchange of halves. Encryption runs the steps first to last; decryption
# undoes them last to first, the same function as the paper's decryption, and
# decrypt(encrypt(b)) == b is provable for every key and block: a round is
# undone whatever F is. The byte swaps and the 1-bit rotations a round undoes
# are computed on bits (cipher-core.bend), so a proof computes through
# them; F (the key-dependent S-boxes, the MDS matrix, the PHT) and the key
# schedule use native word operations.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ../cipher-core/cipher-core.bend as L

# The permutations q0 and q1 (section 4.3.5): their 4-bit tables t0 .. t3

def tf.q0.t() -> List<&2, U32>:
  [8, 1, 7, 13, 6, 15, 3, 2, 0, 11, 5, 9, 14, 12, 10, 4,
    14, 12, 11, 8, 1, 2, 3, 5, 15, 4, 10, 6, 7, 0, 9, 13,
    11, 10, 5, 14, 6, 13, 9, 0, 12, 8, 15, 3, 2, 4, 7, 1,
    13, 7, 15, 4, 1, 2, 6, 14, 9, 11, 3, 0, 8, 5, 12, 10]

def tf.q1.t() -> List<&2, U32>:
  [2, 8, 11, 13, 15, 7, 6, 14, 3, 1, 9, 4, 0, 10, 12, 5,
    1, 14, 2, 11, 4, 12, 3, 7, 6, 13, 10, 5, 15, 9, 0, 8,
    4, 12, 7, 5, 1, 6, 9, 10, 0, 14, 13, 8, 2, 11, 3, 15,
    11, 9, 5, 1, 12, 3, 13, 14, 6, 4, 7, 15, 2, 0, 8, 10]

# entry x of table i (0 to 3) of ts
def tf.t(+ts: List<&2, U32>, i: Nat, +x: U32) -> U32:
  L.lc.at(ts, Nat.add(Nat.mul(16n, i), U32.to_nat(x)))

# a 4-bit value rotated right by one bit
def tf.ror4(+x: U32) -> U32:
  U32.and(15, U32.or(U32.shr(x), U32.shln(x, 3n)))

def tf.q.half(+a: U32, +b: U32) -> U32:
  U32.xor(U32.xor(a, tf.ror4(b)), U32.and(15, U32.shln(a, 3n)))

def tf.q.go(+ts: List<&2, U32>, +a2: U32, +b2: U32) -> U32:
  U32.add(U32.mul(16, tf.t(ts, 3n, tf.q.half(a2, b2))), tf.t(ts, 2n, U32.xor(a2, b2)))

# q(x) from its tables
def tf.q.raw(+ts: List<&2, U32>, +x: U32) -> U32:
  +a0 = U32.shrn(x, 4n)
  +b0 = U32.and(15, x)
  tf.q.go(ts, tf.t(ts, 0n, U32.xor(a0, b0)), tf.t(ts, 1n, tf.q.half(a0, b0)))

def tf.gen(~f: U32 -> U32, n: Nat, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{f(i), tf.gen(~f, p, U32.add(i, 1))}

def tf.q0() -> L.LcTab:
  L.lc.tab(8n, tf.gen(~(x => tf.q.raw(tf.q0.t(), x)), 256n, 0))

def tf.q1() -> L.LcTab:
  L.lc.tab(8n, tf.gen(~(x => tf.q.raw(tf.q1.t(), x)), 256n, 0))

# The tables, built once per key (internal): q0, q1 and the MDS columns
type LcTfTabs is Data:
  LcTfTabs{q0: L.LcTab, q1: L.LcTab, m0: L.LcTab, m1: L.LcTab, m2: L.LcTab, m3: L.LcTab}

def tf.q(t: LcTfTabs, one: Bool, +x: U32) -> U32:
  match t:
    case LcTfTabs{q0, q1, m0, m1, m2, m3}:
      match one:
        case True{}:
          L.lc.tab.get(8n, q1, x)
        case False{}:
          L.lc.tab.get(8n, q0, x)

# GF(2^8) multiplication modulo the polynomial poly (with its x^8 term)

def tf.xt(+a: U32, +poly: U32) -> U32:
  U32.and(255, U32.xor(U32.shl(a), U32.and(poly, U32.sub(0, U32.and(1, U32.shrn(a, 7n))))))

def tf.gmul.go(n: Nat, +a: U32, +b: U32, +poly: U32, p: U32) -> U32:
  match n:
    case 0n:
      p
    case 1n+q:
      tf.gmul.go(q, tf.xt(a, poly), U32.shr(b), poly, U32.xor(p, U32.and(a, U32.sub(0, U32.and(1, b)))))

def tf.gmul(+a: U32, +b: U32, +poly: U32) -> U32:
  tf.gmul.go(8n, a, b, poly, 0)

# The MDS matrix (section 4.2), over GF(2^8) modulo x^8 + x^6 + x^5 + x^3 + 1;
# column j as a table: entry x is the word (MDS[0][j] x, .., MDS[3][j] x),
# row 0 in the low byte

def tf.mds.m() -> List<&2, U32>:
  [1, 239, 91, 91,
    91, 239, 239, 1,
    239, 91, 1, 239,
    239, 1, 239, 91]

def tf.mds.col(+j: Nat, +x: U32) -> U32:
  +m = tf.mds.m()
  L.lc.le(tf.gmul(L.lc.at(m, j), x, 105), tf.gmul(L.lc.at(m, Nat.add(4n, j)), x, 105), tf.gmul(L.lc.at(m, Nat.add(8n, j)), x, 105), tf.gmul(L.lc.at(m, Nat.add(12n, j)), x, 105))

def tf.mds0() -> L.LcTab:
  L.lc.tab(8n, tf.gen(~(x => tf.mds.col(0n, x)), 256n, 0))

def tf.mds1() -> L.LcTab:
  L.lc.tab(8n, tf.gen(~(x => tf.mds.col(1n, x)), 256n, 0))

def tf.mds2() -> L.LcTab:
  L.lc.tab(8n, tf.gen(~(x => tf.mds.col(2n, x)), 256n, 0))

def tf.mds3() -> L.LcTab:
  L.lc.tab(8n, tf.gen(~(x => tf.mds.col(3n, x)), 256n, 0))

def tf.tables() -> LcTfTabs:
  LcTfTabs{tf.q0(), tf.q1(), tf.mds0(), tf.mds1(), tf.mds2(), tf.mds3()}

def tf.mds(t: LcTfTabs, +y: U32) -> U32:
  match t:
    case LcTfTabs{q0, q1, m0, m1, m2, m3}:
      U32.xor(U32.xor(L.lc.tab.get(8n, m0, L.lc.byte(y, 0n)), L.lc.tab.get(8n, m1, L.lc.byte(y, 1n))), U32.xor(L.lc.tab.get(8n, m2, L.lc.byte(y, 2n)), L.lc.tab.get(8n, m3, L.lc.byte(y, 3n))))

# The function h (section 4.3.2)

# byte i of x through q (q1 if p_i), then XOR byte i of l
def tf.stage(+t: LcTfTabs, p0: Bool, p1: Bool, p2: Bool, p3: Bool, +x: U32, +l: U32) -> U32:
  L.lc.le(U32.xor(tf.q(t, p0, L.lc.byte(x, 0n)), L.lc.byte(l, 0n)), U32.xor(tf.q(t, p1, L.lc.byte(x, 1n)), L.lc.byte(l, 1n)), U32.xor(tf.q(t, p2, L.lc.byte(x, 2n)), L.lc.byte(l, 2n)), U32.xor(tf.q(t, p3, L.lc.byte(x, 3n)), L.lc.byte(l, 3n)))

# the stages every key length shares: with L_1, with L_0, then q alone
def tf.h2(+t: LcTfTabs, +x: U32, +l0: U32, +l1: U32) -> U32:
  tf.mds(t, tf.stage(t, True{}, False{}, True{}, False{}, tf.stage(t, False{}, False{}, True{}, True{}, tf.stage(t, False{}, True{}, False{}, True{}, x, l1), l0), 0))

def tf.h3(+t: LcTfTabs, +x: U32, +l0: U32, +l1: U32, +l2: U32) -> U32:
  tf.h2(t, tf.stage(t, True{}, True{}, False{}, False{}, x, l2), l0, l1)

def tf.h4(+t: LcTfTabs, +x: U32, +l0: U32, +l1: U32, +l2: U32, +l3: U32) -> U32:
  tf.h3(t, tf.stage(t, True{}, False{}, False{}, True{}, x, l3), l0, l1, l2)

# h(X, L) for L = L_0 .. L_(k-1), k = 2, 3 or 4
def tf.h(+t: LcTfTabs, +x: U32, l: List<&2, U32>) -> U32:
  match l:
    case Con{l0, Con{l1, Nil{}}}:
      tf.h2(t, x, l0, l1)
    case Con{l0, Con{l1, Con{l2, Nil{}}}}:
      tf.h3(t, x, l0, l1, l2)
    case Con{l0, Con{l1, Con{l2, Con{l3, more}}}}:
      tf.h4(t, x, l0, l1, l2, l3)
    case _:
      0

# The function F (section 4.3): g(X) = h(X, S), then the PHT and the round
# subkeys K_(2r+8), K_(2r+9); F0 and F1 as an LcBlock64

def tf.f(+t: LcTfTabs, +s: List<&2, U32>, r0: U32, r1: U32, ka: U32, kb: U32) -> L.LcBlock64:
  +t0 = tf.h(t, r0, s)
  +t1 = tf.h(t, L.lc.rotl(r1, 8n), s)
  L.LcBlock64{U32.add(U32.add(t0, t1), ka), U32.add(U32.add(t0, U32.add(t1, t1)), kb)}

def tf.f0(x: L.LcBlock64) -> U32:
  match x:
    case L.LcBlock64{a, b}:
      a

def tf.f1(x: L.LcBlock64) -> U32:
  match x:
    case L.LcBlock64{a, b}:
      b

# The steps of the cipher (internal)
type LcTfOp is Data:
  LcTfBswap{}
  LcTfWhite{k: M.CmBlock}
  LcTfRound{t: LcTfTabs, s: List<&2, U32>, ka: U32, kb: U32}
  LcTfSwap{}

def tf.op(o: LcTfOp, s: M.CmBlock) -> M.CmBlock:
  match o:
    case LcTfBswap{}:
      match s:
        case M.CmBlock{a, b, c, d}:
          M.CmBlock{L.lc.bswap.bits(a), L.lc.bswap.bits(b), L.lc.bswap.bits(c), L.lc.bswap.bits(d)}
    case LcTfWhite{k}:
      M.CmBlock.xor(s, k)
    case LcTfRound{tb, sk, ka, kb}:
      match s:
        case M.CmBlock{+r0, +r1, r2, r3}:
          +f = tf.f(tb, sk, r0, r1, ka, kb)
          M.CmBlock{L.lc.rotl31.bits(U32.xor(r2, tf.f0(f))), U32.xor(L.lc.rotl1.bits(r3), tf.f1(f)), r0, r1}
    case LcTfSwap{}:
      match s:
        case M.CmBlock{a, b, c, d}:
          M.CmBlock{c, d, a, b}

# the step undone
def tf.unop(o: LcTfOp, s: M.CmBlock) -> M.CmBlock:
  match o:
    case LcTfBswap{}:
      match s:
        case M.CmBlock{a, b, c, d}:
          M.CmBlock{L.lc.bswap.bits(a), L.lc.bswap.bits(b), L.lc.bswap.bits(c), L.lc.bswap.bits(d)}
    case LcTfWhite{k}:
      M.CmBlock.xor(s, k)
    case LcTfRound{tb, sk, ka, kb}:
      match s:
        case M.CmBlock{a, b, +c, +d}:
          +f = tf.f(tb, sk, c, d, ka, kb)
          M.CmBlock{c, d, U32.xor(L.lc.rotl1.bits(a), tf.f0(f)), L.lc.rotl31.bits(U32.xor(b, tf.f1(f)))}
    case LcTfSwap{}:
      match s:
        case M.CmBlock{a, b, c, d}:
          M.CmBlock{c, d, a, b}

def tf.run(os: List<&2, LcTfOp>, s: M.CmBlock) -> M.CmBlock:
  match os:
    case Nil{}:
      s
    case Con{o, t}:
      tf.run(t, tf.op(o, s))

def tf.unrun(os: List<&2, LcTfOp>, s: M.CmBlock) -> M.CmBlock:
  match os:
    case Nil{}:
      s
    case Con{o, t}:
      tf.unop(o, tf.unrun(t, s))

# The key schedule (section 4.3)

# the little-endian words of the key bytes xs, every other one from word i
def tf.words(n: Nat, +xs: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +j = Nat.mul(4n, i)
      Con{L.lc.le(L.lc.at(xs, j), L.lc.at(xs, Nat.add(j, 1n)), L.lc.at(xs, Nat.add(j, 2n)), L.lc.at(xs, Nat.add(j, 3n))), tf.words(p, xs, Nat.add(i, 2n))}

# The RS matrix (section 4.3), over GF(2^8) modulo x^8 + x^6 + x^3 + x^2 + 1
def tf.rs() -> List<&2, U32>:
  [1, 164, 85, 135, 90, 88, 219, 158,
    164, 86, 130, 243, 30, 198, 104, 229,
    2, 161, 252, 193, 71, 174, 61, 25,
    164, 85, 135, 90, 88, 219, 158, 3]

# row r of RS times the 8 key bytes from byte j
def tf.rs.row(n: Nat, +xs: List<&2, U32>, +r: Nat, +j: Nat, +c: Nat, acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      tf.rs.row(p, xs, r, j, Nat.add(c, 1n), U32.xor(acc, tf.gmul(L.lc.at(tf.rs(), Nat.add(Nat.mul(8n, r), c)), L.lc.at(xs, Nat.add(j, c)), 77)))

# S_i: RS times key bytes 8i .. 8i + 7
def tf.s_word(+xs: List<&2, U32>, +i: Nat) -> U32:
  +j = Nat.mul(8n, i)
  L.lc.le(tf.rs.row(8n, xs, 0n, j, 0n, 0), tf.rs.row(8n, xs, 1n, j, 0n, 0), tf.rs.row(8n, xs, 2n, j, 0n, 0), tf.rs.row(8n, xs, 3n, j, 0n, 0))

# S = (S_(k-1), .., S_0), the k words of the key-dependent S-boxes
def tf.svec(n: Nat, +xs: List<&2, U32>, +i: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      tf.svec(p, xs, Nat.add(i, 1n), Con{tf.s_word(xs, i), acc})

# K_(2i) and K_(2i+1) as an LcBlock64
def tf.kpair(+t: LcTfTabs, +me: List<&2, U32>, +mo: List<&2, U32>, +i: U32) -> L.LcBlock64:
  +a = tf.h(t, U32.mul(U32.mul(2, i), 16843009), me)
  +b = L.lc.rotl(tf.h(t, U32.mul(U32.add(U32.mul(2, i), 1), 16843009), mo), 8n)
  L.LcBlock64{U32.add(a, b), L.lc.rotl(U32.add(a, U32.add(b, b)), 9n)}

# the rounds' steps from round r, with the pairs K_(2r+8), K_(2r+9) in ks
def tf.rounds(ks: List<&2, L.LcBlock64>, +t: LcTfTabs, +s: List<&2, U32>) -> List<&2, LcTfOp>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{L.LcBlock64{a, b}, rest}:
      Con{LcTfRound{t, s, a, b}, tf.rounds(rest, t, s)}

def tf.kpairs(n: Nat, +t: LcTfTabs, +me: List<&2, U32>, +mo: List<&2, U32>, +i: U32) -> List<&2, L.LcBlock64>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{tf.kpair(t, me, mo, i), tf.kpairs(p, t, me, mo, U32.add(i, 1))}

def tf.white.le(a: L.LcBlock64, b: L.LcBlock64) -> LcTfOp:
  match a b:
    case L.LcBlock64{k0, k1} L.LcBlock64{k2, k3}:
      LcTfWhite{M.CmBlock{k0, k1, k2, k3}}

def tf.append(xs: List<&2, LcTfOp>, ys: List<&2, LcTfOp>) -> List<&2, LcTfOp>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, tf.append(t, ys)}

# the steps from the subkey pairs (K_0, K_1) .. (K_38, K_39)
def tf.ops(ks: List<&2, L.LcBlock64>, +t: LcTfTabs, +s: List<&2, U32>) -> List<&2, LcTfOp>:
  match ks:
    case Con{p0, Con{p1, Con{p2, Con{p3, rest}}}}:
      Con{LcTfBswap{}, Con{tf.white.le(p0, p1), tf.append(tf.rounds(rest, t, s), [LcTfSwap{}, tf.white.le(p2, p3), LcTfBswap{}])}}
    case _:
      Nil{}

# A Twofish key: the steps of the cipher (opaque; built by LcTwofish.key)
type LcTwofishKey is Data:
  LcTwofishKey{ops: List<&2, LcTfOp>}

# the key from k = 2, 3 or 4 64-bit words of key bytes xs
def tf.key(+k: Nat, +xs: List<&2, U32>) -> LcTwofishKey:
  +t = tf.tables()
  LcTwofishKey{tf.ops(tf.kpairs(20n, t, tf.words(k, xs, 0n), tf.words(k, xs, 1n), 0), t, tf.svec(k, xs, 0n, Nil{}))}

def tf.key.pick(n16: Bool, n24: Bool, n32: Bool, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcTwofishKey>:
  match n16 n24 n32:
    case True{} _ _:
      Done{tf.key(2n, xs)}
    case False{} True{} _:
      Done{tf.key(3n, xs)}
    case False{} False{} True{}:
      Done{tf.key(4n, xs)}
    case False{} False{} False{}:
      Fail{L.LcBadKeyLength{B.len(xs)}}

# The cipher

# a 16-, 24- or 32-byte key (Twofish-128, -192, -256, by its length)
def LcTwofish.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcTwofishKey>:
  +xs = B.Octets.to_list(o)
  +n = B.len(xs)
  tf.key.pick(Nat.is_eq(n, 16n), Nat.is_eq(n, 24n), Nat.is_eq(n, 32n), xs)

# the key padded with zero bytes to 16, 24 or 32 bytes (section 4.3: keys
# shorter than 256 bits are padded with zeros to the next defined length)
def tf.pad.pick(n16: Bool, n24: Bool, n32: Bool, +n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcTwofishKey>:
  match n16 n24 n32:
    case True{} _ _:
      Done{tf.key(2n, B.append(xs, B.zeros(Nat.sub(16n, n))))}
    case False{} True{} _:
      Done{tf.key(3n, B.append(xs, B.zeros(Nat.sub(24n, n))))}
    case False{} False{} True{}:
      Done{tf.key(4n, B.append(xs, B.zeros(Nat.sub(32n, n))))}
    case False{} False{} False{}:
      Fail{L.LcBadKeyLength{n}}

# a key of 1 to 32 bytes, zero-padded as the specification says
def LcTwofish.key_padded(o: B.Octets) -> Result<&2, &2, L.LcError, LcTwofishKey>:
  +xs = B.Octets.to_list(o)
  +n = B.len(xs)
  tf.pad.pick(Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, 16n)), Nat.is_le(n, 24n), Nat.is_le(n, 32n), n, xs)

def LcTwofish.encrypt(k: LcTwofishKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcTwofishKey{ops}:
      tf.run(ops, b)

def LcTwofish.decrypt(k: LcTwofishKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcTwofishKey{ops}:
      tf.unrun(ops, b)
