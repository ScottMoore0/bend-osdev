# Camellia (RFC 3713, A Description of the Camellia Encryption Algorithm,
# 2004): a 128-bit block cipher with 128-, 192- or 256-bit keys, as a cipher
# for cipher-modes' modes (~LcCamelliaKey, ~LcCamellia.encrypt,
# ~LcCamellia.decrypt).
#
# The state is the block as a CmBlock: D1 is its first two words, D2 its last
# two. The key schedule turns the key into a list of steps, each one
# invertible: the whitening XORs, the Feistel rounds (D2 ^= F(D1, k), then
# D1 ^= F(D2, k)), the FL / FL^-1 layers, and the final swap of D1 and D2.
# Encryption runs the steps first to last; decryption undoes them last to
# first. That is the same function as RFC 3713's decryption with the
# subkeys reversed, and it makes decrypt(encrypt(b)) == b provable for every
# key and block: each step is undone whatever F is.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-core/cipher-core.bend as L

# SBOX1 (RFC 3713, 2.4.4); SBOX2, SBOX3 and SBOX4 are derived from it
def cam.sbox1.list() -> List<&2, U32>:
  [112, 130, 44, 236, 179, 39, 192, 229, 228, 133, 87, 53, 234, 12, 174, 65,
    35, 239, 107, 147, 69, 25, 165, 33, 237, 14, 79, 78, 29, 101, 146, 189,
    134, 184, 175, 143, 124, 235, 31, 206, 62, 48, 220, 95, 94, 197, 11, 26,
    166, 225, 57, 202, 213, 71, 93, 61, 217, 1, 90, 214, 81, 86, 108, 77,
    139, 13, 154, 102, 251, 204, 176, 45, 116, 18, 43, 32, 240, 177, 132, 153,
    223, 76, 203, 194, 52, 126, 118, 5, 109, 183, 169, 49, 209, 23, 4, 215,
    20, 88, 58, 97, 222, 27, 17, 28, 50, 15, 156, 22, 83, 24, 242, 34,
    254, 68, 207, 178, 195, 181, 122, 145, 36, 8, 232, 168, 96, 252, 105, 80,
    170, 208, 160, 125, 161, 137, 98, 151, 84, 91, 30, 149, 224, 255, 100, 210,
    16, 196, 0, 72, 163, 247, 117, 219, 138, 3, 230, 218, 9, 63, 221, 148,
    135, 92, 131, 2, 205, 74, 144, 51, 115, 103, 246, 243, 157, 127, 191, 226,
    82, 155, 216, 38, 200, 55, 198, 59, 129, 150, 111, 75, 19, 190, 99, 46,
    233, 121, 167, 140, 159, 110, 188, 142, 41, 245, 249, 182, 47, 253, 180, 89,
    120, 152, 6, 106, 231, 70, 113, 186, 212, 37, 171, 66, 136, 162, 141, 250,
    114, 7, 185, 85, 248, 238, 172, 10, 54, 73, 42, 104, 60, 56, 241, 164,
    64, 40, 211, 123, 187, 201, 67, 193, 21, 227, 173, 244, 119, 199, 128, 158]

# a byte rotated left by n
def cam.rotl8(+x: U32, +n: Nat) -> U32:
  U32.and(255, U32.or(U32.shln(x, n), U32.shrn(x, Nat.sub(8n, n))))

# the entries of a table for x = i, i + 1, .., i + n - 1
def cam.gen(~f: U32 -> U32, n: Nat, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{f(i), cam.gen(~f, p, U32.add(i, 1))}

def cam.s1.raw(+x: U32) -> U32:
  L.lc.at(cam.sbox1.list(), U32.to_nat(x))

def cam.s1() -> L.LcTab:
  L.lc.tab(8n, cam.sbox1.list())

# SBOX2[x] = SBOX1[x] <<< 1, SBOX3[x] = SBOX1[x] <<< 7, SBOX4[x] = SBOX1[x <<< 1]
def cam.s2() -> L.LcTab:
  L.lc.tab(8n, cam.gen(~(x => cam.rotl8(cam.s1.raw(x), 1n)), 256n, 0))

def cam.s3() -> L.LcTab:
  L.lc.tab(8n, cam.gen(~(x => cam.rotl8(cam.s1.raw(x), 7n)), 256n, 0))

def cam.s4() -> L.LcTab:
  L.lc.tab(8n, cam.gen(~(x => cam.s1.raw(cam.rotl8(x, 1n))), 256n, 0))

# The four S-boxes as tables, built once per key (internal)
type LcCamTabs is Data:
  LcCamTabs{s1: L.LcTab, s2: L.LcTab, s3: L.LcTab, s4: L.LcTab}

def cam.tables() -> LcCamTabs:
  LcCamTabs{cam.s1(), cam.s2(), cam.s3(), cam.s4()}

# The F-function (RFC 3713, 2.4.1), on 64-bit values as LcBlock64

def cam.hi(x: L.LcBlock64) -> U32:
  match x:
    case L.LcBlock64{h, l}:
      h

def cam.lo(x: L.LcBlock64) -> U32:
  match x:
    case L.LcBlock64{h, l}:
      l

def cam.p(+t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32) -> L.LcBlock64:
  +y1 = U32.xor(U32.xor(U32.xor(t1, t3), U32.xor(t4, t6)), U32.xor(t7, t8))
  +y2 = U32.xor(U32.xor(U32.xor(t1, t2), U32.xor(t4, t5)), U32.xor(t7, t8))
  +y3 = U32.xor(U32.xor(U32.xor(t1, t2), U32.xor(t3, t5)), U32.xor(t6, t8))
  +y4 = U32.xor(U32.xor(U32.xor(t2, t3), U32.xor(t4, t5)), U32.xor(t6, t7))
  +y5 = U32.xor(U32.xor(U32.xor(t1, t2), t6), U32.xor(t7, t8))
  +y6 = U32.xor(U32.xor(U32.xor(t2, t3), t5), U32.xor(t7, t8))
  +y7 = U32.xor(U32.xor(U32.xor(t3, t4), t5), U32.xor(t6, t8))
  +y8 = U32.xor(U32.xor(U32.xor(t1, t4), t5), U32.xor(t6, t7))
  L.LcBlock64{L.lc.be(y1, y2, y3, y4), L.lc.be(y5, y6, y7, y8)}

def cam.f(t: LcCamTabs, x: L.LcBlock64, k: L.LcBlock64) -> L.LcBlock64:
  match t x k:
    case LcCamTabs{+s1, +s2, +s3, +s4} L.LcBlock64{xh, xl} L.LcBlock64{kh, kl}:
      +a = U32.xor(xh, kh)
      +b = U32.xor(xl, kl)
      cam.p(L.lc.tab.get(8n, s1, L.lc.byte(a, 3n)), L.lc.tab.get(8n, s2, L.lc.byte(a, 2n)), L.lc.tab.get(8n, s3, L.lc.byte(a, 1n)), L.lc.tab.get(8n, s4, L.lc.byte(a, 0n)), L.lc.tab.get(8n, s2, L.lc.byte(b, 3n)), L.lc.tab.get(8n, s3, L.lc.byte(b, 2n)), L.lc.tab.get(8n, s4, L.lc.byte(b, 1n)), L.lc.tab.get(8n, s1, L.lc.byte(b, 0n)))

# FL and FL^-1 (RFC 3713, 2.4.2)
def cam.fl(x: L.LcBlock64, k: L.LcBlock64) -> L.LcBlock64:
  match x k:
    case L.LcBlock64{+x1, x2} L.LcBlock64{k1, k2}:
      +y2 = U32.xor(x2, L.lc.rotl(U32.and(x1, k1), 1n))
      L.LcBlock64{U32.xor(x1, U32.or(y2, k2)), y2}

def cam.flinv(y: L.LcBlock64, k: L.LcBlock64) -> L.LcBlock64:
  match y k:
    case L.LcBlock64{y1, +y2} L.LcBlock64{k1, k2}:
      +x1 = U32.xor(y1, U32.or(y2, k2))
      L.LcBlock64{x1, U32.xor(y2, L.lc.rotl(U32.and(x1, k1), 1n))}

# D1 ^= a, D2 ^= b
def cam.white(a: L.LcBlock64, b: L.LcBlock64, s: M.CmBlock) -> M.CmBlock:
  match a b:
    case L.LcBlock64{a0, a1} L.LcBlock64{b0, b1}:
      M.CmBlock.xor(s, M.CmBlock{a0, a1, b0, b1})

# The steps of the cipher (internal)
type LcCamOp is Data:
  LcCamWhite{a: L.LcBlock64, b: L.LcBlock64}
  LcCamF1{t: LcCamTabs, k: L.LcBlock64}
  LcCamF2{t: LcCamTabs, k: L.LcBlock64}
  LcCamFl{a: L.LcBlock64, b: L.LcBlock64}
  LcCamSwap{}

def cam.op(o: LcCamOp, s: M.CmBlock) -> M.CmBlock:
  match o:
    case LcCamWhite{a, b}:
      cam.white(a, b, s)
    case LcCamF1{t, k}:
      match s:
        case M.CmBlock{+s0, +s1, s2, s3}:
          +f = cam.f(t, L.LcBlock64{s0, s1}, k)
          M.CmBlock{s0, s1, U32.xor(s2, cam.hi(f)), U32.xor(s3, cam.lo(f))}
    case LcCamF2{t, k}:
      match s:
        case M.CmBlock{s0, s1, +s2, +s3}:
          +f = cam.f(t, L.LcBlock64{s2, s3}, k)
          M.CmBlock{U32.xor(s0, cam.hi(f)), U32.xor(s1, cam.lo(f)), s2, s3}
    case LcCamFl{a, b}:
      match s:
        case M.CmBlock{s0, s1, s2, s3}:
          +d1 = cam.fl(L.LcBlock64{s0, s1}, a)
          +d2 = cam.flinv(L.LcBlock64{s2, s3}, b)
          M.CmBlock{cam.hi(d1), cam.lo(d1), cam.hi(d2), cam.lo(d2)}
    case LcCamSwap{}:
      match s:
        case M.CmBlock{s0, s1, s2, s3}:
          M.CmBlock{s2, s3, s0, s1}

# the step undone
def cam.unop(o: LcCamOp, s: M.CmBlock) -> M.CmBlock:
  match o:
    case LcCamWhite{a, b}:
      cam.white(a, b, s)
    case LcCamF1{t, k}:
      match s:
        case M.CmBlock{+s0, +s1, s2, s3}:
          +f = cam.f(t, L.LcBlock64{s0, s1}, k)
          M.CmBlock{s0, s1, U32.xor(s2, cam.hi(f)), U32.xor(s3, cam.lo(f))}
    case LcCamF2{t, k}:
      match s:
        case M.CmBlock{s0, s1, +s2, +s3}:
          +f = cam.f(t, L.LcBlock64{s2, s3}, k)
          M.CmBlock{U32.xor(s0, cam.hi(f)), U32.xor(s1, cam.lo(f)), s2, s3}
    case LcCamFl{a, b}:
      match s:
        case M.CmBlock{s0, s1, s2, s3}:
          +d1 = cam.flinv(L.LcBlock64{s0, s1}, a)
          +d2 = cam.fl(L.LcBlock64{s2, s3}, b)
          M.CmBlock{cam.hi(d1), cam.lo(d1), cam.hi(d2), cam.lo(d2)}
    case LcCamSwap{}:
      match s:
        case M.CmBlock{s0, s1, s2, s3}:
          M.CmBlock{s2, s3, s0, s1}

def cam.run(os: List<&2, LcCamOp>, s: M.CmBlock) -> M.CmBlock:
  match os:
    case Nil{}:
      s
    case Con{o, t}:
      cam.run(t, cam.op(o, s))

def cam.unrun(os: List<&2, LcCamOp>, s: M.CmBlock) -> M.CmBlock:
  match os:
    case Nil{}:
      s
    case Con{o, t}:
      cam.unop(o, cam.unrun(t, s))

# The key schedule (RFC 3713, 2.2), on 128-bit values as CmBlocks

def cam.xor128(a: M.CmBlock, b: M.CmBlock) -> M.CmBlock:
  M.CmBlock.xor(a, b)

# q rotated left by 32 bits, and by r bits (r = 0 to 31)
def cam.rotw(q: M.CmBlock) -> M.CmBlock:
  match q:
    case M.CmBlock{a, b, c, d}:
      M.CmBlock{b, c, d, a}

def cam.rotb(q: M.CmBlock, +r: Nat) -> M.CmBlock:
  match q:
    case M.CmBlock{+a, +b, +c, +d}:
      +s = Nat.sub(32n, r)
      M.CmBlock{U32.or(U32.shln(a, r), U32.shrn(b, s)), U32.or(U32.shln(b, r), U32.shrn(c, s)), U32.or(U32.shln(c, r), U32.shrn(d, s)), U32.or(U32.shln(d, r), U32.shrn(a, s))}

def cam.rotws(n: Nat, q: M.CmBlock) -> M.CmBlock:
  match n:
    case 0n:
      q
    case 1n+p:
      cam.rotws(p, cam.rotw(q))

# q <<< n
def cam.rol(q: M.CmBlock, +n: Nat) -> M.CmBlock:
  cam.rotb(cam.rotws(Nat.div(n, 32n), q), Nat.mod(n, 32n))

def cam.top(q: M.CmBlock) -> L.LcBlock64:
  match q:
    case M.CmBlock{a, b, c, d}:
      L.LcBlock64{a, b}

def cam.bot(q: M.CmBlock) -> L.LcBlock64:
  match q:
    case M.CmBlock{a, b, c, d}:
      L.LcBlock64{c, d}

# the high and the low 64 bits of q <<< n
def cam.h(q: M.CmBlock, +n: Nat) -> L.LcBlock64:
  cam.top(cam.rol(q, n))

def cam.l(q: M.CmBlock, +n: Nat) -> L.LcBlock64:
  cam.bot(cam.rol(q, n))

def cam.sigma(n: Nat) -> L.LcBlock64:
  match n:
    case 0n:
      L.LcBlock64{2694735487, 1003262091}
    case 1n:
      L.LcBlock64{3061508184, 1286239154}
    case 2n:
      L.LcBlock64{3337565999, 3914302142}
    case 3n:
      L.LcBlock64{1426019237, 4057165596}
    case 4n:
      L.LcBlock64{283453434, 3731369245}
    case _:
      L.LcBlock64{2958461122, 3018244605}

# D2 ^= F(D1, Sigma_i); D1 ^= F(D2, Sigma_(i+1)), on the 128-bit value D1:D2
def cam.mix(+t: LcCamTabs, q: M.CmBlock, +i: Nat) -> M.CmBlock:
  cam.op(LcCamF2{t, cam.sigma(Nat.add(i, 1n))}, cam.op(LcCamF1{t, cam.sigma(i)}, q))

# KA from KL and KR
def cam.ka(+t: LcCamTabs, +kl: M.CmBlock, kr: M.CmBlock) -> M.CmBlock:
  cam.mix(t, cam.xor128(kl, cam.mix(t, cam.xor128(kl, kr), 0n)), 2n)

# KB from KA and KR
def cam.kb(t: LcCamTabs, ka: M.CmBlock, kr: M.CmBlock) -> M.CmBlock:
  cam.mix(t, cam.xor128(ka, kr), 4n)

# the steps for a 128-bit key
def cam.ops128(+t: LcCamTabs, +kl: M.CmBlock, +ka: M.CmBlock) -> List<&2, LcCamOp>:
  [LcCamWhite{cam.h(kl, 0n), cam.l(kl, 0n)},
    LcCamF1{t, cam.h(ka, 0n)}, LcCamF2{t, cam.l(ka, 0n)}, LcCamF1{t, cam.h(kl, 15n)}, LcCamF2{t, cam.l(kl, 15n)}, LcCamF1{t, cam.h(ka, 15n)}, LcCamF2{t, cam.l(ka, 15n)},
    LcCamFl{cam.h(ka, 30n), cam.l(ka, 30n)},
    LcCamF1{t, cam.h(kl, 45n)}, LcCamF2{t, cam.l(kl, 45n)}, LcCamF1{t, cam.h(ka, 45n)}, LcCamF2{t, cam.l(kl, 60n)}, LcCamF1{t, cam.h(ka, 60n)}, LcCamF2{t, cam.l(ka, 60n)},
    LcCamFl{cam.h(kl, 77n), cam.l(kl, 77n)},
    LcCamF1{t, cam.h(kl, 94n)}, LcCamF2{t, cam.l(kl, 94n)}, LcCamF1{t, cam.h(ka, 94n)}, LcCamF2{t, cam.l(ka, 94n)}, LcCamF1{t, cam.h(kl, 111n)}, LcCamF2{t, cam.l(kl, 111n)},
    LcCamSwap{}, LcCamWhite{cam.h(ka, 111n), cam.l(ka, 111n)}]

# the steps for a 192- or 256-bit key
def cam.ops256(+t: LcCamTabs, +kl: M.CmBlock, +kr: M.CmBlock, +ka: M.CmBlock, +kb: M.CmBlock) -> List<&2, LcCamOp>:
  [LcCamWhite{cam.h(kl, 0n), cam.l(kl, 0n)},
    LcCamF1{t, cam.h(kb, 0n)}, LcCamF2{t, cam.l(kb, 0n)}, LcCamF1{t, cam.h(kr, 15n)}, LcCamF2{t, cam.l(kr, 15n)}, LcCamF1{t, cam.h(ka, 15n)}, LcCamF2{t, cam.l(ka, 15n)},
    LcCamFl{cam.h(kr, 30n), cam.l(kr, 30n)},
    LcCamF1{t, cam.h(kb, 30n)}, LcCamF2{t, cam.l(kb, 30n)}, LcCamF1{t, cam.h(kl, 45n)}, LcCamF2{t, cam.l(kl, 45n)}, LcCamF1{t, cam.h(ka, 45n)}, LcCamF2{t, cam.l(ka, 45n)},
    LcCamFl{cam.h(kl, 60n), cam.l(kl, 60n)},
    LcCamF1{t, cam.h(kr, 60n)}, LcCamF2{t, cam.l(kr, 60n)}, LcCamF1{t, cam.h(kb, 60n)}, LcCamF2{t, cam.l(kb, 60n)}, LcCamF1{t, cam.h(kl, 77n)}, LcCamF2{t, cam.l(kl, 77n)},
    LcCamFl{cam.h(ka, 77n), cam.l(ka, 77n)},
    LcCamF1{t, cam.h(kr, 94n)}, LcCamF2{t, cam.l(kr, 94n)}, LcCamF1{t, cam.h(ka, 94n)}, LcCamF2{t, cam.l(ka, 94n)}, LcCamF1{t, cam.h(kl, 111n)}, LcCamF2{t, cam.l(kl, 111n)},
    LcCamSwap{}, LcCamWhite{cam.h(kb, 111n), cam.l(kb, 111n)}]

# A Camellia key: the steps of the cipher (opaque; built by LcCamellia.key)
type LcCamelliaKey is Data:
  LcCamelliaKey{ops: List<&2, LcCamOp>}

# word i (big-endian) of the key bytes xs
def cam.w(+xs: List<&2, U32>, +i: Nat) -> U32:
  +j = Nat.mul(4n, i)
  L.lc.be(L.lc.at(xs, j), L.lc.at(xs, Nat.add(j, 1n)), L.lc.at(xs, Nat.add(j, 2n)), L.lc.at(xs, Nat.add(j, 3n)))

def cam.key128(+xs: List<&2, U32>) -> LcCamelliaKey:
  +kl = {M.CmBlock{cam.w(xs, 0n), cam.w(xs, 1n), cam.w(xs, 2n), cam.w(xs, 3n)} : M.CmBlock}
  +t = cam.tables()
  LcCamelliaKey{cam.ops128(t, kl, cam.ka(t, kl, M.CmBlock.zero()))}

def cam.key256.go(+kl: M.CmBlock, +kr: M.CmBlock) -> LcCamelliaKey:
  +t = cam.tables()
  +ka = cam.ka(t, kl, kr)
  LcCamelliaKey{cam.ops256(t, kl, kr, ka, cam.kb(t, ka, kr))}

# a 192-bit key's KR is its last 64 bits, then their complement
def cam.key192(+xs: List<&2, U32>) -> LcCamelliaKey:
  +r0 = cam.w(xs, 4n)
  +r1 = cam.w(xs, 5n)
  cam.key256.go(M.CmBlock{cam.w(xs, 0n), cam.w(xs, 1n), cam.w(xs, 2n), cam.w(xs, 3n)}, M.CmBlock{r0, r1, U32.not(r0), U32.not(r1)})

def cam.key256(+xs: List<&2, U32>) -> LcCamelliaKey:
  cam.key256.go(M.CmBlock{cam.w(xs, 0n), cam.w(xs, 1n), cam.w(xs, 2n), cam.w(xs, 3n)}, M.CmBlock{cam.w(xs, 4n), cam.w(xs, 5n), cam.w(xs, 6n), cam.w(xs, 7n)})

# the key for 16, 24 or 32 bytes, if n says so
def cam.key.pick(n16: Bool, n24: Bool, n32: Bool, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcCamelliaKey>:
  match n16 n24 n32:
    case True{} _ _:
      Done{cam.key128(xs)}
    case False{} True{} _:
      Done{cam.key192(xs)}
    case False{} False{} True{}:
      Done{cam.key256(xs)}
    case False{} False{} False{}:
      Fail{L.LcBadKeyLength{B.len(xs)}}

# The cipher

# a 16-, 24- or 32-byte key (Camellia-128, -192, -256, by its length)
def LcCamellia.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcCamelliaKey>:
  +xs = B.Octets.to_list(o)
  +n = B.len(xs)
  cam.key.pick(Nat.is_eq(n, 16n), Nat.is_eq(n, 24n), Nat.is_eq(n, 32n), xs)

# a key of exactly this size
def LcCamellia.key128(o: B.Octets) -> Result<&2, &2, L.LcError, LcCamelliaKey>:
  +xs = B.Octets.to_list(o)
  cam.key.pick(Nat.is_eq(B.len(xs), 16n), False{}, False{}, xs)

def LcCamellia.key192(o: B.Octets) -> Result<&2, &2, L.LcError, LcCamelliaKey>:
  +xs = B.Octets.to_list(o)
  cam.key.pick(False{}, Nat.is_eq(B.len(xs), 24n), False{}, xs)

def LcCamellia.key256(o: B.Octets) -> Result<&2, &2, L.LcError, LcCamelliaKey>:
  +xs = B.Octets.to_list(o)
  cam.key.pick(False{}, False{}, Nat.is_eq(B.len(xs), 32n), xs)

def LcCamellia.encrypt(k: LcCamelliaKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcCamelliaKey{ops}:
      cam.run(ops, b)

def LcCamellia.decrypt(k: LcCamelliaKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcCamelliaKey{ops}:
      cam.unrun(ops, b)
