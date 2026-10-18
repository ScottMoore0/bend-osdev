# SM4 (GB/T 32907-2016, Information security technology - SM4 block cipher
# algorithm; in English, draft-ribose-cfrg-sm4 and RFC 8998, section 2.1):
# a 128-bit block cipher with a 128-bit key, as a cipher for cipher-modes'
# modes (~LcSm4Key, ~LcSm4.encrypt, ~LcSm4.decrypt).
#
# The state is four 32-bit words X0..X3, big-endian from the block, which is
# exactly a CmBlock. Each of the 32 rounds is
#   (X0, X1, X2, X3) -> (X1, X2, X3, X0 xor T(X1 xor X2 xor X3 xor rk_i))
# and the output is the last four words in reverse order. Decryption undoes
# each step in reverse order, which is the same function as the
# specification's "the round keys in reverse order", and makes
# decrypt(encrypt(b)) == b provable for every key and block: a round is
# undone whatever T is.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ./legacy-ciphers.bend as L

# The S-box (GB/T 32907-2016, 6.2: row i, column j is entry 16i + j)
def sm4.sbox.list() -> List<&2, U32>:
  [214, 144, 233, 254, 204, 225, 61, 183, 22, 182, 20, 194, 40, 251, 44, 5,
    43, 103, 154, 118, 42, 190, 4, 195, 170, 68, 19, 38, 73, 134, 6, 153,
    156, 66, 80, 244, 145, 239, 152, 122, 51, 84, 11, 67, 237, 207, 172, 98,
    228, 179, 28, 169, 201, 8, 232, 149, 128, 223, 148, 250, 117, 143, 63, 166,
    71, 7, 167, 252, 243, 115, 23, 186, 131, 89, 60, 25, 230, 133, 79, 168,
    104, 107, 129, 178, 113, 100, 218, 139, 248, 235, 15, 75, 112, 86, 157, 53,
    30, 36, 14, 94, 99, 88, 209, 162, 37, 34, 124, 59, 1, 33, 120, 135,
    212, 0, 70, 87, 159, 211, 39, 82, 76, 54, 2, 231, 160, 196, 200, 158,
    234, 191, 138, 210, 64, 199, 56, 181, 163, 247, 242, 206, 249, 97, 21, 161,
    224, 174, 93, 164, 155, 52, 26, 85, 173, 147, 50, 48, 245, 140, 177, 227,
    29, 246, 226, 46, 130, 102, 202, 96, 192, 41, 35, 171, 13, 83, 78, 111,
    213, 219, 55, 69, 222, 253, 142, 47, 3, 255, 106, 114, 109, 108, 91, 81,
    141, 27, 175, 146, 187, 221, 188, 127, 17, 217, 92, 65, 31, 16, 90, 216,
    10, 193, 49, 136, 165, 205, 123, 189, 45, 116, 208, 18, 184, 229, 180, 176,
    137, 105, 151, 74, 12, 150, 119, 126, 101, 185, 241, 9, 197, 110, 198, 132,
    24, 240, 125, 236, 58, 220, 77, 32, 121, 238, 95, 62, 215, 203, 57, 72]

def sm4.sbox() -> L.LcTab:
  L.lc.tab(8n, sm4.sbox.list())

def sm4.s(+tab: L.LcTab, +a: U32, n: Nat) -> U32:
  L.lc.tab.get(8n, tab, L.lc.byte(a, n))

# tau: the S-box on each byte of a word
def sm4.tau(+tab: L.LcTab, +a: U32) -> U32:
  L.lc.be(sm4.s(tab, a, 3n), sm4.s(tab, a, 2n), sm4.s(tab, a, 1n), sm4.s(tab, a, 0n))

# T = L(tau(x)), L(B) = B xor B<<<2 xor B<<<10 xor B<<<18 xor B<<<24
def sm4.t(+tab: L.LcTab, x: U32) -> U32:
  +b = sm4.tau(tab, x)
  U32.xor(U32.xor(U32.xor(b, L.lc.rotl(b, 2n)), U32.xor(L.lc.rotl(b, 10n), L.lc.rotl(b, 18n))), L.lc.rotl(b, 24n))

# T' of the key schedule: L'(B) = B xor B<<<13 xor B<<<23
def sm4.t2(+tab: L.LcTab, x: U32) -> U32:
  +b = sm4.tau(tab, x)
  U32.xor(U32.xor(b, L.lc.rotl(b, 13n)), L.lc.rotl(b, 23n))

# The rounds, on the state as a CmBlock

def sm4.step(+tab: L.LcTab, rk: U32, s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, +x1, +x2, +x3}:
      M.CmBlock{x1, x2, x3, U32.xor(x0, sm4.t(tab, U32.xor(U32.xor(U32.xor(x1, x2), x3), rk)))}

# the round undone
def sm4.unstep(+tab: L.LcTab, rk: U32, s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{+y0, +y1, +y2, y3}:
      M.CmBlock{U32.xor(y3, sm4.t(tab, U32.xor(U32.xor(U32.xor(y0, y1), y2), rk))), y0, y1, y2}

def sm4.rounds(+tab: L.LcTab, rks: List<&2, U32>, s: M.CmBlock) -> M.CmBlock:
  match rks:
    case Nil{}:
      s
    case Con{k, t}:
      sm4.rounds(tab, t, sm4.step(tab, k, s))

def sm4.unrounds(+tab: L.LcTab, rks: List<&2, U32>, s: M.CmBlock) -> M.CmBlock:
  match rks:
    case Nil{}:
      s
    case Con{k, t}:
      sm4.unstep(tab, k, sm4.unrounds(tab, t, s))

# the reverse transformation R: (A0, A1, A2, A3) -> (A3, A2, A1, A0)
def sm4.rev(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{a, b, c, d}:
      M.CmBlock{d, c, b, a}

# The key schedule (GB/T 32907-2016, 7.3)

# FK and CK_i (ck_(i,j) = (4i + j) * 7 mod 256)
def sm4.fk(n: Nat) -> U32:
  L.lc.at([2746333894, 1453994832, 1736282519, 2993693404], n)

def sm4.ck(+i: U32) -> U32:
  +b = U32.mul(i, 28)
  L.lc.be(b, U32.add(b, 7), U32.add(b, 14), U32.add(b, 21))

# rk_i = K_(i+4) = K_i xor T'(K_(i+1) xor K_(i+2) xor K_(i+3) xor CK_i), for
# n more rounds from round i, the window K_i .. K_(i+3) in k0 .. k3
def sm4.schedule(n: Nat, +tab: L.LcTab, +i: U32, k0: U32, +k1: U32, +k2: U32, +k3: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +k4 = U32.xor(k0, sm4.t2(tab, U32.xor(U32.xor(U32.xor(k1, k2), k3), sm4.ck(i))))
      Con{k4, sm4.schedule(p, tab, U32.add(i, 1), k1, k2, k3, k4)}

# An SM4 key: the S-box table (built once per key) and the 32 round keys
# (opaque; built by LcSm4.key)
type LcSm4Key is Data:
  LcSm4Key{tab: L.LcTab, rks: List<&2, U32>}

def sm4.mk(+xs: List<&2, U32>, +i: Nat) -> U32:
  +j = Nat.mul(4n, i)
  U32.xor(L.lc.be(L.lc.at(xs, j), L.lc.at(xs, Nat.add(j, 1n)), L.lc.at(xs, Nat.add(j, 2n)), L.lc.at(xs, Nat.add(j, 3n))), sm4.fk(i))

def sm4.key.pick(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcSm4Key>:
  match ok:
    case True{}:
      +tab = sm4.sbox()
      Done{LcSm4Key{tab, sm4.schedule(32n, tab, 0, sm4.mk(xs, 0n), sm4.mk(xs, 1n), sm4.mk(xs, 2n), sm4.mk(xs, 3n))}}
    case False{}:
      Fail{L.LcBadKeyLength{B.len(xs)}}

# The cipher

# a 16-byte key
def LcSm4.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcSm4Key>:
  +xs = B.Octets.to_list(o)
  sm4.key.pick(Nat.is_eq(B.len(xs), 16n), xs)

def LcSm4.encrypt(k: LcSm4Key, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcSm4Key{+tab, rks}:
      sm4.rev(sm4.rounds(tab, rks, b))

def LcSm4.decrypt(k: LcSm4Key, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcSm4Key{+tab, rks}:
      sm4.unrounds(tab, rks, sm4.rev(b))
