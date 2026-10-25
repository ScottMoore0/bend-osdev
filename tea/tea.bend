# TEA (D. Wheeler, R. Needham, "TEA, a Tiny Encryption Algorithm", Fast
# Software Encryption 1994): a 64-bit block cipher with a 128-bit key. This
# file also holds the steps TEA and XTEA (xtea.bend) share.
#
# The block is two 32-bit words y, z and the key four words k0 .. k3. Each
# cycle adds delta (0x9E3779B9) to sum, then
#   y += ((z << 4) + k0) xor (z + sum) xor ((z >> 5) + k1)
#   z += ((y << 4) + k2) xor (y + sum) xor ((y >> 5) + k3)
# The key schedule turns the key into a list of such steps (each adds a
# function of one half to the other); decryption undoes them last to first,
# each by subtracting what it added: the same function as the paper's decode
# routine, and decrypt(encrypt(b)) == b is provable for every key and block
# (an addition is undone by a subtraction, for every word).
#
# The paper fixes 32-bit words and leaves their byte order open ("same
# endian coding or decoding"). The order is a parameter: little-endian words
# (the Linux kernel's "tea") are LcTea.key, big-endian ones LcTea.key_be; the
# number of cycles (32 recommended) is a parameter of LcTea.key_with. A
# little-endian key reverses the bytes of each block word on the way in and
# out (a step undone by itself).
import Base
import ../bytes/bytes.bend as B
import ../cipher-core/cipher-core.bend as L

# The steps (internal), on the block as LcBlock64{y, z}
type LcTeaOp is Data:
  LcTeaY{s: U32, a: U32, b: U32}
  LcTeaZ{s: U32, a: U32, b: U32}
  LcXteaY{c: U32}
  LcXteaZ{c: U32}
  LcTeaBswap{}

# TEA's function of one half: ((x << 4) + a) xor (x + s) xor ((x >> 5) + b)
def tea.g(+x: U32, s: U32, a: U32, b: U32) -> U32:
  U32.xor(U32.xor(U32.add(U32.shln(x, 4n), a), U32.add(x, s)), U32.add(U32.shrn(x, 5n), b))

# XTEA's: (((x << 4) xor (x >> 5)) + x) xor c
def xtea.g(+x: U32, c: U32) -> U32:
  U32.xor(U32.add(U32.xor(U32.shln(x, 4n), U32.shrn(x, 5n)), x), c)

def tea.op(o: LcTeaOp, b: L.LcBlock64) -> L.LcBlock64:
  match o:
    case LcTeaY{s, ka, kb}:
      match b:
        case L.LcBlock64{y, +z}:
          L.LcBlock64{U32.add(y, tea.g(z, s, ka, kb)), z}
    case LcTeaZ{s, ka, kb}:
      match b:
        case L.LcBlock64{+y, z}:
          L.LcBlock64{y, U32.add(z, tea.g(y, s, ka, kb))}
    case LcXteaY{c}:
      match b:
        case L.LcBlock64{y, +z}:
          L.LcBlock64{U32.add(y, xtea.g(z, c)), z}
    case LcXteaZ{c}:
      match b:
        case L.LcBlock64{+y, z}:
          L.LcBlock64{y, U32.add(z, xtea.g(y, c))}
    case LcTeaBswap{}:
      match b:
        case L.LcBlock64{y, z}:
          L.LcBlock64{L.lc.bswap.bits(y), L.lc.bswap.bits(z)}

# the step undone
def tea.unop(o: LcTeaOp, b: L.LcBlock64) -> L.LcBlock64:
  match o:
    case LcTeaY{s, ka, kb}:
      match b:
        case L.LcBlock64{y, +z}:
          L.LcBlock64{U32.sub(y, tea.g(z, s, ka, kb)), z}
    case LcTeaZ{s, ka, kb}:
      match b:
        case L.LcBlock64{+y, z}:
          L.LcBlock64{y, U32.sub(z, tea.g(y, s, ka, kb))}
    case LcXteaY{c}:
      match b:
        case L.LcBlock64{y, +z}:
          L.LcBlock64{U32.sub(y, xtea.g(z, c)), z}
    case LcXteaZ{c}:
      match b:
        case L.LcBlock64{+y, z}:
          L.LcBlock64{y, U32.sub(z, xtea.g(y, c))}
    case LcTeaBswap{}:
      match b:
        case L.LcBlock64{y, z}:
          L.LcBlock64{L.lc.bswap.bits(y), L.lc.bswap.bits(z)}

def tea.run(os: List<&2, LcTeaOp>, b: L.LcBlock64) -> L.LcBlock64:
  match os:
    case Nil{}:
      b
    case Con{o, t}:
      tea.run(t, tea.op(o, b))

def tea.unrun(os: List<&2, LcTeaOp>, b: L.LcBlock64) -> L.LcBlock64:
  match os:
    case Nil{}:
      b
    case Con{o, t}:
      tea.unop(o, tea.unrun(t, b))

# The key and its byte order (shared with XTEA)

def tea.delta() -> U32:
  2654435769

# the four key words, little-endian (le True) or big-endian
def tea.word(le: Bool, +xs: List<&2, U32>, +i: Nat) -> U32:
  match le:
    case True{}:
      L.lc.le(L.lc.at(xs, i), L.lc.at(xs, Nat.add(i, 1n)), L.lc.at(xs, Nat.add(i, 2n)), L.lc.at(xs, Nat.add(i, 3n)))
    case False{}:
      L.lc.be(L.lc.at(xs, i), L.lc.at(xs, Nat.add(i, 1n)), L.lc.at(xs, Nat.add(i, 2n)), L.lc.at(xs, Nat.add(i, 3n)))

def tea.append(xs: List<&2, LcTeaOp>, ys: List<&2, LcTeaOp>) -> List<&2, LcTeaOp>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, tea.append(t, ys)}

# the steps in the chosen byte order: little-endian words are byte-swapped
# on the way in and out
def tea.order(le: Bool, os: List<&2, LcTeaOp>) -> List<&2, LcTeaOp>:
  match le:
    case True{}:
      Con{LcTeaBswap{}, tea.append(os, [LcTeaBswap{}])}
    case False{}:
      os

# TEA's steps for n more cycles, sum the value before the next
def tea.cycles(n: Nat, +s: U32, +k0: U32, +k1: U32, +k2: U32, +k3: U32) -> List<&2, LcTeaOp>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +s1 = U32.add(s, tea.delta())
      Con{LcTeaY{s1, k0, k1}, Con{LcTeaZ{s1, k2, k3}, tea.cycles(p, s1, k0, k1, k2, k3)}}

# A TEA key: the steps of the cipher (opaque; built by LcTea.key)
type LcTeaKey is Data:
  LcTeaKey{ops: List<&2, LcTeaOp>}

def tea.key.pick(ok: Bool, +le: Bool, n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcTeaKey>:
  match ok:
    case True{}:
      Done{LcTeaKey{tea.order(le, tea.cycles(n, 0, tea.word(le, xs, 0n), tea.word(le, xs, 4n), tea.word(le, xs, 8n), tea.word(le, xs, 12n)))}}
    case False{}:
      Fail{L.LcBadKeyLength{B.len(xs)}}

# The cipher

# a 16-byte key, words in the order le picks (True: little-endian), and n
# cycles (32 recommended)
def LcTea.key_with(le: Bool, n: Nat, o: B.Octets) -> Result<&2, &2, L.LcError, LcTeaKey>:
  +xs = B.Octets.to_list(o)
  tea.key.pick(Nat.is_eq(B.len(xs), 16n), le, n, xs)

# the named default: little-endian words (the Linux kernel's "tea"), 32
# cycles
def LcTea.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcTeaKey>:
  LcTea.key_with(True{}, 32n, o)

# big-endian words, 32 cycles
def LcTea.key_be(o: B.Octets) -> Result<&2, &2, L.LcError, LcTeaKey>:
  LcTea.key_with(False{}, 32n, o)

def LcTea.encrypt(k: LcTeaKey, b: L.LcBlock64) -> L.LcBlock64:
  match k:
    case LcTeaKey{ops}:
      tea.run(ops, b)

def LcTea.decrypt(k: LcTeaKey, b: L.LcBlock64) -> L.LcBlock64:
  match k:
    case LcTeaKey{ops}:
      tea.unrun(ops, b)
