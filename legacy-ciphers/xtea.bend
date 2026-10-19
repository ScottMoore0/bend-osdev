# XTEA (R. Needham, D. Wheeler, "Tea extensions", 1997, the routine
# "tean"): TEA with a different key schedule, a 64-bit block cipher with a
# 128-bit key. Each cycle is
#   y += (((z << 4) xor (z >> 5)) + z) xor (sum + k[sum & 3])
#   sum += delta
#   z += (((y << 4) xor (y >> 5)) + y) xor (sum + k[(sum >> 11) & 3])
# The key schedule computes each step's sum + k[..] once, as a step of
# tea.bend's (LcXteaY, LcXteaZ); decryption undoes the steps last to first,
# the paper's decoding, so decrypt(encrypt(b)) == b is provable for every key
# and block, as for TEA.
#
# The byte order of the words is a parameter, as for TEA: little-endian
# (the Linux kernel's "xtea") is LcXtea.key, big-endian LcXtea.key_be, and
# LcXtea.key_with takes the order and the number of cycles (32 recommended).
import Base
import ../bytes/bytes.bend as B
import ./legacy-ciphers.bend as L
import ./tea.bend as T

# key word i & 3 of k0 .. k3
def xtea.kw(+i: U32, +k0: U32, +k1: U32, +k2: U32, +k3: U32) -> U32:
  L.lc.at([k0, k1, k2, k3], U32.to_nat(U32.and(3, i)))

# XTEA's steps for n more cycles from sum s
def xtea.cycles(n: Nat, +s: U32, +k0: U32, +k1: U32, +k2: U32, +k3: U32) -> List<&2, T.LcTeaOp>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +s1 = U32.add(s, T.tea.delta())
      Con{T.LcXteaY{U32.add(s, xtea.kw(s, k0, k1, k2, k3))}, Con{T.LcXteaZ{U32.add(s1, xtea.kw(U32.shrn(s1, 11n), k0, k1, k2, k3))}, xtea.cycles(p, s1, k0, k1, k2, k3)}}

# An XTEA key: the steps of the cipher (opaque; built by LcXtea.key)
type LcXteaKey is Data:
  LcXteaKey{ops: List<&2, T.LcTeaOp>}

def xtea.key.pick(ok: Bool, +le: Bool, n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcXteaKey>:
  match ok:
    case True{}:
      Done{LcXteaKey{T.tea.order(le, xtea.cycles(n, 0, T.tea.word(le, xs, 0n), T.tea.word(le, xs, 4n), T.tea.word(le, xs, 8n), T.tea.word(le, xs, 12n)))}}
    case False{}:
      Fail{L.LcBadKeyLength{B.len(xs)}}

# The cipher

# a 16-byte key, words in the order le picks (True: little-endian), and n
# cycles (32 recommended)
def LcXtea.key_with(le: Bool, n: Nat, o: B.Octets) -> Result<&2, &2, L.LcError, LcXteaKey>:
  +xs = B.Octets.to_list(o)
  xtea.key.pick(Nat.is_eq(B.len(xs), 16n), le, n, xs)

# the named default: little-endian words (the Linux kernel's "xtea"), 32
# cycles
def LcXtea.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcXteaKey>:
  LcXtea.key_with(True{}, 32n, o)

# big-endian words, 32 cycles
def LcXtea.key_be(o: B.Octets) -> Result<&2, &2, L.LcError, LcXteaKey>:
  LcXtea.key_with(False{}, 32n, o)

def LcXtea.encrypt(k: LcXteaKey, b: L.LcBlock64) -> L.LcBlock64:
  match k:
    case LcXteaKey{ops}:
      T.tea.run(ops, b)

def LcXtea.decrypt(k: LcXteaKey, b: L.LcBlock64) -> L.LcBlock64:
  match k:
    case LcXteaKey{ops}:
      T.tea.unrun(ops, b)
