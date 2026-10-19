# bend-osdev-raid6: the RAID-6 syndromes P and Q of a stripe of data
# blocks, from H. Peter Anvin, "The mathematics of RAID-6" (first version
# 20 January 2004, last updated 20 December 2011), section 2:
#
#   P = D_0 + D_1 + ... + D_(n-1)                          (equation 1)
#   Q = g^0 D_0 + g^1 D_1 + ... + g^(n-1) D_(n-1)          (equation 2)
#
# computed bytewise in GF(2^8), where + is XOR and g a generator of the
# field's multiplicative group. Q is computed by Horner's rule, as in the
# paper's equation (21): Q = ((... D_(n-1) ...) g + D_1) g + D_0.
#
# The field (and with it g) is a parameter, Raid6Spec; the default is the
# paper's: x^8 + x^4 + x^3 + x^2 + 1 (0x11D) with g = {02} (bend-osdev-gf's
# Gf8.raid6()). Blocks are Octets; P is xorblocks' XOR of all the data
# blocks. Blocks of unequal length count as padded with zero bytes.
import Base
import ../bytes/bytes.bend as B
import ../gf/gf.bend as G
import ../xorblocks/xorblocks.bend as X
import ./scale.bend as S

# The field: g is its generator (Gf8.gen)
type Raid6Spec is Data:
  Raid6Spec{field: G.Gf8Field}

# The paper's field and generator: 0x11D, g = {02}
def Raid6.spec() -> Raid6Spec:
  Raid6Spec{G.Gf8.raid6()}

def Raid6.field(s: Raid6Spec) -> G.Gf8Field:
  match s:
    case Raid6Spec{f}:
      f

def Raid6.gen(s: Raid6Spec) -> U32:
  G.Gf8.gen(Raid6.field(s))

# g^i
def Raid6.gpow(s: Raid6Spec, i: Nat) -> U32:
  G.Gf8.exp(Raid6.field(s), i)

# A stripe: the data blocks and the two syndromes
type Raid6Stripe is Data:
  Raid6Stripe{data: List<&2, B.Octets>, p: B.Octets, q: B.Octets}

# P: the XOR of the data blocks (equation 1)
def Raid6.p(ds: List<&2, B.Octets>) -> B.Octets:
  X.Xorb.all(ds)

# Q: D_0 + g (D_1 + g (D_2 + ...)) (equations 2 and 21)
def Raid6.q(+s: Raid6Spec, ds: List<&2, B.Octets>) -> B.Octets:
  match ds:
    case Nil{}:
      B.Octets.empty()
    case Con{d, rest}:
      X.Xorb.xor(d, S.Raid6.scale(Raid6.field(s), Raid6.gen(s), Raid6.q(s, rest)))

# the stripe of the data blocks ds: ds, P and Q
def Raid6.encode(+s: Raid6Spec, +ds: List<&2, B.Octets>) -> Raid6Stripe:
  Raid6Stripe{ds, Raid6.p(ds), Raid6.q(s, ds)}

# Blocks of a stripe, by index

# block i (the empty block past the end)
def Raid6.block(ds: List<&2, B.Octets>, i: Nat) -> B.Octets:
  match ds:
    case Nil{}:
      B.Octets.empty()
    case Con{d, rest}:
      match i:
        case 0n:
          d
        case 1n+k:
          Raid6.block(rest, k)

# block i replaced by b (no change past the end)
def Raid6.set_block(ds: List<&2, B.Octets>, i: Nat, b: B.Octets) -> List<&2, B.Octets>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      match i:
        case 0n:
          Con{b, rest}
        case 1n+k:
          Con{d, Raid6.set_block(rest, k, b)}

# the number of data blocks
def Raid6.width(ds: List<&2, B.Octets>) -> Nat:
  List.length(&2, B.Octets, ds)

# whether every block has the first block's length
def r6.same(+n: Nat, ds: List<&2, B.Octets>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, rest}:
      Bool.and(Nat.is_eq(B.Octets.len(d), n), r6.same(n, rest))

def Raid6.uniform(ds: List<&2, B.Octets>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      r6.same(B.Octets.len(d), rest)
