# bend-osdev-bch, bytes as bits: a BCH code works on bits, and NAND data and
# ECC are bytes. Which bit of a byte comes first is a parameter (BchOrder),
# most significant first by default. Bits are List<&2, Bool>, in order (the
# first bit is the highest power of X).
#
# Packing bits into bytes pads the last byte with zero bits at its end.
import Base
import ../bytes/bytes.bend as B

type BchOrder is Data:
  BchMsbFirst{}
  BchLsbFirst{}

# the default: the most significant bit of each byte first
def Bch.order() -> BchOrder:
  BchMsbFirst{}

# bit i of b
def bch.bit(+b: U32, i: Nat) -> Bool:
  Bool.not(U32.is_eq(U32.and(U32.shrn(b, i), 1), 0))

# the eight bits of a byte, in order, in front of acc
def bch.byte.bits(o: BchOrder, +b: U32, acc: List<&2, Bool>) -> List<&2, Bool>:
  match o:
    case BchMsbFirst{}:
      Con{bch.bit(b, 7n), Con{bch.bit(b, 6n), Con{bch.bit(b, 5n), Con{bch.bit(b, 4n), Con{bch.bit(b, 3n), Con{bch.bit(b, 2n), Con{bch.bit(b, 1n), Con{bch.bit(b, 0n), acc}}}}}}}}
    case BchLsbFirst{}:
      Con{bch.bit(b, 0n), Con{bch.bit(b, 1n), Con{bch.bit(b, 2n), Con{bch.bit(b, 3n), Con{bch.bit(b, 4n), Con{bch.bit(b, 5n), Con{bch.bit(b, 6n), Con{bch.bit(b, 7n), acc}}}}}}}}

# the bytes in reverse, onto acc (so the result is in order)
def bch.bits.go(rev: List<&2, U32>, +o: BchOrder, acc: List<&2, Bool>) -> List<&2, Bool>:
  match rev:
    case Nil{}:
      acc
    case Con{b, t}:
      bch.bits.go(t, o, bch.byte.bits(o, b, acc))

# the bits of a byte string, 8 per byte
def Bch.bits_of(+o: BchOrder, d: B.Octets) -> List<&2, Bool>:
  bch.bits.go(B.rev(B.Octets.to_list(d)), o, Nil{})

def bch.b2(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# where the i-th bit of a byte goes
def bch.place(o: BchOrder, i: Nat) -> Nat:
  match o:
    case BchMsbFirst{}:
      Nat.sub(7n, i)
    case BchLsbFirst{}:
      i

# bytes from bits onto acc (in reverse), the last padded with zeros: cur
# holds the i bits of the byte being filled
def bch.pack(bits: List<&2, Bool>, +o: BchOrder, i: Nat, cur: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match bits:
    case Nil{}:
      match i:
        case 0n:
          acc
        case 1n+k:
          Con{cur, acc}
    case Con{b, t}:
      match i:
        case 0n:
          bch.pack(t, o, 1n, U32.or(cur, U32.shln(bch.b2(b), bch.place(o, 0n))), acc)
        case 1n:
          bch.pack(t, o, 2n, U32.or(cur, U32.shln(bch.b2(b), bch.place(o, 1n))), acc)
        case 2n:
          bch.pack(t, o, 3n, U32.or(cur, U32.shln(bch.b2(b), bch.place(o, 2n))), acc)
        case 3n:
          bch.pack(t, o, 4n, U32.or(cur, U32.shln(bch.b2(b), bch.place(o, 3n))), acc)
        case 4n:
          bch.pack(t, o, 5n, U32.or(cur, U32.shln(bch.b2(b), bch.place(o, 4n))), acc)
        case 5n:
          bch.pack(t, o, 6n, U32.or(cur, U32.shln(bch.b2(b), bch.place(o, 5n))), acc)
        case 6n:
          bch.pack(t, o, 7n, U32.or(cur, U32.shln(bch.b2(b), bch.place(o, 6n))), acc)
        case 7n+k:
          bch.pack(t, o, 0n, 0, Con{U32.or(cur, U32.shln(bch.b2(b), bch.place(o, 7n))), acc})

# the bytes holding these bits, in order
def Bch.octets_of(+o: BchOrder, bits: List<&2, Bool>) -> B.Octets:
  B.Octets.of_list(B.rev(bch.pack(bits, o, 0n, 0, Nil{})))
