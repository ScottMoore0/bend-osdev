# bend-osdev-bytes: byte strings, and the fixed-width fields that formats store
# in them.
#
# A byte string is a List<&2, U32> whose elements are 0 to 255 (the shape Base's
# own I/O uses). Readers take the low 8 bits of each element, so a malformed
# element is masked, never trusted.
#
# The field readers and writers work on bits (slicing and joining words), not
# with shifts and masks, so that their round trips can be proved for every
# value. That costs speed: use them for header fields, not bulk data.
import Base
import ../word64/word64.bend as W

# Bytes and bits

# the low 8 bits of a word, as bits
def bits8(b: U32) -> Word(8n):
  match b:
    case U32{w}:
      W.W64.bits.lo(8n, 24n, w)

# the byte (0 to 255) with these 8 bits
def of_bits8(s: Word(8n)) -> U32:
  U32{W.W64.bits.cat(8n, 24n, s, Word.zero(24n))}

# the byte of a word: its low 8 bits
def byte(b: U32) -> U32:
  of_bits8(bits8(b))

# List operations

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

# the first n bytes (all of them if there are fewer)
def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, take(p, t)}

# all but the first n bytes
def drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          drop(p, t)

def append(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

# n zero bytes
def zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{0, zeros(p)}

# the byte at offset i, if there is one
def at.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{h, t}:
      Some{byte(h)}
    case Nil{}:
      None{}

def at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  at.head(drop(i, xs))

# Fields: writing (each answers its bytes, in storage order)

# the low 16 bits of a word
def low16(v: U32) -> U32:
  match v:
    case U32{w}:
      U32{W.W64.bits.cat(16n, 16n, W.W64.bits.lo(16n, 16n, w), Word.zero(16n))}

def le16(v: U32) -> List<&2, U32>:
  match v:
    case U32{w}:
      +lo = W.W64.bits.lo(16n, 16n, w)
      [of_bits8(W.W64.bits.lo(8n, 8n, lo)), of_bits8(W.W64.bits.hi(8n, 8n, lo))]

def be16(v: U32) -> List<&2, U32>:
  match v:
    case U32{w}:
      +lo = W.W64.bits.lo(16n, 16n, w)
      [of_bits8(W.W64.bits.hi(8n, 8n, lo)), of_bits8(W.W64.bits.lo(8n, 8n, lo))]

# the four bytes of a word, least significant first
def le32(+v: U32) -> List<&2, U32>:
  match v:
    case U32{w}:
      +r1 = W.W64.bits.hi(8n, 24n, w)
      +r2 = W.W64.bits.hi(8n, 16n, r1)
      [of_bits8(W.W64.bits.lo(8n, 24n, w)), of_bits8(W.W64.bits.lo(8n, 16n, r1)), of_bits8(W.W64.bits.lo(8n, 8n, r2)), of_bits8(W.W64.bits.hi(8n, 8n, r2))]

def be32.rev(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      [d, c, b, a]
    case _:
      Nil{}

def be32(v: U32) -> List<&2, U32>:
  be32.rev(le32(v))

def le64(+v: W.W64) -> List<&2, U32>:
  append(le32(W.W64.lo(v)), le32(W.W64.hi(v)))

def be64(+v: W.W64) -> List<&2, U32>:
  append(be32(W.W64.hi(v)), be32(W.W64.lo(v)))

# Fields: reading at the head of a byte string

def le16.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, t}}:
      Some{U32{W.W64.bits.cat(16n, 16n, W.W64.bits.cat(8n, 8n, bits8(a), bits8(b)), Word.zero(16n))}}
    case _:
      None{}

def be16.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, t}}:
      Some{U32{W.W64.bits.cat(16n, 16n, W.W64.bits.cat(8n, 8n, bits8(b), bits8(a)), Word.zero(16n))}}
    case _:
      None{}

def le32.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Some{U32{W.W64.bits.cat(8n, 24n, bits8(a), W.W64.bits.cat(8n, 16n, bits8(b), W.W64.bits.cat(8n, 8n, bits8(c), bits8(d))))}}
    case _:
      None{}

def be32.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Some{U32{W.W64.bits.cat(8n, 24n, bits8(d), W.W64.bits.cat(8n, 16n, bits8(c), W.W64.bits.cat(8n, 8n, bits8(b), bits8(a))))}}
    case _:
      None{}

def le64.join(lo: Maybe<&2, U32>, hi: Maybe<&2, U32>) -> Maybe<&2, W.W64>:
  match lo hi:
    case Some{l} Some{h}:
      Some{W.W64.from_parts(h, l)}
    case _ _:
      None{}

# Fields: reading at an offset (None if the string is too short)

def le16_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  le16.head(drop(i, xs))

def be16_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  be16.head(drop(i, xs))

def le32_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  le32.head(drop(i, xs))

def be32_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  be32.head(drop(i, xs))

def le64_at(+xs: List<&2, U32>, +i: Nat) -> Maybe<&2, W.W64>:
  le64.join(le32_at(xs, i), le32_at(xs, Nat.add(i, 4n)))

def be64_at(+xs: List<&2, U32>, +i: Nat) -> Maybe<&2, W.W64>:
  le64.join(be32_at(xs, Nat.add(i, 4n)), be32_at(xs, i))

# Text

def of_string(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{byte(c), of_string(t)}

def to_string(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      SCon{Chr{byte(h)}, to_string(t)}

def hex.digit.pick(lt: Bool, d: U32) -> Char:
  match lt:
    case True{}:
      Chr{U32.add(48, d)}
    case False{}:
      Chr{U32.add(87, d)}

def hex.digit(+d: U32) -> Char:
  hex.digit.pick(U32.is_lt(d, 10), d)

# two lower-case hex digits per byte
def hex(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      +b = byte(h)
      SCon{hex.digit(U32.shrn(b, 4n)), SCon{hex.digit(U32.and(b, 15)), hex(t)}}
