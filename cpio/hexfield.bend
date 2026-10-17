# bend-osdev-cpio, hexfield.bend: a 32-bit value as eight ASCII hex digits,
# most significant first, as every field of a newc or crc cpio header is
# stored (cpio(5)). The writer uses upper-case digits; the reader takes
# either case.
#
# Public: hexfield_encode, hexfield_decode. The list-level defs below them
# are internal (cpio.bend reads header fields with them).
#
# The digits are computed from the value's bits by slicing (W64.bits.lo/hi),
# not with shifts and masks, so that the round trip can be proved for every
# value.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

# the ASCII hex digit (0-9, A-F) of four bits, least significant first
def nibble.encode.go(b3: Bool, b2: Bool, b1: Bool, b0: Bool) -> U32:
  match b3 b2 b1 b0:
    case False{} False{} False{} False{}:
      48
    case False{} False{} False{} True{}:
      49
    case False{} False{} True{} False{}:
      50
    case False{} False{} True{} True{}:
      51
    case False{} True{} False{} False{}:
      52
    case False{} True{} False{} True{}:
      53
    case False{} True{} True{} False{}:
      54
    case False{} True{} True{} True{}:
      55
    case True{} False{} False{} False{}:
      56
    case True{} False{} False{} True{}:
      57
    case True{} False{} True{} False{}:
      65
    case True{} False{} True{} True{}:
      66
    case True{} True{} False{} False{}:
      67
    case True{} True{} False{} True{}:
      68
    case True{} True{} True{} False{}:
      69
    case True{} True{} True{} True{}:
      70

def nibble.encode(w: Word(4n)) -> U32:
  match w:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WNil{}}}}}:
      nibble.encode.go(b3, b2, b1, b0)

# the low four bits of a word
def nibble.low4(v: U32) -> Word(4n):
  match v:
    case U32{w}:
      W.W64.bits.lo(4n, 28n, w)

# Reading a hex digit (either case); c is a byte, below 256.
def nibble.decode.lower(lt: Bool, +c: U32) -> Maybe<&2, Word(4n)>:
  match lt:
    case True{}:
      Some{nibble.low4(U32.sub(c, 87))}
    case False{}:
      None{}

def nibble.decode.gap2(lt: Bool, +c: U32) -> Maybe<&2, Word(4n)>:
  match lt:
    case True{}:
      None{}
    case False{}:
      nibble.decode.lower(U32.is_lt(c, 103), c)

def nibble.decode.upper(lt: Bool, +c: U32) -> Maybe<&2, Word(4n)>:
  match lt:
    case True{}:
      Some{nibble.low4(U32.sub(c, 55))}
    case False{}:
      nibble.decode.gap2(U32.is_lt(c, 97), c)

def nibble.decode.gap1(lt: Bool, +c: U32) -> Maybe<&2, Word(4n)>:
  match lt:
    case True{}:
      None{}
    case False{}:
      nibble.decode.upper(U32.is_lt(c, 71), c)

def nibble.decode.digit(lt: Bool, +c: U32) -> Maybe<&2, Word(4n)>:
  match lt:
    case True{}:
      Some{nibble.low4(U32.sub(c, 48))}
    case False{}:
      nibble.decode.gap1(U32.is_lt(c, 65), c)

def nibble.decode.low(lt: Bool, +c: U32) -> Maybe<&2, Word(4n)>:
  match lt:
    case True{}:
      None{}
    case False{}:
      nibble.decode.digit(U32.is_lt(c, 58), c)

# the four bits of a hex digit; None if the byte (its low 8 bits) is not one
def nibble.decode(x: U32) -> Maybe<&2, Word(4n)>:
  +c = U32.and(x, 255)
  nibble.decode.low(U32.is_lt(c, 48), c)

# the eight digits of a value, most significant first
def field.encode(v: U32) -> List<&2, U32>:
  match v:
    case U32{+w}:
      +r1 = W.W64.bits.hi(4n, 28n, w)
      +r2 = W.W64.bits.hi(4n, 24n, r1)
      +r3 = W.W64.bits.hi(4n, 20n, r2)
      +r4 = W.W64.bits.hi(4n, 16n, r3)
      +r5 = W.W64.bits.hi(4n, 12n, r4)
      +r6 = W.W64.bits.hi(4n, 8n, r5)
      +r7 = W.W64.bits.hi(4n, 4n, r6)
      [nibble.encode(r7), nibble.encode(W.W64.bits.lo(4n, 4n, r6)), nibble.encode(W.W64.bits.lo(4n, 8n, r5)), nibble.encode(W.W64.bits.lo(4n, 12n, r4)), nibble.encode(W.W64.bits.lo(4n, 16n, r3)), nibble.encode(W.W64.bits.lo(4n, 20n, r2)), nibble.encode(W.W64.bits.lo(4n, 24n, r1)), nibble.encode(W.W64.bits.lo(4n, 28n, w))]

# the value whose eight digits read as these, most significant first
def field.join(m7: Maybe<&2, Word(4n)>, m6: Maybe<&2, Word(4n)>, m5: Maybe<&2, Word(4n)>, m4: Maybe<&2, Word(4n)>, m3: Maybe<&2, Word(4n)>, m2: Maybe<&2, Word(4n)>, m1: Maybe<&2, Word(4n)>, m0: Maybe<&2, Word(4n)>) -> Maybe<&2, U32>:
  match m7 m6 m5 m4 m3 m2 m1 m0:
    case Some{n7} Some{n6} Some{n5} Some{n4} Some{n3} Some{n2} Some{n1} Some{n0}:
      Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}}
    case _ _ _ _ _ _ _ _:
      None{}

# the value in the first eight bytes; None if they are not eight hex digits
def field.decode(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{c7, Con{c6, Con{c5, Con{c4, Con{c3, Con{c2, Con{c1, Con{c0, t}}}}}}}}:
      field.join(nibble.decode(c7), nibble.decode(c6), nibble.decode(c5), nibble.decode(c4), nibble.decode(c3), nibble.decode(c2), nibble.decode(c1), nibble.decode(c0))
    case _:
      None{}

# Public

# the eight upper-case hex digits of v
def hexfield_encode(v: U32) -> B.Octets:
  B.Octets.of_list(field.encode(v))

# the value of the eight hex digits at the head of o (either case); None if o
# is shorter than eight bytes or they are not all hex digits
def hexfield_decode(o: B.Octets) -> Maybe<&2, U32>:
  field.decode(B.Octets.to_list(o))
