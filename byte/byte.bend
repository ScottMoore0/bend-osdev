# bend-osdev-byte: an 8-bit word, ByteU8, built as Base builds U32 (a
# Word(8n): wrapping arithmetic and bit operations, comparisons, Nat and
# U32 views), and a U32's bytes, least significant first. word16.bend holds
# the 16-bit word, ByteU16. Converting from a U32 keeps its low bits.
#
# From bendlang/bend#1660 (Byte and Word16 for Base, which the Bend team
# preferred to see as a hub package), renamed with this package's prefix:
# Byte is ByteU8, U32.to_byte is ByteU32.to_byte, U32.byte, U32.of_bytes
# and U32.of_bytes_be are ByteU32.byte, .of_bytes and .of_bytes_be, and
# Word.lo, Word.hi and Word.cat are bits.bend's ByteBits.lo, .hi and .cat.
# No natives: these run as ordinary defs in every lane.
import Base
import ./bits.bend as Bt

type ByteU8 is Data:
  ByteU8{data: Word(8n)}

def ByteU8.add(a: ByteU8, b: ByteU8) -> ByteU8:
  match a b:
    case ByteU8{x} ByteU8{y}:
      ByteU8{Word.add(8n, x, y)}

def ByteU8.sub(a: ByteU8, b: ByteU8) -> ByteU8:
  match a b:
    case ByteU8{x} ByteU8{y}:
      ByteU8{Word.sub(8n, x, y)}

def ByteU8.mul(a: ByteU8, b: ByteU8) -> ByteU8:
  match a b:
    case ByteU8{x} ByteU8{y}:
      ByteU8{Word.mul(8n, x, y)}

def ByteU8.and(a: ByteU8, b: ByteU8) -> ByteU8:
  match a b:
    case ByteU8{x} ByteU8{y}:
      ByteU8{Word.and(8n, x, y)}

def ByteU8.or(a: ByteU8, b: ByteU8) -> ByteU8:
  match a b:
    case ByteU8{x} ByteU8{y}:
      ByteU8{Word.or(8n, x, y)}

def ByteU8.xor(a: ByteU8, b: ByteU8) -> ByteU8:
  match a b:
    case ByteU8{x} ByteU8{y}:
      ByteU8{Word.xor(8n, x, y)}

def ByteU8.not(a: ByteU8) -> ByteU8:
  match a:
    case ByteU8{x}:
      ByteU8{Word.not(8n, x)}

def ByteU8.inc(a: ByteU8) -> ByteU8:
  match a:
    case ByteU8{x}:
      ByteU8{Word.inc(8n, x)}

# shifts by one bit
def ByteU8.shl(a: ByteU8) -> ByteU8:
  match a:
    case ByteU8{x}:
      ByteU8{Word.shl(8n, x)}

def ByteU8.shr(a: ByteU8) -> ByteU8:
  match a:
    case ByteU8{x}:
      ByteU8{Word.shr(8n, x)}

def ByteU8.cmp(a: ByteU8, b: ByteU8) -> Cmp:
  match a b:
    case ByteU8{x} ByteU8{y}:
      Word.cmp(8n, x, y)

def ByteU8.is_eq(a: ByteU8, b: ByteU8) -> Bool:
  Cmp.is_eq(ByteU8.cmp(a, b))

def ByteU8.is_lt(a: ByteU8, b: ByteU8) -> Bool:
  Cmp.is_lt(ByteU8.cmp(a, b))

def ByteU8.is_le(a: ByteU8, b: ByteU8) -> Bool:
  Cmp.is_le(ByteU8.cmp(a, b))

def ByteU8.is_gt(a: ByteU8, b: ByteU8) -> Bool:
  Cmp.is_gt(ByteU8.cmp(a, b))

def ByteU8.is_ge(a: ByteU8, b: ByteU8) -> Bool:
  Cmp.is_ge(ByteU8.cmp(a, b))

def ByteU8.to_nat(a: ByteU8) -> Nat:
  match a:
    case ByteU8{w}:
      Word.to_nat(8n, w)

# the byte as a U32 (0 to 255)
def ByteU8.to_u32(a: ByteU8) -> U32:
  match a:
    case ByteU8{w}:
      U32{Bt.ByteBits.cat(8n, 24n, w, Word.zero(24n))}

# the low 8 bits of a U32
def ByteU32.to_byte(a: U32) -> ByteU8:
  match a:
    case U32{w}:
      ByteU8{Bt.ByteBits.lo(8n, 24n, w)}

# n mod 256
def ByteU8.from_nat(n: Nat) -> ByteU8:
  ByteU32.to_byte(U32.from_nat(n))

# decimal
def ByteU8.show(a: ByteU8) -> String:
  U32.show(ByteU8.to_u32(a))

# byte i of a U32 (0 the least significant)
def ByteU32.byte(a: U32, i: Nat) -> ByteU8:
  ByteU32.to_byte(U32.shrn(a, Nat.mul(8n, i)))

# the U32 of four bytes, least significant first
def ByteU32.of_bytes(b0: ByteU8, b1: ByteU8, b2: ByteU8, b3: ByteU8) -> U32:
  match b0 b1 b2 b3:
    case ByteU8{w0} ByteU8{w1} ByteU8{w2} ByteU8{w3}:
      U32{Bt.ByteBits.cat(8n, 24n, w0, Bt.ByteBits.cat(8n, 16n, w1, Bt.ByteBits.cat(8n, 8n, w2, w3)))}

# the U32 of four bytes, most significant first
def ByteU32.of_bytes_be(b3: ByteU8, b2: ByteU8, b1: ByteU8, b0: ByteU8) -> U32:
  ByteU32.of_bytes(b0, b1, b2, b3)
