# A 16-bit word, ByteU16, built as ByteU8 is (byte.bend): wrapping
# arithmetic and bit operations, comparisons, Nat and U32 views, the low 16
# bits of a U32, and the ByteU16 of two bytes. bendlang/bend#1660's Word16,
# U32.to_word16 and Word16.of_bytes, renamed with this package's prefix.
import Base
import ./bits.bend as Bt
import ./byte.bend as By

type ByteU16 is Data:
  ByteU16{data: Word(16n)}

def ByteU16.add(a: ByteU16, b: ByteU16) -> ByteU16:
  match a b:
    case ByteU16{x} ByteU16{y}:
      ByteU16{Word.add(16n, x, y)}

def ByteU16.sub(a: ByteU16, b: ByteU16) -> ByteU16:
  match a b:
    case ByteU16{x} ByteU16{y}:
      ByteU16{Word.sub(16n, x, y)}

def ByteU16.mul(a: ByteU16, b: ByteU16) -> ByteU16:
  match a b:
    case ByteU16{x} ByteU16{y}:
      ByteU16{Word.mul(16n, x, y)}

def ByteU16.and(a: ByteU16, b: ByteU16) -> ByteU16:
  match a b:
    case ByteU16{x} ByteU16{y}:
      ByteU16{Word.and(16n, x, y)}

def ByteU16.or(a: ByteU16, b: ByteU16) -> ByteU16:
  match a b:
    case ByteU16{x} ByteU16{y}:
      ByteU16{Word.or(16n, x, y)}

def ByteU16.xor(a: ByteU16, b: ByteU16) -> ByteU16:
  match a b:
    case ByteU16{x} ByteU16{y}:
      ByteU16{Word.xor(16n, x, y)}

def ByteU16.not(a: ByteU16) -> ByteU16:
  match a:
    case ByteU16{x}:
      ByteU16{Word.not(16n, x)}

def ByteU16.inc(a: ByteU16) -> ByteU16:
  match a:
    case ByteU16{x}:
      ByteU16{Word.inc(16n, x)}

# shifts by one bit
def ByteU16.shl(a: ByteU16) -> ByteU16:
  match a:
    case ByteU16{x}:
      ByteU16{Word.shl(16n, x)}

def ByteU16.shr(a: ByteU16) -> ByteU16:
  match a:
    case ByteU16{x}:
      ByteU16{Word.shr(16n, x)}

def ByteU16.cmp(a: ByteU16, b: ByteU16) -> Cmp:
  match a b:
    case ByteU16{x} ByteU16{y}:
      Word.cmp(16n, x, y)

def ByteU16.is_eq(a: ByteU16, b: ByteU16) -> Bool:
  Cmp.is_eq(ByteU16.cmp(a, b))

def ByteU16.is_lt(a: ByteU16, b: ByteU16) -> Bool:
  Cmp.is_lt(ByteU16.cmp(a, b))

def ByteU16.is_le(a: ByteU16, b: ByteU16) -> Bool:
  Cmp.is_le(ByteU16.cmp(a, b))

def ByteU16.is_gt(a: ByteU16, b: ByteU16) -> Bool:
  Cmp.is_gt(ByteU16.cmp(a, b))

def ByteU16.is_ge(a: ByteU16, b: ByteU16) -> Bool:
  Cmp.is_ge(ByteU16.cmp(a, b))

def ByteU16.to_nat(a: ByteU16) -> Nat:
  match a:
    case ByteU16{w}:
      Word.to_nat(16n, w)

# the word as a U32 (0 to 65535)
def ByteU16.to_u32(a: ByteU16) -> U32:
  match a:
    case ByteU16{w}:
      U32{Bt.ByteBits.cat(16n, 16n, w, Word.zero(16n))}

# the low 16 bits of a U32
def ByteU32.to_word16(a: U32) -> ByteU16:
  match a:
    case U32{w}:
      ByteU16{Bt.ByteBits.lo(16n, 16n, w)}

# n mod 65536
def ByteU16.from_nat(n: Nat) -> ByteU16:
  ByteU32.to_word16(U32.from_nat(n))

# decimal
def ByteU16.show(a: ByteU16) -> String:
  U32.show(ByteU16.to_u32(a))

# the ByteU16 of two bytes, least significant first
def ByteU16.of_bytes(b0: By.ByteU8, b1: By.ByteU8) -> ByteU16:
  match b0 b1:
    case By.ByteU8{w0} By.ByteU8{w1}:
      ByteU16{Bt.ByteBits.cat(8n, 8n, w0, w1)}
