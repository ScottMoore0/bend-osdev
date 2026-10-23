import Base
import ./byte.bend as By
import ./word16.bend as Wd
import ./LAWS.bend as Laws

# Each law about bits splits its words into their bits with a deep pattern;
# the conversions then compute on the symbolic bits.

def Laws.u8_to_u32_to_byte(b):
  match b:
    case By.ByteU8{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}}}}}}:
      {==}

def Laws.u16_to_u32_to_word16(w):
  match w:
    case Wd.ByteU16{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WNil{}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.u32_to_byte_low(a):
  match a:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.u32_to_word16_low(a):
  match a:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.u32_bytes_join(a):
  match a:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.u32_join_bytes(b0, b1, b2, b3):
  match b0 b1 b2 b3:
    case By.ByteU8{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}} By.ByteU8{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}} By.ByteU8{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}}} By.ByteU8{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}}:
      {==}

def Laws.u16_of_bytes_u32(b0, b1):
  match b0 b1:
    case By.ByteU8{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}} By.ByteU8{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}}:
      {==}

def Laws.u8_add_comm(a, b):
  match a b:
    case By.ByteU8{x} By.ByteU8{y}:
      Equal.cong(Word(8n), By.ByteU8, z => By.ByteU8{z}, Word.add(8n, x, y), Word.add(8n, y, x), Word.add_comm(8n, x, y))

def Laws.u16_add_comm(a, b):
  match a b:
    case Wd.ByteU16{x} Wd.ByteU16{y}:
      Equal.cong(Word(16n), Wd.ByteU16, z => Wd.ByteU16{z}, Word.add(16n, x, y), Word.add(16n, y, x), Word.add_comm(16n, x, y))

def Laws.vec_bytes_join():
  {==}

def Laws.vec_of_bytes_be():
  {==}

def Laws.vec_add_wraps():
  {==}
