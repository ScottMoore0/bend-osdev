# The laws of ByteU8, ByteU16 and a U32's bytes, over the public interface.
#
# Properties, for every input: a byte (a 16-bit word) taken to a U32 and
# back is itself (bendlang/bend#1660's one law, Byte.to_u32_to_byte, and its
# 16-bit twin); a U32 taken to a byte (a 16-bit word) and back is its low 8
# (16) bits; a U32's four bytes join back to it, and four bytes joined are
# the U32's four bytes; two bytes joined as a 16-bit word are the U32 with
# those low bytes; addition commutes.
#
# Vectors: bendlang/bend#1660's test (tests/base/byte_word16.bend): a U32
# split into bytes and joined, a big-endian join, and a byte sum that wraps.
import Base
import ./byte.bend as By
import ./word16.bend as Wd

# Properties

law u8_to_u32_to_byte:
  for b: By.ByteU8
  {By.ByteU32.to_byte(By.ByteU8.to_u32(b)) == b : By.ByteU8}

law u16_to_u32_to_word16:
  for w: Wd.ByteU16
  {Wd.ByteU32.to_word16(Wd.ByteU16.to_u32(w)) == w : Wd.ByteU16}

law u32_to_byte_low:
  for a: U32
  {By.ByteU8.to_u32(By.ByteU32.to_byte(a)) == U32.and(255, a) : U32}

law u32_to_word16_low:
  for a: U32
  {Wd.ByteU16.to_u32(Wd.ByteU32.to_word16(a)) == U32.and(65535, a) : U32}

law u32_bytes_join:
  for +a: U32
  {By.ByteU32.of_bytes(By.ByteU32.byte(a, 0n), By.ByteU32.byte(a, 1n), By.ByteU32.byte(a, 2n), By.ByteU32.byte(a, 3n)) == a : U32}

law u32_join_bytes:
  for +b0: By.ByteU8
  for +b1: By.ByteU8
  for +b2: By.ByteU8
  for +b3: By.ByteU8
  {[By.ByteU32.byte(By.ByteU32.of_bytes(b0, b1, b2, b3), 0n), By.ByteU32.byte(By.ByteU32.of_bytes(b0, b1, b2, b3), 1n), By.ByteU32.byte(By.ByteU32.of_bytes(b0, b1, b2, b3), 2n), By.ByteU32.byte(By.ByteU32.of_bytes(b0, b1, b2, b3), 3n)] == [b0, b1, b2, b3] : List<By.ByteU8>}

law u16_of_bytes_u32:
  for b0: By.ByteU8
  for b1: By.ByteU8
  {Wd.ByteU16.to_u32(Wd.ByteU16.of_bytes(b0, b1)) == By.ByteU32.of_bytes(b0, b1, By.ByteU8.from_nat(0n), By.ByteU8.from_nat(0n)) : U32}

law u8_add_comm:
  for a: By.ByteU8
  for b: By.ByteU8
  {By.ByteU8.add(a, b) == By.ByteU8.add(b, a) : By.ByteU8}

law u16_add_comm:
  for a: Wd.ByteU16
  for b: Wd.ByteU16
  {Wd.ByteU16.add(a, b) == Wd.ByteU16.add(b, a) : Wd.ByteU16}

# Vectors (0x12345678 = 305419896)

law vec_bytes_join:
  {By.ByteU32.of_bytes(By.ByteU32.byte(305419896, 0n), By.ByteU32.byte(305419896, 1n), By.ByteU32.byte(305419896, 2n), By.ByteU32.byte(305419896, 3n)) == 305419896 : U32}

law vec_of_bytes_be:
  {By.ByteU32.of_bytes_be(By.ByteU8.from_nat(18n), By.ByteU8.from_nat(52n), By.ByteU8.from_nat(86n), By.ByteU8.from_nat(120n)) == 305419896 : U32}

law vec_add_wraps:
  {By.ByteU8.add(By.ByteU8.from_nat(250n), By.ByteU8.from_nat(10n)) == By.ByteU8.from_nat(4n) : By.ByteU8}
