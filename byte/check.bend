# ByteU8 and ByteU16 on small examples: bendlang/bend#1660's test line
# (arithmetic that wraps at 8 and 16 bits, U32 views of the low bits, a U32
# split into bytes and joined back both ways), then comparisons, Nat views,
# the bits of a U32 beyond 16, and decimal text. ref/ compares every
# operation with Python's integers.
import Base
import ./byte.bend as By
import ./word16.bend as Wd

def b(n: Nat) -> By.ByteU8:
  By.ByteU8.from_nat(n)

def w(n: Nat) -> Wd.ByteU16:
  Wd.ByteU16.from_nat(n)

def u32s(xs: List<U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match t:
        case Nil{}:
          U32.show(x)
        case Con{y, r}:
          U32.show(x) ++ ", " ++ u32s(Con{y, r})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("[" ++ u32s([By.ByteU8.to_u32(By.ByteU8.add(b(250n), b(10n))), By.ByteU8.to_u32(By.ByteU8.sub(b(3n), b(5n))), By.ByteU8.to_u32(By.ByteU8.mul(b(16n), b(17n))), By.ByteU8.to_u32(By.ByteU8.xor(b(170n), b(255n))), By.ByteU8.to_u32(By.ByteU8.shl(b(129n))), By.ByteU8.to_u32(By.ByteU32.byte(305419896, 0n)), By.ByteU8.to_u32(By.ByteU32.byte(305419896, 3n)), Wd.ByteU16.to_u32(Wd.ByteU16.add(Wd.ByteU32.to_word16(65535), Wd.ByteU32.to_word16(2))), Wd.ByteU16.to_u32(Wd.ByteU16.of_bytes(b(52n), b(18n))), By.ByteU32.of_bytes(b(120n), b(86n), b(52n), b(18n)), By.ByteU32.of_bytes_be(b(18n), b(52n), b(86n), b(120n))]) ++ "]")
    IO.print("200 < 7: " ++ Bool.show(By.ByteU8.is_lt(b(200n), b(7n))) ++ ", 7 <= 7: " ++ Bool.show(By.ByteU8.is_le(b(7n), b(7n))) ++ ", 300 is " ++ By.ByteU8.show(b(300n)))
    IO.print("not 0: " ++ By.ByteU8.show(By.ByteU8.not(b(0n))) ++ ", 255 + 1: " ++ By.ByteU8.show(By.ByteU8.inc(b(255n))) ++ ", 255 >> 1: " ++ By.ByteU8.show(By.ByteU8.shr(b(255n))) ++ ", as Nat: " ++ Nat.show(By.ByteU8.to_nat(b(201n))))
    IO.print("16 bits: 70000 is " ++ Wd.ByteU16.show(w(70000n)) ++ ", 300 * 300 is " ++ Wd.ByteU16.show(Wd.ByteU16.mul(w(300n), w(300n))) ++ ", 1 - 2 is " ++ Wd.ByteU16.show(Wd.ByteU16.sub(w(1n), w(2n))) ++ ", 32768 << 1 is " ++ Wd.ByteU16.show(Wd.ByteU16.shl(w(32768n))))
    IO.print("the low 16 bits of 3735928559: " ++ Wd.ByteU16.show(Wd.ByteU32.to_word16(3735928559)) ++ ", its low byte: " ++ By.ByteU8.show(By.ByteU32.to_byte(3735928559)))

#|[4, 254, 16, 85, 2, 120, 18, 1, 4660, 305419896, 305419896]
#|200 < 7: False, 7 <= 7: True, 300 is 44
#|not 0: 255, 255 + 1: 0, 255 >> 1: 127, as Nat: 201
#|16 bits: 70000 is 4464, 300 * 300 is 24464, 1 - 2 is 65535, 32768 << 1 is 0
#|the low 16 bits of 3735928559: 48879, its low byte: 239
