import Base
import ../word64/word64.bend as W
import ./bytes.bend as B

def show_u32(m: Maybe<&2, U32>) -> String:
  match m:
    case Some{v}:
      U32.show(v)
    case None{}:
      "none"

def show_w64(m: Maybe<&2, W.W64>) -> String:
  match m:
    case Some{v}:
      W.W64.show_hex(v)
    case None{}:
      "none"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(B.hex(B.be32(305419896)))
    IO.print(B.hex(B.le32(305419896)))
    IO.print(B.hex(B.le64(W.W64.from_parts(16909060, 84281096))))
    IO.print(show_u32(B.be16_at([0, 1, 2, 3], 1n)))
    IO.print(show_u32(B.le32_at(B.of_string("Bend"), 0n)))
    IO.print(show_w64(B.be64_at([0, 1, 2, 3, 4, 5, 6, 7, 8], 1n)))
    IO.print(show_u32(B.le32_at([1, 2, 3], 0n)))
    IO.print(B.hex(B.append(B.take(2n, [1, 2, 3, 4]), B.zeros(2n))))
    IO.print(B.to_string(B.drop(2n, B.of_string("osdev"))))

#|12345678
#|78563412
#|0807060504030201
#|258
#|1684956482
#|0102030405060708
#|none
#|01020000
#|dev
