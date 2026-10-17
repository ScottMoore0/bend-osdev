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

# n bytes 0, 1, 2, ... (mod 256), built tail-recursively
def ramp(n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      ramp(p, Con{U32.and(U32.from_nat(p), 255), acc})

# the fast Octets forms against the list layer, on a string short enough for
# the structural list functions
def same_as_list(+o: B.Octets) -> Bool:
  Bool.and(String.eq(B.Octets.hex(o), B.hex(B.Octets.to_list(o))), String.eq(B.Octets.to_string(o), B.to_string(B.Octets.to_list(o))))

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
    IO.print(Bool.show(same_as_list(B.Octets.of_list(ramp(3000n, Nil{})))))
    IO.print(Nat.show(B.Octets.len(B.Octets.append(B.Octets.of_list(ramp(60000n, Nil{})), B.Octets.zeros(40000n)))))
    IO.print(String.take(B.Octets.hex(B.Octets.drop(59998n, B.Octets.of_list(ramp(60000n, Nil{})))), 4n))

#|12345678
#|78563412
#|0807060504030201
#|258
#|1684956482
#|0102030405060708
#|none
#|01020000
#|dev
#|True
#|100000
#|5e5f
