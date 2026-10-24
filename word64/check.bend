import Base
import ./word64.bend as W

# 10^12 = 0xE8_D4A51000
def trillion() -> W.W64:
  W.W64.from_parts(232, 3567587328)

# a / b and a mod b, as decimal text
def dm(+a: W.W64, +b: W.W64) -> String:
  W.W64.show(W.W64.div(a, b)) ++ " " ++ W.W64.show(W.W64.mod(a, b))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(W.W64.show(W.W64.max()))
    IO.print(W.W64.show_hex(W.W64.add(W.W64.max(), W.W64.one())))
    IO.print(W.W64.show_hex(W.W64.mul(W.W64.from_u32(4294967295), W.W64.from_u32(4294967295))))
    IO.print(W.W64.show_hex(W.W64.shl(W.W64.from_parts(3735928559, 3405691582), 8n)))
    IO.print(U32.show(W.W64.hi(W.W64.from_parts(7, 9))))
    IO.print(W.W64.show(W.W64.div(trillion(), W.W64.from_u32(7))))
    IO.print(W.W64.show(W.W64.mod(trillion(), W.W64.from_u32(7))))
    IO.print(Bool.show(W.W64.is_lt(W.W64.from_parts(1, 0), W.W64.from_parts(0, 4294967295))))
    IO.print(dm(W.W64.from_parts(3735928559, 3405691582), W.W64.from_parts(0, 0)))
    IO.print(dm(W.W64.from_parts(4294967295, 4294967295), W.W64.from_parts(0, 1)))
    IO.print(dm(W.W64.from_parts(0, 5), W.W64.from_parts(0, 7)))
    IO.print(dm(W.W64.from_parts(2147483648, 5), W.W64.from_parts(2147483648, 5)))
    IO.print(dm(W.W64.from_parts(4294967295, 4294967295), W.W64.from_parts(2147483648, 1)))
    IO.print(dm(W.W64.from_parts(2147483648, 3), W.W64.from_parts(0, 3)))
    IO.print(dm(W.W64.from_parts(4294967295, 4294967295), W.W64.from_parts(1, 1)))
    IO.print(dm(W.W64.from_parts(305419896, 2596069104), W.W64.from_parts(0, 267242409)))

#|18446744073709551615
#|0000000000000000
#|fffffffe00000001
#|adbeefcafebabe00
#|7
#|142857142857
#|1
#|False
#|0 16045690984503098046
#|18446744073709551615 0
#|0 5
#|1 0
#|1 9223372036854775806
#|3074457345618258603 2
#|4294967295 0
#|4908534062 76354962
