import Base
import ./word64.bend as W

# 10^12 = 0xE8_D4A51000
def trillion() -> W.W64:
  W.W64.from_parts(232, 3567587328)

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

#|18446744073709551615
#|0000000000000000
#|fffffffe00000001
#|adbeefcafebabe00
#|7
#|142857142857
#|1
#|False
