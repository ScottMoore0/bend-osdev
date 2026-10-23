import Base
import ./u32.bend as U

# the two sides of u32_add_wrap and u32_sub_wrap, at run time
def add_lhs(+a: U32, +b: U32) -> Nat:
  Nat.add(U32.to_nat(U32.add(a, b)), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32.add(a, b), a))))

def sub_lhs(+a: U32, +b: U32) -> Nat:
  Nat.add(U32.to_nat(U32.sub(a, b)), U32.to_nat(b))

def sub_rhs(+a: U32, +b: U32) -> Nat:
  Nat.add(U32.to_nat(a), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(a, b))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(U.U32Nat.dbl(32n, 1n)))
    IO.print(Nat.show(U.U32Nat.dbl(3n, 5n)))
    IO.print(Nat.show(U.U32Nat.half(1001n)))
    IO.print(Nat.show(add_lhs(4294967295, 2)))
    IO.print(Nat.show(Nat.add(U32.to_nat(4294967295), U32.to_nat(2))))
    IO.print(Nat.show(add_lhs(3000000000, 1000000000)))
    IO.print(Nat.show(sub_lhs(1, 3)))
    IO.print(Nat.show(sub_rhs(1, 3)))
    IO.print(Nat.show(sub_lhs(7, 3)))
    IO.print(Nat.show(U32.to_nat(U32.shln(3, 30n))))

#|4294967296
#|40
#|500
#|4294967297
#|4294967297
#|4000000000
#|4294967297
#|4294967297
#|7
#|3221225472
