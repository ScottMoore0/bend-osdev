import Base
import ../bytes/bytes.bend as B
import ./xorblocks.bend as X

# n pseudo-random bytes (a linear congruential generator), built tail-recursively
def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def bulk(n: Nat, seed: U32) -> B.Octets:
  B.Octets.of_list(bulk.go(n, seed, Nil{}))

def yes(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def main() -> IO(Unit):
  +a = bulk(200000n, 7)
  +b = bulk(200000n, 11)
  +c = bulk(150000n, 13)
  +x = X.Xorb.xor(a, b)
  do IO<Unit>:
    IO.print(B.Octets.hex(X.Xorb.xor(B.Octets.of_list([1, 2, 3]), B.Octets.of_list([255, 15]))))
    IO.print(B.Octets.hex(X.Xorb.xor_cut(B.Octets.of_list([1, 2, 3]), B.Octets.of_list([255, 15]))))
    IO.print(B.Octets.hex(X.Xorb.into(B.Octets.of_list([170, 85]), [B.Octets.of_list([1, 2]), B.Octets.of_list([4, 8]), B.Octets.of_list([16, 32])])))
    IO.print(B.Octets.hex(X.Xorb.into_with(X.XorbShorter{}, B.Octets.of_list([170, 85, 1]), [B.Octets.of_list([1, 2]), B.Octets.of_list([4, 8, 9])])))
    IO.print(B.Octets.hex(X.Xorb.all([B.Octets.of_list([1]), B.Octets.of_list([2, 3]), B.Octets.of_list([4, 5, 6])])))
    IO.print(yes(B.Octets.is_eq(X.Xorb.xor(x, b), a)))
    IO.print(Nat.show(B.Octets.len(X.Xorb.xor(a, c))))
    IO.print(Nat.show(B.Octets.len(X.Xorb.xor_cut(a, c))))
    IO.print(yes(B.Octets.is_eq(X.Xorb.xor(a, a), B.Octets.zeros(200000n))))
    IO.print(yes(B.Octets.is_eq(X.Xorb.xor(B.Octets.append(a, c), B.Octets.append(b, c)), B.Octets.append(x, B.Octets.zeros(150000n)))))
    IO.print(yes(B.Octets.is_eq(X.Xorb.into(a, [b, c, b, c]), a)))

#|fe0d03
#|fe0d
#|bf7f
#|af5f
#|070606
#|yes
#|200000
#|150000
#|yes
#|yes
#|yes
