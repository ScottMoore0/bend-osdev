import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./khash.bend as J
import ./golden.bend as G

def u(x: U32) -> String:
  U32.show(x)

# n pseudo-random bytes (a linear congruential generator)
def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(u(J.Jhash.jhash(B.Octets.empty(), 0)))
    IO.print(u(J.Jhash.jhash(B.Octets.empty(), 3735928559)))
    IO.print(u(J.Jhash.jhash(B.Octets.of_string("Four score and seven years ago"), 0)))
    IO.print(u(J.Jhash.jhash(B.Octets.of_string("Four score and seven years ago"), 1)))
    IO.print(u(J.Jhash.jhash2([1, 2, 3, 4, 5, 6, 7], 13)))
    IO.print(u(J.Jhash.jhash_3words(1, 2, 3, 4)))
    IO.print(u(G.KHash.hash_32(12345, 16n)))
    IO.print(u(G.KHash.hash_long(W.W64.from_parts(28744, 2249056121), 16n)))
    IO.print(u(J.Jhash.jhash(B.Octets.of_list(bulk.go(100000n, 7, Nil{})), 0)))

#|3735928559
#|3176889822
#|393676113
#|3445784929
#|317751706
#|2164462655
#|24275
#|14966
#|2568538116
