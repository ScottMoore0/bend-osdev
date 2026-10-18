import Base
import ../bytes/bytes.bend as B
import bend-kit-bytes@0.3.2.0/bytes.bend as KB
import ./kitbytes.bend as K

def second(r: KB.Bytes & B.Octets) -> B.Octets:
  (b, o) = r
  o

# n pseudo-random bytes (a linear congruential generator), built tail-recursively
def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def bulk(n: Nat) -> B.Octets:
  B.Octets.of_list(bulk.go(n, 7, Nil{}))

def main() -> IO(Unit):
  +big = bulk(102400n)
  do IO<Unit>:
    IO.print(B.Octets.hex(K.round_trip(B.Octets.of_list([0, 1, 127, 128, 254, 255]))))
    IO.print(B.Octets.to_string(second(K.to_octets(KB.from_string("kernel")))))
    IO.print(KB.to_string(K.of_octets(B.Octets.of_string("osdev"))))
    IO.print(Bool.show(B.Octets.is_eq(K.round_trip(big), big)))

#|00017f80feff
#|kernel
#|osdev
#|True
