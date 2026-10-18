import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./crc.bend as C
import ./table.bend as T

def nine() -> B.Octets:
  B.Octets.of_string("123456789")

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
    IO.print(B.hex(B.be32(C.crc32c(nine()))))
    IO.print(B.hex(B.be32(C.crc32(nine()))))
    IO.print(B.hex(B.be16(C.crc16(nine()))))
    IO.print(B.hex(B.be16(C.crc_t10dif(nine()))))
    IO.print(W.W64.show_hex(C.crc64_ecma(nine())))
    IO.print(W.W64.show_hex(C.crc64_xz(nine())))
    IO.print(W.W64.show_hex(C.crc64_nvme(nine())))
    IO.print(B.hex(B.be32(C.Crc32Spec.finish(C.crc32c.spec(), C.Crc32Spec.update(C.crc32c.spec(), C.Crc32Spec.update(C.crc32c.spec(), C.Crc32Spec.start(C.crc32c.spec()), B.Octets.of_string("1234")), B.Octets.of_string("56789"))))))
    IO.print(B.hex(B.be32(C.crc32c(big))))
    IO.print(B.hex(B.be32(T.Crc32Spec.compute_fast(C.crc32c.spec(), big))))
    IO.print(W.W64.show_hex(T.Crc64Spec.compute_fast(C.crc64_xz.spec(), big)))

#|e3069283
#|cbf43926
#|bb3d
#|d0db
#|6c40df5f0b497347
#|995dc9bbdf1939fa
#|ae8b14860a799888
#|e3069283
#|70cabb82
#|70cabb82
#|5fffa685dfdeb9c0
