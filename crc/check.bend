import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./crc.bend as C

def nine() -> B.Octets:
  B.Octets.of_string("123456789")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(B.hex(B.be32(C.crc32c(nine()))))
    IO.print(B.hex(B.be32(C.crc32(nine()))))
    IO.print(B.hex(B.be16(C.crc16(nine()))))
    IO.print(B.hex(B.be16(C.crc_t10dif(nine()))))
    IO.print(W.W64.show_hex(C.crc64_ecma(nine())))
    IO.print(W.W64.show_hex(C.crc64_xz(nine())))
    IO.print(W.W64.show_hex(C.crc64_nvme(nine())))
    IO.print(B.hex(B.be32(C.Crc32Spec.finish(C.crc32c.spec(), C.Crc32Spec.update(C.crc32c.spec(), C.Crc32Spec.update(C.crc32c.spec(), C.Crc32Spec.start(C.crc32c.spec()), B.Octets.of_string("1234")), B.Octets.of_string("56789"))))))

#|e3069283
#|cbf43926
#|bb3d
#|d0db
#|6c40df5f0b497347
#|995dc9bbdf1939fa
#|ae8b14860a799888
#|e3069283
