import Base
import ../bytes/bytes.bend as B
import bend-kit-bytes@0.3.2.0/bytes.bend as KB
import ./kitbytes.bend as K

def second(r: KB.Bytes & B.Octets) -> B.Octets:
  (b, o) = r
  o

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(B.Octets.hex(K.round_trip(B.Octets.of_list([0, 1, 127, 128, 254, 255]))))
    IO.print(B.Octets.to_string(second(K.to_octets(KB.from_string("kernel")))))
    IO.print(KB.to_string(K.of_octets(B.Octets.of_string("osdev"))))

#|00017f80feff
#|kernel
#|osdev
