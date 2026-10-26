# The checksum (5.2.6), for every input: AcpiChecksum.fix(i, o), which
# writes the checksum byte at offset i, makes the bytes sum to zero modulo
# 256 whenever o has a byte i, whatever the other bytes are.
import Base
import ../bytes/bytes.bend as B
import ./checksum.bend as C

law fix_ok:
  for +i: Nat
  for +o: B.Octets
  for +h: {Nat.is_lt(i, B.Octets.len(o)) == True{} : Bool}
  {C.AcpiChecksum.ok(C.AcpiChecksum.fix(i, o)) == True{} : Bool}

# the hypothesis holds, and the law with it, at an example
law fix_example:
  {(Nat.is_lt(1n, B.Octets.len(B.Octets.of_list([7, 200, 99]))), C.AcpiChecksum.ok(C.AcpiChecksum.fix(1n, B.Octets.of_list([7, 200, 99])))) == (True{}, True{}) : Bool & Bool}
