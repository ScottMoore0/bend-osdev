# bend-osdev-acpi, checksum.bend: the ACPI checksum (ACPI 6.5, section
# 5.2.6, and 5.2.5.3 for the RSDP). A table is valid when all its bytes,
# its checksum byte included, sum to zero modulo 256.
import Base
import ../bytes/bytes.bend as B

# the sum of the bytes, modulo 2^32 (tail-recursive)
def ck.sum.go(xs: List<&2, U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      ck.sum.go(t, U32.add(acc, U32.and(255, h)))

# the sum of the bytes, modulo 256
def AcpiChecksum.sum(o: B.Octets) -> U32:
  U32.and(255, ck.sum.go(B.Octets.to_list(o), 0))

# the bytes sum to zero modulo 256
def AcpiChecksum.ok(o: B.Octets) -> Bool:
  U32.is_eq(AcpiChecksum.sum(o), 0)

# the byte that, put at offset i of o (whose byte there is ignored), makes
# o sum to zero modulo 256
def AcpiChecksum.byte_for(+i: Nat, +o: B.Octets) -> U32:
  +without = U32.and(255, U32.sub(AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))))
  U32.and(255, U32.sub(256, without))

def ck.fix.pick(fits: Bool, +i: Nat, +o: B.Octets) -> B.Octets:
  match fits:
    case True{}:
      B.Octets.concat([B.Octets.take(i, o), B.Octets.of_list([AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o)])
    case False{}:
      o

# o with its byte at offset i replaced by the checksum byte (o unchanged if
# it has no byte i)
def AcpiChecksum.fix(+i: Nat, +o: B.Octets) -> B.Octets:
  ck.fix.pick(Nat.is_lt(i, B.Octets.len(o)), i, o)
