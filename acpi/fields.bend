# bend-osdev-acpi, fields.bend (internal): little-endian field readers for
# table parsers, over bytes whose length the parser has already checked. A
# field past the end reads as zero; every parser checks a table's length
# before reading the fields that length must hold.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

def AcpiF.u8(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, i), 0)

def AcpiF.u16(o: B.Octets, +i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le16_at(o, i), 0)

def AcpiF.u32(o: B.Octets, +i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le32_at(o, i), 0)

def AcpiF.u64(o: B.Octets, +i: Nat) -> W.W64:
  Maybe.default(&2, W.W64, B.Octets.le64_at(o, i), W.W64.zero())

# the 3-byte little-endian field at offset i
def AcpiF.u24(+o: B.Octets, +i: Nat) -> U32:
  U32.or(AcpiF.u16(o, i), U32.shln(AcpiF.u8(o, Nat.add(i, 2n)), 16n))

# n bytes at offset i (fewer if o ends first)
def AcpiF.bytes(o: B.Octets, +i: Nat, n: Nat) -> B.Octets:
  B.Octets.slice(i, n, o)

# bit k of a word
def AcpiF.bit(+v: U32, k: Nat) -> Bool:
  U32.is_eq(U32.and(U32.shrn(v, k), 1), 1)

# bits k .. k + n - 1 of a word
def AcpiF.bits(+v: U32, k: Nat, n: Nat) -> U32:
  U32.and(U32.shrn(v, k), U32.sub(U32.shln(1, n), 1))

# one byte, as Octets
def AcpiF.byte(v: U32) -> B.Octets:
  B.Octets.of_list([v])

def AcpiF.le16(v: U32) -> B.Octets:
  B.Octets.le16(v)

def AcpiF.le32(v: U32) -> B.Octets:
  B.Octets.le32(v)

def AcpiF.le64(v: W.W64) -> B.Octets:
  B.Octets.le64(v)

# the 3-byte little-endian encoding of the low 24 bits of v
def AcpiF.le24(+v: U32) -> B.Octets:
  B.Octets.of_list([v, U32.shrn(v, 8n), U32.shrn(v, 16n)])

# o cut or padded with zeros to exactly n bytes
def AcpiF.fit(+n: Nat, +o: B.Octets) -> B.Octets:
  +h = B.Octets.take(n, o)
  B.Octets.append(h, B.Octets.zeros(Nat.sub(n, B.Octets.len(h))))
