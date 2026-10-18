# bend-osdev-acpi, entries.bend: the variable-length sub-structures that the
# MADT (ACPI 6.5, section 5.2.12) and the SRAT (5.2.16) carry after their
# fixed fields. Each begins with a type byte and a length byte (the
# structure's whole length, these two bytes included).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./fields.bend as F

# one structure: its type, its offset from the start of the table, and its
# bytes (the type and length bytes included)
type AcpiRawEntry is Data:
  AcpiRawEntry{kind: U32, offset: Nat, data: B.Octets}

def AcpiRawEntry.kind(e: AcpiRawEntry) -> U32:
  match e:
    case AcpiRawEntry{k, off, d}:
      k

def AcpiRawEntry.data(e: AcpiRawEntry) -> B.Octets:
  match e:
    case AcpiRawEntry{k, off, d}:
      d

# what comes next in the bytes: nothing, a structure of type k and length l,
# or a structure of type k whose length is bad
type AcpiEntNext is Data:
  AcpiEntEnd{}
  AcpiEntOk{kind: U32, len: Nat}
  AcpiEntBad{kind: U32}

def ent.next.pick(ok: Bool, +k: U32, l: Nat) -> AcpiEntNext:
  match ok:
    case True{}:
      AcpiEntOk{k, l}
    case False{}:
      AcpiEntBad{k}

def ent.next.go(empty: Bool, +o: B.Octets, +n: Nat) -> AcpiEntNext:
  match empty:
    case True{}:
      AcpiEntEnd{}
    case False{}:
      +l = U32.to_nat(F.AcpiF.u8(o, 1n))
      ent.next.pick(Bool.and(Nat.is_le(2n, l), Nat.is_le(l, n)), F.AcpiF.u8(o, 0n), l)

def ent.next(+o: B.Octets) -> AcpiEntNext:
  +n = B.Octets.len(o)
  ent.next.go(Nat.is_eq(n, 0n), o, n)

def ent.rev(xs: List<&2, AcpiRawEntry>, acc: List<&2, AcpiRawEntry>) -> List<&2, AcpiRawEntry>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      ent.rev(t, Con{h, acc})

# every structure consumes at least 2 bytes, so len(o) steps are enough
def ent.go(fuel: Nat, nx: AcpiEntNext, +o: B.Octets, +off: Nat, acc: List<&2, AcpiRawEntry>) -> Result<&2, &2, E.AcpiError, List<&2, AcpiRawEntry>>:
  match fuel:
    case 0n:
      Done{ent.rev(acc, Nil{})}
    case 1n+p:
      match nx:
        case AcpiEntEnd{}:
          Done{ent.rev(acc, Nil{})}
        case AcpiEntBad{k}:
          Fail{E.AcpiBadEntry{off, k}}
        case AcpiEntOk{k, +l}:
          +rest = B.Octets.drop(l, o)
          ent.go(p, ent.next(rest), rest, Nat.add(off, l), Con{AcpiRawEntry{k, off, B.Octets.take(l, o)}, acc})

# the structures in o, which starts at offset off of its table; AcpiBadEntry
# names the first one whose length is below 2 or runs past the end
def AcpiRawEntry.split(+o: B.Octets, +off: Nat) -> Result<&2, &2, E.AcpiError, List<&2, AcpiRawEntry>>:
  ent.go(B.Octets.len(o), ent.next(o), o, off, Nil{})

# the structure as bytes: its type, its length, then body (the bytes after
# the two header bytes)
def AcpiRawEntry.encode(+k: U32, +body: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.of_list([k, U32.from_nat(Nat.add(2n, B.Octets.len(body)))]), body)
