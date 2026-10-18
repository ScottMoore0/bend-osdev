# bend-osdev-acpi, rsdt.bend: the Root and Extended System Description
# Tables (ACPI 6.5, sections 5.2.7 and 5.2.8): a header, then the physical
# addresses of the other tables, 4 bytes each in the RSDT ("RSDT"), 8 bytes
# each in the XSDT ("XSDT"). Addresses are answered as W64 for both.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./fields.bend as F

type AcpiSdtList is Data:
  AcpiSdtList{header: H.AcpiHeader, entries: List<&2, W.W64>}

def AcpiSdtList.entries(t: AcpiSdtList) -> List<&2, W.W64>:
  match t:
    case AcpiSdtList{h, es}:
      es

def AcpiSdtList.header(t: AcpiSdtList) -> H.AcpiHeader:
  match t:
    case AcpiSdtList{h, es}:
      h

def sl.rev(xs: List<&2, W.W64>, acc: List<&2, W.W64>) -> List<&2, W.W64>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      sl.rev(t, Con{h, acc})

# n entries of width 4 or 8 bytes from the front of o
def sl.read(n: Nat, wide: Bool, +o: B.Octets, acc: List<&2, W.W64>) -> List<&2, W.W64>:
  match n:
    case 0n:
      sl.rev(acc, Nil{})
    case 1n+p:
      match wide:
        case True{}:
          sl.read(p, True{}, B.Octets.drop(8n, o), Con{F.AcpiF.u64(o, 0n), acc})
        case False{}:
          sl.read(p, False{}, B.Octets.drop(4n, o), Con{W.W64.from_u32(F.AcpiF.u32(o, 0n)), acc})

def sl.width(wide: Bool) -> Nat:
  match wide:
    case True{}:
      8n
    case False{}:
      4n

def sl.body(ok: Bool, +wide: Bool, +h: H.AcpiHeader, +body: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSdtList>:
  match ok:
    case False{}:
      Fail{E.AcpiBadSize{B.Octets.len(body)}}
    case True{}:
      Done{AcpiSdtList{h, sl.read(Nat.div(B.Octets.len(body), sl.width(wide)), wide, body, Nil{})}}

# a checked table's body as entries; AcpiBadSize if it is not a whole
# number of them
def sl.of_sdt(+wide: Bool, t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiSdtList>:
  match t:
    case H.AcpiSdt{h, +body}:
      sl.body(Nat.is_eq(Nat.mod(B.Octets.len(body), sl.width(wide)), 0n), wide, h, body)

def AcpiRsdt.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiSdtList>:
  sl.of_sdt(False{}, t)

def AcpiXsdt.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiSdtList>:
  sl.of_sdt(True{}, t)

def sl.parse(+wide: Bool, r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiSdtList>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      sl.of_sdt(wide, t)

def AcpiRsdt.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSdtList>:
  sl.parse(False{}, H.AcpiSdt.parse_sig(B.Octets.of_string("RSDT"), o))

def AcpiXsdt.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSdtList>:
  sl.parse(True{}, H.AcpiSdt.parse_sig(B.Octets.of_string("XSDT"), o))

def sl.enc(xs: List<&2, W.W64>, wide: Bool) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match wide:
        case True{}:
          Con{B.Octets.le64(h), sl.enc(t, True{})}
        case False{}:
          Con{B.Octets.le32(W.W64.lo(h)), sl.enc(t, False{})}

# the table (header from H.AcpiHeader.make or decoded; its signature is
# replaced, its length and checksum computed). RSDT entries keep the low 32
# bits of each address.
def AcpiRsdt.build(h: H.AcpiHeader, xs: List<&2, W.W64>) -> B.Octets:
  match h:
    case H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("RSDT"), l, r, c, o, t, orv, ci, cr}, B.Octets.concat(sl.enc(xs, False{})))

def AcpiXsdt.build(h: H.AcpiHeader, xs: List<&2, W.W64>) -> B.Octets:
  match h:
    case H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("XSDT"), l, r, c, o, t, orv, ci, cr}, B.Octets.concat(sl.enc(xs, True{})))
