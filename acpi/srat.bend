# bend-osdev-acpi, srat.bend: the System Resource Affinity Table, "SRAT"
# (ACPI 6.5, section 5.2.16): after the header, 4 reserved bytes (1, for
# compatibility) and 8 reserved bytes, then static resource allocation
# structures from offset 48 (entries.bend). The structures read here, with
# their lengths:
#
#   type  structure (section)                                length
#      0  Processor Local APIC/SAPIC Affinity (5.2.16.1)          16
#      1  Memory Affinity (5.2.16.2)                              40
#      2  Processor Local x2APIC Affinity (5.2.16.3)              24
#      3  GICC Affinity (5.2.16.4)                                18
#      4  GIC ITS Affinity (5.2.16.5)                             12
#      5  Generic Initiator Affinity (5.2.16.6)                   32
#      6  Generic Port Affinity (5.2.16.7, same layout as 5)      32
#
# Flags: bit 0 Enabled; for memory also bit 1 Hot Pluggable, bit 2
# NonVolatile. Other types are kept as AcpiSratOther with their bytes.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./fields.bend as F
import ./entries.bend as N

type AcpiSratEntry is Data:
  # the proximity domain joined from its low byte (offset 2) and its high
  # three bytes (offset 9)
  AcpiSratLapic{domain: U32, apic_id: U32, flags: U32, sapic_eid: U32, clock_domain: U32}
  AcpiSratMemory{domain: U32, base: W.W64, length: W.W64, flags: U32}
  AcpiSratX2apic{domain: U32, x2apic_id: U32, flags: U32, clock_domain: U32}
  AcpiSratGicc{domain: U32, uid: U32, flags: U32, clock_domain: U32}
  AcpiSratGicIts{domain: U32, its_id: U32}
  # kind 5 (generic initiator) or 6 (generic port); the 16-byte device
  # handle as stored (ACPI or PCI form, by handle_type)
  AcpiSratGeneric{kind: U32, handle_type: U32, domain: U32, handle: B.Octets, flags: U32}
  AcpiSratOther{kind: U32, data: B.Octets}

type AcpiSrat is Data:
  AcpiSrat{header: H.AcpiHeader, entries: List<&2, AcpiSratEntry>}

def AcpiSrat.entries(s: AcpiSrat) -> List<&2, AcpiSratEntry>:
  match s:
    case AcpiSrat{h, es}:
      es

def srat.min(k: Nat) -> Nat:
  match k:
    case 0n:
      16n
    case 1n:
      40n
    case 2n:
      24n
    case 3n:
      18n
    case 4n:
      12n
    case 5n:
      32n
    case 6n:
      32n
    case _:
      2n

def srat.typed(k: Nat, +d: B.Octets) -> AcpiSratEntry:
  match k:
    case 0n:
      AcpiSratLapic{U32.or(F.AcpiF.u8(d, 2n), U32.shln(F.AcpiF.u24(d, 9n), 8n)), F.AcpiF.u8(d, 3n), F.AcpiF.u32(d, 4n), F.AcpiF.u8(d, 8n), F.AcpiF.u32(d, 12n)}
    case 1n:
      AcpiSratMemory{F.AcpiF.u32(d, 2n), F.AcpiF.u64(d, 8n), F.AcpiF.u64(d, 16n), F.AcpiF.u32(d, 28n)}
    case 2n:
      AcpiSratX2apic{F.AcpiF.u32(d, 4n), F.AcpiF.u32(d, 8n), F.AcpiF.u32(d, 12n), F.AcpiF.u32(d, 16n)}
    case 3n:
      AcpiSratGicc{F.AcpiF.u32(d, 2n), F.AcpiF.u32(d, 6n), F.AcpiF.u32(d, 10n), F.AcpiF.u32(d, 14n)}
    case 4n:
      AcpiSratGicIts{F.AcpiF.u32(d, 2n), F.AcpiF.u32(d, 8n)}
    case 5n:
      AcpiSratGeneric{5, F.AcpiF.u8(d, 3n), F.AcpiF.u32(d, 4n), F.AcpiF.bytes(d, 8n, 16n), F.AcpiF.u32(d, 24n)}
    case 6n:
      AcpiSratGeneric{6, F.AcpiF.u8(d, 3n), F.AcpiF.u32(d, 4n), F.AcpiF.bytes(d, 8n, 16n), F.AcpiF.u32(d, 24n)}
    case _:
      AcpiSratOther{F.AcpiF.u8(d, 0n), B.Octets.drop(2n, d)}

def srat.entry.pick(ok: Bool, +k: U32, +off: Nat, +d: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSratEntry>:
  match ok:
    case True{}:
      Done{srat.typed(U32.to_nat(k), d)}
    case False{}:
      Fail{E.AcpiBadEntry{off, k}}

def AcpiSratEntry.of_raw(e: N.AcpiRawEntry) -> Result<&2, &2, E.AcpiError, AcpiSratEntry>:
  match e:
    case N.AcpiRawEntry{+k, off, +d}:
      srat.entry.pick(Nat.is_le(srat.min(U32.to_nat(k)), B.Octets.len(d)), k, off, d)

def srat.rev(xs: List<&2, AcpiSratEntry>, acc: List<&2, AcpiSratEntry>) -> List<&2, AcpiSratEntry>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      srat.rev(t, Con{h, acc})

def srat.push(acc: Result<&2, &2, E.AcpiError, List<&2, AcpiSratEntry>>, r: Result<&2, &2, E.AcpiError, AcpiSratEntry>) -> Result<&2, &2, E.AcpiError, List<&2, AcpiSratEntry>>:
  match acc r:
    case Fail{e} _:
      Fail{e}
    case Done{xs} Done{x}:
      Done{Con{x, xs}}
    case Done{xs} Fail{e}:
      Fail{e}

def srat.all(es: List<&2, N.AcpiRawEntry>, acc: Result<&2, &2, E.AcpiError, List<&2, AcpiSratEntry>>) -> Result<&2, &2, E.AcpiError, List<&2, AcpiSratEntry>>:
  match es:
    case Nil{}:
      acc
    case Con{h, t}:
      srat.all(t, srat.push(acc, AcpiSratEntry.of_raw(h)))

def srat.mk(+h: H.AcpiHeader, r: Result<&2, &2, E.AcpiError, List<&2, AcpiSratEntry>>) -> Result<&2, &2, E.AcpiError, AcpiSrat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{es}:
      Done{AcpiSrat{h, srat.rev(es, Nil{})}}

def srat.raw(+h: H.AcpiHeader, r: Result<&2, &2, E.AcpiError, List<&2, N.AcpiRawEntry>>) -> Result<&2, &2, E.AcpiError, AcpiSrat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{es}:
      srat.mk(h, srat.all(es, Done{Nil{}}))

def srat.body(ok: Bool, +h: H.AcpiHeader, +body: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSrat>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{48n, Nat.add(36n, B.Octets.len(body))}}
    case True{}:
      srat.raw(h, N.AcpiRawEntry.split(B.Octets.drop(12n, body), 48n))

def AcpiSrat.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiSrat>:
  match t:
    case H.AcpiSdt{h, +body}:
      srat.body(Nat.is_le(12n, B.Octets.len(body)), h, body)

def srat.parse(r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiSrat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      AcpiSrat.of_sdt(t)

def AcpiSrat.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSrat>:
  srat.parse(H.AcpiSdt.parse_sig(B.Octets.of_string("SRAT"), o))

# Writing

def srat.z(n: Nat) -> B.Octets:
  B.Octets.zeros(n)

def AcpiSratEntry.encode(e: AcpiSratEntry) -> B.Octets:
  match e:
    case AcpiSratLapic{+dm, a, f, s, c}:
      N.AcpiRawEntry.encode(0, B.Octets.concat([B.Octets.of_list([dm, a]), B.Octets.le32(f), B.Octets.of_list([s]), F.AcpiF.le24(U32.shrn(dm, 8n)), B.Octets.le32(c)]))
    case AcpiSratMemory{dm, b, l, f}:
      N.AcpiRawEntry.encode(1, B.Octets.concat([B.Octets.le32(dm), srat.z(2n), B.Octets.le64(b), B.Octets.le64(l), srat.z(4n), B.Octets.le32(f), srat.z(8n)]))
    case AcpiSratX2apic{dm, x, f, c}:
      N.AcpiRawEntry.encode(2, B.Octets.concat([srat.z(2n), B.Octets.le32(dm), B.Octets.le32(x), B.Octets.le32(f), B.Octets.le32(c), srat.z(4n)]))
    case AcpiSratGicc{dm, u, f, c}:
      N.AcpiRawEntry.encode(3, B.Octets.concat([B.Octets.le32(dm), B.Octets.le32(u), B.Octets.le32(f), B.Octets.le32(c)]))
    case AcpiSratGicIts{dm, i}:
      N.AcpiRawEntry.encode(4, B.Octets.concat([B.Octets.le32(dm), srat.z(2n), B.Octets.le32(i)]))
    case AcpiSratGeneric{k, ht, dm, hd, f}:
      N.AcpiRawEntry.encode(k, B.Octets.concat([srat.z(1n), B.Octets.of_list([ht]), B.Octets.le32(dm), F.AcpiF.fit(16n, hd), B.Octets.le32(f), srat.z(4n)]))
    case AcpiSratOther{k, d}:
      N.AcpiRawEntry.encode(k, d)

def srat.enc(es: List<&2, AcpiSratEntry>) -> List<&2, B.Octets>:
  match es:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{AcpiSratEntry.encode(h), srat.enc(t)}

def AcpiSrat.build(s: AcpiSrat) -> B.Octets:
  match s:
    case AcpiSrat{H.AcpiHeader{sg, l, r, c, o, t, orv, ci, cr}, es}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("SRAT"), l, r, c, o, t, orv, ci, cr}, B.Octets.concat([B.Octets.le32(1), srat.z(8n), B.Octets.concat(srat.enc(es))]))
