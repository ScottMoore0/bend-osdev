# bend-osdev-acpi, madt.bend: the Multiple APIC Description Table, "APIC"
# (ACPI 6.5, section 5.2.12): after the header, the local interrupt
# controller address (4 bytes, offset 36) and flags (4 bytes, offset 40;
# bit 0 PCAT_COMPAT, dual 8259s present), then interrupt controller
# structures from offset 44 (entries.bend). The structures read here, with
# their minimum lengths (later revisions may lengthen a structure; the extra
# bytes are ignored):
#
#   type  structure (table)                          length
#      0  Processor Local APIC (5.2.12.2)                 8
#      1  I/O APIC (5.2.12.3)                            12
#      2  Interrupt Source Override (5.2.12.5)           10
#      3  NMI Source (5.2.12.6)                           8
#      4  Local APIC NMI (5.2.12.7)                       6
#      5  Local APIC Address Override (5.2.12.8)         12
#      9  Processor Local x2APIC (5.2.12.12)             16
#     10  Local x2APIC NMI (5.2.12.13)                   12
#     11  GIC CPU Interface, GICC (5.2.12.14)  76 (80 from ACPI 6.0, 82
#         from 6.5: the SPE and TRBE interrupts read as 0 when absent)
#     12  GIC Distributor, GICD (5.2.12.15)              24
#     13  GIC MSI Frame (5.2.12.16)                      24
#     14  GIC Redistributor, GICR (5.2.12.17)            16
#     15  GIC Interrupt Translation Service (5.2.12.18)  20
#     16  Multiprocessor Wakeup (5.2.12.19)              16
#
# Every other type (I/O SAPIC, Local SAPIC, platform interrupt sources, the
# LoongArch controllers, OEM types) is kept as AcpiMadtOther with its bytes.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./fields.bend as F
import ./entries.bend as N

# the GICC's addresses, grouped (bendlang/bend#1069: records of many W64s)
type AcpiGiccAddrs is Data:
  AcpiGiccAddrs{parked: W.W64, base: W.W64, gicv: W.W64, gich: W.W64, gicr: W.W64}

type AcpiMadtEntry is Data:
  # flags: bit 0 Enabled, bit 1 Online Capable
  AcpiMadtLapic{uid: U32, apic_id: U32, flags: U32}
  AcpiMadtIoApic{id: U32, address: U32, gsi_base: U32}
  # flags: MPS INTI flags, bits 0-1 polarity, bits 2-3 trigger mode
  AcpiMadtIso{bus: U32, source: U32, gsi: U32, flags: U32}
  AcpiMadtNmiSource{flags: U32, gsi: U32}
  # uid 0xFF: every processor
  AcpiMadtLapicNmi{uid: U32, flags: U32, lint: U32}
  AcpiMadtLapicOverride{address: W.W64}
  AcpiMadtX2apic{x2apic_id: U32, flags: U32, uid: U32}
  # uid 0xFFFFFFFF: every processor
  AcpiMadtX2apicNmi{flags: U32, uid: U32, lint: U32}
  AcpiMadtGicc{cpu_interface: U32, uid: U32, flags: U32, parking_version: U32, perf_gsiv: U32, vgic_gsiv: U32, addrs: AcpiGiccAddrs, mpidr: W.W64, efficiency_class: U32, spe_gsiv: U32, trbe_gsiv: U32}
  AcpiMadtGicd{gic_id: U32, base: W.W64, version: U32}
  AcpiMadtGicMsi{id: U32, base: W.W64, flags: U32, spi_count: U32, spi_base: U32}
  AcpiMadtGicr{base: W.W64, length: U32}
  AcpiMadtGicIts{id: U32, base: W.W64}
  AcpiMadtWakeup{version: U32, mailbox: W.W64}
  # any other type: its type and its bytes after the two header bytes
  AcpiMadtOther{kind: U32, data: B.Octets}

type AcpiMadt is Data:
  AcpiMadt{header: H.AcpiHeader, lapic_address: U32, flags: U32, entries: List<&2, AcpiMadtEntry>}

def AcpiMadt.entries(m: AcpiMadt) -> List<&2, AcpiMadtEntry>:
  match m:
    case AcpiMadt{h, a, f, es}:
      es

def AcpiMadt.lapic_address32(m: AcpiMadt) -> U32:
  match m:
    case AcpiMadt{h, a, f, es}:
      a

def AcpiMadt.flags(m: AcpiMadt) -> U32:
  match m:
    case AcpiMadt{h, a, f, es}:
      f

# Reading one structure from its bytes (d: all of them, type and length
# included); the minimum length of each type is checked first

def madt.min.go(k: Nat) -> Nat:
  match k:
    case 0n:
      8n
    case 1n:
      12n
    case 2n:
      10n
    case 3n:
      8n
    case 4n:
      6n
    case 5n:
      12n
    case 9n:
      16n
    case 10n:
      12n
    case 11n:
      76n
    case 12n:
      24n
    case 13n:
      24n
    case 14n:
      16n
    case 15n:
      20n
    case 16n:
      16n
    case _:
      2n

def madt.min(+k: U32) -> Nat:
  madt.min.go(U32.to_nat(k))

def madt.gicc(+d: B.Octets) -> AcpiMadtEntry:
  AcpiMadtGicc{F.AcpiF.u32(d, 4n), F.AcpiF.u32(d, 8n), F.AcpiF.u32(d, 12n), F.AcpiF.u32(d, 16n), F.AcpiF.u32(d, 20n), F.AcpiF.u32(d, 56n), AcpiGiccAddrs{F.AcpiF.u64(d, 24n), F.AcpiF.u64(d, 32n), F.AcpiF.u64(d, 40n), F.AcpiF.u64(d, 48n), F.AcpiF.u64(d, 60n)}, F.AcpiF.u64(d, 68n), F.AcpiF.u8(d, 76n), F.AcpiF.u16(d, 78n), F.AcpiF.u16(d, 80n)}

def madt.typed(k: Nat, +d: B.Octets) -> AcpiMadtEntry:
  match k:
    case 0n:
      AcpiMadtLapic{F.AcpiF.u8(d, 2n), F.AcpiF.u8(d, 3n), F.AcpiF.u32(d, 4n)}
    case 1n:
      AcpiMadtIoApic{F.AcpiF.u8(d, 2n), F.AcpiF.u32(d, 4n), F.AcpiF.u32(d, 8n)}
    case 2n:
      AcpiMadtIso{F.AcpiF.u8(d, 2n), F.AcpiF.u8(d, 3n), F.AcpiF.u32(d, 4n), F.AcpiF.u16(d, 8n)}
    case 3n:
      AcpiMadtNmiSource{F.AcpiF.u16(d, 2n), F.AcpiF.u32(d, 4n)}
    case 4n:
      AcpiMadtLapicNmi{F.AcpiF.u8(d, 2n), F.AcpiF.u16(d, 3n), F.AcpiF.u8(d, 5n)}
    case 5n:
      AcpiMadtLapicOverride{F.AcpiF.u64(d, 4n)}
    case 9n:
      AcpiMadtX2apic{F.AcpiF.u32(d, 4n), F.AcpiF.u32(d, 8n), F.AcpiF.u32(d, 12n)}
    case 10n:
      AcpiMadtX2apicNmi{F.AcpiF.u16(d, 2n), F.AcpiF.u32(d, 4n), F.AcpiF.u8(d, 8n)}
    case 11n:
      madt.gicc(d)
    case 12n:
      AcpiMadtGicd{F.AcpiF.u32(d, 4n), F.AcpiF.u64(d, 8n), F.AcpiF.u8(d, 20n)}
    case 13n:
      AcpiMadtGicMsi{F.AcpiF.u32(d, 4n), F.AcpiF.u64(d, 8n), F.AcpiF.u32(d, 16n), F.AcpiF.u16(d, 20n), F.AcpiF.u16(d, 22n)}
    case 14n:
      AcpiMadtGicr{F.AcpiF.u64(d, 4n), F.AcpiF.u32(d, 12n)}
    case 15n:
      AcpiMadtGicIts{F.AcpiF.u32(d, 4n), F.AcpiF.u64(d, 8n)}
    case 16n:
      AcpiMadtWakeup{F.AcpiF.u16(d, 2n), F.AcpiF.u64(d, 8n)}
    case _:
      AcpiMadtOther{F.AcpiF.u8(d, 0n), B.Octets.drop(2n, d)}

def madt.entry.pick(ok: Bool, +k: U32, +off: Nat, +d: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiMadtEntry>:
  match ok:
    case True{}:
      Done{madt.typed(U32.to_nat(k), d)}
    case False{}:
      Fail{E.AcpiBadEntry{off, k}}

def AcpiMadtEntry.of_raw(e: N.AcpiRawEntry) -> Result<&2, &2, E.AcpiError, AcpiMadtEntry>:
  match e:
    case N.AcpiRawEntry{+k, off, +d}:
      madt.entry.pick(Nat.is_le(madt.min(k), B.Octets.len(d)), k, off, d)

def madt.rev(xs: List<&2, AcpiMadtEntry>, acc: List<&2, AcpiMadtEntry>) -> List<&2, AcpiMadtEntry>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      madt.rev(t, Con{h, acc})

def madt.push(acc: Result<&2, &2, E.AcpiError, List<&2, AcpiMadtEntry>>, r: Result<&2, &2, E.AcpiError, AcpiMadtEntry>) -> Result<&2, &2, E.AcpiError, List<&2, AcpiMadtEntry>>:
  match acc r:
    case Fail{e} _:
      Fail{e}
    case Done{xs} Done{x}:
      Done{Con{x, xs}}
    case Done{xs} Fail{e}:
      Fail{e}

def madt.fin(r: Result<&2, &2, E.AcpiError, List<&2, AcpiMadtEntry>>) -> Result<&2, &2, E.AcpiError, List<&2, AcpiMadtEntry>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{xs}:
      Done{madt.rev(xs, Nil{})}

def madt.all(es: List<&2, N.AcpiRawEntry>, acc: Result<&2, &2, E.AcpiError, List<&2, AcpiMadtEntry>>) -> Result<&2, &2, E.AcpiError, List<&2, AcpiMadtEntry>>:
  match es:
    case Nil{}:
      madt.fin(acc)
    case Con{h, t}:
      madt.all(t, madt.push(acc, AcpiMadtEntry.of_raw(h)))

def madt.mk2(+h: H.AcpiHeader, +a: U32, +f: U32, r: Result<&2, &2, E.AcpiError, List<&2, AcpiMadtEntry>>) -> Result<&2, &2, E.AcpiError, AcpiMadt>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{es}:
      Done{AcpiMadt{h, a, f, es}}

def madt.mk(+h: H.AcpiHeader, +a: U32, +f: U32, r: Result<&2, &2, E.AcpiError, List<&2, N.AcpiRawEntry>>) -> Result<&2, &2, E.AcpiError, AcpiMadt>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{es}:
      madt.mk2(h, a, f, madt.all(es, Done{Nil{}}))

def madt.body(ok: Bool, +h: H.AcpiHeader, +body: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiMadt>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{44n, Nat.add(36n, B.Octets.len(body))}}
    case True{}:
      madt.mk(h, F.AcpiF.u32(body, 0n), F.AcpiF.u32(body, 4n), N.AcpiRawEntry.split(B.Octets.drop(8n, body), 44n))

# a checked table (header.bend: AcpiSdt.parse) as an MADT
def AcpiMadt.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiMadt>:
  match t:
    case H.AcpiSdt{h, +body}:
      madt.body(Nat.is_le(8n, B.Octets.len(body)), h, body)

def madt.parse(r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiMadt>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      AcpiMadt.of_sdt(t)

# the MADT at the front of o: checked (length, checksum, signature "APIC"),
# then read
def AcpiMadt.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiMadt>:
  madt.parse(H.AcpiSdt.parse_sig(B.Octets.of_string("APIC"), o))

# Queries

def madt.override(es: List<&2, AcpiMadtEntry>, +dflt: W.W64) -> W.W64:
  match es:
    case Nil{}:
      dflt
    case Con{AcpiMadtLapicOverride{a}, t}:
      a
    case Con{e, t}:
      madt.override(t, dflt)

# the local APIC's physical address: the 64-bit override structure's, if
# there is one (5.2.12.8), else the 32-bit field
def AcpiMadt.lapic_address(m: AcpiMadt) -> W.W64:
  match m:
    case AcpiMadt{h, a, f, es}:
      madt.override(es, W.W64.from_u32(a))

# Writing: each structure as bytes (the lengths of this revision: GICC 82)

def madt.u16(v: U32) -> B.Octets:
  B.Octets.le16(v)

def madt.u32(v: U32) -> B.Octets:
  B.Octets.le32(v)

def madt.u64(v: W.W64) -> B.Octets:
  B.Octets.le64(v)

def madt.u8(v: U32) -> B.Octets:
  B.Octets.of_list([v])

def madt.z(n: Nat) -> B.Octets:
  B.Octets.zeros(n)

def AcpiMadtEntry.encode(e: AcpiMadtEntry) -> B.Octets:
  match e:
    case AcpiMadtLapic{u, a, f}:
      N.AcpiRawEntry.encode(0, B.Octets.concat([madt.u8(u), madt.u8(a), madt.u32(f)]))
    case AcpiMadtIoApic{i, a, g}:
      N.AcpiRawEntry.encode(1, B.Octets.concat([madt.u8(i), madt.z(1n), madt.u32(a), madt.u32(g)]))
    case AcpiMadtIso{b, s, g, f}:
      N.AcpiRawEntry.encode(2, B.Octets.concat([madt.u8(b), madt.u8(s), madt.u32(g), madt.u16(f)]))
    case AcpiMadtNmiSource{f, g}:
      N.AcpiRawEntry.encode(3, B.Octets.concat([madt.u16(f), madt.u32(g)]))
    case AcpiMadtLapicNmi{u, f, l}:
      N.AcpiRawEntry.encode(4, B.Octets.concat([madt.u8(u), madt.u16(f), madt.u8(l)]))
    case AcpiMadtLapicOverride{a}:
      N.AcpiRawEntry.encode(5, B.Octets.concat([madt.z(2n), madt.u64(a)]))
    case AcpiMadtX2apic{x, f, u}:
      N.AcpiRawEntry.encode(9, B.Octets.concat([madt.z(2n), madt.u32(x), madt.u32(f), madt.u32(u)]))
    case AcpiMadtX2apicNmi{f, u, l}:
      N.AcpiRawEntry.encode(10, B.Octets.concat([madt.u16(f), madt.u32(u), madt.u8(l), madt.z(3n)]))
    case AcpiMadtGicc{ci, u, f, pv, pg, vg, AcpiGiccAddrs{pk, b, gv, gh, gr}, mp, ec, sp, tr}:
      N.AcpiRawEntry.encode(11, B.Octets.concat([madt.z(2n), madt.u32(ci), madt.u32(u), madt.u32(f), madt.u32(pv), madt.u32(pg), madt.u64(pk), madt.u64(b), madt.u64(gv), madt.u64(gh), madt.u32(vg), madt.u64(gr), madt.u64(mp), madt.u8(ec), madt.z(1n), madt.u16(sp), madt.u16(tr)]))
    case AcpiMadtGicd{i, b, v}:
      N.AcpiRawEntry.encode(12, B.Octets.concat([madt.z(2n), madt.u32(i), madt.u64(b), madt.z(4n), madt.u8(v), madt.z(3n)]))
    case AcpiMadtGicMsi{i, b, f, c, s}:
      N.AcpiRawEntry.encode(13, B.Octets.concat([madt.z(2n), madt.u32(i), madt.u64(b), madt.u32(f), madt.u16(c), madt.u16(s)]))
    case AcpiMadtGicr{b, l}:
      N.AcpiRawEntry.encode(14, B.Octets.concat([madt.z(2n), madt.u64(b), madt.u32(l)]))
    case AcpiMadtGicIts{i, b}:
      N.AcpiRawEntry.encode(15, B.Octets.concat([madt.z(2n), madt.u32(i), madt.u64(b), madt.z(4n)]))
    case AcpiMadtWakeup{v, m}:
      N.AcpiRawEntry.encode(16, B.Octets.concat([madt.u16(v), madt.z(4n), madt.u64(m)]))
    case AcpiMadtOther{k, d}:
      N.AcpiRawEntry.encode(k, d)

def madt.enc(es: List<&2, AcpiMadtEntry>) -> List<&2, B.Octets>:
  match es:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{AcpiMadtEntry.encode(h), madt.enc(t)}

# the table (signature set to "APIC", length and checksum computed)
def AcpiMadt.build(m: AcpiMadt) -> B.Octets:
  match m:
    case AcpiMadt{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}, a, f, es}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("APIC"), l, r, c, o, t, orv, ci, cr}, B.Octets.append(B.Octets.append(madt.u32(a), madt.u32(f)), B.Octets.concat(madt.enc(es))))
