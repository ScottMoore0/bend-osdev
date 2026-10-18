# bend-osdev-acpi, mcfg.bend: the PCI Express memory-mapped configuration
# space table, "MCFG" (PCI Firmware Specification, revision 3.3, PCI-SIG,
# section 4.1.2; its signature is reserved by ACPI 6.5, section 5.2.6):
# after the header, 8 reserved bytes, then 16-byte allocation structures
# from offset 44:
#
#   offset  size  field
#        0     8  Base Address of the enhanced configuration (ECAM) region
#        8     2  PCI Segment Group Number
#       10     1  Start Bus Number
#       11     1  End Bus Number
#       12     4  Reserved
#
# The base address is that of bus 0 of the segment, whatever the start bus
# (PCI Firmware Specification, 4.1.2), so bus b, device d, function f,
# register r is at base + (b << 20 | d << 15 | f << 12 | r).
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./fields.bend as F

type AcpiMcfgEntry is Data:
  AcpiMcfgEntry{base: W.W64, segment: U32, start_bus: U32, end_bus: U32}

type AcpiMcfg is Data:
  AcpiMcfg{header: H.AcpiHeader, entries: List<&2, AcpiMcfgEntry>}

def mcfg.read(n: Nat, +o: B.Octets) -> List<&2, AcpiMcfgEntry>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{AcpiMcfgEntry{F.AcpiF.u64(o, 0n), F.AcpiF.u16(o, 8n), F.AcpiF.u8(o, 10n), F.AcpiF.u8(o, 11n)}, mcfg.read(p, B.Octets.drop(16n, o))}

def mcfg.body(ok: Bool, +h: H.AcpiHeader, +body: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiMcfg>:
  match ok:
    case False{}:
      Fail{E.AcpiBadSize{B.Octets.len(body)}}
    case True{}:
      +es = B.Octets.drop(8n, body)
      Done{AcpiMcfg{h, mcfg.read(Nat.div(B.Octets.len(es), 16n), es)}}

# a checked table as an MCFG: the body is 8 reserved bytes and a whole
# number of 16-byte structures (AcpiBadSize otherwise)
def AcpiMcfg.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiMcfg>:
  match t:
    case H.AcpiSdt{h, +body}:
      +n = B.Octets.len(body)
      mcfg.body(Bool.and(Nat.is_le(8n, n), Nat.is_eq(Nat.mod(Nat.sub(n, 8n), 16n), 0n)), h, body)

def mcfg.parse(r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiMcfg>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      AcpiMcfg.of_sdt(t)

def AcpiMcfg.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiMcfg>:
  mcfg.parse(H.AcpiSdt.parse_sig(B.Octets.of_string("MCFG"), o))

def AcpiMcfg.entries(m: AcpiMcfg) -> List<&2, AcpiMcfgEntry>:
  match m:
    case AcpiMcfg{h, es}:
      es

def mcfg.covers(+seg: U32, +bus: U32, e: AcpiMcfgEntry) -> Bool:
  match e:
    case AcpiMcfgEntry{b, s, lo, hi}:
      Bool.and(U32.is_eq(s, seg), Bool.and(U32.is_le(lo, bus), U32.is_le(bus, hi)))

def mcfg.addr(+e: AcpiMcfgEntry, +bus: U32, +dev: U32, +fun: U32, +reg: U32) -> W.W64:
  match e:
    case AcpiMcfgEntry{b, s, lo, hi}:
      W.W64.add(b, W.W64.from_u32(U32.or(U32.shln(U32.and(bus, 255), 20n), U32.or(U32.shln(U32.and(dev, 31), 15n), U32.or(U32.shln(U32.and(fun, 7), 12n), U32.and(reg, 4095))))))

def mcfg.hit(hit: Bool, +e: AcpiMcfgEntry, +bus: U32, +dev: U32, +fun: U32, +reg: U32) -> Maybe<&2, W.W64>:
  match hit:
    case True{}:
      Some{mcfg.addr(e, bus, dev, fun, reg)}
    case False{}:
      None{}

def mcfg.first(es: List<&2, AcpiMcfgEntry>, +seg: U32, +bus: U32, +dev: U32, +fun: U32, +reg: U32) -> Maybe<&2, W.W64>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, t}:
      Maybe.or(&2, W.W64, mcfg.hit(mcfg.covers(seg, bus, e), e, bus, dev, fun, reg), mcfg.first(t, seg, bus, dev, fun, reg))

def mcfg.enc(es: List<&2, AcpiMcfgEntry>) -> List<&2, B.Octets>:
  match es:
    case Nil{}:
      Nil{}
    case Con{AcpiMcfgEntry{b, s, lo, hi}, t}:
      Con{B.Octets.concat([B.Octets.le64(b), B.Octets.le16(s), B.Octets.of_list([lo, hi]), B.Octets.zeros(4n)]), mcfg.enc(t)}

# the physical address of a configuration register, if a structure covers
# the segment and bus
def AcpiMcfg.ecam_address(m: AcpiMcfg, +seg: U32, +bus: U32, +dev: U32, +fun: U32, +reg: U32) -> Maybe<&2, W.W64>:
  mcfg.first(AcpiMcfg.entries(m), seg, bus, dev, fun, reg)

def AcpiMcfg.build(m: AcpiMcfg) -> B.Octets:
  match m:
    case AcpiMcfg{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}, es}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("MCFG"), l, r, c, o, t, orv, ci, cr}, B.Octets.append(B.Octets.zeros(8n), B.Octets.concat(mcfg.enc(es))))
