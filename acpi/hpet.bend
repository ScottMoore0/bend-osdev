# bend-osdev-acpi, hpet.bend: the HPET Description Table, "HPET" (IA-PC HPET
# (High Precision Event Timers) Specification, revision 1.0a, Intel, 2004,
# section 3.2.4; its signature is reserved by ACPI 6.5, section 5.2.6),
# 56 bytes:
#
#   offset  size  field
#       36     4  Event Timer Block ID: bits 0-7 hardware revision, 8-12
#                 number of comparators in the first block minus one, 13
#                 COUNT_SIZE_CAP (64-bit counter), 15 legacy replacement
#                 IRQ routing capable, 16-31 PCI vendor ID
#       40    12  Base Address (a Generic Address Structure, gas.bend)
#       52     1  HPET Number
#       53     2  Main Counter Minimum Clock Tick in Periodic Mode
#       55     1  Page Protection and OEM Attribute
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./fields.bend as F
import ./gas.bend as G

type AcpiHpet is Data:
  AcpiHpet{header: H.AcpiHeader, block_id: U32, base: G.AcpiGas, number: U32, min_tick: U32, page_protection: U32}

def hpet.read(ok: Bool, +h: H.AcpiHeader, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiHpet>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{56n, B.Octets.len(o)}}
    case True{}:
      Done{AcpiHpet{h, F.AcpiF.u32(o, 36n), G.AcpiGas.at(o, 40n), F.AcpiF.u8(o, 52n), F.AcpiF.u16(o, 53n), F.AcpiF.u8(o, 55n)}}

def AcpiHpet.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiHpet>:
  match t:
    case H.AcpiSdt{+h, body}:
      +o = B.Octets.append(H.AcpiHeader.encode(h), body)
      hpet.read(Nat.is_le(56n, B.Octets.len(o)), h, o)

def hpet.parse(r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiHpet>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      AcpiHpet.of_sdt(t)

def AcpiHpet.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiHpet>:
  hpet.parse(H.AcpiSdt.parse_sig(B.Octets.of_string("HPET"), o))

def AcpiHpet.block_id(t: AcpiHpet) -> U32:
  match t:
    case AcpiHpet{h, id, g, n, m, p}:
      id

def AcpiHpet.base(t: AcpiHpet) -> G.AcpiGas:
  match t:
    case AcpiHpet{h, id, g, n, m, p}:
      g

# the fields of the Event Timer Block ID
def AcpiHpet.vendor_id(t: AcpiHpet) -> U32:
  F.AcpiF.bits(AcpiHpet.block_id(t), 16n, 16n)

def AcpiHpet.comparators(t: AcpiHpet) -> U32:
  U32.add(F.AcpiF.bits(AcpiHpet.block_id(t), 8n, 5n), 1)

def AcpiHpet.counter_64(t: AcpiHpet) -> Bool:
  F.AcpiF.bit(AcpiHpet.block_id(t), 13n)

def AcpiHpet.legacy_capable(t: AcpiHpet) -> Bool:
  F.AcpiF.bit(AcpiHpet.block_id(t), 15n)

def AcpiHpet.build(t: AcpiHpet) -> B.Octets:
  match t:
    case AcpiHpet{H.AcpiHeader{s, l, r, c, o, tid, orv, ci, cr}, id, g, n, m, p}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("HPET"), l, r, c, o, tid, orv, ci, cr}, B.Octets.concat([B.Octets.le32(id), G.AcpiGas.encode(g), B.Octets.of_list([n]), B.Octets.le16(m), B.Octets.of_list([p])]))
