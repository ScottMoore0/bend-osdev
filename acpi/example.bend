# bend-osdev-acpi, example.bend: AcpiExample, a small x86 machine's tables
# built with this package's writers, for the tests and as a guide: an RSDP
# leading to an XSDT (and an RSDT), an FADT, FACS, MADT, HPET, MCFG, SRAT,
# SLIT, BGRT, an SSDT, and a DSDT in AML that has a PCI host bridge with
# _HID, _CID, _CRS and _PRT, an LPC bridge whose PIRQ routing registers are
# a PCI_Config field, a PCI interrupt link device whose _STA and _CRS read
# them (the CreateWordField pattern), an embedded controller with an
# EmbeddedControl region and a query method that sends a Notify, a thermal
# zone, a power button and a processor device. Its shape follows the
# examples of ACPI 6.5, sections 6.2.13 (_PRT), 6.4 (resource templates)
# and 11 (thermal zones).
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./header.bend as H
import ./rsdp.bend as P
import ./rsdt.bend as S
import ./fadt.bend as F
import ./facs.bend as FS
import ./gas.bend as G
import ./madt.bend as M
import ./hpet.bend as Hp
import ./mcfg.bend as Mc
import ./srat.bend as Sr
import ./slit.bend as Sl
import ./bgrt.bend as Bg
import ./dsdt.bend as D
import ./acpi.bend as A
import ./aml_term.bend as T
import ./aml_resource.bend as R
import ./aml_host.bend as Hs

def ex.hdr(s: String, r: U32) -> H.AcpiHeader:
  H.AcpiHeader.make(B.Octets.of_string(s), r, B.Octets.of_string("BENDOS"), B.Octets.of_string("EXAMPLE"))

def ex.i(v: U32) -> T.AmlTerm:
  T.AmlT.int32(v)

# Physical addresses
def AcpiExample.rsdp_address() -> W.W64:
  W.W64.from_u32(917520)

def AcpiExample.base() -> U32:
  1048576

def ex.at(off: U32) -> U32:
  U32.add(AcpiExample.base(), off)

def ex.at64(+off: U32) -> W.W64:
  W.W64.from_u32(ex.at(off))

# the offsets of the tables from the base
def ex.xsdt() -> U32:
  0

def ex.rsdt() -> U32:
  256

def ex.fadt() -> U32:
  512

def ex.facs() -> U32:
  1024

def ex.madt() -> U32:
  1280

def ex.hpet() -> U32:
  1536

def ex.mcfg() -> U32:
  1664

def ex.srat() -> U32:
  1792

def ex.slit() -> U32:
  2048

def ex.bgrt() -> U32:
  2176

def ex.ssdt() -> U32:
  2304

def ex.dsdt() -> U32:
  3072

# The DSDT

def ex.lnk.crs() -> List<&2, T.AmlTerm>:
  [T.AmlT.name("RTLA", T.AmlT.buf(R.AmlResource.template([R.AmlRIrq{0, 24}]))),
   T.AmlT.create_field(139, T.AmlT.nm("RTLA"), T.AmlT.one(), "IRQ0"),
   T.AmlT.store(T.AmlT.zero(), T.AmlT.nm("IRQ0")),
   T.AmlT.shift_left(T.AmlT.one(), T.AmlT.and(T.AmlT.nm("^^PCI0.LPCB.PIRA"), ex.i(15), T.AmlT.none()), T.AmlT.nm("IRQ0")),
   T.AmlT.ret(T.AmlT.nm("RTLA"))]

def ex.lnka() -> T.AmlTerm:
  T.AmlT.device("LNKA", [
    T.AmlT.name("_HID", T.AmlT.eisaid("PNP0C0F")),
    T.AmlT.name("_UID", T.AmlT.one()),
    T.AmlT.method("_STA", 0n, False{}, [T.AmlT.if_else(T.AmlT.and(T.AmlT.nm("^^PCI0.LPCB.PIRA"), ex.i(128), T.AmlT.none()), [T.AmlT.ret(ex.i(9))], [T.AmlT.ret(ex.i(11))])]),
    T.AmlT.method("_CRS", 0n, True{}, ex.lnk.crs())])

def ex.pci.crs() -> B.Octets:
  R.AmlResource.template([
    R.AmlRAddr{16, 2, 12, 0, R.AmlRange{W.W64.zero(), W.W64.zero(), W.W64.from_u32(255), W.W64.zero(), W.W64.from_u32(256)}},
    R.AmlRIo{1, 3320, 3320, 1, 8},
    R.AmlRAddr{16, 1, 12, 3, R.AmlRange{W.W64.zero(), W.W64.zero(), W.W64.from_u32(3319), W.W64.zero(), W.W64.from_u32(3320)}},
    R.AmlRAddr{32, 0, 12, 1, R.AmlRange{W.W64.zero(), W.W64.from_u32(2147483648), W.W64.from_u32(4273995775), W.W64.zero(), W.W64.from_u32(2126512128)}}])

def ex.prt() -> T.AmlTerm:
  T.AmlT.package([
    T.AmlT.package([ex.i(131071), T.AmlT.zero(), T.AmlT.nm("^LNKA"), T.AmlT.zero()]),
    T.AmlT.package([ex.i(131071), T.AmlT.one(), T.AmlT.zero(), ex.i(17)]),
    T.AmlT.package([ex.i(2031615), T.AmlT.zero(), T.AmlT.zero(), ex.i(16)])])

def ex.ec() -> T.AmlTerm:
  T.AmlT.device("EC0_", [
    T.AmlT.name("_HID", T.AmlT.eisaid("PNP0C09")),
    T.AmlT.name("_CRS", T.AmlT.buf(R.AmlResource.template([R.AmlRIo{1, 98, 98, 0, 1}, R.AmlRIo{1, 102, 102, 0, 1}]))),
    T.AmlT.name("_GPE", ex.i(23)),
    T.AmlT.region("ECOR", 3, T.AmlT.zero(), ex.i(256)),
    T.AmlT.field("ECOR", T.AmlT.field_flags(1, True{}, 0), [T.AmlFReserved{128}, T.AmlT.fnamed("TMP0", 8), T.AmlT.fnamed("FAN0", 1), T.AmlT.fnamed("LID0", 1)]),
    T.AmlT.method("_Q01", 0n, False{}, [T.AmlT.notify(T.AmlT.nm("\\_TZ.TZ00"), ex.i(128))])])

def ex.lpcb() -> T.AmlTerm:
  T.AmlT.device("LPCB", [
    T.AmlT.name("_ADR", ex.i(2031616)),
    T.AmlT.region("LPCR", 2, ex.i(96), ex.i(4)),
    T.AmlT.field("LPCR", T.AmlT.field_flags(1, False{}, 0), [T.AmlT.fnamed("PIRA", 8), T.AmlT.fnamed("PIRB", 8), T.AmlT.fnamed("PIRC", 8), T.AmlT.fnamed("PIRD", 8)]),
    ex.ec()])

def ex.pci0() -> T.AmlTerm:
  T.AmlT.device("PCI0", [
    T.AmlT.name("_HID", T.AmlT.eisaid("PNP0A08")),
    T.AmlT.name("_CID", T.AmlT.eisaid("PNP0A03")),
    T.AmlT.name("_ADR", T.AmlT.zero()),
    T.AmlT.name("_BBN", T.AmlT.zero()),
    T.AmlT.name("_UID", T.AmlT.zero()),
    T.AmlT.name("_CRS", T.AmlT.buf(ex.pci.crs())),
    T.AmlT.name("_PRT", ex.prt()),
    ex.lpcb()])

def ex.osys() -> T.AmlTerm:
  T.AmlT.method("OSYS", 0n, False{}, [
    T.AmlT.store(ex.i(2000), T.AmlT.local(0)),
    T.AmlT.if_(T.AmlT.call("\\_OSI", [T.AmlT.str("Windows 2015")]), [T.AmlT.store(ex.i(2015), T.AmlT.local(0))]),
    T.AmlT.if_(T.AmlT.call("\\_OSI", [T.AmlT.str("Linux")]), [T.AmlT.store(ex.i(1), T.AmlT.local(0))]),
    T.AmlT.ret(T.AmlT.local(0))])

# the DSDT's terms
def AcpiExample.dsdt_terms() -> List<&2, T.AmlTerm>:
  [T.AmlT.scope("\\_SB", [
     ex.pci0(),
     ex.lnka(),
     T.AmlT.device("PWRB", [T.AmlT.name("_HID", T.AmlT.eisaid("PNP0C0C"))]),
     T.AmlT.device("CPU0", [T.AmlT.name("_HID", T.AmlT.str("ACPI0007")), T.AmlT.name("_UID", T.AmlT.zero())]),
     ex.osys(),
     T.AmlT.method("SUM_", 1n, False{}, [
       T.AmlT.store(T.AmlT.zero(), T.AmlT.local(0)),
       T.AmlT.store(T.AmlT.zero(), T.AmlT.local(1)),
       T.AmlT.while_(T.AmlT.lless_equal(T.AmlT.local(1), T.AmlT.arg(0)), [
         T.AmlT.add(T.AmlT.local(0), T.AmlT.local(1), T.AmlT.local(0)),
         T.AmlT.increment(T.AmlT.local(1))]),
       T.AmlT.ret(T.AmlT.local(0))]),
     T.AmlT.method("SPIN", 0n, False{}, [T.AmlT.while_(T.AmlT.one(), [T.AmlT.noop()])])]),
   T.AmlT.scope("\\_TZ", [
     T.AmlT.thermal_zone("TZ00", [
       T.AmlT.method("_TMP", 0n, False{}, [T.AmlT.ret(T.AmlT.add(T.AmlT.multiply(T.AmlT.nm("\\_SB.PCI0.LPCB.EC0.TMP0"), ex.i(10), T.AmlT.none()), ex.i(2732), T.AmlT.none()))]),
       T.AmlT.name("_CRT", ex.i(3732))])])]

def AcpiExample.dsdt_aml() -> B.Octets:
  T.AmlT.encode(AcpiExample.dsdt_terms())

def AcpiExample.dsdt() -> D.AcpiAml:
  D.AcpiAml{ex.hdr("DSDT", 2), AcpiExample.dsdt_aml()}

# an SSDT that adds a device to a scope the DSDT defines
def AcpiExample.ssdt() -> D.AcpiAml:
  D.AcpiAml{ex.hdr("SSDT", 2), T.AmlT.encode([
    T.AmlT.external("\\_SB.PCI0", 6, 0),
    T.AmlT.scope("\\_SB.PCI0", [T.AmlT.device("GFX0", [T.AmlT.name("_ADR", ex.i(131072)), T.AmlT.method("_STA", 0n, False{}, [T.AmlT.ret(ex.i(15))])])])])}

# The other tables

def ex.blocks() -> F.AcpiFadtBlocks:
  F.AcpiFadtBlocks{1536, 0, 1540, 0, 1616, 1544, 1568, 0}

def ex.lens() -> F.AcpiFadtLens:
  F.AcpiFadtLens{4, 2, 1, 4, 16, 0, 0}

def ex.io(+port: U32, +len: U32) -> G.AcpiGas:
  G.AcpiGas{1, U32.mul(len, 8), 0, 0, W.W64.from_u32(port)}

def AcpiExample.fadt() -> F.AcpiFadt:
  +z = G.AcpiGas.zero()
  +core = {F.AcpiFadtCore{ex.at(ex.facs()), ex.at(ex.dsdt()), 0, 1, 9, 178, 240, 241, 0, 0, ex.blocks(), ex.lens(), 0, 101, 1001, 0, 0, 1, 3, 13, 0, 50, 3, 34101} : F.AcpiFadtCore}
  +x = {F.AcpiFadtX{ex.io(1536, 4), z, ex.io(1540, 2), z, ex.io(1616, 1), ex.io(1544, 4), ex.io(1568, 16), z} : F.AcpiFadtX}
  F.AcpiFadt{ex.hdr("FACP", 6), core, Some{F.AcpiFadtExt{G.AcpiGas{1, 8, 0, 1, W.W64.from_u32(3321)}, 6, 0, 5, ex.at64(ex.facs()), ex.at64(ex.dsdt()), x}}, Some{F.AcpiFadtSleep{z, z}}, Some{W.W64.zero()}}

def AcpiExample.facs() -> FS.AcpiFacs:
  FS.AcpiFacs{64, 305419896, 0, 0, 0, W.W64.zero(), 2, 0}

def AcpiExample.madt() -> M.AcpiMadt:
  M.AcpiMadt{ex.hdr("APIC", 5), 4276092928, 1, {[M.AcpiMadtLapic{0, 0, 1}, M.AcpiMadtLapic{1, 1, 1}, M.AcpiMadtIoApic{2, 4273995776, 0}, M.AcpiMadtIso{0, 0, 2, 0}, M.AcpiMadtIso{0, 9, 9, 13}, M.AcpiMadtLapicNmi{255, 5, 1}, M.AcpiMadtX2apic{256, 1, 2}] : List<&2, M.AcpiMadtEntry>}}

def AcpiExample.hpet() -> Hp.AcpiHpet:
  Hp.AcpiHpet{ex.hdr("HPET", 1), 2156306945, G.AcpiGas{0, 64, 0, 0, W.W64.from_u32(4275044352)}, 0, 14318, 0}

def AcpiExample.mcfg() -> Mc.AcpiMcfg:
  Mc.AcpiMcfg{ex.hdr("MCFG", 1), [Mc.AcpiMcfgEntry{W.W64.from_u32(3758096384), 0, 0, 255}]}

def AcpiExample.srat() -> Sr.AcpiSrat:
  Sr.AcpiSrat{ex.hdr("SRAT", 3), {[Sr.AcpiSratLapic{0, 0, 1, 0, 0}, Sr.AcpiSratLapic{1, 1, 1, 0, 0}, Sr.AcpiSratMemory{0, W.W64.zero(), W.W64.from_u32(2147483648), 1}, Sr.AcpiSratMemory{1, W.W64.from_parts(1, 0), W.W64.from_u32(2147483648), 1}] : List<&2, Sr.AcpiSratEntry>}}

def AcpiExample.slit() -> Sl.AcpiSlit:
  Sl.AcpiSlit{ex.hdr("SLIT", 1), 2n, B.Octets.of_list([10, 21, 21, 10])}

def AcpiExample.bgrt() -> Bg.AcpiBgrt:
  Bg.AcpiBgrt{ex.hdr("BGRT", 1), 1, 1, 0, W.W64.from_u32(2113929216), 100, 200}

def AcpiExample.rsdp() -> P.AcpiRsdp:
  P.AcpiRsdp{B.Octets.of_string("BENDOS"), 2, ex.at(ex.rsdt()), Some{P.AcpiRsdpExt{36, ex.at64(ex.xsdt())}}}

def ex.listed() -> List<&2, W.W64>:
  [ex.at64(ex.fadt()), ex.at64(ex.madt()), ex.at64(ex.hpet()), ex.at64(ex.mcfg()), ex.at64(ex.srat()), ex.at64(ex.slit()), ex.at64(ex.bgrt()), ex.at64(ex.ssdt())]

# each table as bytes, with its offset from the base
type AcpiExamplePiece is Data:
  AcpiExamplePiece{offset: U32, bytes: B.Octets}

def AcpiExample.pieces() -> List<&2, AcpiExamplePiece>:
  [AcpiExamplePiece{ex.xsdt(), S.AcpiXsdt.build(ex.hdr("XSDT", 1), ex.listed())},
   AcpiExamplePiece{ex.rsdt(), S.AcpiRsdt.build(ex.hdr("RSDT", 1), ex.listed())},
   AcpiExamplePiece{ex.fadt(), F.AcpiFadt.build(AcpiExample.fadt())},
   AcpiExamplePiece{ex.facs(), FS.AcpiFacs.build(AcpiExample.facs())},
   AcpiExamplePiece{ex.madt(), M.AcpiMadt.build(AcpiExample.madt())},
   AcpiExamplePiece{ex.hpet(), Hp.AcpiHpet.build(AcpiExample.hpet())},
   AcpiExamplePiece{ex.mcfg(), Mc.AcpiMcfg.build(AcpiExample.mcfg())},
   AcpiExamplePiece{ex.srat(), Sr.AcpiSrat.build(AcpiExample.srat())},
   AcpiExamplePiece{ex.slit(), Sl.AcpiSlit.build(AcpiExample.slit())},
   AcpiExamplePiece{ex.bgrt(), Bg.AcpiBgrt.build(AcpiExample.bgrt())},
   AcpiExamplePiece{ex.ssdt(), D.AcpiAml.build(AcpiExample.ssdt())},
   AcpiExamplePiece{ex.dsdt(), D.AcpiAml.build(AcpiExample.dsdt())}]

# the pieces laid out from offset at, zeros between them
def ex.lay(ps: List<&2, AcpiExamplePiece>, +at: Nat) -> List<&2, B.Octets>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{AcpiExamplePiece{off, +o}, t}:
      +gap = Nat.sub(U32.to_nat(off), at)
      Con{B.Octets.zeros(gap), Con{o, ex.lay(t, Nat.add(Nat.add(at, gap), B.Octets.len(o)))}}

def AcpiExample.region() -> B.Octets:
  B.Octets.concat(ex.lay(AcpiExample.pieces(), 0n))

# physical memory: the RSDP at 0xE0010, the tables from 0x100000
def AcpiExample.memory() -> A.AcpiMemImage:
  A.AcpiMemImage{[A.AcpiMemRegion{W.W64.from_u32(917504), B.Octets.append(B.Octets.zeros(16n), P.AcpiRsdp.build(AcpiExample.rsdp()))}, A.AcpiMemRegion{W.W64.from_u32(AcpiExample.base()), AcpiExample.region()}]}

# the host the DSDT runs against: the LPC bridge's PIRQ registers (PCI
# config space of device 0x1F, from offset 0x60: PIRQA routed to IRQ 11,
# PIRQB disabled) and the EC's temperature byte (offset 0x10: 30 degrees)
def AcpiExample.host() -> Hs.AmlMemHost:
  +pci = Hs.AmlMemHost.poke(Hs.AmlMemHost.new(), 2, W.W64.add(Hs.AmlPci.address(0, 0, 31, 0, 0), W.W64.from_u32(96)), B.Octets.of_list([11, 128, 10, 5]))
  Hs.AmlMemHost.poke(pci, 3, W.W64.from_u32(16), B.Octets.of_list([30]))
