import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./checksum.bend as C
import ./header.bend as H
import ./rsdp.bend as P
import ./rsdt.bend as S
import ./fadt.bend as F
import ./gas.bend as G
import ./madt.bend as M
import ./hpet.bend as Hp
import ./mcfg.bend as Mc
import ./slit.bend as Sl
import ./dsdt.bend as D
import ./registry.bend as R
import ./acpi.bend as A
import ./aml_pkglength.bend as K
import ./aml_name.bend as N
import ./aml_term.bend as T
import ./aml_value.bend as V
import ./aml_host.bend as Hs
import ./aml_interp.bend as I
import ./aml.bend as Am
import ./aml_resource.bend as Rs
import ./aml_device.bend as Dv
import ./example.bend as X

def err(e: E.AcpiError) -> String:
  match e:
    case E.AcpiTooShort{n, g}:
      "too short " ++ Nat.show(n) ++ " " ++ Nat.show(g)
    case E.AcpiBadSignature{s}:
      "bad signature " ++ B.Octets.to_string(s)
    case E.AcpiBadLength{l}:
      "bad length " ++ U32.show(l)
    case E.AcpiBadChecksum{s}:
      "bad checksum " ++ U32.show(s)
    case E.AcpiRsdpBadChecksum{s}:
      "bad RSDP checksum " ++ U32.show(s)
    case E.AcpiNotMapped{a}:
      "not mapped " ++ W.W64.show_hex(a)
    case E.AcpiAmlUndefined{p}:
      "undefined " ++ p
    case E.AcpiAmlStepLimit{}:
      "step limit"
    case E.AcpiAmlBadOpcode{c}:
      "bad opcode " ++ U32.show(c)
    case E.AcpiAmlBadOperand{c}:
      "bad operand " ++ U32.show(c)
    case E.AcpiAmlBadType{s}:
      "bad type " ++ s
    case E.AcpiAmlDuplicate{p}:
      "duplicate " ++ p
    case E.AcpiAmlUnsupported{s}:
      "unsupported " ++ s
    case E.AcpiAmlTruncated{}:
      "truncated"
    case E.AcpiAmlRange{}:
      "range"
    case _:
      "error"

def loaded(l: A.AcpiLoaded<R.AcpiNoExt>) -> String:
  match l:
    case A.AcpiLoaded{a, Done{t}}:
      W.W64.show_hex(a) ++ " " ++ R.AcpiTable.name(~R.AcpiNoExt, t)
    case A.AcpiLoaded{a, Fail{e}}:
      W.W64.show_hex(a) ++ " " ++ err(e)

def loadeds(ls: List<&2, A.AcpiLoaded<R.AcpiNoExt>>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{loaded(h), loadeds(t)}

def tables(r: Result<&2, &2, E.AcpiError, A.AcpiTableSet<R.AcpiNoExt>>) -> String:
  match r:
    case Done{A.AcpiTableSet{rp, root, ts, Some{Done{f}}}}:
      String.join(loadeds(ts), ", ") ++ "; FACS ok"
    case Done{A.AcpiTableSet{rp, root, ts, f}}:
      String.join(loadeds(ts), ", ") ++ "; no FACS"
    case Fail{e}:
      err(e)

def madt.e(e: M.AcpiMadtEntry) -> String:
  match e:
    case M.AcpiMadtLapic{u, a, f}:
      "lapic " ++ U32.show(a)
    case M.AcpiMadtIoApic{i, a, g}:
      "ioapic " ++ U32.show(i) ++ " at " ++ U32.show(a)
    case M.AcpiMadtIso{b, s, g, f}:
      "irq " ++ U32.show(s) ++ "->" ++ U32.show(g) ++ "/" ++ U32.show(f)
    case M.AcpiMadtLapicNmi{u, f, l}:
      "nmi lint" ++ U32.show(l)
    case M.AcpiMadtX2apic{x, f, u}:
      "x2apic " ++ U32.show(x)
    case _:
      "other"

def madt.es(es: List<&2, M.AcpiMadtEntry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{madt.e(h), madt.es(t)}

def madt(r: Result<&2, &2, E.AcpiError, M.AcpiMadt>) -> String:
  match r:
    case Done{+m}:
      W.W64.show_hex(M.AcpiMadt.lapic_address(m)) ++ ": " ++ String.join(madt.es(M.AcpiMadt.entries(m)), ", ")
    case Fail{e}:
      err(e)

def fadt(r: Result<&2, &2, E.AcpiError, F.AcpiFadt>) -> String:
  match r:
    case Done{+f}:
      "dsdt " ++ W.W64.show_hex(F.AcpiFadt.dsdt_address(f)) ++ " pm1a_evt " ++ G.AcpiGas.show(F.AcpiFadt.block(f, F.AcpiFadtPm1aEvt{})) ++ " pm1b_cnt " ++ G.AcpiGas.show(F.AcpiFadt.block(f, F.AcpiFadtPm1bCnt{})) ++ " reduced " ++ Bool.show(F.AcpiFadt.hw_reduced(f))
    case Fail{e}:
      err(e)

def hpet(r: Result<&2, &2, E.AcpiError, Hp.AcpiHpet>) -> String:
  match r:
    case Done{+h}:
      "vendor " ++ U32.show(Hp.AcpiHpet.vendor_id(h)) ++ " comparators " ++ U32.show(Hp.AcpiHpet.comparators(h)) ++ " 64-bit " ++ Bool.show(Hp.AcpiHpet.counter_64(h))
    case Fail{e}:
      err(e)

def mw(m: Maybe<&2, W.W64>) -> String:
  match m:
    case Some{a}:
      W.W64.show_hex(a)
    case None{}:
      "none"

def mcfg(r: Result<&2, &2, E.AcpiError, Mc.AcpiMcfg>) -> String:
  match r:
    case Done{+m}:
      mw(Mc.AcpiMcfg.ecam_address(m, 0, 0, 31, 0, 96)) ++ " " ++ mw(Mc.AcpiMcfg.ecam_address(m, 1, 0, 0, 0, 0))
    case Fail{e}:
      err(e)

def mu(m: Maybe<&2, U32>) -> String:
  match m:
    case Some{a}:
      U32.show(a)
    case None{}:
      "none"

def slit(r: Result<&2, &2, E.AcpiError, Sl.AcpiSlit>) -> String:
  match r:
    case Done{+s}:
      mu(Sl.AcpiSlit.distance(s, 0n, 1n)) ++ " " ++ mu(Sl.AcpiSlit.distance(s, 1n, 1n)) ++ " " ++ mu(Sl.AcpiSlit.distance(s, 2n, 0n))
    case Fail{e}:
      err(e)

def sdt(r: Result<&2, &2, E.AcpiError, B.Octets>) -> String:
  match r:
    case Done{o}:
      "ok " ++ Nat.show(B.Octets.len(o))
    case Fail{e}:
      err(e)

def rsdp(r: Result<&2, &2, E.AcpiError, P.AcpiRsdp>) -> String:
  match r:
    case Done{+p}:
      "revision " ++ U32.show(P.AcpiRsdp.revision(p)) ++ " xsdt " ++ W.W64.show_hex(P.AcpiRsdp.xsdt_address(p))
    case Fail{e}:
      err(e)

def mn(m: Maybe<&2, Nat>) -> String:
  match m:
    case Some{n}:
      Nat.show(n)
    case None{}:
      "none"

# a byte of o changed
def poke(+o: B.Octets, +i: Nat, +b: U32) -> B.Octets:
  B.Octets.concat([B.Octets.take(i, o), B.Octets.of_list([b]), B.Octets.drop(1n+i, o)])

# AML

def boot(r: Result<&2, &2, E.AcpiError, Am.AmlSystem<Hs.AmlMemHost>>) -> Am.AmlSystem<Hs.AmlMemHost>:
  match r:
    case Done{s}:
      s
    case Fail{e}:
      Am.Aml.mem_system(True{})

def sys() -> Am.AmlSystem<Hs.AmlMemHost>:
  boot(Am.Aml.boot(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, I.AmlOptions.default(), X.AcpiExample.host(), [X.AcpiExample.dsdt(), X.AcpiExample.ssdt()], 100000n))

def val(r: Result<&2, &2, E.AcpiError, V.AmlValue>) -> String:
  match r:
    case Done{v}:
      V.AmlValue.show(v)
    case Fail{e}:
      err(e)

def ev(+s: Am.AmlSystem<Hs.AmlMemHost>, p: String, args: List<&2, V.AmlValue>, n: Nat) -> String:
  +o = Am.Aml.eval_mem(s, p, args, n)
  val(Am.AmlOutcome.result(Hs.AmlMemHost, o)) ++ " in " ++ Nat.show(Am.AmlOutcome.steps(Hs.AmlMemHost, o)) ++ " steps"

def hid(m: Maybe<&2, Result<&2, &2, E.AcpiError, String>>) -> String:
  match m:
    case None{}:
      "-"
    case Some{Done{s}}:
      s
    case Some{Fail{e}}:
      err(e)

def sta(r: Result<&2, &2, E.AcpiError, W.W64>) -> String:
  match r:
    case Done{x}:
      V.AmlValue.show_int(x)
    case Fail{e}:
      err(e)

def devs(+s: Am.AmlSystem<Hs.AmlMemHost>, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      Con{p ++ " " ++ hid(Dv.AmlDevice.hid(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, p, 1000n)) ++ " " ++ sta(Dv.AmlDevice.status(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, p, 1000n)), devs(s, t)}

def res.list(xs: List<&2, Rs.AmlResource>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{Rs.AmlResource.show(h), res.list(t)}

def crs(r: Result<&2, &2, E.AcpiError, List<&2, Rs.AmlResource>>) -> String:
  match r:
    case Done{xs}:
      String.join(res.list(xs), "; ")
    case Fail{e}:
      err(e)

def prt.list(xs: List<&2, Dv.AmlPrtEntry>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Dv.AmlPrtEntry{a, p, s, i}, t}:
      Con{V.AmlValue.show_int(a) ++ " pin " ++ U32.show(p) ++ " " ++ s ++ " " ++ U32.show(i), prt.list(t)}

def prt(r: Result<&2, &2, E.AcpiError, List<&2, Dv.AmlPrtEntry>>) -> String:
  match r:
    case Done{xs}:
      String.join(prt.list(xs), "; ")
    case Fail{e}:
      err(e)

def notes(xs: List<&2, I.AmlNote>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{I.AmlNote{p, v}, t}:
      Con{"Notify(" ++ p ++ ", " ++ V.AmlValue.show_int(v) ++ ")", notes(t)}

def note(+s: Am.AmlSystem<Hs.AmlMemHost>, p: String) -> String:
  String.join(notes(Am.AmlOutcome.notes(Hs.AmlMemHost, Am.Aml.eval_mem(s, p, Nil{}, 1000n))), "; ")

def log(+s: Am.AmlSystem<Hs.AmlMemHost>, p: String) -> String:
  Hs.AmlMemHost.show_log(Am.AmlOutcome.host(Hs.AmlMemHost, Am.Aml.eval_mem(s, p, Nil{}, 1000n)))

# a 32-bit definition block: integers are 32 bits wide
def narrow() -> String:
  +s = Am.Aml.mem_system(False{})
  +lo = Am.Aml.load_mem(s, T.AmlT.encode([T.AmlT.method("ONES", 0n, False{}, [T.AmlT.ret(T.AmlT.add(T.AmlT.ones(), T.AmlT.one(), T.AmlT.none()))]), T.AmlT.method("NOT_", 0n, False{}, [T.AmlT.ret(T.AmlT.not(T.AmlT.zero(), T.AmlT.none()))])]), 1000n)
  +s2 = Am.AmlSystem.after(Hs.AmlMemHost, s, lo)
  ev(s2, "\\ONES", Nil{}, 100n) ++ ", " ++ ev(s2, "\\NOT_", Nil{}, 100n)

def main() -> IO(Unit):
  +mem = X.AcpiExample.memory()
  +s = sys()
  +madt_o = M.AcpiMadt.build(X.AcpiExample.madt())
  +rsdp_o = P.AcpiRsdp.build(X.AcpiExample.rsdp())
  do IO<Unit>:
    IO.print("rsdp at " ++ mn(P.AcpiRsdp.find(B.Octets.append(B.Octets.zeros(16n), rsdp_o))))
    IO.print(rsdp(P.AcpiRsdp.parse(rsdp_o)))
    IO.print(rsdp(P.AcpiRsdp.parse(poke(rsdp_o, 10n, 0))))
    IO.print(tables(A.AcpiTables.load(~A.AcpiMemImage, ~A.AcpiMemImage.read, mem, X.AcpiExample.rsdp_address())))
    IO.print(tables(A.AcpiTables.load_with(~A.AcpiMemImage, ~A.AcpiMemImage.read, ~R.AcpiNoExt, ~R.AcpiNoExt.parse, A.AcpiLoadOptions{False{}, R.AcpiRegistry.empty()}, mem, X.AcpiExample.rsdp_address())))
    IO.print(madt(M.AcpiMadt.parse(madt_o)))
    IO.print(sdt(H.AcpiSdt.check(madt_o)))
    IO.print(sdt(H.AcpiSdt.check(poke(madt_o, 40n, 7))))
    IO.print(sdt(H.AcpiSdt.check(B.Octets.take(30n, madt_o))))
    IO.print(fadt(F.AcpiFadt.parse(F.AcpiFadt.build(X.AcpiExample.fadt()))))
    IO.print(hpet(Hp.AcpiHpet.parse(Hp.AcpiHpet.build(X.AcpiExample.hpet()))))
    IO.print(mcfg(Mc.AcpiMcfg.parse(Mc.AcpiMcfg.build(X.AcpiExample.mcfg()))))
    IO.print(slit(Sl.AcpiSlit.parse(Sl.AcpiSlit.build(X.AcpiExample.slit()))))
    IO.print(B.Octets.hex(K.AmlPkgLength.encode(63)) ++ " " ++ B.Octets.hex(K.AmlPkgLength.encode(64)) ++ " " ++ B.Octets.hex(K.AmlPkgLength.encode(4095)) ++ " " ++ B.Octets.hex(K.AmlPkgLength.encode(4096)) ++ " " ++ B.Octets.hex(K.AmlPkgLength.encode(268435455)))
    IO.print(B.Octets.hex(N.AmlName.encode(N.AmlName.of_text("\\_SB.PCI0.LPCB"))) ++ " " ++ B.Octets.hex(N.AmlName.encode(N.AmlName.of_text("^^_STA"))))
    IO.print(B.Octets.hex(T.AmlT.encode1(T.AmlT.name("_HID", T.AmlT.eisaid("PNP0A03")))) ++ " " ++ Dv.AmlEisaId.text(T.AmlT.eisaid_value("PNP0C0F")))
    IO.print(String.join(devs(s, Dv.AmlDevice.list(Am.AmlSystem.ns(Hs.AmlMemHost, s))), ", "))
    IO.print(crs(Dv.AmlDevice.crs(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, "\\_SB_.PCI0", 1000n)))
    IO.print(crs(Dv.AmlDevice.crs(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, "\\_SB_.LNKA", 1000n)))
    IO.print(log(s, "\\_SB_.LNKA._CRS"))
    IO.print(prt(Dv.AmlDevice.prt(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, "\\_SB_.PCI0", 1000n)))
    IO.print(ev(s, "\\_TZ_.TZ00._TMP", Nil{}, 1000n))
    IO.print(ev(s, "\\_SB_.SUM_", [V.AmlInt{W.W64.from_u32(100)}], 100000n))
    IO.print(ev(s, "\\_SB_.OSYS", Nil{}, 1000n))
    IO.print(note(s, "\\_SB_.PCI0.LPCB.EC0_._Q01"))
    IO.print(ev(s, "\\_SB_.SPIN", Nil{}, 1000n))
    IO.print(ev(s, "\\_SB_.NONE", Nil{}, 1000n))
    IO.print(narrow())

#|rsdp at 16
#|revision 2 xsdt 0000000000100000
#|bad RSDP checksum 187
#|0000000000100200 FACP, 0000000000100500 APIC, 0000000000100600 HPET, 0000000000100680 MCFG, 0000000000100700 SRAT, 0000000000100800 SLIT, 0000000000100880 BGRT, 0000000000100900 SSDT, 0000000000100c00 DSDT; FACS ok
#|0000000000100200 FACP, 0000000000100500 APIC, 0000000000100600 HPET, 0000000000100680 MCFG, 0000000000100700 SRAT, 0000000000100800 SLIT, 0000000000100880 BGRT, 0000000000100900 SSDT; no FACS
#|00000000fee00000: lapic 0, lapic 1, ioapic 2 at 4273995776, irq 0->2/0, irq 9->9/13, nmi lint1, x2apic 256
#|ok 114
#|bad checksum 6
#|bad length 114
#|dsdt 0000000000100c00 pm1a_evt {1 32 0 0 0000000000000600} pm1b_cnt {1 16 0 0 0000000000000000} reduced False
#|vendor 32902 comparators 3 64-bit True
#|00000000e00f8060 none
#|21 10 none
#|3f 4004 4fff 800001 cfffffff
#|5c2f035f53425f504349304c504342 5e5e5f535441
#|085f4849440c41d00a03 PNP0C0F
#|\_SB_ - 0xf, \_SB_.CPU0 ACPI0007 0xf, \_SB_.LNKA PNP0C0F 0xb, \_SB_.PCI0 PNP0A08 0xf, \_SB_.PCI0.GFX0 - 0xf, \_SB_.PCI0.LPCB - 0xf, \_SB_.PCI0.LPCB.EC0_ PNP0C09 0xf, \_SB_.PWRB PNP0C0C 0xf
#|addr16 type 2 0000000000000000-00000000000000ff len 0000000000000100; io 3320-3320 align 1 len 8; addr16 type 1 0000000000000000-0000000000000cf7 len 0000000000000cf8; addr32 type 0 0000000080000000-00000000febfffff len 000000007ec00000
#|irq mask 2048 flags 24
#|read 2:0000001f00000060/8
#|0x1ffff pin 0 \_SB_.LNKA 0; 0x1ffff pin 1  17; 0x1effff pin 0  16
#|0xbd8 in 15 steps
#|0x13ba in 2145 steps
#|0x7df in 26 steps
#|Notify(\_TZ_.TZ00, 0x80)
#|step limit in 1000 steps
#|undefined \_SB_.NONE in 0 steps
#|0x0 in 9 steps, 0xffffffff in 7 steps
