# bend-osdev-acpi, show.bend: tables, errors and AML values as one line of
# text each, for logs and for the differential test (ref/gen.py writes the
# same text from its own reader). Numbers are decimal, 64-bit values 16 hex
# digits, byte strings hex.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./gas.bend as G
import ./rsdp.bend as P
import ./rsdt.bend as S
import ./madt.bend as M
import ./fadt.bend as F
import ./facs.bend as FS
import ./hpet.bend as Hp
import ./mcfg.bend as Mc
import ./srat.bend as Sr
import ./slit.bend as Sl
import ./bgrt.bend as Bg
import ./dsdt.bend as D
import ./registry.bend as R

def sh.u(+v: U32) -> String:
  U32.show(v)

def sh.n(+v: Nat) -> String:
  Nat.show(v)

def sh.w(+v: W.W64) -> String:
  W.W64.show_hex(v)

def sh.x(o: B.Octets) -> String:
  B.Octets.hex(o)

def sh.list(xs: List<&2, String>, sep: String) -> String:
  String.join(xs, sep)

def AcpiShow.error(e: E.AcpiError) -> String:
  match e:
    case E.AcpiTooShort{n, g}:
      "TooShort " ++ sh.n(n) ++ " " ++ sh.n(g)
    case E.AcpiBadSignature{s}:
      "BadSignature " ++ sh.x(s)
    case E.AcpiBadLength{l}:
      "BadLength " ++ sh.u(l)
    case E.AcpiBadChecksum{s}:
      "BadChecksum " ++ sh.u(s)
    case E.AcpiRsdpBadChecksum{s}:
      "RsdpBadChecksum " ++ sh.u(s)
    case E.AcpiRsdpBadExtChecksum{s}:
      "RsdpBadExtChecksum " ++ sh.u(s)
    case E.AcpiBadRevision{r}:
      "BadRevision " ++ sh.u(r)
    case E.AcpiBadEntry{o, k}:
      "BadEntry " ++ sh.n(o) ++ " " ++ sh.u(k)
    case E.AcpiBadSize{n}:
      "BadSize " ++ sh.n(n)
    case E.AcpiNotMapped{a}:
      "NotMapped " ++ sh.w(a)
    case E.AcpiTableMissing{s}:
      "TableMissing " ++ sh.x(s)
    case E.AcpiAmlTruncated{}:
      "AmlTruncated"
    case E.AcpiAmlBadOpcode{c}:
      "AmlBadOpcode " ++ sh.u(c)
    case E.AcpiAmlBadPkgLength{}:
      "AmlBadPkgLength"
    case E.AcpiAmlBadName{}:
      "AmlBadName"
    case E.AcpiAmlUndefined{p}:
      "AmlUndefined " ++ p
    case E.AcpiAmlDuplicate{p}:
      "AmlDuplicate " ++ p
    case E.AcpiAmlBadOperand{c}:
      "AmlBadOperand " ++ sh.u(c)
    case E.AcpiAmlBadType{s}:
      "AmlBadType"
    case E.AcpiAmlRange{}:
      "AmlRange"
    case E.AcpiAmlDivZero{}:
      "AmlDivZero"
    case E.AcpiAmlBadControl{}:
      "AmlBadControl"
    case E.AcpiAmlFatal{t, c, a}:
      "AmlFatal " ++ sh.u(t) ++ " " ++ sh.u(c) ++ " " ++ sh.w(a)
    case E.AcpiAmlUnsupported{s}:
      "AmlUnsupported " ++ s
    case E.AcpiAmlStepLimit{}:
      "AmlStepLimit"
    case E.AcpiAmlHost{c}:
      "AmlHost " ++ sh.u(c)

def AcpiShow.header(h: H.AcpiHeader) -> String:
  match h:
    case H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      sh.x(s) ++ " " ++ sh.u(l) ++ " " ++ sh.u(r) ++ " " ++ sh.u(c) ++ " " ++ sh.x(o) ++ " " ++ sh.x(t) ++ " " ++ sh.u(orv) ++ " " ++ sh.x(ci) ++ " " ++ sh.u(cr)

def AcpiShow.gas(g: G.AcpiGas) -> String:
  G.AcpiGas.show(g)

def sh.rsdp.ext(m: Maybe<&2, P.AcpiRsdpExt>) -> String:
  match m:
    case None{}:
      "none"
    case Some{P.AcpiRsdpExt{l, x}}:
      sh.u(l) ++ " " ++ sh.w(x)

def AcpiShow.rsdp(r: P.AcpiRsdp) -> String:
  match r:
    case P.AcpiRsdp{o, v, a, x}:
      "RSDP " ++ sh.x(o) ++ " " ++ sh.u(v) ++ " " ++ sh.u(a) ++ " " ++ sh.rsdp.ext(x)

def sh.ws(xs: List<&2, W.W64>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{sh.w(h), sh.ws(t)}

def AcpiShow.sdt_list(t: S.AcpiSdtList) -> String:
  match t:
    case S.AcpiSdtList{h, es}:
      "SDT [" ++ sh.list(sh.ws(es), ",") ++ "]"

def AcpiShow.madt_entry(e: M.AcpiMadtEntry) -> String:
  match e:
    case M.AcpiMadtLapic{u, a, f}:
      "lapic " ++ sh.u(u) ++ " " ++ sh.u(a) ++ " " ++ sh.u(f)
    case M.AcpiMadtIoApic{i, a, g}:
      "ioapic " ++ sh.u(i) ++ " " ++ sh.u(a) ++ " " ++ sh.u(g)
    case M.AcpiMadtIso{b, s, g, f}:
      "iso " ++ sh.u(b) ++ " " ++ sh.u(s) ++ " " ++ sh.u(g) ++ " " ++ sh.u(f)
    case M.AcpiMadtNmiSource{f, g}:
      "nmisrc " ++ sh.u(f) ++ " " ++ sh.u(g)
    case M.AcpiMadtLapicNmi{u, f, l}:
      "lapicnmi " ++ sh.u(u) ++ " " ++ sh.u(f) ++ " " ++ sh.u(l)
    case M.AcpiMadtLapicOverride{a}:
      "override " ++ sh.w(a)
    case M.AcpiMadtX2apic{x, f, u}:
      "x2apic " ++ sh.u(x) ++ " " ++ sh.u(f) ++ " " ++ sh.u(u)
    case M.AcpiMadtX2apicNmi{f, u, l}:
      "x2nmi " ++ sh.u(f) ++ " " ++ sh.u(u) ++ " " ++ sh.u(l)
    case M.AcpiMadtGicc{ci, u, f, pv, pg, vg, M.AcpiGiccAddrs{pk, b, gv, gh, gr}, mp, ec, sp, tr}:
      "gicc " ++ sh.u(ci) ++ " " ++ sh.u(u) ++ " " ++ sh.u(f) ++ " " ++ sh.u(pv) ++ " " ++ sh.u(pg) ++ " " ++ sh.u(vg) ++ " " ++ sh.w(pk) ++ " " ++ sh.w(b) ++ " " ++ sh.w(gv) ++ " " ++ sh.w(gh) ++ " " ++ sh.w(gr) ++ " " ++ sh.w(mp) ++ " " ++ sh.u(ec) ++ " " ++ sh.u(sp) ++ " " ++ sh.u(tr)
    case M.AcpiMadtGicd{i, b, v}:
      "gicd " ++ sh.u(i) ++ " " ++ sh.w(b) ++ " " ++ sh.u(v)
    case M.AcpiMadtGicMsi{i, b, f, c, s}:
      "gicmsi " ++ sh.u(i) ++ " " ++ sh.w(b) ++ " " ++ sh.u(f) ++ " " ++ sh.u(c) ++ " " ++ sh.u(s)
    case M.AcpiMadtGicr{b, l}:
      "gicr " ++ sh.w(b) ++ " " ++ sh.u(l)
    case M.AcpiMadtGicIts{i, b}:
      "gicits " ++ sh.u(i) ++ " " ++ sh.w(b)
    case M.AcpiMadtWakeup{v, m}:
      "wakeup " ++ sh.u(v) ++ " " ++ sh.w(m)
    case M.AcpiMadtOther{k, d}:
      "other " ++ sh.u(k) ++ " " ++ sh.x(d)

def sh.madt.es(es: List<&2, M.AcpiMadtEntry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{AcpiShow.madt_entry(h), sh.madt.es(t)}

def AcpiShow.madt(m: M.AcpiMadt) -> String:
  match m:
    case M.AcpiMadt{h, a, f, es}:
      "MADT " ++ sh.u(a) ++ " " ++ sh.u(f) ++ " [" ++ sh.list(sh.madt.es(es), "; ") ++ "]"

def sh.fadt.core(c: F.AcpiFadtCore) -> String:
  match c:
    case F.AcpiFadtCore{fc, d, im, pp, sci, smi, en, dis, s4, ps, F.AcpiFadtBlocks{e1a, e1b, c1a, c1b, c2, tm, g0, g1}, F.AcpiFadtLens{le, lc, l2, lt, lg0, lg1, gb}, cst, p2, p3, fs, fst, doff, dw, da, ma, ce, ia, fl}:
      sh.list([sh.u(fc), sh.u(d), sh.u(im), sh.u(pp), sh.u(sci), sh.u(smi), sh.u(en), sh.u(dis), sh.u(s4), sh.u(ps), sh.u(e1a), sh.u(e1b), sh.u(c1a), sh.u(c1b), sh.u(c2), sh.u(tm), sh.u(g0), sh.u(g1), sh.u(le), sh.u(lc), sh.u(l2), sh.u(lt), sh.u(lg0), sh.u(lg1), sh.u(gb), sh.u(cst), sh.u(p2), sh.u(p3), sh.u(fs), sh.u(fst), sh.u(doff), sh.u(dw), sh.u(da), sh.u(ma), sh.u(ce), sh.u(ia), sh.u(fl)], ",")

def sh.fadt.ext(m: Maybe<&2, F.AcpiFadtExt>) -> String:
  match m:
    case None{}:
      "none"
    case Some{F.AcpiFadtExt{rr, rv, ab, mv, xfc, xd, F.AcpiFadtX{e1a, e1b, c1a, c1b, c2, tm, g0, g1}}}:
      sh.list([AcpiShow.gas(rr), sh.u(rv), sh.u(ab), sh.u(mv), sh.w(xfc), sh.w(xd), AcpiShow.gas(e1a), AcpiShow.gas(e1b), AcpiShow.gas(c1a), AcpiShow.gas(c1b), AcpiShow.gas(c2), AcpiShow.gas(tm), AcpiShow.gas(g0), AcpiShow.gas(g1)], ",")

def sh.fadt.sleep(m: Maybe<&2, F.AcpiFadtSleep>) -> String:
  match m:
    case None{}:
      "none"
    case Some{F.AcpiFadtSleep{c, s}}:
      AcpiShow.gas(c) ++ "," ++ AcpiShow.gas(s)

def sh.fadt.hyp(m: Maybe<&2, W.W64>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      sh.w(v)

def AcpiShow.fadt(+f: F.AcpiFadt) -> String:
  match f:
    case F.AcpiFadt{h, c, x, s, v}:
      "FADT " ++ sh.fadt.core(c) ++ " ext " ++ sh.fadt.ext(x) ++ " sleep " ++ sh.fadt.sleep(s) ++ " hyp " ++ sh.fadt.hyp(v) ++ " dsdt " ++ sh.w(F.AcpiFadt.dsdt_address(f)) ++ " facs " ++ sh.w(F.AcpiFadt.facs_address(f)) ++ " pm1a " ++ AcpiShow.gas(F.AcpiFadt.block(f, F.AcpiFadtPm1aEvt{}))

def AcpiShow.facs(f: FS.AcpiFacs) -> String:
  match f:
    case FS.AcpiFacs{l, hs, wv, gl, fl, xw, v, of}:
      "FACS " ++ sh.list([sh.u(l), sh.u(hs), sh.u(wv), sh.u(gl), sh.u(fl), sh.w(xw), sh.u(v), sh.u(of)], " ")

def AcpiShow.hpet(t: Hp.AcpiHpet) -> String:
  match t:
    case Hp.AcpiHpet{h, id, g, n, m, p}:
      "HPET " ++ sh.u(id) ++ " " ++ AcpiShow.gas(g) ++ " " ++ sh.u(n) ++ " " ++ sh.u(m) ++ " " ++ sh.u(p)

def sh.mcfg.es(es: List<&2, Mc.AcpiMcfgEntry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Mc.AcpiMcfgEntry{b, s, lo, hi}, t}:
      Con{sh.w(b) ++ " " ++ sh.u(s) ++ " " ++ sh.u(lo) ++ " " ++ sh.u(hi), sh.mcfg.es(t)}

def AcpiShow.mcfg(m: Mc.AcpiMcfg) -> String:
  match m:
    case Mc.AcpiMcfg{h, es}:
      "MCFG [" ++ sh.list(sh.mcfg.es(es), "; ") ++ "]"

def AcpiShow.srat_entry(e: Sr.AcpiSratEntry) -> String:
  match e:
    case Sr.AcpiSratLapic{d, a, f, s, c}:
      "lapic " ++ sh.u(d) ++ " " ++ sh.u(a) ++ " " ++ sh.u(f) ++ " " ++ sh.u(s) ++ " " ++ sh.u(c)
    case Sr.AcpiSratMemory{d, b, l, f}:
      "mem " ++ sh.u(d) ++ " " ++ sh.w(b) ++ " " ++ sh.w(l) ++ " " ++ sh.u(f)
    case Sr.AcpiSratX2apic{d, x, f, c}:
      "x2apic " ++ sh.u(d) ++ " " ++ sh.u(x) ++ " " ++ sh.u(f) ++ " " ++ sh.u(c)
    case Sr.AcpiSratGicc{d, u, f, c}:
      "gicc " ++ sh.u(d) ++ " " ++ sh.u(u) ++ " " ++ sh.u(f) ++ " " ++ sh.u(c)
    case Sr.AcpiSratGicIts{d, i}:
      "its " ++ sh.u(d) ++ " " ++ sh.u(i)
    case Sr.AcpiSratGeneric{k, ht, d, hd, f}:
      "gen " ++ sh.u(k) ++ " " ++ sh.u(ht) ++ " " ++ sh.u(d) ++ " " ++ sh.x(hd) ++ " " ++ sh.u(f)
    case Sr.AcpiSratOther{k, d}:
      "other " ++ sh.u(k) ++ " " ++ sh.x(d)

def sh.srat.es(es: List<&2, Sr.AcpiSratEntry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{AcpiShow.srat_entry(h), sh.srat.es(t)}

def AcpiShow.srat(s: Sr.AcpiSrat) -> String:
  match s:
    case Sr.AcpiSrat{h, es}:
      "SRAT [" ++ sh.list(sh.srat.es(es), "; ") ++ "]"

def AcpiShow.slit(s: Sl.AcpiSlit) -> String:
  match s:
    case Sl.AcpiSlit{h, n, m}:
      "SLIT " ++ sh.n(n) ++ " " ++ sh.x(m)

def AcpiShow.bgrt(t: Bg.AcpiBgrt) -> String:
  match t:
    case Bg.AcpiBgrt{h, v, st, it, a, x, y}:
      "BGRT " ++ sh.u(v) ++ " " ++ sh.u(st) ++ " " ++ sh.u(it) ++ " " ++ sh.w(a) ++ " " ++ sh.u(x) ++ " " ++ sh.u(y)

def AcpiShow.aml(t: D.AcpiAml) -> String:
  match t:
    case D.AcpiAml{h, a}:
      "AML " ++ sh.n(B.Octets.len(a))

# a table read through a registry: its header, then its parser's dump
def AcpiShow.table(~X: Data, t: R.AcpiTable<X>) -> String:
  match t:
    case R.AcpiTRsdt{a}:
      AcpiShow.sdt_list(a)
    case R.AcpiTXsdt{a}:
      AcpiShow.sdt_list(a)
    case R.AcpiTMadt{a}:
      AcpiShow.madt(a)
    case R.AcpiTFadt{a}:
      AcpiShow.fadt(a)
    case R.AcpiTHpet{a}:
      AcpiShow.hpet(a)
    case R.AcpiTMcfg{a}:
      AcpiShow.mcfg(a)
    case R.AcpiTSrat{a}:
      AcpiShow.srat(a)
    case R.AcpiTSlit{a}:
      AcpiShow.slit(a)
    case R.AcpiTBgrt{a}:
      AcpiShow.bgrt(a)
    case R.AcpiTAml{a}:
      AcpiShow.aml(a)
    case R.AcpiTRaw{H.AcpiSdt{h, b}}:
      "RAW " ++ sh.n(B.Octets.len(b))
    case R.AcpiTExt{tag, x}:
      "EXT " ++ sh.u(tag)

def AcpiShow.result(~X: Data, r: Result<&2, &2, E.AcpiError, R.AcpiTable<X>>) -> String:
  match r:
    case Done{t}:
      AcpiShow.table(~X, t)
    case Fail{e}:
      AcpiShow.error(e)
