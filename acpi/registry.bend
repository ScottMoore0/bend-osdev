# bend-osdev-acpi, registry.bend: tables by signature. A registry maps each
# signature to the parser that reads it; AcpiTable.parse checks a table
# (length, checksum: header.bend) and hands it to the parser its signature
# names. A new table plugs in two ways: map its signature to AcpiKRaw{} or to
# one of the parsers here (AcpiRegistry.set), or give it a tag,
# AcpiKExt{tag}, and pass a parser for it as the template argument of
# AcpiTable.parse_with, which answers that parser's own type in AcpiTExt.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./rsdt.bend as S
import ./madt.bend as M
import ./fadt.bend as F
import ./hpet.bend as P
import ./mcfg.bend as C
import ./srat.bend as R
import ./slit.bend as L
import ./bgrt.bend as G
import ./dsdt.bend as D

# the parsers a signature can name
type AcpiKind is Data:
  AcpiKRsdt{}
  AcpiKXsdt{}
  AcpiKMadt{}
  AcpiKFadt{}
  AcpiKHpet{}
  AcpiKMcfg{}
  AcpiKSrat{}
  AcpiKSlit{}
  AcpiKBgrt{}
  # DSDT, SSDT: the AML definition block, as bytes
  AcpiKAml{}
  # header and body, unread
  AcpiKRaw{}
  # the caller's parser (AcpiTable.parse_with), told this tag
  AcpiKExt{tag: U32}

type AcpiRegEntry is Data:
  AcpiRegEntry{signature: B.Octets, kind: AcpiKind}

type AcpiRegistry is Data:
  AcpiRegistry{entries: List<&2, AcpiRegEntry>}

def reg.e(s: String, k: AcpiKind) -> AcpiRegEntry:
  AcpiRegEntry{B.Octets.of_string(s), k}

# every table this package reads
def AcpiRegistry.default() -> AcpiRegistry:
  AcpiRegistry{[reg.e("RSDT", AcpiKRsdt{}), reg.e("XSDT", AcpiKXsdt{}), reg.e("APIC", AcpiKMadt{}), reg.e("FACP", AcpiKFadt{}), reg.e("HPET", AcpiKHpet{}), reg.e("MCFG", AcpiKMcfg{}), reg.e("SRAT", AcpiKSrat{}), reg.e("SLIT", AcpiKSlit{}), reg.e("BGRT", AcpiKBgrt{}), reg.e("DSDT", AcpiKAml{}), reg.e("SSDT", AcpiKAml{})]}

# no parsers: every table raw
def AcpiRegistry.empty() -> AcpiRegistry:
  AcpiRegistry{Nil{}}

def reg.lookup.pick(hit: Bool, k: AcpiKind, rest: AcpiKind) -> AcpiKind:
  match hit:
    case True{}:
      k
    case False{}:
      rest

def reg.lookup(es: List<&2, AcpiRegEntry>, +sig: B.Octets) -> AcpiKind:
  match es:
    case Nil{}:
      AcpiKRaw{}
    case Con{AcpiRegEntry{s, k}, t}:
      reg.lookup.pick(B.Octets.is_eq(s, sig), k, reg.lookup(t, sig))

# the parser for a signature (AcpiKRaw{} if the registry has none)
def AcpiRegistry.lookup(r: AcpiRegistry, +sig: B.Octets) -> AcpiKind:
  match r:
    case AcpiRegistry{es}:
      reg.lookup(es, sig)

def reg.keep(hit: Bool, e: AcpiRegEntry, rest: List<&2, AcpiRegEntry>) -> List<&2, AcpiRegEntry>:
  match hit:
    case True{}:
      rest
    case False{}:
      Con{e, rest}

def reg.drop(es: List<&2, AcpiRegEntry>, +sig: B.Octets) -> List<&2, AcpiRegEntry>:
  match es:
    case Nil{}:
      Nil{}
    case Con{AcpiRegEntry{+s, k}, t}:
      reg.keep(B.Octets.is_eq(s, sig), AcpiRegEntry{s, k}, reg.drop(t, sig))

# the registry with sig mapped to k (replacing any earlier mapping)
def AcpiRegistry.set(r: AcpiRegistry, +sig: B.Octets, k: AcpiKind) -> AcpiRegistry:
  match r:
    case AcpiRegistry{es}:
      AcpiRegistry{Con{AcpiRegEntry{sig, k}, reg.drop(es, sig)}}

# the registry without sig (its tables then read raw)
def AcpiRegistry.remove(r: AcpiRegistry, +sig: B.Octets) -> AcpiRegistry:
  match r:
    case AcpiRegistry{es}:
      AcpiRegistry{reg.drop(es, sig)}

# A parsed table. X is the type the caller's extension parser answers
# (AcpiNoExt when there is none).
type AcpiTable<-X: Data> is Data:
  AcpiTRsdt{t: S.AcpiSdtList}
  AcpiTXsdt{t: S.AcpiSdtList}
  AcpiTMadt{t: M.AcpiMadt}
  AcpiTFadt{t: F.AcpiFadt}
  AcpiTHpet{t: P.AcpiHpet}
  AcpiTMcfg{t: C.AcpiMcfg}
  AcpiTSrat{t: R.AcpiSrat}
  AcpiTSlit{t: L.AcpiSlit}
  AcpiTBgrt{t: G.AcpiBgrt}
  AcpiTAml{t: D.AcpiAml}
  AcpiTRaw{t: H.AcpiSdt}
  AcpiTExt{tag: U32, x: X}

type AcpiNoExt is Data:
  AcpiNoExt{}

# the extension parser of AcpiTable.parse: refuses every tag
def AcpiNoExt.parse(tag: U32, t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiNoExt>:
  Fail{E.AcpiBadSignature{H.AcpiHeader.signature(H.AcpiSdt.header(t))}}

def reg.wrap(~X: Data, ~A: Data, ~f: A -> AcpiTable<X>, r: Result<&2, &2, E.AcpiError, A>) -> Result<&2, &2, E.AcpiError, AcpiTable<X>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{f(a)}

def reg.ext(~X: Data, +tag: U32, r: Result<&2, &2, E.AcpiError, X>) -> Result<&2, &2, E.AcpiError, AcpiTable<X>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{AcpiTExt{tag, a}}

def reg.dispatch(~X: Data, ~ext: U32 -> H.AcpiSdt -> Result<&2, &2, E.AcpiError, X>, k: AcpiKind, +t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiTable<X>>:
  match k:
    case AcpiKRsdt{}:
      reg.wrap(~X, ~S.AcpiSdtList, ~(a => AcpiTRsdt{a}), S.AcpiRsdt.of_sdt(t))
    case AcpiKXsdt{}:
      reg.wrap(~X, ~S.AcpiSdtList, ~(a => AcpiTXsdt{a}), S.AcpiXsdt.of_sdt(t))
    case AcpiKMadt{}:
      reg.wrap(~X, ~M.AcpiMadt, ~(a => AcpiTMadt{a}), M.AcpiMadt.of_sdt(t))
    case AcpiKFadt{}:
      reg.wrap(~X, ~F.AcpiFadt, ~(a => AcpiTFadt{a}), F.AcpiFadt.of_sdt(t))
    case AcpiKHpet{}:
      reg.wrap(~X, ~P.AcpiHpet, ~(a => AcpiTHpet{a}), P.AcpiHpet.of_sdt(t))
    case AcpiKMcfg{}:
      reg.wrap(~X, ~C.AcpiMcfg, ~(a => AcpiTMcfg{a}), C.AcpiMcfg.of_sdt(t))
    case AcpiKSrat{}:
      reg.wrap(~X, ~R.AcpiSrat, ~(a => AcpiTSrat{a}), R.AcpiSrat.of_sdt(t))
    case AcpiKSlit{}:
      reg.wrap(~X, ~L.AcpiSlit, ~(a => AcpiTSlit{a}), L.AcpiSlit.of_sdt(t))
    case AcpiKBgrt{}:
      reg.wrap(~X, ~G.AcpiBgrt, ~(a => AcpiTBgrt{a}), G.AcpiBgrt.of_sdt(t))
    case AcpiKAml{}:
      reg.wrap(~X, ~D.AcpiAml, ~(a => AcpiTAml{a}), D.AcpiAml.of_sdt(t))
    case AcpiKRaw{}:
      Done{AcpiTRaw{t}}
    case AcpiKExt{+tag}:
      reg.ext(~X, tag, ext(tag, t))

def reg.go(~X: Data, ~ext: U32 -> H.AcpiSdt -> Result<&2, &2, E.AcpiError, X>, +reg: AcpiRegistry, r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiTable<X>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+t}:
      reg.dispatch(~X, ~ext, AcpiRegistry.lookup(reg, H.AcpiHeader.signature(H.AcpiSdt.header(t))), t)

# the table at the front of o: checked (AcpiSdt.check: length and checksum),
# then read by the parser the registry names for its signature, with ext
# for AcpiKExt tags
def AcpiTable.parse_with(~X: Data, ~ext: U32 -> H.AcpiSdt -> Result<&2, &2, E.AcpiError, X>, +reg: AcpiRegistry, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiTable<X>>:
  reg.go(~X, ~ext, reg, H.AcpiSdt.parse(o))

# the same without extension parsers
def AcpiTable.parse(+reg: AcpiRegistry, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiTable<AcpiNoExt>>:
  AcpiTable.parse_with(~AcpiNoExt, ~AcpiNoExt.parse, reg, o)

# the name of the parser that read the table
def AcpiTable.name(~X: Data, t: AcpiTable<X>) -> String:
  match t:
    case AcpiTRsdt{a}:
      "RSDT"
    case AcpiTXsdt{a}:
      "XSDT"
    case AcpiTMadt{a}:
      "APIC"
    case AcpiTFadt{a}:
      "FACP"
    case AcpiTHpet{a}:
      "HPET"
    case AcpiTMcfg{a}:
      "MCFG"
    case AcpiTSrat{a}:
      "SRAT"
    case AcpiTSlit{a}:
      "SLIT"
    case AcpiTBgrt{a}:
      "BGRT"
    case AcpiTAml{a}:
      B.Octets.to_string(H.AcpiHeader.signature(D.AcpiAml.header(a)))
    case AcpiTRaw{a}:
      B.Octets.to_string(H.AcpiHeader.signature(H.AcpiSdt.header(a)))
    case AcpiTExt{tag, x}:
      "ext " ++ U32.show(tag)
