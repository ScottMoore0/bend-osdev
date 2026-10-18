# bend-osdev-acpi, aml_device.bend: the device objects OSPM reads most
# (ACPI 6.5, chapter 6, Device Configuration): _HID (6.1.5) and its EISA ID
# form (EISAID, chapter 19), _STA (6.3.7), _CRS (6.2.2, resource templates:
# aml_resource.bend) and _PRT (6.2.13, PCI interrupt routing), and the
# devices of a namespace.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./aml_value.bend as V
import ./aml_ns.bend as S
import ./aml_host.bend as Hs
import ./aml_interp.bend as I
import ./aml.bend as A
import ./aml_resource.bend as R

# EISA IDs: a DWord holding three letters of five bits and four hex digits,
# most significant byte first in memory ("PNP0A03" is 0x030AD041)

def dv.hex.pick(lt: Bool, +d: U32) -> U32:
  match lt:
    case True{}:
      U32.add(48, d)
    case False{}:
      U32.add(55, d)

def dv.hex(+d: U32) -> U32:
  dv.hex.pick(U32.is_lt(d, 10), d)

def AmlEisaId.text(+v: U32) -> String:
  +id = U32.or(U32.or(U32.shln(U32.and(v, 255), 24n), U32.shln(U32.and(U32.shrn(v, 8n), 255), 16n)), U32.or(U32.shln(U32.and(U32.shrn(v, 16n), 255), 8n), U32.and(U32.shrn(v, 24n), 255)))
  B.to_string([U32.add(64, U32.and(U32.shrn(id, 26n), 31)), U32.add(64, U32.and(U32.shrn(id, 21n), 31)), U32.add(64, U32.and(U32.shrn(id, 16n), 31)), dv.hex(U32.and(U32.shrn(id, 12n), 15)), dv.hex(U32.and(U32.shrn(id, 8n), 15)), dv.hex(U32.and(U32.shrn(id, 4n), 15)), dv.hex(U32.and(id, 15))])

# The objects of a device

def dv.get.pick(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, has: Bool, +s: A.AmlSystem<H>, +p: String, +n: Nat) -> Maybe<&2, Result<&2, &2, E.AcpiError, V.AmlValue>>:
  match has:
    case True{}:
      Some{A.AmlOutcome.result(H, A.Aml.eval(~H, ~io, s, p, Nil{}, n))}
    case False{}:
      None{}

# an object of a device evaluated (a method run with no arguments), in at
# most n steps; None if the device has no such object
def AmlDevice.get(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +s: A.AmlSystem<H>, +dev: String, +seg: String, +n: Nat) -> Maybe<&2, Result<&2, &2, E.AcpiError, V.AmlValue>>:
  +p = S.AmlPath.child(dev, seg)
  dv.get.pick(~H, ~io, S.AmlNs.has(A.AmlSystem.ns(H, s), p), s, p, n)

def dv.sta(m: Maybe<&2, Result<&2, &2, E.AcpiError, V.AmlValue>>) -> Result<&2, &2, E.AcpiError, W.W64>:
  match m:
    case None{}:
      Done{W.W64.from_u32(15)}
    case Some{Fail{e}}:
      Fail{e}
    case Some{Done{v}}:
      V.AmlValue.to_int(True{}, v)

# _STA: bit 0 present, 1 enabled, 2 shown in the UI, 3 functioning,
# 4 battery present; a device without _STA is 0x0F (6.3.7)
def AmlDevice.status(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +s: A.AmlSystem<H>, +dev: String, +n: Nat) -> Result<&2, &2, E.AcpiError, W.W64>:
  dv.sta(AmlDevice.get(~H, ~io, s, dev, "_STA", n))

def dv.id(v: V.AmlValue) -> Result<&2, &2, E.AcpiError, String>:
  match v:
    case V.AmlInt{x}:
      Done{AmlEisaId.text(W.W64.lo(x))}
    case V.AmlStr{t}:
      Done{B.Octets.to_string(t)}
    case _:
      Fail{E.AcpiAmlBadType{"_HID is not an integer or a string"}}

def dv.hid(m: Maybe<&2, Result<&2, &2, E.AcpiError, V.AmlValue>>) -> Maybe<&2, Result<&2, &2, E.AcpiError, String>>:
  match m:
    case None{}:
      None{}
    case Some{Fail{e}}:
      Some{Fail{e}}
    case Some{Done{v}}:
      Some{dv.id(v)}

# _HID as text: an EISA ID ("PNP0A03") or the string itself ("ACPI0003")
def AmlDevice.hid(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +s: A.AmlSystem<H>, +dev: String, +n: Nat) -> Maybe<&2, Result<&2, &2, E.AcpiError, String>>:
  dv.hid(AmlDevice.get(~H, ~io, s, dev, "_HID", n))

def dv.crs(m: Maybe<&2, Result<&2, &2, E.AcpiError, V.AmlValue>>) -> Result<&2, &2, E.AcpiError, List<&2, R.AmlResource>>:
  match m:
    case None{}:
      Done{Nil{}}
    case Some{Fail{e}}:
      Fail{e}
    case Some{Done{V.AmlBuf{b}}}:
      R.AmlResource.parse(b)
    case Some{Done{v}}:
      Fail{E.AcpiAmlBadType{"_CRS is not a buffer"}}

# _CRS: the resources the device uses (none if it has no _CRS)
def AmlDevice.crs(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +s: A.AmlSystem<H>, +dev: String, +n: Nat) -> Result<&2, &2, E.AcpiError, List<&2, R.AmlResource>>:
  dv.crs(AmlDevice.get(~H, ~io, s, dev, "_CRS", n))

# _PRT entries (6.2.13): the device's address (high word: device, low word:
# 0xFFFF for any function), the PCI pin (0 INTA to 3 INTD), and the source:
# the path of a link device and its index, or an empty path and the global
# system interrupt in index
type AmlPrtEntry is Data:
  AmlPrtEntry{address: W.W64, pin: U32, source: String, index: U32}

def dv.prt.src(v: V.AmlValue) -> String:
  match v:
    case V.AmlRef{V.AmlLName{p}}:
      p
    case V.AmlStr{t}:
      B.Octets.to_string(t)
    case _:
      ""

def dv.prt.one(v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlPrtEntry>:
  match v:
    case V.AmlPkg{[V.AmlInt{a}, V.AmlInt{p}, src, V.AmlInt{i}]}:
      Done{AmlPrtEntry{a, W.W64.lo(p), dv.prt.src(src), W.W64.lo(i)}}
    case _:
      Fail{E.AcpiAmlBadType{"a _PRT entry is not a package of four"}}

def dv.prt.cons(r: Result<&2, &2, E.AcpiError, AmlPrtEntry>, rs: Result<&2, &2, E.AcpiError, List<&2, AmlPrtEntry>>) -> Result<&2, &2, E.AcpiError, List<&2, AmlPrtEntry>>:
  match r rs:
    case Done{e} Done{es}:
      Done{Con{e, es}}
    case Fail{e} _:
      Fail{e}
    case Done{e} Fail{x}:
      Fail{x}

def dv.prt.all(xs: List<&2, V.AmlValue>) -> Result<&2, &2, E.AcpiError, List<&2, AmlPrtEntry>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{x, t}:
      dv.prt.cons(dv.prt.one(x), dv.prt.all(t))

def dv.prt(m: Maybe<&2, Result<&2, &2, E.AcpiError, V.AmlValue>>) -> Result<&2, &2, E.AcpiError, List<&2, AmlPrtEntry>>:
  match m:
    case None{}:
      Done{Nil{}}
    case Some{Fail{e}}:
      Fail{e}
    case Some{Done{V.AmlPkg{xs}}}:
      dv.prt.all(xs)
    case Some{Done{v}}:
      Fail{E.AcpiAmlBadType{"_PRT is not a package"}}

# _PRT of a PCI bridge (none if it has no _PRT)
def AmlDevice.prt(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +s: A.AmlSystem<H>, +dev: String, +n: Nat) -> Result<&2, &2, E.AcpiError, List<&2, AmlPrtEntry>>:
  dv.prt(AmlDevice.get(~H, ~io, s, dev, "_PRT", n))

def dv.kind(o: Maybe<&2, S.AmlObject>) -> U32:
  match o:
    case Some{x}:
      S.AmlObject.type(x)
    case None{}:
      0

def dv.devs.pick(dev: Bool, p: String, rest: List<&2, String>) -> List<&2, String>:
  match dev:
    case True{}:
      Con{p, rest}
    case False{}:
      rest

def dv.devs(ps: List<&2, String>, +ns: S.AmlNs) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      dv.devs.pick(U32.is_eq(dv.kind(S.AmlNs.get(ns, p)), 6), p, dv.devs(t, ns))

# every Device (and \_SB_) of a namespace, in path order
def AmlDevice.list(+ns: S.AmlNs) -> List<&2, String>:
  dv.devs(S.AmlNs.paths(ns), ns)
