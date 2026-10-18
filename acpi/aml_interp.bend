# bend-osdev-acpi, aml_interp.bend: the AML interpreter (ACPI 6.5, chapter
# 19, ASL Reference, for what each operator does; chapter 20, AML
# Specification, for its encoding).
#
# The interpreter is a small-step machine over the AML bytes: a cursor (the
# bytes left in the term list being run), a stack of frames (the operator
# whose operands are being read, the If, While, method call or package
# being run), and the world it changes (the method's Arg and Local values,
# the namespace, the operation-region host, notifications and the Debug
# log). Each step reads one opcode, or gives one value to the frame on top.
# AmlM.run stops after its step bound whatever the AML does (LAWS.bend:
# run_steps_bound), so a method that loops for ever ends with
# AcpiAmlStepLimit.
#
# Operation regions are reached through the host, a template argument
# (aml_host.bend): ~H: Data, ~io: H -> AmlHostOp -> Result<..., AmlHostAns<H>>.
#
# Method calls take their argument count from the namespace when they are
# reached, which is how AML is meant to be read (a MethodInvocation is a
# NameString followed by as many TermArgs as the method takes, 20.2.5.4).
# What is not supported is listed in README.md.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./aml_pkglength.bend as K
import ./aml_name.bend as N
import ./aml_value.bend as V
import ./aml_ns.bend as S
import ./aml_host.bend as Hs
import ./aml_field.bend as F

# Options

type AmlOptions is Data:
  # the strings \_OSI answers True for; \_OS and \_REV
  AmlOptions{osi: List<&2, String>, os: String, rev: U32}

# \_OSI answers True for the Windows releases firmware tests for, as
# operating systems commonly do, and for "Module Device" and "Processor
# Device"; \_OS is "Microsoft Windows NT"; \_REV is 2 (ACPI 6.5, 5.7.2)
def AmlOptions.default() -> AmlOptions:
  AmlOptions{["Windows 2000", "Windows 2001", "Windows 2001 SP1", "Windows 2001 SP2", "Windows 2001.1", "Windows 2001.1 SP1", "Windows 2006", "Windows 2006 SP1", "Windows 2006.1", "Windows 2009", "Windows 2012", "Windows 2013", "Windows 2015", "Windows 2016", "Windows 2017", "Windows 2017.2", "Windows 2018", "Windows 2018.2", "Windows 2019", "Windows 2020", "Windows 2021", "Windows 2022", "Module Device", "Processor Device", "3.0 Thermal Model", "Extended Address Space Descriptor"], "Microsoft Windows NT", 2}

# The machine

# the bytes left in the current term list: the list from here, and how
# many of its bytes belong to the list
type AmlCur is Data:
  AmlCur{code: List<&2, U32>, lim: Nat}

# what an operand must be
type AmlArgK is Data:
  # a TermArg: a value
  AmlKTerm{}
  # a Target or SuperName: a location
  AmlKTarget{}
  # a source (Index, SizeOf, ObjectType, CreateField): its location if it
  # has one, its value otherwise
  AmlKBase{}
  # CondRefOf's operand: a location, or nothing if the name is undefined
  AmlKCond{}
  # a package element: a value, or a name as a reference (not run)
  AmlKElem{}
  # immediate data
  AmlKByte{}
  AmlKWord{}
  AmlKDWord{}
  # a NameString, as the path it names from the current scope
  AmlKName{}

type AmlOp is Data:
  # an operator, by opcode (an extended opcode 0x5B xx is 256 + xx)
  AmlOpCode{code: U32}
  AmlOpCall{path: String, nargs: Nat}
  AmlOpOsi{}

type AmlCtx is Data:
  # the scope names resolve from; Arg0-6; Local0-7; the names this method
  # call created (removed when it returns)
  AmlCtx{scope: String, args: List<&2, V.AmlValue>, locals: List<&2, V.AmlValue>, temps: List<&2, String>}

type AmlFrame is Data:
  AmlFArgs{op: AmlOp, got: List<&2, V.AmlValue>, todo: List<&2, AmlArgK>}
  # a nested term list (Scope, Device, Else, ...): where to resume, and the
  # scope to restore
  AmlFSeq{after: AmlCur, scope: String}
  # an If whose predicate is being read
  AmlFIf{after: AmlCur}
  # an If whose body is running
  AmlFIfBody{after: AmlCur}
  # a While: its predicate's start, what follows it, and whether the body
  # is running (else the predicate is being read)
  AmlFWhile{start: AmlCur, after: AmlCur, body: Bool}
  # a method call's return point
  AmlFCall{ctx: AmlCtx, back: AmlCur}
  # a Buffer whose size is being read; the rest of its package is its
  # initializer
  AmlFBuffer{after: AmlCur}
  # a Package: its NumElements, the elements so far (last first)
  AmlFPkg{count: Nat, got: List<&2, V.AmlValue>, after: AmlCur}
  # a VarPackage whose count is being read
  AmlFVarPkg{after: AmlCur}
  # the bottom: the definition block, or the method evaluated
  AmlFTop{}

type AmlMode is Data:
  # the next term of a term list, or the list's end
  AmlMExec{}
  # one operand, of this kind
  AmlMEval{k: AmlArgK}
  # a value for the frame on top
  AmlMGive{v: V.AmlValue}
  AmlMDone{v: V.AmlValue}
  AmlMFail{e: E.AcpiError}

# a Notify: the object's path and the value
type AmlNote is Data:
  AmlNote{path: String, value: W.W64}

type AmlEnv is Data:
  # wide: 64-bit integers; notes and debug: last first; clock: Timer, in
  # 100 ns units (Sleep and Stall advance it)
  AmlEnv{wide: Bool, opts: AmlOptions, notes: List<&2, AmlNote>, debug: List<&2, V.AmlValue>, clock: W.W64}

type AmlWorld<-H: Data> is Data:
  AmlWorld{ctx: AmlCtx, ns: S.AmlNs, host: H, env: AmlEnv}

type AmlMachine<-H: Data> is Data:
  AmlMachine{mode: AmlMode, cur: AmlCur, frames: List<&2, AmlFrame>, w: AmlWorld<H>}

# a value read, and the world after reading it
type AmlRead<-H: Data> is Data:
  AmlRead{w: AmlWorld<H>, v: V.AmlValue}

def AmlMachine.mode(-H: Data, m: AmlMachine<H>) -> AmlMode:
  match m:
    case AmlMachine{md, c, fs, w}:
      md

def AmlMachine.world(-H: Data, m: AmlMachine<H>) -> AmlWorld<H>:
  match m:
    case AmlMachine{md, c, fs, w}:
      w

# the machine has stopped: Done or Fail
def AmlMachine.halted(-H: Data, m: AmlMachine<H>) -> Bool:
  match m:
    case AmlMachine{AmlMDone{v}, c, fs, w}:
      True{}
    case AmlMachine{AmlMFail{e}, c, fs, w}:
      True{}
    case AmlMachine{md, c, fs, w}:
      False{}

def in.fail(-H: Data, +e: E.AcpiError, c: AmlCur, fs: List<&2, AmlFrame>, w: AmlWorld<H>) -> AmlMachine<H>:
  AmlMachine{AmlMFail{e}, c, fs, w}

# World parts

def AmlWorld.ctx(-H: Data, w: AmlWorld<H>) -> AmlCtx:
  match w:
    case AmlWorld{c, n, h, e}:
      c

def AmlWorld.ns(-H: Data, w: AmlWorld<H>) -> S.AmlNs:
  match w:
    case AmlWorld{c, n, h, e}:
      n

def AmlWorld.env(-H: Data, w: AmlWorld<H>) -> AmlEnv:
  match w:
    case AmlWorld{c, n, h, e}:
      e

def AmlWorld.host(-H: Data, w: AmlWorld<H>) -> H:
  match w:
    case AmlWorld{c, n, h, e}:
      h

def in.scope(-H: Data, w: AmlWorld<H>) -> String:
  match w:
    case AmlWorld{AmlCtx{s, a, l, t}, n, h, e}:
      s

def in.wide(-H: Data, w: AmlWorld<H>) -> Bool:
  match w:
    case AmlWorld{c, n, h, AmlEnv{wd, o, nt, d, cl}}:
      wd

def in.with_ns(-H: Data, w: AmlWorld<H>, n: S.AmlNs) -> AmlWorld<H>:
  match w:
    case AmlWorld{c, n0, h, e}:
      AmlWorld{c, n, h, e}

def in.with_host(-H: Data, w: AmlWorld<H>, h: H) -> AmlWorld<H>:
  match w:
    case AmlWorld{c, n, h0, e}:
      AmlWorld{c, n, h, e}

def in.with_ctx(-H: Data, w: AmlWorld<H>, c: AmlCtx) -> AmlWorld<H>:
  match w:
    case AmlWorld{c0, n, h, e}:
      AmlWorld{c, n, h, e}

def in.with_env(-H: Data, w: AmlWorld<H>, e: AmlEnv) -> AmlWorld<H>:
  match w:
    case AmlWorld{c, n, h, e0}:
      AmlWorld{c, n, h, e}

def in.with_scope(-H: Data, w: AmlWorld<H>, s: String) -> AmlWorld<H>:
  match w:
    case AmlWorld{AmlCtx{s0, a, l, t}, n, h, e}:
      AmlWorld{AmlCtx{s, a, l, t}, n, h, e}

# a name created: in the namespace, and among the method call's names
def in.define(-H: Data, w: AmlWorld<H>, +p: String, o: S.AmlObject) -> AmlWorld<H>:
  match w:
    case AmlWorld{AmlCtx{s, a, l, t}, n, h, e}:
      AmlWorld{AmlCtx{s, a, l, Con{p, t}}, S.AmlNs.set(n, p, o), h, e}

def in.note(-H: Data, w: AmlWorld<H>, nt: AmlNote) -> AmlWorld<H>:
  match w:
    case AmlWorld{c, n, h, AmlEnv{wd, o, nts, d, cl}}:
      AmlWorld{c, n, h, AmlEnv{wd, o, Con{nt, nts}, d, cl}}

def in.debug(-H: Data, w: AmlWorld<H>, v: V.AmlValue) -> AmlWorld<H>:
  match w:
    case AmlWorld{c, n, h, AmlEnv{wd, o, nts, d, cl}}:
      AmlWorld{c, n, h, AmlEnv{wd, o, nts, Con{v, d}, cl}}

def in.tick(-H: Data, w: AmlWorld<H>, +dt: W.W64) -> AmlWorld<H>:
  match w:
    case AmlWorld{c, n, h, AmlEnv{wd, o, nts, d, cl}}:
      AmlWorld{c, n, h, AmlEnv{wd, o, nts, d, W.W64.add(cl, dt)}}

def in.clock(-H: Data, w: AmlWorld<H>) -> W.W64:
  match w:
    case AmlWorld{c, n, h, AmlEnv{wd, o, nts, d, cl}}:
      cl

def in.opts(-H: Data, w: AmlWorld<H>) -> AmlOptions:
  match w:
    case AmlWorld{c, n, h, AmlEnv{wd, o, nts, d, cl}}:
      o

# Decoding: reading from the cursor

type AmlB is Data:
  AmlB{b: U32, cur: AmlCur}

type AmlPkgC is Data:
  # the package's contents, and what follows the package
  AmlPkgC{body: AmlCur, after: AmlCur}

type AmlNameC is Data:
  AmlNameC{name: N.AmlName, cur: AmlCur}

def cur.byte(c: AmlCur) -> Result<&2, &2, E.AcpiError, AmlB>:
  match c:
    case AmlCur{code, lim}:
      match code lim:
        case Con{h, t} 1n+p:
          Done{AmlB{h, AmlCur{t, p}}}
        case _ _:
          Fail{E.AcpiAmlTruncated{}}

def cur.at_end(c: AmlCur) -> Bool:
  match c:
    case AmlCur{code, lim}:
      Nat.is_eq(lim, 0n)

# the next byte, if the list has one
def cur.peek(c: AmlCur) -> Maybe<&2, U32>:
  match c:
    case AmlCur{code, lim}:
      match lim:
        case 0n:
          None{}
        case 1n+p:
          List.head(&2, U32, code)

def cur.skip(+n: Nat, c: AmlCur) -> AmlCur:
  match c:
    case AmlCur{code, lim}:
      AmlCur{B.drop(n, code), Nat.sub(lim, n)}

def cur.take(+n: Nat, c: AmlCur) -> B.Octets:
  match c:
    case AmlCur{code, lim}:
      B.Octets.of_list(B.take.fast(n, code))

def cur.len(c: AmlCur) -> Nat:
  match c:
    case AmlCur{code, lim}:
      lim

def cur.pkg.k(ok: Bool, +inner: Nat, rest: List<&2, U32>, +outer: Nat) -> Result<&2, &2, E.AcpiError, AmlPkgC>:
  match ok:
    case False{}:
      Fail{E.AcpiAmlBadPkgLength{}}
    case True{}:
      +r = rest
      Done{AmlPkgC{AmlCur{r, inner}, AmlCur{B.drop(inner, r), outer}}}

def cur.pkg.go(r: Result<&2, &2, E.AcpiError, K.AmlPkgL>, +lim: Nat) -> Result<&2, &2, E.AcpiError, AmlPkgC>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{K.AmlPkgL{v, +size, rest}}:
      +total = U32.to_nat(v)
      cur.pkg.k(Bool.and(Nat.is_le(size, total), Nat.is_le(total, lim)), Nat.sub(total, size), rest, Nat.sub(lim, total))

# a PkgLength and the package it covers (the value counts the PkgLength's
# own bytes); AcpiAmlBadPkgLength if it runs past the enclosing list
def cur.pkg(c: AmlCur) -> Result<&2, &2, E.AcpiError, AmlPkgC>:
  match c:
    case AmlCur{+code, +lim}:
      cur.pkg.go(K.pk.dec(code), lim)

def cur.name.fit(ok: Bool, n: N.AmlName, rest: List<&2, U32>, left: Nat) -> Result<&2, &2, E.AcpiError, AmlNameC>:
  match ok:
    case False{}:
      Fail{E.AcpiAmlTruncated{}}
    case True{}:
      Done{AmlNameC{n, AmlCur{rest, left}}}

def cur.name.k(ok: Bool, +n: N.AmlName, +size: Nat, rest: List<&2, U32>, +lim: Nat) -> Result<&2, &2, E.AcpiError, AmlNameC>:
  match ok:
    case False{}:
      Fail{E.AcpiAmlUnsupported{"a NameString not in its shortest form"}}
    case True{}:
      cur.name.fit(Nat.is_le(size, lim), n, rest, Nat.sub(lim, size))

def cur.name.go(r: Result<&2, &2, E.AcpiError, N.AmlNameL>, +code: List<&2, U32>, +lim: Nat) -> Result<&2, &2, E.AcpiError, AmlNameC>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{N.AmlNameL{+n, rest}}:
      +size = N.AmlName.size(n)
      cur.name.k(B.list_eq.fast(B.take.fast(size, code), N.nm.enc(n)), n, size, rest, lim)

# a NameString (in the shortest form, as compilers write it)
def cur.name(c: AmlCur) -> Result<&2, &2, E.AcpiError, AmlNameC>:
  match c:
    case AmlCur{+code, +lim}:
      cur.name.go(N.nm.dec(code), code, lim)

def cur.fold(xs: List<&2, U32>, +sh: Nat, acc: W.W64) -> W.W64:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      cur.fold(t, Nat.add(sh, 8n), W.W64.or(acc, W.W64.shl(W.W64.from_u32(U32.and(h, 255)), sh)))

type AmlImm is Data:
  AmlImm{v: W.W64, cur: AmlCur}

def cur.imm.k(ok: Bool, +n: Nat, c: AmlCur) -> Result<&2, &2, E.AcpiError, AmlImm>:
  match ok:
    case False{}:
      Fail{E.AcpiAmlTruncated{}}
    case True{}:
      match c:
        case AmlCur{+code, lim}:
          Done{AmlImm{cur.fold(B.take.fast(n, code), 0n, W.W64.zero()), AmlCur{B.drop(n, code), Nat.sub(lim, n)}}}

# n bytes of immediate data, little-endian
def cur.imm(+n: Nat, +c: AmlCur) -> Result<&2, &2, E.AcpiError, AmlImm>:
  cur.imm.k(Nat.is_le(n, cur.len(c)), n, c)

# Named objects

def in.alias.go(n: Nat, +ns: S.AmlNs, +p: String, o: Maybe<&2, S.AmlObject>) -> String:
  match n:
    case 0n:
      p
    case 1n+k:
      match o:
        case Some{S.AmlOAlias{+t}}:
          in.alias.go(k, ns, t, S.AmlNs.get(ns, t))
        case _:
          p

# an alias followed to what it names (up to 8 aliases deep)
def in.unalias(+ns: S.AmlNs, +p: String) -> String:
  in.alias.go(8n, ns, p, S.AmlNs.get(ns, p))

def in.int.of(o: Maybe<&2, S.AmlObject>) -> W.W64:
  match o:
    case Some{S.AmlOData{V.AmlInt{x}}}:
      x
    case _:
      W.W64.zero()

# the Integer a Name holds (0 if there is none)
def in.name_int(+ns: S.AmlNs, +p: String) -> W.W64:
  in.int.of(S.AmlNs.get(ns, p))

def in.up.go(n: Nat, hit: Bool, +ns: S.AmlNs, +p: String, +seg: String) -> W.W64:
  match n:
    case 0n:
      W.W64.zero()
    case 1n+k:
      match hit:
        case True{}:
          in.name_int(ns, S.AmlPath.child(p, seg))
        case False{}:
          +up = S.AmlPath.parent(p)
          in.up.go(k, S.AmlNs.has(ns, S.AmlPath.child(up, seg)), ns, up, seg)

# the Integer seg names in p or the nearest scope enclosing it (0 if none)
def in.up_int(+ns: S.AmlNs, +p: String, +seg: String) -> W.W64:
  in.up.go(String.length(p), S.AmlNs.has(ns, S.AmlPath.child(p, seg)), ns, p, seg)

def in.base.pick(pci: Bool, +ns: S.AmlNs, +parent: String, +off: W.W64) -> W.W64:
  match pci:
    case False{}:
      off
    case True{}:
      +adr = W.W64.lo(in.name_int(ns, S.AmlPath.child(parent, "_ADR")))
      +bus = W.W64.lo(in.up_int(ns, parent, "_BBN"))
      +seg = W.W64.lo(in.up_int(ns, parent, "_SEG"))
      W.W64.add(Hs.AmlPci.address(seg, bus, U32.shrn(adr, 16n), U32.and(adr, 65535), 0), off)

def in.desc.go(o: Maybe<&2, S.AmlObject>, +ns: S.AmlNs, +off: Nat, +bits: Nat, +flags: U32) -> Result<&2, &2, E.AcpiError, F.AmlFieldDesc>:
  match o:
    case Some{S.AmlORegion{+sp, +roff, len, +parent}}:
      Done{F.AmlFieldDesc{sp, in.base.pick(U32.is_eq(sp, 2), ns, parent, roff), len, off, bits, flags}}
    case _:
      Fail{E.AcpiAmlBadType{"the region of a field is not an OperationRegion"}}

# a field unit of a region, its region resolved
def in.desc(+ns: S.AmlNs, +region: String, +off: Nat, +bits: Nat, +flags: U32) -> Result<&2, &2, E.AcpiError, F.AmlFieldDesc>:
  in.desc.go(S.AmlNs.get(ns, in.unalias(ns, region)), ns, off, bits, flags)

def in.fdesc(o: Maybe<&2, S.AmlObject>, +ns: S.AmlNs) -> Result<&2, &2, E.AcpiError, F.AmlFieldDesc>:
  match o:
    case Some{S.AmlOField{r, off, bits, flags}}:
      in.desc(ns, r, off, bits, flags)
    case _:
      Fail{E.AcpiAmlBadType{"a register of an IndexField is not a field"}}

# Reading

def in.nth(xs: List<&2, V.AmlValue>, i: Nat) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match xs i:
    case Nil{} _:
      Fail{E.AcpiAmlRange{}}
    case Con{h, t} 0n:
      Done{h}
    case Con{h, t} 1n+k:
      in.nth(t, k)

def in.byte.at(m: Maybe<&2, U32>) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match m:
    case None{}:
      Fail{E.AcpiAmlRange{}}
    case Some{b}:
      Done{V.AmlInt{W.W64.from_u32(b)}}

# element i of a package, buffer or string
def AmlValue.element(v: V.AmlValue, +i: Nat) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match v:
    case V.AmlPkg{xs}:
      in.nth(xs, i)
    case V.AmlBuf{b}:
      in.byte.at(B.Octets.at(b, i))
    case V.AmlStr{s}:
      in.byte.at(B.Octets.at(s, i))
    case _:
      Fail{E.AcpiAmlBadType{"Index of a value that is not a package, buffer or string"}}

def in.ctx.arg(-H: Data, w: AmlWorld<H>, i: Nat) -> V.AmlValue:
  match w:
    case AmlWorld{AmlCtx{s, a, l, t}, n, h, e}:
      Maybe.default(&2, V.AmlValue, List.get(&2, V.AmlValue, a, i), V.AmlUninit{})

def in.ctx.local(-H: Data, w: AmlWorld<H>, i: Nat) -> V.AmlValue:
  match w:
    case AmlWorld{AmlCtx{s, a, l, t}, n, h, e}:
      Maybe.default(&2, V.AmlValue, List.get(&2, V.AmlValue, l, i), V.AmlUninit{})

# xs with element i replaced (padded with Uninitialized up to i)
def in.list.set(i: Nat, xs: List<&2, V.AmlValue>, v: V.AmlValue) -> List<&2, V.AmlValue>:
  match i xs:
    case 0n Nil{}:
      [v]
    case 0n Con{h, t}:
      Con{v, t}
    case 1n+k Nil{}:
      Con{V.AmlUninit{}, in.list.set(k, Nil{}, v)}
    case 1n+k Con{h, t}:
      Con{h, in.list.set(k, t, v)}

def in.set.arg(-H: Data, w: AmlWorld<H>, i: Nat, v: V.AmlValue) -> AmlWorld<H>:
  match w:
    case AmlWorld{AmlCtx{s, a, l, t}, n, h, e}:
      AmlWorld{AmlCtx{s, in.list.set(i, a, v), l, t}, n, h, e}

def in.set.local(-H: Data, w: AmlWorld<H>, i: Nat, v: V.AmlValue) -> AmlWorld<H>:
  match w:
    case AmlWorld{AmlCtx{s, a, l, t}, n, h, e}:
      AmlWorld{AmlCtx{s, a, in.list.set(i, l, v), t}, n, h, e}

def in.wrap(-H: Data, w: AmlWorld<H>, r: Result<&2, &2, E.AcpiError, V.AmlValue>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      Done{AmlRead{w, v}}

def in.got.int(-H: Data, +wide: Bool, w: AmlWorld<H>, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Hs.AmlHostAns{h, x}}:
      Done{AmlRead{in.with_host(H, w, h), V.AmlInt{V.AmlInt.fit(wide, x)}}}

def in.got.buf(-H: Data, w: AmlWorld<H>, r: Result<&2, &2, E.AcpiError, F.AmlFieldBuf<H>>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{F.AmlFieldBuf{h, o}}:
      Done{AmlRead{in.with_host(H, w, h), V.AmlBuf{o}}}

def in.field.rd(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, small: Bool, +w: AmlWorld<H>, r: Result<&2, &2, E.AcpiError, F.AmlFieldDesc>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match small:
    case True{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{+d}:
          in.got.int(H, in.wide(H, w), w, F.AmlField.read_int(~H, ~io, d, AmlWorld.host(H, w)))
    case False{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{+d}:
          in.got.buf(H, w, F.AmlField.read_buf(~H, ~io, d, AmlWorld.host(H, w)))

def in.ixfield.rd(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, ri: Result<&2, &2, E.AcpiError, F.AmlFieldDesc>, rd: Result<&2, &2, E.AcpiError, F.AmlFieldDesc>, +f: F.AmlFieldDesc, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match ri rd:
    case Done{+i} Done{+d}:
      in.got.int(H, in.wide(H, w), w, F.AmlField.read_indexed(~H, ~io, i, d, f, AmlWorld.host(H, w)))
    case Fail{e} _:
      Fail{e}
    case Done{i} Fail{e}:
      Fail{e}

def in.data.of(o: Maybe<&2, S.AmlObject>) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match o:
    case Some{S.AmlOData{v}}:
      Done{v}
    case _:
      Fail{E.AcpiAmlBadType{"the source of a buffer field is not data"}}

# the data a location holds, without reading hardware: a Name value, a
# Local, an Arg (the buffer behind a buffer field)
def in.read_data(-H: Data, +w: AmlWorld<H>, l: V.AmlLoc) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match l:
    case V.AmlLName{+p}:
      in.data.of(S.AmlNs.get(AmlWorld.ns(H, w), in.unalias(AmlWorld.ns(H, w), p)))
    case V.AmlLLocal{i}:
      Done{in.ctx.local(H, w, i)}
    case V.AmlLArg{i}:
      Done{in.ctx.arg(H, w, i)}
    case _:
      Fail{E.AcpiAmlUnsupported{"a buffer field of an element"}}

def in.bf.rd.pick(-H: Data, small: Bool, +wide: Bool, +w: AmlWorld<H>, +b: B.Octets, +off: Nat, +bits: Nat) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match small:
    case True{}:
      in.wrap(H, w, Result.map(&2, &2, E.AcpiError, W.W64, V.AmlValue, x => V.AmlInt{V.AmlInt.fit(wide, x)}, F.AmlBits.get(b, off, bits)))
    case False{}:
      Done{AmlRead{w, V.AmlBuf{F.AmlBits.get_buf(b, off, bits)}}}

def in.bf.rd(-H: Data, +wide: Bool, +w: AmlWorld<H>, r: Result<&2, &2, E.AcpiError, V.AmlValue>, +off: Nat, +bits: Nat) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{V.AmlBuf{+b}}:
      in.bf.rd.pick(H, Nat.is_le(bits, 64n), wide, w, b, off, bits)
    case Done{v}:
      Fail{E.AcpiAmlBadType{"the source of a buffer field is not a buffer"}}

def in.ix.desc(+ns: S.AmlNs, +off: Nat, +bits: Nat, +flags: U32) -> F.AmlFieldDesc:
  F.AmlFieldDesc{0, W.W64.zero(), W.W64.max(), off, bits, flags}

# the value of a named object (alias followed): a field unit is read
# through the host
def in.read_obj(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +w: AmlWorld<H>, +p: String, o: Maybe<&2, S.AmlObject>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match o:
    case None{}:
      Fail{E.AcpiAmlUndefined{p}}
    case Some{S.AmlOData{v}}:
      Done{AmlRead{w, v}}
    case Some{S.AmlOField{r, +off, +bits, +flags}}:
      in.field.rd(~H, ~io, Nat.is_le(bits, 64n), w, in.desc(AmlWorld.ns(H, w), r, off, bits, flags))
    case Some{S.AmlOIndexField{i, d, +off, +bits, +flags}}:
      in.ixfield.rd(~H, ~io, in.fdesc(S.AmlNs.get(AmlWorld.ns(H, w), i), AmlWorld.ns(H, w)), in.fdesc(S.AmlNs.get(AmlWorld.ns(H, w), d), AmlWorld.ns(H, w)), in.ix.desc(AmlWorld.ns(H, w), off, bits, flags), w)
    case Some{S.AmlOBufField{l, +off, +bits}}:
      in.bf.rd(H, in.wide(H, w), w, in.read_data(H, w, l), off, bits)
    case Some{+obj}:
      Done{AmlRead{w, V.AmlObj{p, S.AmlObject.type(obj)}}}

def in.elem.rd(-H: Data, r: Result<&2, &2, E.AcpiError, AmlRead<H>>, +i: Nat) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlRead{w, v}}:
      in.wrap(H, w, AmlValue.element(v, i))

# the value at a location
def in.read_loc(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, l: V.AmlLoc, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match l:
    case V.AmlLName{+p}:
      +q = in.unalias(AmlWorld.ns(H, w), p)
      in.read_obj(~H, ~io, w, q, S.AmlNs.get(AmlWorld.ns(H, w), q))
    case V.AmlLLocal{i}:
      Done{AmlRead{w, in.ctx.local(H, w, i)}}
    case V.AmlLArg{i}:
      Done{AmlRead{w, in.ctx.arg(H, w, i)}}
    case V.AmlLIndex{base, +i}:
      in.elem.rd(H, in.read_loc(~H, ~io, base, w), i)
    case V.AmlLElem{v, +i}:
      in.wrap(H, w, AmlValue.element(v, i))
    case V.AmlLDebug{}:
      Done{AmlRead{w, V.AmlUninit{}}}
    case V.AmlLNone{}:
      Done{AmlRead{w, V.AmlUninit{}}}

# Writing

def in.host.w(-H: Data, w: AmlWorld<H>, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Hs.AmlHostAns{h, x}}:
      Done{in.with_host(H, w, h)}

def in.field.wr.int(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +w: AmlWorld<H>, +d: F.AmlFieldDesc, r: Result<&2, &2, E.AcpiError, W.W64>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      in.host.w(H, w, F.AmlField.write_int(~H, ~io, d, AmlWorld.host(H, w), x))

def in.field.wr.buf(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +w: AmlWorld<H>, +d: F.AmlFieldDesc, r: Result<&2, &2, E.AcpiError, B.Octets>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      in.host.w(H, w, F.AmlField.write_buf(~H, ~io, d, AmlWorld.host(H, w), o))

def in.field.wr(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, small: Bool, +w: AmlWorld<H>, r: Result<&2, &2, E.AcpiError, F.AmlFieldDesc>, v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match small:
    case True{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{+d}:
          in.field.wr.int(~H, ~io, w, d, V.AmlValue.to_int(in.wide(H, w), v))
    case False{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{+d}:
          in.field.wr.buf(~H, ~io, w, d, V.AmlValue.to_buf(in.wide(H, w), v))

def in.ixfield.wr(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, ri: Result<&2, &2, E.AcpiError, F.AmlFieldDesc>, rd: Result<&2, &2, E.AcpiError, F.AmlFieldDesc>, rx: Result<&2, &2, E.AcpiError, W.W64>, +f: F.AmlFieldDesc, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match ri rd rx:
    case Done{+i} Done{+d} Done{+x}:
      in.host.w(H, w, F.AmlField.write_indexed(~H, ~io, i, d, f, AmlWorld.host(H, w), x))
    case Fail{e} _ _:
      Fail{e}
    case Done{i} Fail{e} _:
      Fail{e}
    case Done{i} Done{d} Fail{e}:
      Fail{e}

def in.fit.buf(+n: Nat, +o: B.Octets) -> B.Octets:
  +h = B.Octets.take(n, o)
  B.Octets.append(h, B.Octets.zeros(Nat.sub(n, B.Octets.len(h))))

# the value v stored where a Name holds old: converted to old type when
# old is an Integer, a String or a Buffer (a Buffer keeps its length)
def in.convert(+wide: Bool, old: V.AmlValue, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match old:
    case V.AmlInt{x}:
      Result.map(&2, &2, E.AcpiError, W.W64, V.AmlValue, y => V.AmlInt{y}, V.AmlValue.to_int(wide, v))
    case V.AmlStr{s}:
      Result.map(&2, &2, E.AcpiError, B.Octets, V.AmlValue, t => V.AmlStr{t}, V.AmlValue.to_str(wide, v))
    case V.AmlBuf{+b}:
      Result.map(&2, &2, E.AcpiError, B.Octets, V.AmlValue, t => V.AmlBuf{in.fit.buf(B.Octets.len(b), t)}, V.AmlValue.to_buf(wide, v))
    case _:
      Done{v}

def in.set.data(-H: Data, +w: AmlWorld<H>, +p: String, r: Result<&2, &2, E.AcpiError, V.AmlValue>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      Done{in.with_ns(H, w, S.AmlNs.set(AmlWorld.ns(H, w), p, S.AmlOData{v}))}

# a buffer put back where a buffer field found it
def in.put.data(-H: Data, +w: AmlWorld<H>, l: V.AmlLoc, v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match l:
    case V.AmlLName{+p}:
      Done{in.with_ns(H, w, S.AmlNs.set(AmlWorld.ns(H, w), in.unalias(AmlWorld.ns(H, w), p), S.AmlOData{v}))}
    case V.AmlLLocal{i}:
      Done{in.set.local(H, w, i, v)}
    case V.AmlLArg{i}:
      Done{in.set.arg(H, w, i, v)}
    case _:
      Fail{E.AcpiAmlUnsupported{"a buffer field of an element"}}

def in.bf.wr.go(-H: Data, +w: AmlWorld<H>, l: V.AmlLoc, r: Result<&2, &2, E.AcpiError, B.Octets>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{b}:
      in.put.data(H, w, l, V.AmlBuf{b})

def in.bf.wr(-H: Data, +w: AmlWorld<H>, +l: V.AmlLoc, src: Result<&2, &2, E.AcpiError, V.AmlValue>, +off: Nat, +bits: Nat, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match src:
    case Fail{e}:
      Fail{e}
    case Done{V.AmlBuf{+b}}:
      in.bf.wr.go(H, w, l, Result.bind(&2, &2, E.AcpiError, W.W64, B.Octets, V.AmlValue.to_int(in.wide(H, w), v), x => F.AmlBits.set(b, off, Nat.min(bits, 64n), x)))
    case Done{o}:
      Fail{E.AcpiAmlBadType{"the source of a buffer field is not a buffer"}}

# Store to a named object (chapter 19, Store): a Name converted to its type, a field
# unit written through the host, a buffer field into its buffer
def in.store.obj(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +w: AmlWorld<H>, +p: String, o: Maybe<&2, S.AmlObject>, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match o:
    case None{}:
      Fail{E.AcpiAmlUndefined{p}}
    case Some{S.AmlOData{old}}:
      in.set.data(H, w, p, in.convert(in.wide(H, w), old, v))
    case Some{S.AmlOField{r, +off, +bits, +flags}}:
      in.field.wr(~H, ~io, Nat.is_le(bits, 64n), w, in.desc(AmlWorld.ns(H, w), r, off, bits, flags), v)
    case Some{S.AmlOIndexField{i, d, +off, +bits, +flags}}:
      in.ixfield.wr(~H, ~io, in.fdesc(S.AmlNs.get(AmlWorld.ns(H, w), i), AmlWorld.ns(H, w)), in.fdesc(S.AmlNs.get(AmlWorld.ns(H, w), d), AmlWorld.ns(H, w)), V.AmlValue.to_int(in.wide(H, w), v), in.ix.desc(AmlWorld.ns(H, w), off, bits, flags), w)
    case Some{S.AmlOBufField{+l, +off, +bits}}:
      in.bf.wr(H, w, l, in.read_data(H, w, l), off, bits, v)
    case Some{obj}:
      Fail{E.AcpiAmlBadType{"Store to an object that holds no data"}}

def in.elem.pkg(ok: Bool, xs: List<&2, V.AmlValue>, i: Nat, v: V.AmlValue) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match ok:
    case True{}:
      Done{V.AmlPkg{in.list.set(i, xs, v)}}
    case False{}:
      Fail{E.AcpiAmlRange{}}

def in.elem.wrap(str: Bool, b: B.Octets) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match str:
    case True{}:
      Done{V.AmlStr{b}}
    case False{}:
      Done{V.AmlBuf{b}}

def in.elem.bytes(ok: Bool, str: Bool, +b: B.Octets, +i: Nat, r: Result<&2, &2, E.AcpiError, W.W64>) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match ok r:
    case False{} _:
      Fail{E.AcpiAmlRange{}}
    case True{} Fail{e}:
      Fail{e}
    case True{} Done{x}:
      +nb = B.Octets.concat([B.Octets.take(i, b), B.Octets.of_list([W.W64.lo(x)]), B.Octets.drop(1n+i, b)])
      in.elem.wrap(str, nb)

def in.elem.set(base: V.AmlValue, +i: Nat, +wide: Bool, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match base:
    case V.AmlPkg{+xs}:
      in.elem.pkg(Nat.is_lt(i, List.length(&2, V.AmlValue, xs)), xs, i, v)
    case V.AmlBuf{+b}:
      in.elem.bytes(Nat.is_lt(i, B.Octets.len(b)), False{}, b, i, V.AmlValue.to_int(wide, v))
    case V.AmlStr{+b}:
      in.elem.bytes(Nat.is_lt(i, B.Octets.len(b)), True{}, b, i, V.AmlValue.to_int(wide, v))
    case _:
      Fail{E.AcpiAmlBadType{"Index of a value that is not a package, buffer or string"}}

type AmlPut<-H: Data> is Data:
  AmlPut{w: AmlWorld<H>, v: V.AmlValue}

def in.put.res(-H: Data, w: AmlWorld<H>, r: Result<&2, &2, E.AcpiError, V.AmlValue>) -> Result<&2, &2, E.AcpiError, AmlPut<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      Done{AmlPut{w, v}}

def in.put.idx.go(-H: Data, r: Result<&2, &2, E.AcpiError, V.AmlValue>, +w: AmlWorld<H>, base: V.AmlLoc) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{nv}:
      in.put.data(H, w, base, nv)

def in.put.idx(-H: Data, r: Result<&2, &2, E.AcpiError, AmlRead<H>>, base: V.AmlLoc, +i: Nat, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlRead{+w, old}}:
      in.put.idx.go(H, in.elem.set(old, i, in.wide(H, w), v), w, base)

# an element of a package, buffer or string at a location replaced
# (Store to Index(...)); the location must be a Name, a Local or an Arg
def in.put.index(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +base: V.AmlLoc, +i: Nat, +w: AmlWorld<H>, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  in.put.idx(H, in.read_loc(~H, ~io, base, w), base, i, v)

def in.is_writable(o: Maybe<&2, S.AmlObject>) -> Bool:
  match o:
    case Some{S.AmlOField{r, off, n, f}}:
      True{}
    case Some{S.AmlOIndexField{i, d, off, n, f}}:
      True{}
    case Some{S.AmlOBufField{l, off, n}}:
      True{}
    case _:
      False{}

def in.put.name(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, fieldy: Bool, +w: AmlWorld<H>, +p: String, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match fieldy:
    case True{}:
      in.store.obj(~H, ~io, w, p, S.AmlNs.get(AmlWorld.ns(H, w), p), v)
    case False{}:
      Done{in.with_ns(H, w, S.AmlNs.set(AmlWorld.ns(H, w), p, S.AmlOData{v}))}

# CopyObject (chapter 19), and how Index writes back: the value replaces what
# the location holds, without conversion (a field unit is written)
def in.put(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, l: V.AmlLoc, +w: AmlWorld<H>, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match l:
    case V.AmlLName{+p}:
      +q = in.unalias(AmlWorld.ns(H, w), p)
      in.put.name(~H, ~io, in.is_writable(S.AmlNs.get(AmlWorld.ns(H, w), q)), w, q, v)
    case V.AmlLLocal{i}:
      Done{in.set.local(H, w, i, v)}
    case V.AmlLArg{i}:
      Done{in.set.arg(H, w, i, v)}
    case V.AmlLIndex{base, i}:
      in.put.index(~H, ~io, base, i, w, v)
    case V.AmlLElem{x, i}:
      Done{w}
    case V.AmlLDebug{}:
      Done{in.debug(H, w, v)}
    case V.AmlLNone{}:
      Done{w}

# Store (chapter 19) to a location, an Arg holding a reference excepted
def in.store.base(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, l: V.AmlLoc, +w: AmlWorld<H>, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match l:
    case V.AmlLName{+p}:
      +q = in.unalias(AmlWorld.ns(H, w), p)
      in.store.obj(~H, ~io, w, q, S.AmlNs.get(AmlWorld.ns(H, w), q), v)
    case V.AmlLLocal{i}:
      Done{in.set.local(H, w, i, v)}
    case V.AmlLArg{i}:
      Done{in.set.arg(H, w, i, v)}
    case V.AmlLIndex{base, i}:
      in.put.index(~H, ~io, base, i, w, v)
    case V.AmlLElem{x, i}:
      Done{w}
    case V.AmlLDebug{}:
      Done{in.debug(H, w, v)}
    case V.AmlLNone{}:
      Done{w}

def in.store.arg(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, cur: V.AmlValue, +i: Nat, +w: AmlWorld<H>, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match cur:
    case V.AmlRef{l2}:
      in.store.base(~H, ~io, l2, w, v)
    case _:
      Done{in.set.arg(H, w, i, v)}

# Store to a location; an Arg that holds a reference is stored through
def in.store(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +l: V.AmlLoc, +w: AmlWorld<H>, +v: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match l:
    case V.AmlLArg{+i}:
      in.store.arg(~H, ~io, in.ctx.arg(H, w, i), i, w, v)
    case _:
      in.store.base(~H, ~io, l, w, v)

# Machine transitions

def in.mk(-H: Data, md: AmlMode, c: AmlCur, fs: List<&2, AmlFrame>, w: AmlWorld<H>) -> AmlMachine<H>:
  AmlMachine{md, c, fs, w}

def in.give(-H: Data, v: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, w: AmlWorld<H>) -> AmlMachine<H>:
  AmlMachine{AmlMGive{v}, c, fs, w}

def in.no.cur() -> AmlCur:
  AmlCur{Nil{}, 0n}

# a world after a change, or the failure; then v is given
def in.then.give(-H: Data, r: Result<&2, &2, E.AcpiError, AmlWorld<H>>, v: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{w2}:
      AmlMachine{AmlMGive{v}, c, fs, w2}

def in.read.give(-H: Data, r: Result<&2, &2, E.AcpiError, AmlRead<H>>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{AmlRead{w2, v}}:
      AmlMachine{AmlMGive{v}, c, fs, w2}

def in.val.give(-H: Data, r: Result<&2, &2, E.AcpiError, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{v}:
      AmlMachine{AmlMGive{v}, c, fs, w}

def in.loc(v: V.AmlValue) -> Result<&2, &2, E.AcpiError, V.AmlLoc>:
  match v:
    case V.AmlRef{l}:
      Done{l}
    case V.AmlUninit{}:
      Done{V.AmlLNone{}}
    case _:
      Fail{E.AcpiAmlBadOperand{112}}

def in.store.give2(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, V.AmlLoc>, +v: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{l}:
      in.then.give(H, in.store(~H, ~io, l, w, v), v, c, fs, w)

# the result of an operator stored in its Target, then given
def in.store.give(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, V.AmlValue>, t: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{+v}:
      in.store.give2(~H, ~io, in.loc(t), v, c, fs, w)

# Integer operators (19.6: Add, Subtract, Multiply, ShiftLeft, ShiftRight,
# And, NAnd, Or, NOr, XOr, Mod). Mod by zero is AcpiAmlDivZero.

def in.mod(z: Bool, +x: W.W64, +y: W.W64) -> Result<&2, &2, E.AcpiError, W.W64>:
  match z:
    case True{}:
      Fail{E.AcpiAmlDivZero{}}
    case False{}:
      Done{W.W64.mod(x, y)}

def in.shift.pick(big: Bool, left: Bool, +wide: Bool, +x: W.W64, +n: Nat) -> W.W64:
  match big:
    case True{}:
      W.W64.zero()
    case False{}:
      match left:
        case True{}:
          V.AmlInt.fit(wide, W.W64.shl(x, n))
        case False{}:
          W.W64.shr(x, n)

# shifts by 64 or more give 0
def in.shift(left: Bool, +wide: Bool, +x: W.W64, +y: W.W64) -> W.W64:
  in.shift.pick(Bool.or(Bool.not(U32.is_eq(W.W64.hi(y), 0)), U32.is_le(64, W.W64.lo(y))), left, wide, x, U32.to_nat(W.W64.lo(y)))

def in.int2(+op: Nat, +wide: Bool, +x: W.W64, +y: W.W64) -> Result<&2, &2, E.AcpiError, W.W64>:
  match op:
    case 114n:
      Done{V.AmlInt.fit(wide, W.W64.add(x, y))}
    case 116n:
      Done{V.AmlInt.fit(wide, W.W64.sub(x, y))}
    case 119n:
      Done{V.AmlInt.fit(wide, W.W64.mul(x, y))}
    case 121n:
      Done{in.shift(True{}, wide, x, y)}
    case 122n:
      Done{in.shift(False{}, wide, x, y)}
    case 123n:
      Done{W.W64.and(x, y)}
    case 124n:
      Done{V.AmlInt.fit(wide, W.W64.not(W.W64.and(x, y)))}
    case 125n:
      Done{W.W64.or(x, y)}
    case 126n:
      Done{V.AmlInt.fit(wide, W.W64.not(W.W64.or(x, y)))}
    case 127n:
      Done{W.W64.xor(x, y)}
    case 133n:
      in.mod(W.W64.is_zero(y), x, y)
    case _:
      Fail{E.AcpiAmlBadOpcode{U32.from_nat(op)}}

type AmlInts is Data:
  AmlInts{x: W.W64, y: W.W64}

def in.ints.go(ra: Result<&2, &2, E.AcpiError, W.W64>, rb: Result<&2, &2, E.AcpiError, W.W64>) -> Result<&2, &2, E.AcpiError, AmlInts>:
  match ra rb:
    case Done{x} Done{y}:
      Done{AmlInts{x, y}}
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}

def in.ints(+wide: Bool, a: V.AmlValue, b: V.AmlValue) -> Result<&2, &2, E.AcpiError, AmlInts>:
  in.ints.go(V.AmlValue.to_int(wide, a), V.AmlValue.to_int(wide, b))

def in.bad(-H: Data, +code: U32, c: AmlCur, fs: List<&2, AmlFrame>, w: AmlWorld<H>) -> AmlMachine<H>:
  AmlMachine{AmlMFail{E.AcpiAmlBadOperand{code}}, c, fs, w}

def in.int2.v(+op: Nat, +wide: Bool, r: Result<&2, &2, E.AcpiError, AmlInts>) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlInts{x, y}}:
      Result.map(&2, &2, E.AcpiError, W.W64, V.AmlValue, z => V.AmlInt{z}, in.int2(op, wide, x, y))

def in.ap.int2(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +op: Nat, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{a, Con{b, Con{t, Nil{}}}}:
      in.store.give(~H, ~io, in.int2.v(op, in.wide(H, w), in.ints(in.wide(H, w), a, b)), t, c, fs, w)
    case _:
      in.bad(H, U32.from_nat(op), c, fs, w)

def in.div.pick(z: Bool, +x: W.W64, +y: W.W64) -> Result<&2, &2, E.AcpiError, AmlInts>:
  match z:
    case True{}:
      Fail{E.AcpiAmlDivZero{}}
    case False{}:
      Done{AmlInts{W.W64.div(x, y), W.W64.mod(x, y)}}

# Divide: the remainder to its Target, the quotient to its own
def in.div.v(r: Result<&2, &2, E.AcpiError, AmlInts>) -> Result<&2, &2, E.AcpiError, AmlInts>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlInts{+x, +y}}:
      in.div.pick(W.W64.is_zero(y), x, y)

def in.div.q(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, AmlWorld<H>>, +q: W.W64, qt: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{+w2}:
      in.store.give(~H, ~io, Done{V.AmlInt{q}}, qt, c, fs, w2)

def in.div.st(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, AmlInts>, rt: V.AmlValue, qt: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{AmlInts{+q, rm}}:
      in.div.q(~H, ~io, Result.bind(&2, &2, E.AcpiError, V.AmlLoc, AmlWorld<H>, in.loc(rt), l => in.store(~H, ~io, l, w, V.AmlInt{rm})), q, qt, c, fs, w)

def in.ap.div(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{a, Con{b, Con{rt, Con{qt, Nil{}}}}}:
      in.div.st(~H, ~io, in.div.v(in.ints(in.wide(H, w), a, b)), rt, qt, c, fs, w)
    case _:
      in.bad(H, 120, c, fs, w)

# Not, FindSetLeftBit, FindSetRightBit: one operand and a Target

def in.fsb.first(none: Bool, +i: Nat, acc: Nat) -> Nat:
  match none:
    case True{}:
      Nat.add(i, 1n)
    case False{}:
      acc

def in.fsb.pick(set: Bool, left: Bool, +i: Nat, +acc: Nat) -> Nat:
  match set:
    case False{}:
      acc
    case True{}:
      match left:
        case True{}:
          Nat.add(i, 1n)
        case False{}:
          in.fsb.first(Nat.is_eq(acc, 0n), i, acc)

def in.fsb.go(n: Nat, +x: W.W64, +i: Nat, +left: Bool, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      in.fsb.go(p, x, Nat.add(i, 1n), left, in.fsb.pick(W.W64.is_eq(W.W64.and(W.W64.shr(x, i), W.W64.one()), W.W64.one()), left, i, acc))

def in.int1(+op: Nat, +wide: Bool, +x: W.W64) -> W.W64:
  match op:
    case 128n:
      V.AmlInt.fit(wide, W.W64.not(x))
    case 129n:
      W.W64.from_nat(in.fsb.go(64n, x, 0n, True{}, 0n))
    case _:
      W.W64.from_nat(in.fsb.go(64n, x, 0n, False{}, 0n))

def in.ap.int1(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +op: Nat, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{a, Con{t, Nil{}}}:
      in.store.give(~H, ~io, Result.map(&2, &2, E.AcpiError, W.W64, V.AmlValue, x => V.AmlInt{in.int1(op, in.wide(H, w), x)}, V.AmlValue.to_int(in.wide(H, w), a)), t, c, fs, w)
    case _:
      in.bad(H, U32.from_nat(op), c, fs, w)

# Increment, Decrement: read, change, store back

def in.incdec.op(inc: Bool, +x: W.W64) -> W.W64:
  match inc:
    case True{}:
      W.W64.add(x, W.W64.one())
    case False{}:
      W.W64.sub(x, W.W64.one())

def in.incdec.v(-H: Data, +inc: Bool, +wide: Bool, r: Result<&2, &2, E.AcpiError, AmlRead<H>>) -> Result<&2, &2, E.AcpiError, AmlPut<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlRead{w2, v}}:
      in.put.res(H, w2, Result.map(&2, &2, E.AcpiError, W.W64, V.AmlValue, x => V.AmlInt{V.AmlInt.fit(wide, in.incdec.op(inc, x))}, V.AmlValue.to_int(wide, v)))

def in.incdec.st(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, AmlPut<H>>, +l: V.AmlLoc, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{AmlPut{+w2, +v}}:
      in.then.give(H, in.store(~H, ~io, l, w2, v), v, c, fs, w2)

def in.incdec.loc(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +inc: Bool, r: Result<&2, &2, E.AcpiError, V.AmlLoc>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{+l}:
      in.incdec.st(~H, ~io, in.incdec.v(H, inc, in.wide(H, w), in.read_loc(~H, ~io, l, w)), l, c, fs, w)

def in.ap.incdec(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +inc: Bool, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{t, Nil{}}:
      in.incdec.loc(~H, ~io, inc, in.loc(t), c, fs, w)
    case _:
      in.bad(H, 117, c, fs, w)

# Logical operators (LAnd, LOr, LNot, LEqual, LGreater, LLess): Ones or 0

def in.truth(+wide: Bool, v: V.AmlValue) -> Result<&2, &2, E.AcpiError, Bool>:
  Result.map(&2, &2, E.AcpiError, W.W64, Bool, x => Bool.not(W.W64.is_zero(x)), V.AmlValue.to_int(wide, v))

def in.bool.v(+wide: Bool, r: Result<&2, &2, E.AcpiError, Bool>) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  Result.map(&2, &2, E.AcpiError, Bool, V.AmlValue, b => V.AmlInt{V.AmlInt.of_bool(wide, b)}, r)

def in.logic2(ra: Result<&2, &2, E.AcpiError, Bool>, rb: Result<&2, &2, E.AcpiError, Bool>, op: Nat) -> Result<&2, &2, E.AcpiError, Bool>:
  match ra rb:
    case Done{x} Done{y}:
      match op:
        case 144n:
          Done{Bool.and(x, y)}
        case _:
          Done{Bool.or(x, y)}
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}

def in.cmp.op(+op: Nat, c: Cmp) -> Bool:
  match op:
    case 147n:
      Cmp.is_eq(c)
    case 148n:
      Cmp.is_gt(c)
    case _:
      Cmp.is_lt(c)

def in.logic.pick(cmp: Bool, +op: Nat, +wide: Bool, a: V.AmlValue, +b: V.AmlValue) -> Result<&2, &2, E.AcpiError, Bool>:
  match cmp:
    case True{}:
      Result.map(&2, &2, E.AcpiError, Cmp, Bool, x => in.cmp.op(op, x), V.AmlValue.compare(wide, a, b))
    case False{}:
      in.logic2(in.truth(wide, a), in.truth(wide, b), op)

def in.logic.two(+op: Nat, +wide: Bool, a: V.AmlValue, +b: V.AmlValue) -> Result<&2, &2, E.AcpiError, Bool>:
  in.logic.pick(Nat.is_le(147n, op), op, wide, a, b)

def in.ap.logic(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +op: Nat, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{a, Nil{}}:
      +wide = in.wide(H, w)
      in.val.give(H, in.bool.v(wide, Result.map(&2, &2, E.AcpiError, Bool, Bool, b => Bool.not(b), in.truth(wide, a))), c, fs, w)
    case Con{a, Con{b, Nil{}}}:
      +wide = in.wide(H, w)
      in.val.give(H, in.bool.v(wide, in.logic.two(op, wide, a, b)), c, fs, w)
    case _:
      in.bad(H, U32.from_nat(op), c, fs, w)

# Store, CopyObject, RefOf, DerefOf

def in.ap.store(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{v, Con{t, Nil{}}}:
      in.store.give(~H, ~io, Done{v}, t, c, fs, w)
    case _:
      in.bad(H, 112, c, fs, w)

def in.put.give(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, V.AmlLoc>, +v: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{l}:
      in.then.give(H, in.put(~H, ~io, l, w, v), v, c, fs, w)

def in.ap.copy(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{+v, Con{t, Nil{}}}:
      in.put.give(~H, ~io, in.loc(t), v, c, fs, w)
    case _:
      in.bad(H, 157, c, fs, w)

def in.deref.name(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, m: Maybe<&2, String>, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match m:
    case None{}:
      Fail{E.AcpiAmlUndefined{"DerefOf of a name"}}
    case Some{p}:
      in.read_loc(~H, ~io, V.AmlLName{p}, w)

def in.deref(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, v: V.AmlValue, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match v:
    case V.AmlRef{l}:
      in.read_loc(~H, ~io, l, w)
    case V.AmlStr{s}:
      in.deref.name(~H, ~io, S.AmlNs.resolve(AmlWorld.ns(H, w), in.scope(H, w), N.AmlName.of_text(B.Octets.to_string(s))), w)
    case _:
      Fail{E.AcpiAmlBadOperand{131}}

def in.ap.deref(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{v, Nil{}}:
      in.read.give(H, in.deref(~H, ~io, v, w), c, fs, w)
    case _:
      in.bad(H, 131, c, fs, w)

# Index (chapter 19): a reference to an element; it is also put in the Target

def in.index.ref(base: V.AmlValue, +i: Nat) -> V.AmlValue:
  match base:
    case V.AmlRef{l}:
      V.AmlRef{V.AmlLIndex{l, i}}
    case _:
      V.AmlRef{V.AmlLElem{base, i}}

def in.size.of(v: V.AmlValue) -> Result<&2, &2, E.AcpiError, Nat>:
  match v:
    case V.AmlStr{s}:
      Done{B.Octets.len(s)}
    case V.AmlBuf{b}:
      Done{B.Octets.len(b)}
    case V.AmlPkg{xs}:
      Done{List.length(&2, V.AmlValue, xs)}
    case _:
      Fail{E.AcpiAmlBadType{"SizeOf or Index of a value that is not a string, buffer or package"}}

# the value a source operand stands for (read when it is a location)
def in.source(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, v: V.AmlValue, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlRead<H>>:
  match v:
    case V.AmlRef{l}:
      in.read_loc(~H, ~io, l, w)
    case _:
      Done{AmlRead{w, v}}

def in.index.put(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, ok: Bool, +ref: V.AmlValue, t: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match ok:
    case False{}:
      AmlMachine{AmlMFail{E.AcpiAmlRange{}}, c, fs, w}
    case True{}:
      in.put.give(~H, ~io, in.loc(t), ref, c, fs, w)

def in.index.fits(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, Nat>, +base: V.AmlValue, +i: Nat, t: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{n}:
      in.index.put(~H, ~io, Nat.is_lt(i, n), in.index.ref(base, i), t, c, fs, w)

def in.index.chk(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, AmlRead<H>>, +base: V.AmlValue, +i: Nat, t: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{AmlRead{+w2, v}}:
      in.index.fits(~H, ~io, in.size.of(v), base, i, t, c, fs, w2)

def in.index.go(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, ri: Result<&2, &2, E.AcpiError, W.W64>, +base: V.AmlValue, t: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match ri:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{x}:
      in.index.chk(~H, ~io, in.source(~H, ~io, base, w), base, W.W64.to_nat(x), t, c, fs, w)

def in.small.pick(ok: Bool, x: W.W64) -> Result<&2, &2, E.AcpiError, W.W64>:
  match ok:
    case True{}:
      Done{x}
    case False{}:
      Fail{E.AcpiAmlRange{}}

def in.small.chk(r: Result<&2, &2, E.AcpiError, W.W64>) -> Result<&2, &2, E.AcpiError, W.W64>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+x}:
      in.small.pick(U32.is_eq(W.W64.hi(x), 0), x)

# an Integer operand that must be small (an index or a count: below 2^32)
def in.small.int(+wide: Bool, v: V.AmlValue) -> Result<&2, &2, E.AcpiError, W.W64>:
  in.small.chk(V.AmlValue.to_int(wide, v))

def in.ap.index(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{+base, Con{i, Con{t, Nil{}}}}:
      in.index.go(~H, ~io, in.small.int(in.wide(H, w), i), base, t, c, fs, w)
    case _:
      in.bad(H, 136, c, fs, w)

# SizeOf, ObjectType

def in.size.give(-H: Data, r: Result<&2, &2, E.AcpiError, AmlRead<H>>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{AmlRead{w2, v}}:
      in.val.give(H, Result.map(&2, &2, E.AcpiError, Nat, V.AmlValue, n => V.AmlInt{W.W64.from_nat(n)}, in.size.of(v)), c, fs, w2)

def in.ap.size(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{v, Nil{}}:
      in.size.give(H, in.source(~H, ~io, v, w), c, fs, w)
    case _:
      in.bad(H, 135, c, fs, w)

def in.otype.obj(o: Maybe<&2, S.AmlObject>) -> U32:
  match o:
    case Some{x}:
      S.AmlObject.type(x)
    case None{}:
      0

def in.otype(-H: Data, v: V.AmlValue, +w: AmlWorld<H>) -> U32:
  match v:
    case V.AmlRef{V.AmlLName{+p}}:
      in.otype.obj(S.AmlNs.get(AmlWorld.ns(H, w), in.unalias(AmlWorld.ns(H, w), p)))
    case V.AmlRef{V.AmlLLocal{i}}:
      V.AmlValue.type(in.ctx.local(H, w, i))
    case V.AmlRef{V.AmlLArg{i}}:
      V.AmlValue.type(in.ctx.arg(H, w, i))
    case V.AmlRef{V.AmlLDebug{}}:
      16
    case _:
      V.AmlValue.type(v)

def in.ap.otype(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{v, Nil{}}:
      in.give(H, V.AmlInt{W.W64.from_u32(in.otype(H, v, w))}, c, fs, w)
    case _:
      in.bad(H, 142, c, fs, w)

def in.condref.put(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, V.AmlLoc>, +v: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{l}:
      in.then.give(H, in.put(~H, ~io, l, w, v), V.AmlInt{V.AmlInt.ones(in.wide(H, w))}, c, fs, w)

# CondRefOf (chapter 19): Ones and the reference in the Target if the object
# exists, Zero otherwise
def in.ap.condref(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{V.AmlRef{l}, Con{t, Nil{}}}:
      in.condref.put(~H, ~io, in.loc(t), V.AmlRef{l}, c, fs, w)
    case Con{x, Con{t, Nil{}}}:
      in.give(H, V.AmlInt{W.W64.zero()}, c, fs, w)
    case _:
      in.bad(H, 274, c, fs, w)

# Concatenate (chapter 19): by the first operand type

def in.concat(+wide: Bool, a: V.AmlValue, +b: V.AmlValue) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match a:
    case V.AmlInt{x}:
      Result.map(&2, &2, E.AcpiError, W.W64, V.AmlValue, y => V.AmlBuf{B.Octets.append(V.val.int.bytes(wide, x), V.val.int.bytes(wide, y))}, V.AmlValue.to_int(wide, b))
    case V.AmlStr{s}:
      Result.map(&2, &2, E.AcpiError, B.Octets, V.AmlValue, t => V.AmlStr{B.Octets.append(s, t)}, V.AmlValue.to_str(wide, b))
    case V.AmlBuf{s}:
      Result.map(&2, &2, E.AcpiError, B.Octets, V.AmlValue, t => V.AmlBuf{B.Octets.append(s, t)}, V.AmlValue.to_buf(wide, b))
    case _:
      Fail{E.AcpiAmlBadType{"Concatenate of a value that is not an integer, string or buffer"}}

def in.ap.concat(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{a, Con{b, Con{t, Nil{}}}}:
      in.store.give(~H, ~io, in.concat(in.wide(H, w), a, b), t, c, fs, w)
    case _:
      in.bad(H, 115, c, fs, w)

# ToInteger, ToBuffer (chapter 19)

def in.to_int(+wide: Bool, v: V.AmlValue) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match v:
    case V.AmlStr{s}:
      Done{V.AmlInt{V.AmlValue.parse_int(wide, B.Octets.to_list(s))}}
    case _:
      Result.map(&2, &2, E.AcpiError, W.W64, V.AmlValue, x => V.AmlInt{x}, V.AmlValue.to_int(wide, v))

def in.conv.v(+op: Nat, +wide: Bool, a: V.AmlValue) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match op:
    case 153n:
      in.to_int(wide, a)
    case _:
      Result.map(&2, &2, E.AcpiError, B.Octets, V.AmlValue, b => V.AmlBuf{b}, V.AmlValue.to_buf(wide, a))

def in.ap.conv(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +op: Nat, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{a, Con{t, Nil{}}}:
      in.store.give(~H, ~io, in.conv.v(op, in.wide(H, w), a), t, c, fs, w)
    case _:
      in.bad(H, U32.from_nat(op), c, fs, w)

# Notify (chapter 19; 5.6.6, device object notifications): recorded, for the caller

def in.notify(-H: Data, t: V.AmlValue, r: Result<&2, &2, E.AcpiError, W.W64>, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match t r:
    case V.AmlRef{V.AmlLName{p}} Done{x}:
      Done{in.note(H, w, AmlNote{p, x})}
    case _ Fail{e}:
      Fail{e}
    case _ Done{x}:
      Fail{E.AcpiAmlBadOperand{134}}

def in.ap.notify(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{t, Con{v, Nil{}}}:
      in.then.give(H, in.notify(H, t, V.AmlValue.to_int(in.wide(H, w), v), w), V.AmlUninit{}, c, fs, w)
    case _:
      in.bad(H, 134, c, fs, w)

# Sleep and Stall advance the clock Timer reads (by 10000 and 10 units of
# 100 ns per millisecond and microsecond); nothing waits

def in.sleep.go(-H: Data, r: Result<&2, &2, E.AcpiError, W.W64>, +per: U32, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{x}:
      in.give(H, V.AmlUninit{}, c, fs, in.tick(H, w, W.W64.mul(x, W.W64.from_u32(per))))

def in.ap.sleep(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +per: U32, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{v, Nil{}}:
      in.sleep.go(H, V.AmlValue.to_int(in.wide(H, w), v), per, c, fs, w)
    case _:
      in.bad(H, 290, c, fs, w)

# Fatal (chapter 19)
def in.ap.fatal(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{V.AmlInt{t}, Con{V.AmlInt{k}, Con{v, Nil{}}}}:
      AmlMachine{AmlMFail{E.AcpiAmlFatal{W.W64.lo(t), W.W64.lo(k), Result.default(&2, &2, E.AcpiError, W.W64, V.AmlValue.to_int(in.wide(H, w), v), W.W64.zero())}}, c, fs, w}
    case _:
      in.bad(H, 306, c, fs, w)

# Definitions: Name, OperationRegion, Alias, External, Mutex, Event and the
# CreateField family. A name already defined is AcpiAmlDuplicate.

def in.path(v: V.AmlValue) -> String:
  match v:
    case V.AmlRef{V.AmlLName{p}}:
      p
    case _:
      ""

def in.def.chk(-H: Data, dup: Bool, +p: String, o: S.AmlObject, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match dup:
    case True{}:
      AmlMachine{AmlMFail{E.AcpiAmlDuplicate{p}}, c, fs, w}
    case False{}:
      in.give(H, V.AmlUninit{}, c, fs, in.define(H, w, p, o))

def in.def.obj(-H: Data, +p: String, o: S.AmlObject, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  in.def.chk(H, S.AmlNs.has(AmlWorld.ns(H, w), p), p, o, c, fs, w)

def in.ap.name(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{n, Con{v, Nil{}}}:
      in.def.obj(H, in.path(n), S.AmlOData{v}, c, fs, w)
    case _:
      in.bad(H, 8, c, fs, w)

def in.region.v(ro: Result<&2, &2, E.AcpiError, W.W64>, rl: Result<&2, &2, E.AcpiError, W.W64>, +sp: U32, +scope: String) -> Result<&2, &2, E.AcpiError, S.AmlObject>:
  match ro rl:
    case Done{o} Done{l}:
      Done{S.AmlORegion{sp, o, l, scope}}
    case Fail{e} _:
      Fail{e}
    case Done{o} Fail{e}:
      Fail{e}

def in.def.res(-H: Data, +p: String, r: Result<&2, &2, E.AcpiError, S.AmlObject>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, fs, w}
    case Done{o}:
      in.def.obj(H, p, o, c, fs, w)

def in.ap.region(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{n, Con{V.AmlInt{sp}, Con{o, Con{l, Nil{}}}}}:
      +wide = in.wide(H, w)
      in.def.res(H, in.path(n), in.region.v(V.AmlValue.to_int(wide, o), V.AmlValue.to_int(wide, l), W.W64.lo(sp), in.scope(H, w)), c, fs, w)
    case _:
      in.bad(H, 384, c, fs, w)

def in.ap.alias(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{src, Con{dst, Nil{}}}:
      in.def.obj(H, in.path(dst), S.AmlOAlias{in.path(src)}, c, fs, w)
    case _:
      in.bad(H, 6, c, fs, w)

def in.ext.pick(-H: Data, has: Bool, +p: String, +k: U32, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match has:
    case True{}:
      in.give(H, V.AmlUninit{}, c, fs, w)
    case False{}:
      in.give(H, V.AmlUninit{}, c, fs, in.define(H, w, p, S.AmlOExternal{k}))

# External declares an object defined elsewhere; it defines nothing if the
# object exists
def in.ap.external(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{n, Con{V.AmlInt{k}, Con{a, Nil{}}}}:
      +p = in.path(n)
      in.ext.pick(H, S.AmlNs.has(AmlWorld.ns(H, w), p), p, W.W64.lo(k), c, fs, w)
    case _:
      in.bad(H, 21, c, fs, w)

def in.ap.mutex(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{n, Con{V.AmlInt{s}, Nil{}}}:
      in.def.obj(H, in.path(n), S.AmlOMutex{W.W64.lo(s)}, c, fs, w)
    case Con{n, Nil{}}:
      in.def.obj(H, in.path(n), S.AmlOEvent{}, c, fs, w)
    case _:
      in.bad(H, 257, c, fs, w)

# CreateBitField, CreateByteField, CreateWordField, CreateDWordField,
# CreateQWordField, CreateField: a buffer field of a buffer Name, Local or Arg

def in.cf.size(+op: Nat) -> Nat:
  match op:
    case 141n:
      1n
    case 140n:
      8n
    case 139n:
      16n
    case 138n:
      32n
    case _:
      64n

def in.cf.off(+op: Nat, +i: Nat) -> Nat:
  match op:
    case 141n:
      i
    case 275n:
      i
    case _:
      Nat.mul(i, 8n)

def in.cf.bits(+op: Nat, +n: Nat) -> Nat:
  match op:
    case 275n:
      n
    case _:
      in.cf.size(op)

def in.cf.mk(+op: Nat, src: V.AmlValue, ri: Result<&2, &2, E.AcpiError, W.W64>, rn: Result<&2, &2, E.AcpiError, W.W64>) -> Result<&2, &2, E.AcpiError, S.AmlObject>:
  match src ri rn:
    case V.AmlRef{l} Done{+i} Done{n}:
      Done{S.AmlOBufField{l, in.cf.off(op, W.W64.to_nat(i)), in.cf.bits(op, W.W64.to_nat(n))}}
    case _ Fail{e} _:
      Fail{e}
    case _ Done{i} Fail{e}:
      Fail{e}
    case _ Done{i} Done{n}:
      Fail{E.AcpiAmlUnsupported{"a buffer field of a buffer that has no name"}}

def in.ap.create(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +op: Nat, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{src, Con{i, Con{n, Nil{}}}}:
      +wide = in.wide(H, w)
      in.def.res(H, in.path(n), in.cf.mk(op, src, in.small.int(wide, i), Done{W.W64.zero()}), c, fs, w)
    case Con{src, Con{i, Con{k, Con{n, Nil{}}}}}:
      +wide = in.wide(H, w)
      in.def.res(H, in.path(n), in.cf.mk(op, src, in.small.int(wide, i), in.small.int(wide, k)), c, fs, w)
    case _:
      in.bad(H, U32.from_nat(op), c, fs, w)

# \_OSI (5.7.2): Ones if the operating system supports the feature named

def in.osi.has(xs: List<&2, String>, +s: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(String.eq(h, s), in.osi.has(t, s))

def in.opts.osi(o: AmlOptions) -> List<&2, String>:
  match o:
    case AmlOptions{osi, os, rev}:
      osi

def in.osi.v(+wide: Bool, +osi: List<&2, String>, r: Result<&2, &2, E.AcpiError, B.Octets>) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      Done{V.AmlInt{V.AmlInt.of_bool(wide, in.osi.has(osi, B.Octets.to_string(s)))}}

def in.ap.osi(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{v, Nil{}}:
      +wide = in.wide(H, w)
      in.val.give(H, in.osi.v(wide, in.opts.osi(in.opts(H, w)), V.AmlValue.to_str(wide, v)), c, fs, w)
    case _:
      in.bad(H, 0, c, fs, w)

# Method calls and returns

def in.mbody(o: Maybe<&2, S.AmlObject>) -> B.Octets:
  match o:
    case Some{S.AmlOMethod{n, f, b}}:
      b
    case _:
      B.Octets.empty()

def in.locals() -> List<&2, V.AmlValue>:
  [V.AmlUninit{}, V.AmlUninit{}, V.AmlUninit{}, V.AmlUninit{}, V.AmlUninit{}, V.AmlUninit{}, V.AmlUninit{}, V.AmlUninit{}]

# the method at p called with args: its body runs in its own scope, with
# fresh Locals; FCall remembers where to come back
def in.call(-H: Data, +p: String, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  +body = B.Octets.to_list(in.mbody(S.AmlNs.get(AmlWorld.ns(H, w), p)))
  AmlMachine{AmlMExec{}, AmlCur{body, B.len.fast(body)}, Con{AmlFCall{AmlWorld.ctx(H, w), c}, fs}, in.with_ctx(H, w, AmlCtx{p, args, in.locals(), Nil{}})}

def in.drop.temps(ts: List<&2, String>, ns: S.AmlNs) -> S.AmlNs:
  match ts:
    case Nil{}:
      ns
    case Con{t, rest}:
      in.drop.temps(rest, S.AmlNs.remove(ns, t))

def in.temps(c: AmlCtx) -> List<&2, String>:
  match c:
    case AmlCtx{s, a, l, t}:
      t

# back from a method: its names removed, the caller context restored
def in.back(-H: Data, w: AmlWorld<H>, saved: AmlCtx) -> AmlWorld<H>:
  match w:
    case AmlWorld{c, n, h, e}:
      AmlWorld{saved, in.drop.temps(in.temps(c), n), h, e}

# Return: frames dropped to the method call (or the bottom)
def in.unwind.ret(-H: Data, fs: List<&2, AmlFrame>, v: V.AmlValue, w: AmlWorld<H>) -> AmlMachine<H>:
  match fs:
    case Nil{}:
      AmlMachine{AmlMDone{v}, in.no.cur(), Nil{}, w}
    case Con{AmlFCall{saved, back}, rest}:
      AmlMachine{AmlMGive{v}, back, rest, in.back(H, w, saved)}
    case Con{AmlFTop{}, rest}:
      AmlMachine{AmlMDone{v}, in.no.cur(), [AmlFTop{}], w}
    case Con{f, rest}:
      in.unwind.ret(H, rest, v, w)

# Break: frames dropped to the While, then on after it
def in.unwind.brk(-H: Data, fs: List<&2, AmlFrame>, w: AmlWorld<H>) -> AmlMachine<H>:
  match fs:
    case Nil{}:
      AmlMachine{AmlMFail{E.AcpiAmlBadControl{}}, in.no.cur(), Nil{}, w}
    case Con{AmlFWhile{s, after, b}, rest}:
      AmlMachine{AmlMExec{}, after, rest, w}
    case Con{AmlFCall{saved, back}, rest}:
      AmlMachine{AmlMFail{E.AcpiAmlBadControl{}}, back, rest, w}
    case Con{AmlFTop{}, rest}:
      AmlMachine{AmlMFail{E.AcpiAmlBadControl{}}, in.no.cur(), rest, w}
    case Con{f, rest}:
      in.unwind.brk(H, rest, w)

# Continue: frames dropped to the While, whose predicate is read again
def in.unwind.cont(-H: Data, fs: List<&2, AmlFrame>, w: AmlWorld<H>) -> AmlMachine<H>:
  match fs:
    case Nil{}:
      AmlMachine{AmlMFail{E.AcpiAmlBadControl{}}, in.no.cur(), Nil{}, w}
    case Con{AmlFWhile{+s, after, b}, rest}:
      AmlMachine{AmlMEval{AmlKTerm{}}, s, Con{AmlFWhile{s, after, False{}}, rest}, w}
    case Con{AmlFCall{saved, back}, rest}:
      AmlMachine{AmlMFail{E.AcpiAmlBadControl{}}, back, rest, w}
    case Con{AmlFTop{}, rest}:
      AmlMachine{AmlMFail{E.AcpiAmlBadControl{}}, in.no.cur(), rest, w}
    case Con{f, rest}:
      in.unwind.cont(H, rest, w)

def in.ap.ret(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match args:
    case Con{v, Nil{}}:
      in.unwind.ret(H, fs, v, w)
    case _:
      in.bad(H, 164, c, fs, w)

# Operators: what each opcode takes (an extended opcode 0x5B xx is 256 + xx)

def in.kT() -> AmlArgK:
  AmlKTerm{}

def in.kG() -> AmlArgK:
  AmlKTarget{}

def in.kS() -> AmlArgK:
  AmlKBase{}

def in.kN() -> AmlArgK:
  AmlKName{}

def in.kY() -> AmlArgK:
  AmlKByte{}

def in.tt.g() -> List<&2, AmlArgK>:
  [in.kT(), in.kT(), in.kG()]

def in.t.g() -> List<&2, AmlArgK>:
  [in.kT(), in.kG()]

def in.kinds(+op: Nat) -> Maybe<&2, List<&2, AmlArgK>>:
  match op:
    case 6n:
      Some{[in.kG(), in.kN()]}
    case 8n:
      Some{[in.kN(), in.kT()]}
    case 21n:
      Some{[in.kN(), in.kY(), in.kY()]}
    case 112n:
      Some{in.t.g()}
    case 113n:
      Some{[in.kG()]}
    case 114n:
      Some{in.tt.g()}
    case 115n:
      Some{in.tt.g()}
    case 116n:
      Some{in.tt.g()}
    case 117n:
      Some{[in.kG()]}
    case 118n:
      Some{[in.kG()]}
    case 119n:
      Some{in.tt.g()}
    case 120n:
      Some{[in.kT(), in.kT(), in.kG(), in.kG()]}
    case 121n:
      Some{in.tt.g()}
    case 122n:
      Some{in.tt.g()}
    case 123n:
      Some{in.tt.g()}
    case 124n:
      Some{in.tt.g()}
    case 125n:
      Some{in.tt.g()}
    case 126n:
      Some{in.tt.g()}
    case 127n:
      Some{in.tt.g()}
    case 128n:
      Some{in.t.g()}
    case 129n:
      Some{in.t.g()}
    case 130n:
      Some{in.t.g()}
    case 131n:
      Some{[in.kT()]}
    case 133n:
      Some{in.tt.g()}
    case 134n:
      Some{[in.kG(), in.kT()]}
    case 135n:
      Some{[in.kS()]}
    case 136n:
      Some{[in.kS(), in.kT(), in.kG()]}
    case 138n:
      Some{[in.kS(), in.kT(), in.kN()]}
    case 139n:
      Some{[in.kS(), in.kT(), in.kN()]}
    case 140n:
      Some{[in.kS(), in.kT(), in.kN()]}
    case 141n:
      Some{[in.kS(), in.kT(), in.kN()]}
    case 142n:
      Some{[in.kS()]}
    case 143n:
      Some{[in.kS(), in.kT(), in.kN()]}
    case 144n:
      Some{[in.kT(), in.kT()]}
    case 145n:
      Some{[in.kT(), in.kT()]}
    case 146n:
      Some{[in.kT()]}
    case 147n:
      Some{[in.kT(), in.kT()]}
    case 148n:
      Some{[in.kT(), in.kT()]}
    case 149n:
      Some{[in.kT(), in.kT()]}
    case 150n:
      Some{in.t.g()}
    case 153n:
      Some{in.t.g()}
    case 157n:
      Some{in.t.g()}
    case 164n:
      Some{[in.kT()]}
    case 257n:
      Some{[in.kN(), in.kY()]}
    case 258n:
      Some{[in.kN()]}
    case 274n:
      Some{[AmlKCond{}, in.kG()]}
    case 275n:
      Some{[in.kS(), in.kT(), in.kT(), in.kN()]}
    case 289n:
      Some{[in.kT()]}
    case 290n:
      Some{[in.kT()]}
    case 291n:
      Some{[in.kG(), AmlKWord{}]}
    case 292n:
      Some{[in.kG()]}
    case 293n:
      Some{[in.kG(), in.kT()]}
    case 294n:
      Some{[in.kG()]}
    case 295n:
      Some{[in.kG()]}
    case 304n:
      Some{Nil{}}
    case 306n:
      Some{[in.kY(), AmlKDWord{}, in.kT()]}
    case 307n:
      Some{Nil{}}
    case 384n:
      Some{[in.kN(), in.kY(), in.kT(), in.kT()]}
    case _:
      None{}

# the operators that are statements: refused where a value is wanted
def in.is_stmt(+op: Nat) -> Bool:
  match op:
    case 6n:
      True{}
    case 8n:
      True{}
    case 21n:
      True{}
    case 134n:
      True{}
    case 138n:
      True{}
    case 139n:
      True{}
    case 140n:
      True{}
    case 141n:
      True{}
    case 143n:
      True{}
    case 164n:
      True{}
    case 257n:
      True{}
    case 258n:
      True{}
    case 275n:
      True{}
    case 289n:
      True{}
    case 290n:
      True{}
    case 292n:
      True{}
    case 294n:
      True{}
    case 295n:
      True{}
    case 306n:
      True{}
    case 384n:
      True{}
    case _:
      False{}

def in.refof(args: List<&2, V.AmlValue>) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match args:
    case Con{t, Nil{}}:
      Done{t}
    case _:
      Fail{E.AcpiAmlBadOperand{113}}

def in.apply.code(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +code: Nat, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match code:
    case 6n:
      in.ap.alias(~H, ~io, args, c, fs, w)
    case 8n:
      in.ap.name(~H, ~io, args, c, fs, w)
    case 21n:
      in.ap.external(~H, ~io, args, c, fs, w)
    case 112n:
      in.ap.store(~H, ~io, args, c, fs, w)
    case 113n:
      in.val.give(H, in.refof(args), c, fs, w)
    case 114n:
      in.ap.int2(~H, ~io, 114n, args, c, fs, w)
    case 115n:
      in.ap.concat(~H, ~io, args, c, fs, w)
    case 116n:
      in.ap.int2(~H, ~io, 116n, args, c, fs, w)
    case 117n:
      in.ap.incdec(~H, ~io, True{}, args, c, fs, w)
    case 118n:
      in.ap.incdec(~H, ~io, False{}, args, c, fs, w)
    case 119n:
      in.ap.int2(~H, ~io, 119n, args, c, fs, w)
    case 120n:
      in.ap.div(~H, ~io, args, c, fs, w)
    case 121n:
      in.ap.int2(~H, ~io, 121n, args, c, fs, w)
    case 122n:
      in.ap.int2(~H, ~io, 122n, args, c, fs, w)
    case 123n:
      in.ap.int2(~H, ~io, 123n, args, c, fs, w)
    case 124n:
      in.ap.int2(~H, ~io, 124n, args, c, fs, w)
    case 125n:
      in.ap.int2(~H, ~io, 125n, args, c, fs, w)
    case 126n:
      in.ap.int2(~H, ~io, 126n, args, c, fs, w)
    case 127n:
      in.ap.int2(~H, ~io, 127n, args, c, fs, w)
    case 128n:
      in.ap.int1(~H, ~io, 128n, args, c, fs, w)
    case 129n:
      in.ap.int1(~H, ~io, 129n, args, c, fs, w)
    case 130n:
      in.ap.int1(~H, ~io, 130n, args, c, fs, w)
    case 131n:
      in.ap.deref(~H, ~io, args, c, fs, w)
    case 133n:
      in.ap.int2(~H, ~io, 133n, args, c, fs, w)
    case 134n:
      in.ap.notify(~H, ~io, args, c, fs, w)
    case 135n:
      in.ap.size(~H, ~io, args, c, fs, w)
    case 136n:
      in.ap.index(~H, ~io, args, c, fs, w)
    case 138n:
      in.ap.create(~H, ~io, 138n, args, c, fs, w)
    case 139n:
      in.ap.create(~H, ~io, 139n, args, c, fs, w)
    case 140n:
      in.ap.create(~H, ~io, 140n, args, c, fs, w)
    case 141n:
      in.ap.create(~H, ~io, 141n, args, c, fs, w)
    case 142n:
      in.ap.otype(~H, ~io, args, c, fs, w)
    case 143n:
      in.ap.create(~H, ~io, 143n, args, c, fs, w)
    case 144n:
      in.ap.logic(~H, ~io, 144n, args, c, fs, w)
    case 145n:
      in.ap.logic(~H, ~io, 145n, args, c, fs, w)
    case 146n:
      in.ap.logic(~H, ~io, 146n, args, c, fs, w)
    case 147n:
      in.ap.logic(~H, ~io, 147n, args, c, fs, w)
    case 148n:
      in.ap.logic(~H, ~io, 148n, args, c, fs, w)
    case 149n:
      in.ap.logic(~H, ~io, 149n, args, c, fs, w)
    case 150n:
      in.ap.conv(~H, ~io, 150n, args, c, fs, w)
    case 153n:
      in.ap.conv(~H, ~io, 153n, args, c, fs, w)
    case 157n:
      in.ap.copy(~H, ~io, args, c, fs, w)
    case 164n:
      in.ap.ret(~H, ~io, args, c, fs, w)
    case 257n:
      in.ap.mutex(~H, ~io, args, c, fs, w)
    case 258n:
      in.ap.mutex(~H, ~io, args, c, fs, w)
    case 274n:
      in.ap.condref(~H, ~io, args, c, fs, w)
    case 275n:
      in.ap.create(~H, ~io, 275n, args, c, fs, w)
    case 289n:
      in.ap.sleep(~H, ~io, 10, args, c, fs, w)
    case 290n:
      in.ap.sleep(~H, ~io, 10000, args, c, fs, w)
    case 291n:
      in.give(H, V.AmlInt{W.W64.zero()}, c, fs, w)
    case 293n:
      in.give(H, V.AmlInt{W.W64.zero()}, c, fs, w)
    case 304n:
      in.give(H, V.AmlInt{W.W64.from_u32(2)}, c, fs, w)
    case 306n:
      in.ap.fatal(~H, ~io, args, c, fs, w)
    case 307n:
      in.give(H, V.AmlInt{in.clock(H, w)}, c, fs, w)
    case 384n:
      in.ap.region(~H, ~io, args, c, fs, w)
    case _:
      AmlMachine{AmlMFail{E.AcpiAmlBadOpcode{U32.from_nat(code)}}, c, fs, w}

def in.apply(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, op: AmlOp, args: List<&2, V.AmlValue>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match op:
    case AmlOpCode{code}:
      in.apply.code(~H, ~io, U32.to_nat(code), args, c, fs, w)
    case AmlOpCall{p, n}:
      in.call(H, p, args, c, fs, w)
    case AmlOpOsi{}:
      in.ap.osi(~H, ~io, args, c, fs, w)

# an operator reached: its operands are read next (if it has any)
def in.start(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, op: AmlOp, ks: List<&2, AmlArgK>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match ks:
    case Nil{}:
      in.apply(~H, ~io, op, Nil{}, c, fs, w)
    case Con{+k, rest}:
      AmlMachine{AmlMEval{k}, c, Con{AmlFArgs{op, Nil{}, Con{k, rest}}, fs}, w}

def in.times(n: Nat, +k: AmlArgK) -> List<&2, AmlArgK>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{k, in.times(p, k)}

def in.invoke(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +p: String, +nargs: Nat, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  in.start(~H, ~io, AmlOpCall{p, nargs}, in.times(nargs, AmlKTerm{}), c, fs, w)

# Names as operands

def in.name.val(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, o: Maybe<&2, S.AmlObject>, +p: String, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match o:
    case Some{S.AmlOMethod{n, f, b}}:
      in.invoke(~H, ~io, p, n, c, fs, w)
    case Some{S.AmlOBuiltin{i}}:
      in.start(~H, ~io, AmlOpOsi{}, [AmlKTerm{}], c, fs, w)
    case _:
      in.read.give(H, in.read_obj(~H, ~io, w, p, o), c, fs, w)

def in.name.base(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, o: Maybe<&2, S.AmlObject>, +p: String, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match o:
    case Some{S.AmlOMethod{n, f, b}}:
      in.invoke(~H, ~io, p, n, c, fs, w)
    case _:
      in.give(H, V.AmlRef{V.AmlLName{p}}, c, fs, w)

def in.name.res(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, k: AmlArgK, m: Maybe<&2, String>, +n: N.AmlName, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match k m:
    case AmlKTarget{} Some{p}:
      in.give(H, V.AmlRef{V.AmlLName{p}}, c, fs, w)
    case AmlKCond{} Some{p}:
      in.give(H, V.AmlRef{V.AmlLName{p}}, c, fs, w)
    case AmlKCond{} None{}:
      in.give(H, V.AmlUninit{}, c, fs, w)
    case AmlKElem{} Some{p}:
      in.give(H, V.AmlRef{V.AmlLName{p}}, c, fs, w)
    case AmlKElem{} None{}:
      in.give(H, V.AmlRef{V.AmlLName{S.AmlPath.of_name(in.scope(H, w), n)}}, c, fs, w)
    case AmlKBase{} Some{+p}:
      +q = in.unalias(AmlWorld.ns(H, w), p)
      in.name.base(~H, ~io, S.AmlNs.get(AmlWorld.ns(H, w), q), q, c, fs, w)
    case _ Some{+p}:
      +q = in.unalias(AmlWorld.ns(H, w), p)
      in.name.val(~H, ~io, S.AmlNs.get(AmlWorld.ns(H, w), q), q, c, fs, w)
    case _ None{}:
      AmlMachine{AmlMFail{E.AcpiAmlUndefined{N.AmlName.show(n)}}, c, fs, w}

def in.name.go(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, AmlNameC>, k: AmlArgK, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlNameC{+n, c}}:
      match k:
        case AmlKName{}:
          in.give(H, V.AmlRef{V.AmlLName{S.AmlPath.of_name(in.scope(H, w), n)}}, c, fs, w)
        case _:
          in.name.res(~H, ~io, k, S.AmlNs.resolve(AmlWorld.ns(H, w), in.scope(H, w), n), n, c, fs, w)

# Data objects

def in.imm.give(-H: Data, +wide: Bool, r: Result<&2, &2, E.AcpiError, AmlImm>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlImm{v, c}}:
      AmlMachine{AmlMGive{V.AmlInt{V.AmlInt.fit(wide, v)}}, c, fs, w}

type AmlStrL is Data:
  AmlStrL{bytes: List<&2, U32>, size: Nat}

def in.str.z(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{+h, t}:
      U32.is_eq(h, 0)
    case Nil{}:
      False{}

def in.str.go(n: Nat, xs: List<&2, U32>, z: Bool, acc: List<&2, U32>, +k: Nat) -> Maybe<&2, AmlStrL>:
  match n:
    case 0n:
      None{}
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case Con{h, +t}:
          match z:
            case True{}:
              Some{AmlStrL{List.reverse(&2, U32, acc), Nat.add(k, 1n)}}
            case False{}:
              in.str.go(p, t, in.str.z(t), Con{h, acc}, Nat.add(k, 1n))

def in.str.give(-H: Data, m: Maybe<&2, AmlStrL>, +c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match m:
    case None{}:
      AmlMachine{AmlMFail{E.AcpiAmlTruncated{}}, c, fs, w}
    case Some{AmlStrL{bs, +n}}:
      AmlMachine{AmlMGive{V.AmlStr{B.Octets.of_list(bs)}}, cur.skip(n, c), fs, w}

# a String: its bytes up to the NUL
def in.string(-H: Data, +c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match c:
    case AmlCur{+code, +lim}:
      in.str.give(H, in.str.go(lim, code, in.str.z(code), Nil{}, 0n), AmlCur{code, lim}, fs, w)

def in.buffer(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      AmlMachine{AmlMEval{AmlKTerm{}}, body, Con{AmlFBuffer{after}, fs}, w}

def in.pad(n: Nat, xs: List<&2, V.AmlValue>) -> List<&2, V.AmlValue>:
  match n xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      Con{V.AmlUninit{}, in.pad(p, Nil{})}
    case 1n+p Con{h, t}:
      Con{h, in.pad(p, t)}

def in.pkg.first(-H: Data, empty: Bool, +n: Nat, body: AmlCur, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match empty:
    case True{}:
      AmlMachine{AmlMGive{V.AmlPkg{in.pad(n, Nil{})}}, after, fs, w}
    case False{}:
      AmlMachine{AmlMEval{AmlKElem{}}, body, Con{AmlFPkg{n, Nil{}, after}, fs}, w}

def in.pkg.start(-H: Data, r: Result<&2, &2, E.AcpiError, AmlImm>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlImm{n, +body}}:
      in.pkg.first(H, cur.at_end(body), W.W64.to_nat(n), body, after, fs, w)

def in.package(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      in.pkg.start(H, cur.imm(1n, body), after, fs, w)

def in.varpackage(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      AmlMachine{AmlMEval{AmlKTerm{}}, body, Con{AmlFVarPkg{after}, fs}, w}

def in.zero(-H: Data, k: AmlArgK, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match k:
    case AmlKTarget{}:
      in.give(H, V.AmlRef{V.AmlLNone{}}, c, fs, w)
    case AmlKCond{}:
      in.give(H, V.AmlRef{V.AmlLNone{}}, c, fs, w)
    case _:
      in.give(H, V.AmlInt{W.W64.zero()}, c, fs, w)

def in.lvar(-H: Data, k: AmlArgK, l: V.AmlLoc, v: V.AmlValue, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match k:
    case AmlKTarget{}:
      in.give(H, V.AmlRef{l}, c, fs, w)
    case AmlKBase{}:
      in.give(H, V.AmlRef{l}, c, fs, w)
    case AmlKCond{}:
      in.give(H, V.AmlRef{l}, c, fs, w)
    case _:
      in.give(H, v, c, fs, w)

# Statements that hold term lists

def in.enter(-H: Data, +path: String, body: AmlCur, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  AmlMachine{AmlMExec{}, body, Con{AmlFSeq{after, in.scope(H, w)}, fs}, in.with_scope(H, w, path)}

def in.scope.target(m: Maybe<&2, String>, +scope: String, n: N.AmlName) -> String:
  match m:
    case Some{p}:
      p
    case None{}:
      S.AmlPath.of_name(scope, n)

def in.scope.k(-H: Data, r: Result<&2, &2, E.AcpiError, AmlNameC>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlNameC{+n, body}}:
      +p = in.scope.target(S.AmlNs.resolve(AmlWorld.ns(H, w), in.scope(H, w), n), in.scope(H, w), n)
      in.enter(H, p, body, after, fs, w)

# Scope (chapter 19): the term list runs in the named scope
def in.scope.op(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      in.scope.k(H, cur.name(body), after, fs, w)

def in.method.flags(-H: Data, +p: String, r: Result<&2, &2, E.AcpiError, AmlB>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlB{+f, +c}}:
      in.def.chk(H, S.AmlNs.has(AmlWorld.ns(H, w), p), p, S.AmlOMethod{U32.to_nat(U32.and(f, 7)), f, cur.take(cur.len(c), c)}, after, fs, w)

def in.method.k(-H: Data, rn: Result<&2, &2, E.AcpiError, AmlNameC>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match rn:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlNameC{n, c}}:
      in.method.flags(H, S.AmlPath.of_name(in.scope(H, w), n), cur.byte(c), after, fs, w)

# Method (chapter 19): defined, its body kept for when it is called
def in.method.op(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      in.method.k(H, cur.name(body), after, fs, w)

def in.dev.go(-H: Data, dup: Bool, +p: String, +kind: U32, body: AmlCur, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match dup:
    case True{}:
      AmlMachine{AmlMFail{E.AcpiAmlDuplicate{p}}, body, fs, w}
    case False{}:
      in.enter(H, p, body, after, fs, in.define(H, w, p, S.AmlOScope{kind}))

def in.dev.fits(-H: Data, ok: Bool, +p: String, +kind: U32, body: AmlCur, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match ok:
    case False{}:
      AmlMachine{AmlMFail{E.AcpiAmlTruncated{}}, body, fs, w}
    case True{}:
      in.dev.go(H, S.AmlNs.has(AmlWorld.ns(H, w), p), p, kind, body, after, fs, w)

def in.dev.k(-H: Data, +kind: U32, +extra: Nat, rn: Result<&2, &2, E.AcpiError, AmlNameC>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match rn:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlNameC{n, +c}}:
      +p = S.AmlPath.of_name(in.scope(H, w), n)
      in.dev.fits(H, Nat.is_le(extra, cur.len(c)), p, kind, cur.skip(extra, c), after, fs, w)

# Device, Processor, PowerResource, ThermalZone (chapter 19): an object whose term list runs in its own scope;
# Processor's ID and block and PowerResource's level and order are skipped
def in.dev.op(-H: Data, +kind: U32, +extra: Nat, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      in.dev.k(H, kind, extra, cur.name(body), after, fs, w)

def in.if.op(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      AmlMachine{AmlMEval{AmlKTerm{}}, body, Con{AmlFIf{after}, fs}, w}

def in.while.op(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{+body, after}}:
      AmlMachine{AmlMEval{AmlKTerm{}}, body, Con{AmlFWhile{body, after, False{}}, fs}, w}

def in.skip.op(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      AmlMachine{AmlMExec{}, after, fs, w}

# Field and IndexField (chapter 19): the field list is read in one
# step, a field unit defined for each NamedField

# what the field units are of
type AmlFk is Data:
  AmlFkRegion{region: String}
  AmlFkIndex{index: String, data: String}

type AmlFlSt<-H: Data> is Data:
  AmlFlSt{c: AmlCur, off: Nat, flags: U32, w: AmlWorld<H>}

type AmlFlNext<-H: Data> is Data:
  AmlFlMore{st: AmlFlSt<H>}
  AmlFlEnd{w: AmlWorld<H>}

def fl.unit(k: AmlFk, +off: Nat, +bits: Nat, +flags: U32) -> S.AmlObject:
  match k:
    case AmlFkRegion{r}:
      S.AmlOField{r, off, bits, flags}
    case AmlFkIndex{i, d}:
      S.AmlOIndexField{i, d, off, bits, flags}

def fl.bits.fit(ok: Bool, v: U32, c: AmlCur) -> Result<&2, &2, E.AcpiError, AmlImm>:
  match ok:
    case True{}:
      Done{AmlImm{W.W64.from_u32(v), c}}
    case False{}:
      Fail{E.AcpiAmlTruncated{}}

def fl.bits.go(r: Result<&2, &2, E.AcpiError, K.AmlPkgL>, +lim: Nat) -> Result<&2, &2, E.AcpiError, AmlImm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{K.AmlPkgL{v, +size, rest}}:
      fl.bits.fit(Nat.is_le(size, lim), v, AmlCur{rest, Nat.sub(lim, size)})

# a PkgLength used as a number of bits
def fl.bits(c: AmlCur) -> Result<&2, &2, E.AcpiError, AmlImm>:
  match c:
    case AmlCur{+code, +lim}:
      fl.bits.go(K.pk.dec(code), lim)

def fl.reserved(-H: Data, r: Result<&2, &2, E.AcpiError, AmlImm>, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlImm{n, c}}:
      Done{AmlFlMore{AmlFlSt{c, Nat.add(off, W.W64.to_nat(n)), flags, w}}}

def fl.access.fit(-H: Data, ok: Bool, c: AmlCur, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match ok:
    case True{}:
      Done{AmlFlMore{AmlFlSt{c, off, flags, w}}}
    case False{}:
      Fail{E.AcpiAmlTruncated{}}

def fl.access(-H: Data, +skip: Nat, r: Result<&2, &2, E.AcpiError, AmlB>, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlB{t, +c}}:
      fl.access.fit(H, Nat.is_le(skip, cur.len(c)), cur.skip(skip, c), off, U32.or(U32.and(flags, 4294967280), U32.and(t, 15)), w)

def fl.named.def(-H: Data, dup: Bool, +p: String, o: S.AmlObject, c: AmlCur, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match dup:
    case True{}:
      Fail{E.AcpiAmlDuplicate{p}}
    case False{}:
      Done{AmlFlMore{AmlFlSt{c, off, flags, in.define(H, w, p, o)}}}

def fl.named.k(-H: Data, k: AmlFk, +seg: String, r: Result<&2, &2, E.AcpiError, AmlImm>, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlImm{n, c}}:
      +bits = W.W64.to_nat(n)
      +p = S.AmlPath.child(in.scope(H, w), seg)
      fl.named.def(H, S.AmlNs.has(AmlWorld.ns(H, w), p), p, fl.unit(k, off, bits, flags), c, Nat.add(off, bits), flags, w)

def fl.named.chk(-H: Data, k: AmlFk, ok: Bool, +seg: String, +c: AmlCur, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match ok:
    case False{}:
      Fail{E.AcpiAmlBadName{}}
    case True{}:
      fl.named.k(H, k, seg, fl.bits(c), off, flags, w)

def fl.named.seg(-H: Data, k: AmlFk, ok: Bool, +b: U32, +c: AmlCur, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match ok:
    case False{}:
      Fail{E.AcpiAmlTruncated{}}
    case True{}:
      +seg = B.Octets.append(B.Octets.of_list([b]), cur.take(3n, c))
      fl.named.chk(H, k, N.AmlName.seg_ok(seg), B.Octets.to_string(seg), cur.skip(3n, c), off, flags, w)

def fl.named(-H: Data, k: AmlFk, +b: U32, +c: AmlCur, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  fl.named.seg(H, k, Nat.is_le(3n, cur.len(c)), b, c, off, flags, w)

def fl.elem(-H: Data, k: AmlFk, +n: Nat, +b: U32, +c: AmlCur, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match n:
    case 0n:
      fl.reserved(H, fl.bits(c), off, flags, w)
    case 1n:
      fl.access(H, 1n, cur.byte(c), off, flags, w)
    case 2n:
      Fail{E.AcpiAmlUnsupported{"ConnectField"}}
    case 3n:
      fl.access(H, 2n, cur.byte(c), off, flags, w)
    case _:
      fl.named(H, k, b, c, off, flags, w)

def fl.byte(-H: Data, k: AmlFk, r: Result<&2, &2, E.AcpiError, AmlB>, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlB{+b, c}}:
      fl.elem(H, k, U32.to_nat(b), b, c, off, flags, w)

def fl.step.go(-H: Data, k: AmlFk, end: Bool, +c: AmlCur, +off: Nat, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match end:
    case True{}:
      Done{AmlFlEnd{w}}
    case False{}:
      fl.byte(H, k, cur.byte(c), off, flags, w)

def fl.step(-H: Data, k: AmlFk, st: AmlFlSt<H>) -> Result<&2, &2, E.AcpiError, AmlFlNext<H>>:
  match st:
    case AmlFlSt{+c, off, flags, w}:
      fl.step.go(H, k, cur.at_end(c), c, off, flags, w)

# every element takes at least two bytes, so the list length is enough fuel
def fl.loop(-H: Data, fuel: Nat, +k: AmlFk, r: Result<&2, &2, E.AcpiError, AmlFlNext<H>>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  match fuel:
    case 0n:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{AmlFlEnd{w}}:
          Done{w}
        case Done{AmlFlMore{st}}:
          Fail{E.AcpiAmlTruncated{}}
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{AmlFlEnd{w}}:
          Done{w}
        case Done{AmlFlMore{st}}:
          fl.loop(H, p, k, fl.step(H, k, st))

def fl.run(-H: Data, +k: AmlFk, +c: AmlCur, +flags: U32, +w: AmlWorld<H>) -> Result<&2, &2, E.AcpiError, AmlWorld<H>>:
  fl.loop(H, cur.len(c), k, Done{AmlFlMore{AmlFlSt{c, 0n, flags, w}}})

def fl.done(-H: Data, r: Result<&2, &2, E.AcpiError, AmlWorld<H>>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, after, fs, w}
    case Done{w2}:
      AmlMachine{AmlMExec{}, after, fs, w2}

def fl.flags(-H: Data, +k: AmlFk, r: Result<&2, &2, E.AcpiError, AmlB>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, after, fs, w}
    case Done{AmlB{f, c}}:
      fl.done(H, fl.run(H, k, c, f, w), after, fs, w)

def fl.path(-H: Data, +n: N.AmlName, +w: AmlWorld<H>) -> String:
  in.scope.target(S.AmlNs.resolve(AmlWorld.ns(H, w), in.scope(H, w), n), in.scope(H, w), n)

def fl.region.k(-H: Data, rn: Result<&2, &2, E.AcpiError, AmlNameC>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match rn:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, after, fs, w}
    case Done{AmlNameC{n, c}}:
      fl.flags(H, AmlFkRegion{fl.path(H, n, w)}, cur.byte(c), after, fs, w)

def fl.field.op(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      fl.region.k(H, cur.name(body), after, fs, w)

def fl.index.d(-H: Data, +i: String, rn: Result<&2, &2, E.AcpiError, AmlNameC>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match rn:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, after, fs, w}
    case Done{AmlNameC{n, c}}:
      fl.flags(H, AmlFkIndex{i, fl.path(H, n, w)}, cur.byte(c), after, fs, w)

def fl.index.k(-H: Data, rn: Result<&2, &2, E.AcpiError, AmlNameC>, after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match rn:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, after, fs, w}
    case Done{AmlNameC{n, c}}:
      fl.index.d(H, fl.path(H, n, w), cur.name(c), after, fs, w)

def fl.indexfield.op(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      fl.index.k(H, cur.name(body), after, fs, w)

# Terms: the dispatch on the first byte

def in.unsupported(-H: Data, +what: String, c: AmlCur, fs: List<&2, AmlFrame>, w: AmlWorld<H>) -> AmlMachine<H>:
  AmlMachine{AmlMFail{E.AcpiAmlUnsupported{what}}, c, fs, w}

def in.expr.ok(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, ok: Bool, +op: Nat, +code: U32, ks: List<&2, AmlArgK>, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match ok:
    case True{}:
      in.start(~H, ~io, AmlOpCode{U32.from_nat(op)}, ks, c, fs, w)
    case False{}:
      AmlMachine{AmlMFail{E.AcpiAmlBadOperand{code}}, c, fs, w}

def in.unknown.name(+n: Nat) -> String:
  match n:
    case 132n:
      "ConcatenateResTemplate"
    case 137n:
      "Match"
    case 151n:
      "ToDecimalString"
    case 152n:
      "ToHexString"
    case 156n:
      "ToString"
    case 158n:
      "Mid"
    case _:
      ""

def in.unknown.go(-H: Data, bad: Bool, what: String, code: U32, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match bad:
    case True{}:
      AmlMachine{AmlMFail{E.AcpiAmlBadOpcode{code}}, c, fs, w}
    case False{}:
      AmlMachine{AmlMFail{E.AcpiAmlUnsupported{what}}, c, fs, w}

def in.unknown.pick(-H: Data, +what: String, +code: U32, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  in.unknown.go(H, String.is_empty(what), what, code, c, fs, w)

# an opcode with no operator here: AcpiAmlUnsupported if ACPI defines it
# (named in README.md), AcpiAmlBadOpcode otherwise
def in.unknown(-H: Data, +n: Nat, +code: U32, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  in.unknown.pick(H, in.unknown.name(n), code, c, fs, w)

def in.expr(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +n: Nat, +code: U32, m: Maybe<&2, List<&2, AmlArgK>>, exec: Bool, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match m:
    case None{}:
      in.unknown(H, n, code, c, fs, w)
    case Some{ks}:
      in.expr.ok(~H, ~io, Bool.or(exec, Bool.not(in.is_stmt(n))), n, code, ks, c, fs, w)

def in.stmt.ext(-H: Data, +x: Nat, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match x:
    case 129n:
      fl.field.op(H, cur.pkg(c), fs, w)
    case 130n:
      in.dev.op(H, 6, 0n, cur.pkg(c), fs, w)
    case 131n:
      in.dev.op(H, 12, 6n, cur.pkg(c), fs, w)
    case 132n:
      in.dev.op(H, 11, 3n, cur.pkg(c), fs, w)
    case 133n:
      in.dev.op(H, 13, 0n, cur.pkg(c), fs, w)
    case _:
      fl.indexfield.op(H, cur.pkg(c), fs, w)

def in.stmt.ext.chk(-H: Data, exec: Bool, +x: Nat, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match exec:
    case True{}:
      in.stmt.ext(H, x, c, fs, w)
    case False{}:
      AmlMachine{AmlMFail{E.AcpiAmlBadOperand{U32.add(23296, U32.from_nat(x))}}, c, fs, w}

# an extended opcode (0x5B, then this byte)
def in.term.ext(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, k: AmlArgK, +x: Nat, +e: U32, +exec: Bool, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match x:
    case 49n:
      in.lvar(H, k, V.AmlLDebug{}, V.AmlUninit{}, c, fs, w)
    case 129n:
      in.stmt.ext.chk(H, exec, 129n, c, fs, w)
    case 130n:
      in.stmt.ext.chk(H, exec, 130n, c, fs, w)
    case 131n:
      in.stmt.ext.chk(H, exec, 131n, c, fs, w)
    case 132n:
      in.stmt.ext.chk(H, exec, 132n, c, fs, w)
    case 133n:
      in.stmt.ext.chk(H, exec, 133n, c, fs, w)
    case 134n:
      in.stmt.ext.chk(H, exec, 134n, c, fs, w)
    case 135n:
      in.unsupported(H, "BankField", c, fs, w)
    case 136n:
      in.unsupported(H, "DataTableRegion", c, fs, w)
    case 31n:
      in.unsupported(H, "LoadTable", c, fs, w)
    case 32n:
      in.unsupported(H, "Load", c, fs, w)
    case 42n:
      in.unsupported(H, "Unload", c, fs, w)
    case 40n:
      in.unsupported(H, "FromBCD", c, fs, w)
    case 41n:
      in.unsupported(H, "ToBCD", c, fs, w)
    case _:
      in.expr(~H, ~io, Nat.add(256n, x), U32.add(23296, e), in.kinds(Nat.add(256n, x)), exec, c, fs, w)

def in.term.extb(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, k: AmlArgK, r: Result<&2, &2, E.AcpiError, AmlB>, +exec: Bool, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlB{+e, c}}:
      in.term.ext(~H, ~io, k, U32.to_nat(e), e, exec, c, fs, w)

def in.name.lead.go(k: N.AmlLeadKind) -> Bool:
  match k:
    case N.AmlLNull{}:
      False{}
    case N.AmlLOther{}:
      False{}
    case _:
      True{}

def in.name.lead(+b: U32) -> Bool:
  in.name.lead.go(N.AmlLead.classify(b))

# the cursor with b in front again (a NameString is read from its start)
def in.unread(+b: U32, c: AmlCur) -> AmlCur:
  match c:
    case AmlCur{code, lim}:
      AmlCur{Con{b, code}, 1n+lim}

def in.term.rest.pick(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, local: Bool, arg: Bool, name: Bool, k: AmlArgK, +n: Nat, +b: U32, +exec: Bool, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match local:
    case True{}:
      +i = Nat.sub(n, 96n)
      in.lvar(H, k, V.AmlLLocal{i}, in.ctx.local(H, w, i), c, fs, w)
    case False{}:
      match arg:
        case True{}:
          +i = Nat.sub(n, 104n)
          in.lvar(H, k, V.AmlLArg{i}, in.ctx.arg(H, w, i), c, fs, w)
        case False{}:
          match name:
            case True{}:
              in.name.go(~H, ~io, cur.name(in.unread(b, c)), k, fs, w)
            case False{}:
              in.expr(~H, ~io, n, b, in.kinds(n), exec, c, fs, w)

def in.term.rest(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, k: AmlArgK, +n: Nat, +b: U32, +exec: Bool, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  in.term.rest.pick(~H, ~io, Bool.and(Nat.is_le(96n, n), Nat.is_le(n, 103n)), Bool.and(Nat.is_le(104n, n), Nat.is_le(n, 110n)), in.name.lead(b), k, n, b, exec, c, fs, w)

def in.stmt.go(-H: Data, +n: Nat, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match n:
    case 16n:
      in.scope.op(H, cur.pkg(c), fs, w)
    case 20n:
      in.method.op(H, cur.pkg(c), fs, w)
    case 160n:
      in.if.op(H, cur.pkg(c), fs, w)
    case 161n:
      in.skip.op(H, cur.pkg(c), fs, w)
    case 162n:
      in.while.op(H, cur.pkg(c), fs, w)
    case 165n:
      in.unwind.brk(H, fs, w)
    case 159n:
      in.unwind.cont(H, fs, w)
    case _:
      AmlMachine{AmlMExec{}, c, fs, w}

# a statement: refused (AcpiAmlBadOperand) where a value is wanted
def in.stmt(-H: Data, exec: Bool, +n: Nat, c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match exec:
    case True{}:
      in.stmt.go(H, n, c, fs, w)
    case False{}:
      AmlMachine{AmlMFail{E.AcpiAmlBadOperand{U32.from_nat(n)}}, c, fs, w}

# the term whose first byte b has been read; exec: at statement level
def in.term(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +n: Nat, k: AmlArgK, +b: U32, +exec: Bool, +c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match n:
    case 0n:
      in.zero(H, k, c, fs, w)
    case 1n:
      in.give(H, V.AmlInt{W.W64.one()}, c, fs, w)
    case 255n:
      in.give(H, V.AmlInt{V.AmlInt.ones(in.wide(H, w))}, c, fs, w)
    case 10n:
      in.imm.give(H, in.wide(H, w), cur.imm(1n, c), fs, w)
    case 11n:
      in.imm.give(H, in.wide(H, w), cur.imm(2n, c), fs, w)
    case 12n:
      in.imm.give(H, in.wide(H, w), cur.imm(4n, c), fs, w)
    case 14n:
      in.imm.give(H, in.wide(H, w), cur.imm(8n, c), fs, w)
    case 13n:
      in.string(H, c, fs, w)
    case 17n:
      in.buffer(H, cur.pkg(c), fs, w)
    case 18n:
      in.package(H, cur.pkg(c), fs, w)
    case 19n:
      in.varpackage(H, cur.pkg(c), fs, w)
    case 91n:
      in.term.extb(~H, ~io, k, cur.byte(c), exec, fs, w)
    case 16n:
      in.stmt(H, exec, 16n, c, fs, w)
    case 20n:
      in.stmt(H, exec, 20n, c, fs, w)
    case 160n:
      in.stmt(H, exec, 160n, c, fs, w)
    case 161n:
      in.stmt(H, exec, 161n, c, fs, w)
    case 162n:
      in.stmt(H, exec, 162n, c, fs, w)
    case 163n:
      in.stmt(H, exec, 163n, c, fs, w)
    case 204n:
      in.stmt(H, exec, 204n, c, fs, w)
    case 165n:
      in.stmt(H, exec, 165n, c, fs, w)
    case 159n:
      in.stmt(H, exec, 159n, c, fs, w)
    case _:
      in.term.rest(~H, ~io, k, n, b, exec, c, fs, w)

def in.read.term(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, k: AmlArgK, r: Result<&2, &2, E.AcpiError, AmlB>, +exec: Bool, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlB{+b, c}}:
      in.term(~H, ~io, U32.to_nat(b), k, b, exec, c, fs, w)

# Eval: one operand
def in.eval(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, k: AmlArgK, +c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match k:
    case AmlKByte{}:
      in.imm.give(H, True{}, cur.imm(1n, c), fs, w)
    case AmlKWord{}:
      in.imm.give(H, True{}, cur.imm(2n, c), fs, w)
    case AmlKDWord{}:
      in.imm.give(H, True{}, cur.imm(4n, c), fs, w)
    case AmlKName{}:
      in.name.go(~H, ~io, cur.name(c), AmlKName{}, fs, w)
    case _:
      in.read.term(~H, ~io, k, cur.byte(c), False{}, fs, w)

def in.skip.else.pick(-H: Data, is_else: Bool, +after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match is_else:
    case True{}:
      in.skip.op(H, cur.pkg(cur.skip(1n, after)), fs, w)
    case False{}:
      AmlMachine{AmlMExec{}, after, fs, w}

# after an If body: an Else that follows is skipped
def in.skip.else(-H: Data, m: Maybe<&2, U32>, +after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match m:
    case Some{+b}:
      in.skip.else.pick(H, U32.is_eq(b, 161), after, fs, w)
    case None{}:
      AmlMachine{AmlMExec{}, after, fs, w}

# the end of a term list: what the frame on top does next
def in.end(-H: Data, fs: List<&2, AmlFrame>, c: AmlCur, +w: AmlWorld<H>) -> AmlMachine<H>:
  match fs:
    case Con{AmlFSeq{after, scope}, rest}:
      AmlMachine{AmlMExec{}, after, rest, in.with_scope(H, w, scope)}
    case Con{AmlFIfBody{+after}, rest}:
      in.skip.else(H, cur.peek(after), after, rest, w)
    case Con{AmlFWhile{+s, after, b}, rest}:
      AmlMachine{AmlMEval{AmlKTerm{}}, s, Con{AmlFWhile{s, after, False{}}, rest}, w}
    case Con{AmlFCall{saved, back}, rest}:
      AmlMachine{AmlMGive{V.AmlUninit{}}, back, rest, in.back(H, w, saved)}
    case Con{AmlFTop{}, rest}:
      AmlMachine{AmlMDone{V.AmlUninit{}}, c, Con{AmlFTop{}, rest}, w}
    case _:
      AmlMachine{AmlMFail{E.AcpiAmlTruncated{}}, c, fs, w}

def in.else.body(-H: Data, r: Result<&2, &2, E.AcpiError, AmlPkgC>, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, in.no.cur(), fs, w}
    case Done{AmlPkgC{body, after}}:
      AmlMachine{AmlMExec{}, body, Con{AmlFSeq{after, in.scope(H, w)}, fs}, w}

def in.else.pick(-H: Data, is_else: Bool, +after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match is_else:
    case True{}:
      in.else.body(H, cur.pkg(cur.skip(1n, after)), fs, w)
    case False{}:
      AmlMachine{AmlMExec{}, after, fs, w}

# a false If: its Else, if one follows, runs
def in.else.run(-H: Data, m: Maybe<&2, U32>, +after: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match m:
    case Some{+b}:
      in.else.pick(H, U32.is_eq(b, 161), after, fs, w)
    case None{}:
      AmlMachine{AmlMExec{}, after, fs, w}

def in.if.k(-H: Data, r: Result<&2, &2, E.AcpiError, Bool>, c: AmlCur, +after: AmlCur, rest: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, rest, w}
    case Done{True{}}:
      AmlMachine{AmlMExec{}, c, Con{AmlFIfBody{after}, rest}, w}
    case Done{False{}}:
      in.else.run(H, cur.peek(after), after, rest, w)

def in.while.k(-H: Data, r: Result<&2, &2, E.AcpiError, Bool>, c: AmlCur, start: AmlCur, after: AmlCur, rest: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, rest, w}
    case Done{True{}}:
      AmlMachine{AmlMExec{}, c, Con{AmlFWhile{start, after, True{}}, rest}, w}
    case Done{False{}}:
      AmlMachine{AmlMExec{}, after, rest, w}

def in.buf.k(-H: Data, r: Result<&2, &2, E.AcpiError, W.W64>, +c: AmlCur, after: AmlCur, rest: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, rest, w}
    case Done{n}:
      +init = cur.take(cur.len(c), c)
      AmlMachine{AmlMGive{V.AmlBuf{in.fit.buf(Nat.max(W.W64.to_nat(n), B.Octets.len(init)), init)}}, after, rest, w}

def in.pkg.k(-H: Data, end: Bool, +n: Nat, +got: List<&2, V.AmlValue>, c: AmlCur, after: AmlCur, rest: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match end:
    case True{}:
      AmlMachine{AmlMGive{V.AmlPkg{in.pad(n, List.reverse(&2, V.AmlValue, got))}}, after, rest, w}
    case False{}:
      AmlMachine{AmlMEval{AmlKElem{}}, c, Con{AmlFPkg{n, got, after}, rest}, w}

def in.varpkg.k(-H: Data, r: Result<&2, &2, E.AcpiError, W.W64>, +c: AmlCur, after: AmlCur, rest: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match r:
    case Fail{e}:
      AmlMachine{AmlMFail{e}, c, rest, w}
    case Done{n}:
      in.pkg.k(H, cur.at_end(c), W.W64.to_nat(n), Nil{}, c, after, rest, w)

def in.give.args(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, op: AmlOp, got: List<&2, V.AmlValue>, todo: List<&2, AmlArgK>, v: V.AmlValue, c: AmlCur, rest: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match todo:
    case Con{k, Con{+k2, m2}}:
      AmlMachine{AmlMEval{k2}, c, Con{AmlFArgs{op, Con{v, got}, Con{k2, m2}}, rest}, w}
    case _:
      in.apply(~H, ~io, op, List.reverse(&2, V.AmlValue, Con{v, got}), c, rest, w)

# Give: a value for the frame on top
def in.give.to(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, fs: List<&2, AmlFrame>, v: V.AmlValue, +c: AmlCur, +w: AmlWorld<H>) -> AmlMachine<H>:
  match fs:
    case Con{AmlFArgs{op, got, todo}, rest}:
      in.give.args(~H, ~io, op, got, todo, v, c, rest, w)
    case Con{AmlFIf{+after}, rest}:
      in.if.k(H, in.truth(in.wide(H, w), v), c, after, rest, w)
    case Con{AmlFWhile{start, after, False{}}, rest}:
      in.while.k(H, in.truth(in.wide(H, w), v), c, start, after, rest, w)
    case Con{AmlFBuffer{after}, rest}:
      in.buf.k(H, in.small.int(in.wide(H, w), v), c, after, rest, w)
    case Con{AmlFPkg{+n, got, after}, rest}:
      in.pkg.k(H, cur.at_end(c), n, Con{v, got}, c, after, rest, w)
    case Con{AmlFVarPkg{after}, rest}:
      in.varpkg.k(H, in.small.int(in.wide(H, w), v), c, after, rest, w)
    case _:
      AmlMachine{AmlMExec{}, c, fs, w}

# Exec: the next term of the list, or its end
def in.exec(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, end: Bool, +c: AmlCur, fs: List<&2, AmlFrame>, +w: AmlWorld<H>) -> AmlMachine<H>:
  match end:
    case True{}:
      in.end(H, fs, c, w)
    case False{}:
      in.read.term(~H, ~io, AmlKTerm{}, cur.byte(c), True{}, fs, w)

# One step of the machine
def AmlM.step(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, m: AmlMachine<H>) -> AmlMachine<H>:
  match m:
    case AmlMachine{md, +c, fs, +w}:
      match md:
        case AmlMExec{}:
          in.exec(~H, ~io, cur.at_end(c), c, fs, w)
        case AmlMEval{k}:
          in.eval(~H, ~io, k, c, fs, w)
        case AmlMGive{v}:
          in.give.to(~H, ~io, fs, v, c, w)
        case AmlMDone{v}:
          AmlMachine{AmlMDone{v}, c, fs, w}
        case AmlMFail{e}:
          AmlMachine{AmlMFail{e}, c, fs, w}

# Running: at most n steps

type AmlRun<-H: Data> is Data:
  AmlRun{m: AmlMachine<H>, steps: Nat}

def AmlRun.steps(-H: Data, r: AmlRun<H>) -> Nat:
  match r:
    case AmlRun{m, s}:
      s

def AmlRun.machine(-H: Data, r: AmlRun<H>) -> AmlMachine<H>:
  match r:
    case AmlRun{m, s}:
      m

# h: m has halted; used: the steps taken so far
def AmlM.run.go(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, n: Nat, h: Bool, m: AmlMachine<H>, used: Nat) -> AmlRun<H>:
  match n:
    case 0n:
      AmlRun{m, used}
    case 1n+p:
      match h:
        case True{}:
          AmlRun{m, used}
        case False{}:
          +m2 = AmlM.step(~H, ~io, m)
          AmlM.run.go(~H, ~io, p, AmlMachine.halted(H, m2), m2, 1n+used)

# the machine run until it halts, or for n steps
def AmlM.run(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, n: Nat, +m: AmlMachine<H>) -> AmlRun<H>:
  AmlM.run.go(~H, ~io, n, AmlMachine.halted(H, m), m, 0n)
