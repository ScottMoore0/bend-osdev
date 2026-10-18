# bend-osdev-acpi, aml.bend: AML definition blocks loaded into a namespace,
# and objects evaluated there (ACPI 6.5, sections 5.4, Definition Block
# Encoding, and 5.5, Using the ACPI Control Method Source Language).
#
# A system is the namespace, the operation-region host, the integer width
# (64 bits unless the DSDT's revision is below 2) and the options. Loading a
# DSDT or SSDT runs its top-level terms (Name, Method, Device, Scope, ...)
# into the namespace; evaluating a path runs a method with arguments, or
# reads any other object. Both take a step bound (aml_interp.bend) and
# answer an AmlOutcome: the result (AcpiAmlStepLimit when the bound ran
# out), the namespace and host after, the steps used, the Notify calls and
# the values stored to Debug.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./dsdt.bend as D
import ./aml_value.bend as V
import ./aml_ns.bend as S
import ./aml_host.bend as Hs
import ./aml_interp.bend as I

type AmlSystem<-H: Data> is Data:
  AmlSystem{opts: I.AmlOptions, wide: Bool, ns: S.AmlNs, host: H}

type AmlOutcome<-H: Data> is Data:
  AmlOutcome{result: Result<&2, &2, E.AcpiError, V.AmlValue>, ns: S.AmlNs, host: H, steps: Nat, notes: List<&2, I.AmlNote>, debug: List<&2, V.AmlValue>}

def AmlOutcome.result(-H: Data, o: AmlOutcome<H>) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match o:
    case AmlOutcome{r, n, h, s, nt, d}:
      r

def AmlOutcome.steps(-H: Data, o: AmlOutcome<H>) -> Nat:
  match o:
    case AmlOutcome{r, n, h, s, nt, d}:
      s

def AmlOutcome.ns(-H: Data, o: AmlOutcome<H>) -> S.AmlNs:
  match o:
    case AmlOutcome{r, n, h, s, nt, d}:
      n

def AmlOutcome.host(-H: Data, o: AmlOutcome<H>) -> H:
  match o:
    case AmlOutcome{r, n, h, s, nt, d}:
      h

def AmlOutcome.notes(-H: Data, o: AmlOutcome<H>) -> List<&2, I.AmlNote>:
  match o:
    case AmlOutcome{r, n, h, s, nt, d}:
      nt

def AmlOutcome.debug(-H: Data, o: AmlOutcome<H>) -> List<&2, V.AmlValue>:
  match o:
    case AmlOutcome{r, n, h, s, nt, d}:
      d

# a system with the initial namespace (\_SB_, \_OSI, ...) and this host
def AmlSystem.new(-H: Data, opts: I.AmlOptions, +wide: Bool, host: H) -> AmlSystem<H>:
  match opts:
    case I.AmlOptions{+osi, +os, +rev}:
      AmlSystem{I.AmlOptions{osi, os, rev}, wide, S.AmlNs.initial(os, rev), host}

def AmlSystem.ns(-H: Data, s: AmlSystem<H>) -> S.AmlNs:
  match s:
    case AmlSystem{o, w, n, h}:
      n

def AmlSystem.host(-H: Data, s: AmlSystem<H>) -> H:
  match s:
    case AmlSystem{o, w, n, h}:
      h

def AmlSystem.wide(-H: Data, s: AmlSystem<H>) -> Bool:
  match s:
    case AmlSystem{o, w, n, h}:
      w

# the system after an outcome: its namespace and host
def AmlSystem.after(-H: Data, s: AmlSystem<H>, o: AmlOutcome<H>) -> AmlSystem<H>:
  match s o:
    case AmlSystem{op, w, n, h} AmlOutcome{r, n2, h2, st, nt, d}:
      AmlSystem{op, w, n2, h2}

def aml.rev.n(xs: List<&2, I.AmlNote>, acc: List<&2, I.AmlNote>) -> List<&2, I.AmlNote>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      aml.rev.n(t, Con{x, acc})

def aml.rev.v(xs: List<&2, V.AmlValue>, acc: List<&2, V.AmlValue>) -> List<&2, V.AmlValue>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      aml.rev.v(t, Con{x, acc})

def aml.result(md: I.AmlMode) -> Result<&2, &2, E.AcpiError, V.AmlValue>:
  match md:
    case I.AmlMDone{v}:
      Done{v}
    case I.AmlMFail{e}:
      Fail{e}
    case _:
      Fail{E.AcpiAmlStepLimit{}}

# what a run came to
def AmlOutcome.of_run(-H: Data, r: I.AmlRun<H>) -> AmlOutcome<H>:
  match r:
    case I.AmlRun{I.AmlMachine{md, c, fs, I.AmlWorld{ctx, ns, h, I.AmlEnv{wd, o, nts, d, cl}}}, s}:
      AmlOutcome{aml.result(md), ns, h, s, aml.rev.n(nts, Nil{}), aml.rev.v(d, Nil{})}

def aml.env(+wide: Bool, opts: I.AmlOptions) -> I.AmlEnv:
  I.AmlEnv{wide, opts, Nil{}, Nil{}, W.W64.zero()}

def aml.ctx(+p: String, args: List<&2, V.AmlValue>) -> I.AmlCtx:
  I.AmlCtx{p, args, I.in.locals(), Nil{}}

# a machine at the start of a definition block, at the root
def AmlSystem.loader(-H: Data, s: AmlSystem<H>, aml: B.Octets) -> I.AmlMachine<H>:
  match s:
    case AmlSystem{o, +wd, n, h}:
      +code = B.Octets.to_list(aml)
      I.AmlMachine{I.AmlMExec{}, I.AmlCur{code, B.len.fast(code)}, [I.AmlFTop{}], I.AmlWorld{aml.ctx("\\", Nil{}), n, h, aml.env(wd, o)}}

def aml.read(-H: Data, r: Result<&2, &2, E.AcpiError, I.AmlRead<H>>, +w: I.AmlWorld<H>) -> I.AmlMachine<H>:
  match r:
    case Fail{e}:
      I.AmlMachine{I.AmlMFail{e}, I.in.no.cur(), [I.AmlFTop{}], w}
    case Done{I.AmlRead{w2, v}}:
      I.AmlMachine{I.AmlMDone{v}, I.in.no.cur(), [I.AmlFTop{}], w2}

def aml.start(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, o: Maybe<&2, S.AmlObject>, +p: String, args: List<&2, V.AmlValue>, +w: I.AmlWorld<H>) -> I.AmlMachine<H>:
  match o:
    case Some{S.AmlOMethod{n, f, +body}}:
      +code = B.Octets.to_list(body)
      I.AmlMachine{I.AmlMExec{}, I.AmlCur{code, B.len.fast(code)}, [I.AmlFTop{}], I.in.with_ctx(H, w, aml.ctx(p, args))}
    case _:
      aml.read(H, I.in.read_obj(~H, ~io, w, p, o), w)

# arguments as the method sees them: Integers cut to 32 bits in a 32-bit
# definition block
def aml.fit.args(+wide: Bool, xs: List<&2, V.AmlValue>) -> List<&2, V.AmlValue>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{V.AmlInt{x}, t}:
      Con{V.AmlInt{V.AmlInt.fit(wide, x)}, aml.fit.args(wide, t)}
    case Con{v, t}:
      Con{v, aml.fit.args(wide, t)}

# a machine about to evaluate the object at path p (a method is called
# with args; any other object is read before the first step)
def AmlSystem.caller(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, s: AmlSystem<H>, +p: String, args: List<&2, V.AmlValue>) -> I.AmlMachine<H>:
  match s:
    case AmlSystem{o, +wd, +n, h}:
      +q = I.in.unalias(n, p)
      aml.start(~H, ~io, S.AmlNs.get(n, q), q, aml.fit.args(wd, args), I.AmlWorld{aml.ctx("\\", Nil{}), n, h, aml.env(wd, o)})

# a definition block run into the system's namespace, in at most n steps
def Aml.load(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, s: AmlSystem<H>, aml: B.Octets, n: Nat) -> AmlOutcome<H>:
  AmlOutcome.of_run(H, I.AmlM.run(~H, ~io, n, AmlSystem.loader(H, s, aml)))

# the object at path p evaluated (a method called with args), in at most n
# steps
def Aml.eval(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, s: AmlSystem<H>, +p: String, args: List<&2, V.AmlValue>, n: Nat) -> AmlOutcome<H>:
  AmlOutcome.of_run(H, I.AmlM.run(~H, ~io, n, AmlSystem.caller(~H, ~io, s, p, args)))

def aml.boot.chk(-H: Data, r: Result<&2, &2, E.AcpiError, V.AmlValue>, s: AmlSystem<H>, o: AmlOutcome<H>) -> Result<&2, &2, E.AcpiError, AmlSystem<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      Done{AmlSystem.after(H, s, o)}

def aml.boot.res(-H: Data, s: AmlSystem<H>, +o: AmlOutcome<H>) -> Result<&2, &2, E.AcpiError, AmlSystem<H>>:
  aml.boot.chk(H, AmlOutcome.result(H, o), s, o)

def aml.boot.one(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, t: D.AcpiAml, +n: Nat, r: Result<&2, &2, E.AcpiError, AmlSystem<H>>) -> Result<&2, &2, E.AcpiError, AmlSystem<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+s}:
      aml.boot.res(H, s, Aml.load(~H, ~io, s, D.AcpiAml.aml(t), n))

def aml.boot.go(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, ts: List<&2, D.AcpiAml>, +n: Nat, r: Result<&2, &2, E.AcpiError, AmlSystem<H>>) -> Result<&2, &2, E.AcpiError, AmlSystem<H>>:
  match ts:
    case Nil{}:
      r
    case Con{t, rest}:
      aml.boot.go(~H, ~io, rest, n, aml.boot.one(~H, ~io, t, n, r))

# the namespace of a machine's tables: the DSDT, then each SSDT, each
# loaded in at most n steps; the integer width is the DSDT's (the first
# table's)
def Aml.boot(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, opts: I.AmlOptions, host: H, ts: List<&2, D.AcpiAml>, +n: Nat) -> Result<&2, &2, E.AcpiError, AmlSystem<H>>:
  match ts:
    case Nil{}:
      Done{AmlSystem.new(H, opts, True{}, host)}
    case Con{+t, rest}:
      aml.boot.go(~H, ~io, Con{t, rest}, n, Done{AmlSystem.new(H, opts, D.AcpiAml.wide(t), host)})

# The defaults: the in-memory host

def Aml.mem_system(+wide: Bool) -> AmlSystem<Hs.AmlMemHost>:
  AmlSystem.new(Hs.AmlMemHost, I.AmlOptions.default(), wide, Hs.AmlMemHost.new())

def Aml.load_mem(s: AmlSystem<Hs.AmlMemHost>, aml: B.Octets, n: Nat) -> AmlOutcome<Hs.AmlMemHost>:
  Aml.load(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, aml, n)

def Aml.eval_mem(s: AmlSystem<Hs.AmlMemHost>, +p: String, args: List<&2, V.AmlValue>, n: Nat) -> AmlOutcome<Hs.AmlMemHost>:
  Aml.eval(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, p, args, n)
