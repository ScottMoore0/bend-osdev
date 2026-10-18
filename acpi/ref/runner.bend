import Base
import ../../word64/word64.bend as W
import ../../bytes/bytes.bend as B
import ../error.bend as E
import ../checksum.bend as C
import ../header.bend as H
import ../rsdp.bend as P
import ../registry.bend as R
import ../acpi.bend as A
import ../show.bend as Sh
import ../dsdt.bend as D
import ../aml_pkglength.bend as K
import ../aml_name.bend as N
import ../aml_value.bend as V
import ../aml_host.bend as Hs
import ../aml_ns.bend as Ns
import ../aml_interp.bend as I
import ../aml.bend as Am
import ../aml_term.bend as T
import ../aml_resource.bend as Rs
import ../aml_device.bend as Dv

# The differential test's runner: reads cases.txt (written by gen.py), one
# case a line, its fields separated by '|': the kind, the label, then the
# inputs (byte strings and names in hex). Prints the label and what the
# package answers, a line a case, for run.sh to compare with expected.txt.
# The cases are data read at run time, so the runner builds once, natively,
# whatever their number.

# Inputs

def hexv.pick(digit: Bool, +c: U32) -> U32:
  match digit:
    case True{}:
      U32.sub(c, 48)
    case False{}:
      U32.sub(c, 87)

def hexv(+c: U32) -> U32:
  hexv.pick(U32.is_le(c, 57), c)

def hexo.go(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SCon{Chr{a}, SCon{Chr{b}, t}}:
      hexo.go(t, Con{U32.or(U32.shln(hexv(a), 4n), hexv(b)), acc})
    case _:
      List.reverse(&2, U32, acc)

def hexo(s: String) -> B.Octets:
  B.Octets.of_list(hexo.go(s, Nil{}))

def num(s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

def text(s: String) -> String:
  B.Octets.to_string(hexo(s))

def i64.go(ps: List<&2, String>) -> V.AmlValue:
  match ps:
    case Con{hi, Con{lo, Nil{}}}:
      V.AmlInt{W.W64.from_parts(num(hi), num(lo))}
    case _:
      V.AmlUninit{}

def i64(s: String) -> V.AmlValue:
  i64.go(String.split(s, ':'))

def i64s(xs: List<&2, String>) -> List<&2, V.AmlValue>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{i64(x), i64s(t)}

def args.pick(empty: Bool, s: String) -> List<&2, V.AmlValue>:
  match empty:
    case True{}:
      Nil{}
    case False{}:
      i64s(String.split(s, ','))

def args(+s: String) -> List<&2, V.AmlValue>:
  args.pick(String.is_empty(s), s)

# Tables

def reg(o: B.Octets) -> String:
  Sh.AcpiShow.result(~R.AcpiNoExt, R.AcpiTable.parse(R.AcpiRegistry.default(), o))

def rsdp(r: Result<&2, &2, E.AcpiError, P.AcpiRsdp>) -> String:
  match r:
    case Done{p}:
      Sh.AcpiShow.rsdp(p)
    case Fail{e}:
      Sh.AcpiShow.error(e)

def header(r: Result<&2, &2, E.AcpiError, H.AcpiHeader>) -> String:
  match r:
    case Done{h}:
      B.Octets.hex(H.AcpiHeader.encode(h))
    case Fail{e}:
      "short"

def ld(l: A.AcpiLoaded<R.AcpiNoExt>) -> String:
  match l:
    case A.AcpiLoaded{a, Done{t}}:
      W.W64.show_hex(a) ++ " " ++ R.AcpiTable.name(~R.AcpiNoExt, t)
    case A.AcpiLoaded{a, Fail{e}}:
      W.W64.show_hex(a) ++ " " ++ Sh.AcpiShow.error(e)

def lds(ls: List<&2, A.AcpiLoaded<R.AcpiNoExt>>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{ld(h), lds(t)}

def tables(r: Result<&2, &2, E.AcpiError, A.AcpiTableSet<R.AcpiNoExt>>) -> String:
  match r:
    case Done{A.AcpiTableSet{rp, root, ts, Some{Done{f}}}}:
      String.join(lds(ts), ", ") ++ "; FACS ok"
    case Done{A.AcpiTableSet{rp, root, ts, f}}:
      String.join(lds(ts), ", ") ++ "; no FACS"
    case Fail{e}:
      Sh.AcpiShow.error(e)

def mach(rp: B.Octets, base: U32, image: B.Octets) -> String:
  tables(A.AcpiTables.load(~A.AcpiMemImage, ~A.AcpiMemImage.read, A.AcpiMemImage{[A.AcpiMemRegion{W.W64.from_u32(917504), rp}, A.AcpiMemRegion{W.W64.from_u32(base), image}]}, W.W64.from_u32(917504)))

# AML encodings

def pk(r: Result<&2, &2, E.AcpiError, K.AmlPkgLen>) -> String:
  match r:
    case Done{K.AmlPkgLen{v, rest}}:
      U32.show(v) ++ " rest " ++ B.Octets.hex(rest)
    case Fail{e}:
      Sh.AcpiShow.error(e)

def nm(r: Result<&2, &2, E.AcpiError, N.AmlNameParsed>) -> String:
  match r:
    case Done{N.AmlNameParsed{n, rest}}:
      N.AmlName.show(n) ++ " rest " ++ B.Octets.hex(rest)
    case Fail{e}:
      Sh.AcpiShow.error(e)

# The interpreter

def val(r: Result<&2, &2, E.AcpiError, V.AmlValue>) -> String:
  match r:
    case Done{v}:
      V.AmlValue.show(v)
    case Fail{e}:
      Sh.AcpiShow.error(e)

def loaded(r: Result<&2, &2, E.AcpiError, V.AmlValue>, +s: Am.AmlSystem<Hs.AmlMemHost>, +o: Am.AmlOutcome<Hs.AmlMemHost>, p: String, xs: List<&2, V.AmlValue>) -> String:
  match r:
    case Fail{e}:
      "load " ++ Sh.AcpiShow.error(e)
    case Done{v}:
      val(Am.AmlOutcome.result(Hs.AmlMemHost, Am.Aml.eval_mem(Am.AmlSystem.after(Hs.AmlMemHost, s, o), p, xs, 200000n)))

def run(+wide: Bool, aml: B.Octets, p: String, xs: List<&2, V.AmlValue>) -> String:
  +s = Am.Aml.mem_system(wide)
  +o = Am.Aml.load_mem(s, aml, 200000n)
  loaded(Am.AmlOutcome.result(Hs.AmlMemHost, o), s, o, p, xs)

def mem.hex(n: Nat, +h: Hs.AmlMemHost, +a: W.W64) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{Hs.AmlMemHost.peek(h, 0, a), mem.hex(k, h, W.W64.add(a, W.W64.one()))}

def fld.after(r: Result<&2, &2, E.AcpiError, V.AmlValue>, +h: Hs.AmlMemHost) -> String:
  match r:
    case Fail{e}:
      Sh.AcpiShow.error(e)
    case Done{v}:
      V.AmlValue.show(v) ++ " " ++ B.hex(mem.hex(16n, h, W.W64.from_u32(4096)))

def fld.go(r: Result<&2, &2, E.AcpiError, V.AmlValue>, +s: Am.AmlSystem<Hs.AmlMemHost>, +o: Am.AmlOutcome<Hs.AmlMemHost>) -> String:
  match r:
    case Fail{e}:
      "load " ++ Sh.AcpiShow.error(e)
    case Done{v}:
      +e = Am.Aml.eval_mem(Am.AmlSystem.after(Hs.AmlMemHost, s, o), "\\TEST", Nil{}, 100000n)
      fld.after(Am.AmlOutcome.result(Hs.AmlMemHost, e), Am.AmlOutcome.host(Hs.AmlMemHost, e))

def fld(aml: B.Octets, init: B.Octets) -> String:
  +s = Am.AmlSystem.new(Hs.AmlMemHost, I.AmlOptions.default(), True{}, Hs.AmlMemHost.poke(Hs.AmlMemHost.new(), 0, W.W64.from_u32(4096), init))
  +o = Am.Aml.load_mem(s, aml, 100000n)
  fld.go(Am.AmlOutcome.result(Hs.AmlMemHost, o), s, o)

def res.list(xs: List<&2, Rs.AmlResource>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{Rs.AmlResource.show(h), res.list(t)}

def res(r: Result<&2, &2, E.AcpiError, List<&2, Rs.AmlResource>>) -> String:
  match r:
    case Done{+xs}:
      String.join(res.list(xs), "; ") ++ " | " ++ B.Octets.hex(Rs.AmlResource.template(xs))
    case Fail{e}:
      Sh.AcpiShow.error(e)

def iasl.table(r: Result<&2, &2, E.AcpiError, D.AcpiAml>) -> String:
  match r:
    case Done{+t}:
      run(D.AcpiAml.wide(t), D.AcpiAml.aml(t), "\\TEST", Nil{})
    case Fail{e}:
      Sh.AcpiShow.error(e)

# The builder (aml_term.bend), driven by tokens in postfix order: each
# token pushes a term, or pops its operands and pushes the term they make

type RpnPop is Data:
  RpnPop{xs: List<&2, T.AmlTerm>, rest: List<&2, T.AmlTerm>}

def rpn.pop(k: Nat, st: List<&2, T.AmlTerm>, acc: List<&2, T.AmlTerm>) -> RpnPop:
  match k st:
    case 0n _:
      RpnPop{acc, st}
    case 1n+p Con{h, t}:
      rpn.pop(p, t, Con{h, acc})
    case 1n+p Nil{}:
      RpnPop{acc, Nil{}}

def rpn.ops() -> List<&2, String>:
  ["i", "s", "a", "l", "n", "none", "zero", "op", "div", "lnot", "land", "lor", "call", "pkg", "buf", "elem", "size", "concat", "toint", "store", "inc", "dec", "if", "ifelse", "ret", "while", "method", "name"]

def rpn.code.sel(hit: Bool, +k: Nat, rest: Nat) -> Nat:
  match hit:
    case True{}:
      k
    case False{}:
      rest

# the position of op in xs (999 if it is not there)
def rpn.code(xs: List<&2, String>, +op: String, +k: Nat) -> Nat:
  match xs:
    case Nil{}:
      999n
    case Con{h, t}:
      rpn.code.sel(String.eq(h, op), k, rpn.code(t, op, 1n+k))

def rpn.arg(xs: List<&2, String>, i: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, xs, i), "")

def rpn.n(xs: List<&2, String>, i: Nat) -> Nat:
  U32.to_nat(num(rpn.arg(xs, i)))

def rpn.at(xs: List<&2, T.AmlTerm>, i: Nat) -> T.AmlTerm:
  Maybe.default(&2, T.AmlTerm, List.get(&2, T.AmlTerm, xs, i), T.AmlT.none())

def rpn.arity(+c: Nat) -> Nat:
  match c:
    case 9n:
      1n
    case 16n:
      1n
    case 18n:
      1n
    case 20n:
      1n
    case 21n:
      1n
    case 24n:
      1n
    case _:
      2n

def rpn.fixed.term(+c: Nat, x: T.AmlTerm, y: T.AmlTerm) -> T.AmlTerm:
  match c:
    case 8n:
      T.AmlT.divide(x, y, T.AmlT.none(), T.AmlT.none())
    case 9n:
      T.AmlT.lnot(x)
    case 10n:
      T.AmlT.land(x, y)
    case 11n:
      T.AmlT.lor(x, y)
    case 15n:
      T.AmlT.deref_of(T.AmlT.index(x, y, T.AmlT.none()))
    case 16n:
      T.AmlT.size_of(x)
    case 17n:
      T.AmlT.concat(x, y, T.AmlT.none())
    case 18n:
      T.AmlT.to_integer(x, T.AmlT.none())
    case 19n:
      T.AmlT.store(x, y)
    case 20n:
      T.AmlT.increment(x)
    case 21n:
      T.AmlT.decrement(x)
    case _:
      T.AmlT.ret(x)

# the operators of fixed arity
def rpn.fixed(+c: Nat, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{+xs, st}:
      Con{rpn.fixed.term(c, rpn.at(xs, 0n), rpn.at(xs, 1n)), st}

def rpn.op(+code: U32, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{xs, st}:
      Con{T.AmlT.op(code, xs), st}

def rpn.call(+name: String, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{xs, st}:
      Con{T.AmlT.call(name, xs), st}

def rpn.pkg(p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{xs, st}:
      Con{T.AmlT.package(xs), st}

def rpn.if.k(body: List<&2, T.AmlTerm>, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{+c, st}:
      Con{T.AmlT.if_(rpn.at(c, 0n), body), st}

def rpn.if(p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{body, st}:
      rpn.if.k(body, rpn.pop(1n, st, Nil{}))

def rpn.ifelse.c(then: List<&2, T.AmlTerm>, els: List<&2, T.AmlTerm>, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{+c, st}:
      Con{T.AmlT.if_else(rpn.at(c, 0n), then, els), st}

def rpn.ifelse.t(els: List<&2, T.AmlTerm>, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{then, st}:
      rpn.ifelse.c(then, els, rpn.pop(1n, st, Nil{}))

def rpn.ifelse(+k1: Nat, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{els, st}:
      rpn.ifelse.t(els, rpn.pop(k1, st, Nil{}))

def rpn.while.k(body: List<&2, T.AmlTerm>, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{+c, st}:
      Con{T.AmlT.while_(rpn.at(c, 0n), body), st}

def rpn.while(p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{body, st}:
      rpn.while.k(body, rpn.pop(1n, st, Nil{}))

def rpn.method(+name: String, +nargs: Nat, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{body, st}:
      Con{T.AmlT.method(name, nargs, False{}, body), st}

def rpn.name(+name: String, p: RpnPop) -> List<&2, T.AmlTerm>:
  match p:
    case RpnPop{+v, st}:
      Con{T.AmlT.name(name, rpn.at(v, 0n)), st}

def rpn.node(+c: Nat, +a: List<&2, String>, st: List<&2, T.AmlTerm>) -> List<&2, T.AmlTerm>:
  match c:
    case 0n:
      Con{T.AmlT.int(W.W64.from_parts(num(rpn.arg(a, 0n)), num(rpn.arg(a, 1n)))), st}
    case 1n:
      Con{T.AmlTStr{hexo(rpn.arg(a, 0n))}, st}
    case 2n:
      Con{T.AmlT.arg(num(rpn.arg(a, 0n))), st}
    case 3n:
      Con{T.AmlT.local(num(rpn.arg(a, 0n))), st}
    case 4n:
      Con{T.AmlT.nm(text(rpn.arg(a, 0n))), st}
    case 5n:
      Con{T.AmlT.none(), st}
    case 6n:
      Con{T.AmlT.zero(), st}
    case 7n:
      rpn.op(num(rpn.arg(a, 0n)), rpn.pop(rpn.n(a, 1n), st, Nil{}))
    case 12n:
      rpn.call(text(rpn.arg(a, 0n)), rpn.pop(rpn.n(a, 1n), st, Nil{}))
    case 13n:
      rpn.pkg(rpn.pop(rpn.n(a, 0n), st, Nil{}))
    case 14n:
      Con{T.AmlT.buf(hexo(rpn.arg(a, 0n))), st}
    case 22n:
      rpn.if(rpn.pop(rpn.n(a, 0n), st, Nil{}))
    case 23n:
      rpn.ifelse(rpn.n(a, 0n), rpn.pop(rpn.n(a, 1n), st, Nil{}))
    case 25n:
      rpn.while(rpn.pop(rpn.n(a, 0n), st, Nil{}))
    case 26n:
      rpn.method(text(rpn.arg(a, 0n)), rpn.n(a, 1n), rpn.pop(rpn.n(a, 2n), st, Nil{}))
    case 27n:
      rpn.name(text(rpn.arg(a, 0n)), rpn.pop(1n, st, Nil{}))
    case _:
      rpn.fixed(c, rpn.pop(rpn.arity(c), st, Nil{}))

def rpn.token(t: List<&2, String>, st: List<&2, T.AmlTerm>) -> List<&2, T.AmlTerm>:
  match t:
    case Nil{}:
      st
    case Con{+op, a}:
      rpn.node(rpn.code(rpn.ops(), op, 0n), a, st)

def rpn.run(ts: List<&2, String>, st: List<&2, T.AmlTerm>) -> List<&2, T.AmlTerm>:
  match ts:
    case Nil{}:
      List.reverse(&2, T.AmlTerm, st)
    case Con{t, rest}:
      rpn.run(rest, rpn.token(String.split(t, ':'), st))

def build(+toks: String) -> String:
  B.Octets.hex(T.AmlT.encode(rpn.run(String.split(toks, ' '), Nil{})))

# Real tables: read from files

def read.done(r: Result<&1, &1, U32 & String, List<&2, U32>>) -> B.Octets:
  match r:
    case Done{xs}:
      B.Octets.of_list(xs)
    case Fail{e}:
      B.Octets.empty()

def read.pair(p: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(B.Octets):
  (f, r) = p
  do IO<B.Octets>:
    File.close(f)
    return read.done(r)

def read(path: String) -> IO(B.Octets):
  do IO<B.Octets>:
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 4000000)
    read.pair(p)

def amls.read(ps: List<&2, String>, acc: List<&2, D.AcpiAml>) -> IO(List<&2, D.AcpiAml>):
  match ps:
    case Nil{}:
      IO.pure(List<&2, D.AcpiAml>, List.reverse(&2, D.AcpiAml, acc))
    case Con{p, t}:
      do IO<List<&2, D.AcpiAml>>:
        o : B.Octets <- read(p)
        amls.read(t, Con{Result.default(&2, &2, E.AcpiError, D.AcpiAml, D.AcpiAml.parse(o), D.AcpiAml{H.AcpiHeader.make(B.Octets.of_string("SSDT"), 2, B.Octets.empty(), B.Octets.empty()), B.Octets.empty()}), acc})

def devs.keep(has: Bool, p: String, rest: List<&2, String>) -> List<&2, String>:
  match has:
    case True{}:
      rest
    case False{}:
      Con{p, rest}

def devs.missing(ps: List<&2, String>, +ns: Ns.AmlNs) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      devs.keep(Ns.AmlNs.has(ns, p), p, devs.missing(t, ns))

def devs.report(+want: List<&2, String>, miss: List<&2, String>) -> String:
  match miss:
    case Nil{}:
      "all " ++ Nat.show(List.length(&2, String, want)) ++ " found"
    case _:
      "missing " ++ String.join(miss, " ")

def devs.list.pick(e: Bool, s: String) -> List<&2, String>:
  match e:
    case True{}:
      Nil{}
    case False{}:
      String.split(s, ' ')

def devs.list(+s: String) -> List<&2, String>:
  devs.list.pick(String.is_empty(s), s)

# every device a static walk of the AML found (want) is in the namespace
def devices(r: Result<&2, &2, E.AcpiError, Am.AmlSystem<Hs.AmlMemHost>>, +want: List<&2, String>) -> String:
  match r:
    case Done{s}:
      devs.report(want, devs.missing(want, Am.AmlSystem.ns(Hs.AmlMemHost, s)))
    case Fail{e}:
      Sh.AcpiShow.error(e)

# One case

def case.fields(+k: Nat, +f: List<&2, String>) -> String:
  match k:
    case 0n:
      U32.show(C.AcpiChecksum.sum(hexo(rpn.arg(f, 0n))))
    case 1n:
      reg(hexo(rpn.arg(f, 0n)))
    case 2n:
      header(H.AcpiHeader.decode(hexo(rpn.arg(f, 0n))))
    case 3n:
      rsdp(P.AcpiRsdp.parse(hexo(rpn.arg(f, 0n))))
    case 4n:
      mach(hexo(rpn.arg(f, 0n)), num(rpn.arg(f, 1n)), hexo(rpn.arg(f, 2n)))
    case 5n:
      B.Octets.hex(K.AmlPkgLength.encode(num(rpn.arg(f, 0n))))
    case 6n:
      pk(K.AmlPkgLength.decode(hexo(rpn.arg(f, 0n))))
    case 7n:
      B.Octets.hex(N.AmlName.encode(N.AmlName.of_text(text(rpn.arg(f, 0n)))))
    case 8n:
      nm(N.AmlName.decode(hexo(rpn.arg(f, 0n))))
    case 9n:
      run(String.eq(rpn.arg(f, 0n), "1"), hexo(rpn.arg(f, 1n)), text(rpn.arg(f, 2n)), args(rpn.arg(f, 3n)))
    case 10n:
      fld(hexo(rpn.arg(f, 0n)), hexo(rpn.arg(f, 1n)))
    case 11n:
      res(Rs.AmlResource.parse(hexo(rpn.arg(f, 0n))))
    case 12n:
      build(rpn.arg(f, 0n))
    case 15n:
      iasl.table(D.AcpiAml.parse(hexo(rpn.arg(f, 0n))))
    case _:
      "unknown case"

def kinds() -> List<&2, String>:
  ["checksum", "table", "header", "rsdp", "machine", "pkenc", "pkdec", "nameenc", "namedec", "aml", "field", "res", "build", "real", "realdevs", "iasl"]

def case.io(+k: Nat, +label: String, +f: List<&2, String>) -> IO(Unit):
  match k:
    case 13n:
      do IO<Unit>:
        o : B.Octets <- read(text(rpn.arg(f, 0n)))
        IO.print(label ++ " " ++ reg(o))
    case 14n:
      do IO<Unit>:
        ts : List<&2, D.AcpiAml> <- amls.read(String.split(text(rpn.arg(f, 0n)), ','), Nil{})
        IO.print(label ++ " " ++ devices(Am.Aml.boot(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, I.AmlOptions.default(), Hs.AmlMemHost.new(), ts, 50000000n), devs.list(text(rpn.arg(f, 1n)))))
    case _:
      IO.print(label ++ " " ++ case.fields(k, f))

def case.line(fs: List<&2, String>) -> IO(Unit):
  match fs:
    case Con{+kind, Con{label, rest}}:
      case.io(rpn.code(kinds(), kind, 0n), label, rest)
    case _:
      IO.pure(Unit, Unit{})

def cases(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        case.line(String.split(l, '|'))
        cases(t)

def lines.nl(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{+h, t}:
      U32.is_eq(h, 10)
    case Nil{}:
      False{}

# the lines of a file, by tail calls (a case file is too long for a
# structural split on the JavaScript lane's stack); nl: the next byte is a
# newline
def lines.go(xs: List<&2, U32>, nl: Bool, cur: List<&2, U32>, acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      List.reverse(&2, String, Con{B.to_string.fast(B.rev(cur)), acc})
    case Con{h, +t}:
      match nl:
        case True{}:
          lines.go(t, lines.nl(t), Nil{}, Con{B.to_string.fast(B.rev(cur)), acc})
        case False{}:
          lines.go(t, lines.nl(t), Con{h, cur}, acc)

def lines(+xs: List<&2, U32>) -> List<&2, String>:
  lines.go(xs, lines.nl(xs), Nil{}, Nil{})

def main() -> IO(Unit):
  do IO<Unit>:
    o : B.Octets <- read("cases.txt")
    cases(lines(B.Octets.to_list(o)))
