# bend-osdev-selinux: a CIL reader and a compiler for a subset of CIL.
#
# CIL, the Common Intermediate Language of SELinux policy, is a language of
# S-expressions (the CIL reference; the secilc(8) man page). SeCil.read turns
# the text into S-expressions; SeCil.compile turns the statements of the
# subset this package supports (README.md, "The CIL subset") into an
# SePolicy, with every name resolved and every attribute expanded. The
# binary policy format is not read: its exact layout is defined only by GPL
# code.
import Base
import ../bytes/bytes.bend as B
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C
import ./constraints.bend as K
import ./policy.bend as P

type SeSexp is Data:
  SeAtom{name: String}
  SeList{items: List<&2, SeSexp>}

# The reader: one pass over the bytes, a byte at a time, with a stack of the
# lists being built (each reversed)

type SeRdMode is Data:
  SeRdSpace{}
  SeRdAtom{acc: List<&2, Char>}
  SeRdString{acc: List<&2, Char>}
  SeRdComment{}

type SeRd is Data:
  SeRdOk{mode: SeRdMode, frames: List<&2, List<&2, SeSexp>>, line: Nat}
  SeRdErr{msg: String}

type SeCh is Data:
  SeChSpace{}
  SeChNewline{}
  SeChOpen{}
  SeChClose{}
  SeChSemi{}
  SeChQuote{}
  SeChOther{}

def SeCil.ch6(sp: Bool) -> SeCh:
  match sp:
    case True{}:
      SeChSpace{}
    case False{}:
      SeChOther{}

def SeCil.ch5(q: Bool, +b: U32) -> SeCh:
  match q:
    case True{}:
      SeChQuote{}
    case False{}:
      SeCil.ch6(Bool.or(U32.is_eq(b, 32), Bool.or(U32.is_eq(b, 9), U32.is_eq(b, 13))))

def SeCil.ch4(semi: Bool, +b: U32) -> SeCh:
  match semi:
    case True{}:
      SeChSemi{}
    case False{}:
      SeCil.ch5(U32.is_eq(b, 34), b)

def SeCil.ch3(nl: Bool, +b: U32) -> SeCh:
  match nl:
    case True{}:
      SeChNewline{}
    case False{}:
      SeCil.ch4(U32.is_eq(b, 59), b)

def SeCil.ch2(close: Bool, +b: U32) -> SeCh:
  match close:
    case True{}:
      SeChClose{}
    case False{}:
      SeCil.ch3(U32.is_eq(b, 10), b)

def SeCil.ch1(open: Bool, +b: U32) -> SeCh:
  match open:
    case True{}:
      SeChOpen{}
    case False{}:
      SeCil.ch2(U32.is_eq(b, 41), b)

def SeCil.chclass(+b: U32) -> SeCh:
  SeCil.ch1(U32.is_eq(b, 40), b)

def SeCil.atom_of(acc: List<&2, Char>) -> SeSexp:
  SeAtom{String.from_list(List.reverse(&2, Char, acc))}

def SeCil.rd.push(frames: List<&2, List<&2, SeSexp>>, e: SeSexp) -> List<&2, List<&2, SeSexp>>:
  match frames:
    case Nil{}:
      Nil{}
    case Con{f, rest}:
      Con{Con{e, f}, rest}

def SeCil.rd.close(frames: List<&2, List<&2, SeSexp>>, line: Nat) -> SeRd:
  match frames:
    case Nil{}:
      SeRdErr{"unbalanced )"}
    case Con{f, rest}:
      match rest:
        case Nil{}:
          SeRdErr{"line " ++ Nat.show(line) ++ ": unbalanced )"}
        case Con{g, more}:
          SeRdOk{SeRdSpace{}, Con{Con{SeList{List.reverse(&2, SeSexp, f)}, g}, more}, line}

# a byte outside an atom, a string and a comment
def SeCil.rd.space(cls: SeCh, b: U32, frames: List<&2, List<&2, SeSexp>>, line: Nat) -> SeRd:
  match cls:
    case SeChSpace{}:
      SeRdOk{SeRdSpace{}, frames, line}
    case SeChNewline{}:
      SeRdOk{SeRdSpace{}, frames, 1n+line}
    case SeChOpen{}:
      SeRdOk{SeRdSpace{}, Con{Nil{}, frames}, line}
    case SeChClose{}:
      SeCil.rd.close(frames, line)
    case SeChSemi{}:
      SeRdOk{SeRdComment{}, frames, line}
    case SeChQuote{}:
      SeRdOk{SeRdString{Nil{}}, frames, line}
    case SeChOther{}:
      SeRdOk{SeRdAtom{Con{Chr{b}, Nil{}}}, frames, line}

def SeCil.rd.comment(cls: SeCh, frames: List<&2, List<&2, SeSexp>>, line: Nat) -> SeRd:
  match cls:
    case SeChNewline{}:
      SeRdOk{SeRdSpace{}, frames, 1n+line}
    case o:
      SeRdOk{SeRdComment{}, frames, line}

def SeCil.rd.string(cls: SeCh, b: U32, acc: List<&2, Char>, frames: List<&2, List<&2, SeSexp>>, line: Nat) -> SeRd:
  match cls:
    case SeChQuote{}:
      SeRdOk{SeRdSpace{}, SeCil.rd.push(frames, SeCil.atom_of(acc)), line}
    case SeChNewline{}:
      SeRdOk{SeRdString{Con{Chr{b}, acc}}, frames, 1n+line}
    case o:
      SeRdOk{SeRdString{Con{Chr{b}, acc}}, frames, line}

def SeCil.rd.atom(cls: SeCh, b: U32, acc: List<&2, Char>, frames: List<&2, List<&2, SeSexp>>, line: Nat) -> SeRd:
  match cls:
    case SeChOther{}:
      SeRdOk{SeRdAtom{Con{Chr{b}, acc}}, frames, line}
    case o:
      SeCil.rd.space(o, b, SeCil.rd.push(frames, SeCil.atom_of(acc)), line)

def SeCil.rd.step(st: SeRd, +b: U32) -> SeRd:
  match st:
    case SeRdErr{m}:
      SeRdErr{m}
    case SeRdOk{mode, frames, line}:
      match mode:
        case SeRdSpace{}:
          SeCil.rd.space(SeCil.chclass(b), b, frames, line)
        case SeRdComment{}:
          SeCil.rd.comment(SeCil.chclass(b), frames, line)
        case SeRdString{acc}:
          SeCil.rd.string(SeCil.chclass(b), b, acc, frames, line)
        case SeRdAtom{acc}:
          SeCil.rd.atom(SeCil.chclass(b), b, acc, frames, line)

def SeCil.rd.go(xs: List<&2, U32>, st: SeRd) -> SeRd:
  match xs:
    case Nil{}:
      st
    case Con{b, t}:
      SeCil.rd.go(t, SeCil.rd.step(st, b))

def SeCil.rd.top(frames: List<&2, List<&2, SeSexp>>) -> Result<&2, &2, P.SeError, List<&2, SeSexp>>:
  match frames:
    case Nil{}:
      Fail{P.SeErrSyntax{"unbalanced )"}}
    case Con{f, rest}:
      match rest:
        case Nil{}:
          Done{List.reverse(&2, SeSexp, f)}
        case Con{g, more}:
          Fail{P.SeErrSyntax{"unbalanced ("}}

def SeCil.rd.finish(st: SeRd) -> Result<&2, &2, P.SeError, List<&2, SeSexp>>:
  match st:
    case SeRdErr{m}:
      Fail{P.SeErrSyntax{m}}
    case SeRdOk{mode, frames, line}:
      match mode:
        case SeRdString{acc}:
          Fail{P.SeErrSyntax{"unterminated string"}}
        case SeRdAtom{acc}:
          SeCil.rd.top(SeCil.rd.push(frames, SeCil.atom_of(acc)))
        case o:
          SeCil.rd.top(frames)

# the S-expressions of a text
def SeCil.read(o: B.Octets) -> Result<&2, &2, P.SeError, List<&2, SeSexp>>:
  SeCil.rd.finish(SeCil.rd.go(B.Octets.to_list(o), SeRdOk{SeRdSpace{}, Con{Nil{}, Nil{}}, 1n}))

def SeSexp.show.go(xs: List<&2, SeSexp>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match h:
        case SeAtom{n}:
          " " ++ n ++ SeSexp.show.go(t)
        case SeList{ys}:
          " (" ++ SeSexp.show.go(ys) ++ ")" ++ SeSexp.show.go(t)

# an S-expression as text (with a leading space)
def SeSexp.show(e: SeSexp) -> String:
  SeSexp.show.go(Con{e, Nil{}})

# Statements

type SeKw is Data:
  SeKAllow{}
  SeKAuditAllow{}
  SeKBoolean{}
  SeKBooleanIf{}
  SeKCategory{}
  SeKCategoryOrder{}
  SeKClass{}
  SeKClassCommon{}
  SeKCommon{}
  SeKConstrain{}
  SeKContext{}
  SeKDontAudit{}
  SeKIgnore{}
  SeKLevel{}
  SeKLevelRange{}
  SeKMls{}
  SeKMlsConstrain{}
  SeKNeverAllow{}
  SeKRole{}
  SeKRoleAllow{}
  SeKRoleTransition{}
  SeKRoleType{}
  SeKSensitivity{}
  SeKSensitivityCategory{}
  SeKSensitivityOrder{}
  SeKType{}
  SeKTypeAlias{}
  SeKTypeAliasActual{}
  SeKTypeAttribute{}
  SeKTypeAttributeSet{}
  SeKTypeChange{}
  SeKTypeMember{}
  SeKTypePermissive{}
  SeKTypeTransition{}
  SeKUser{}
  SeKUserLevel{}
  SeKUserRange{}
  SeKUserRole{}
  SeKUnsupported{}
  SeKUnknown{}

type SeKwEntry is Data:
  SeKwEntry{name: String, kw: SeKw}

# the statement keywords: those of the subset; labeling statements, which do
# not change access decisions, read and ignored; and the CIL statements not
# supported (an error)
def SeCil.keywords() -> List<&2, SeKwEntry>:
  [SeKwEntry{"class", SeKClass{}}, SeKwEntry{"common", SeKCommon{}}, SeKwEntry{"classcommon", SeKClassCommon{}}, SeKwEntry{"classorder", SeKIgnore{}}, SeKwEntry{"type", SeKType{}}, SeKwEntry{"typeattribute", SeKTypeAttribute{}}, SeKwEntry{"typealias", SeKTypeAlias{}}, SeKwEntry{"typealiasactual", SeKTypeAliasActual{}}, SeKwEntry{"typeattributeset", SeKTypeAttributeSet{}}, SeKwEntry{"typepermissive", SeKTypePermissive{}}, SeKwEntry{"role", SeKRole{}}, SeKwEntry{"roletype", SeKRoleType{}}, SeKwEntry{"roleallow", SeKRoleAllow{}}, SeKwEntry{"roletransition", SeKRoleTransition{}}, SeKwEntry{"user", SeKUser{}}, SeKwEntry{"userrole", SeKUserRole{}}, SeKwEntry{"userlevel", SeKUserLevel{}}, SeKwEntry{"userrange", SeKUserRange{}}, SeKwEntry{"sensitivity", SeKSensitivity{}}, SeKwEntry{"sensitivityorder", SeKSensitivityOrder{}}, SeKwEntry{"sensitivitycategory", SeKSensitivityCategory{}}, SeKwEntry{"category", SeKCategory{}}, SeKwEntry{"categoryorder", SeKCategoryOrder{}}, SeKwEntry{"level", SeKLevel{}}, SeKwEntry{"levelrange", SeKLevelRange{}}, SeKwEntry{"context", SeKContext{}}, SeKwEntry{"mls", SeKMls{}}, SeKwEntry{"handleunknown", SeKIgnore{}}, SeKwEntry{"policycap", SeKIgnore{}}, SeKwEntry{"sid", SeKIgnore{}}, SeKwEntry{"sidorder", SeKIgnore{}}, SeKwEntry{"sidcontext", SeKIgnore{}}, SeKwEntry{"boolean", SeKBoolean{}}, SeKwEntry{"booleanif", SeKBooleanIf{}}, SeKwEntry{"allow", SeKAllow{}}, SeKwEntry{"auditallow", SeKAuditAllow{}}, SeKwEntry{"dontaudit", SeKDontAudit{}}, SeKwEntry{"neverallow", SeKNeverAllow{}}, SeKwEntry{"typetransition", SeKTypeTransition{}}, SeKwEntry{"typechange", SeKTypeChange{}}, SeKwEntry{"typemember", SeKTypeMember{}}, SeKwEntry{"constrain", SeKConstrain{}}, SeKwEntry{"mlsconstrain", SeKMlsConstrain{}}, SeKwEntry{"filecon", SeKIgnore{}}, SeKwEntry{"fsuse", SeKIgnore{}}, SeKwEntry{"genfscon", SeKIgnore{}}, SeKwEntry{"portcon", SeKIgnore{}}, SeKwEntry{"nodecon", SeKIgnore{}}, SeKwEntry{"netifcon", SeKIgnore{}}, SeKwEntry{"ioportcon", SeKIgnore{}}, SeKwEntry{"iomemcon", SeKIgnore{}}, SeKwEntry{"pirqcon", SeKIgnore{}}, SeKwEntry{"pcidevicecon", SeKIgnore{}}, SeKwEntry{"devicetreecon", SeKIgnore{}}, SeKwEntry{"ibpkeycon", SeKIgnore{}}, SeKwEntry{"ibendportcon", SeKIgnore{}}, SeKwEntry{"selinuxuser", SeKIgnore{}}, SeKwEntry{"selinuxuserdefault", SeKIgnore{}}, SeKwEntry{"userprefix", SeKIgnore{}}, SeKwEntry{"block", SeKUnsupported{}}, SeKwEntry{"blockinherit", SeKUnsupported{}}, SeKwEntry{"blockabstract", SeKUnsupported{}}, SeKwEntry{"in", SeKUnsupported{}}, SeKwEntry{"macro", SeKUnsupported{}}, SeKwEntry{"call", SeKUnsupported{}}, SeKwEntry{"optional", SeKUnsupported{}}, SeKwEntry{"tunable", SeKUnsupported{}}, SeKwEntry{"tunableif", SeKUnsupported{}}, SeKwEntry{"classpermission", SeKUnsupported{}}, SeKwEntry{"classpermissionset", SeKUnsupported{}}, SeKwEntry{"classmap", SeKUnsupported{}}, SeKwEntry{"classmapping", SeKUnsupported{}}, SeKwEntry{"roleattribute", SeKUnsupported{}}, SeKwEntry{"roleattributeset", SeKUnsupported{}}, SeKwEntry{"userattribute", SeKUnsupported{}}, SeKwEntry{"userattributeset", SeKUnsupported{}}, SeKwEntry{"typebounds", SeKUnsupported{}}, SeKwEntry{"rolebounds", SeKUnsupported{}}, SeKwEntry{"userbounds", SeKUnsupported{}}, SeKwEntry{"rangetransition", SeKUnsupported{}}, SeKwEntry{"validatetrans", SeKUnsupported{}}, SeKwEntry{"mlsvalidatetrans", SeKUnsupported{}}, SeKwEntry{"allowx", SeKUnsupported{}}, SeKwEntry{"auditallowx", SeKUnsupported{}}, SeKwEntry{"dontauditx", SeKUnsupported{}}, SeKwEntry{"neverallowx", SeKUnsupported{}}, SeKwEntry{"permissionx", SeKUnsupported{}}, SeKwEntry{"defaultuser", SeKUnsupported{}}, SeKwEntry{"defaultrole", SeKUnsupported{}}, SeKwEntry{"defaulttype", SeKUnsupported{}}, SeKwEntry{"defaultrange", SeKUnsupported{}}, SeKwEntry{"expandtypeattribute", SeKUnsupported{}}, SeKwEntry{"categoryalias", SeKUnsupported{}}, SeKwEntry{"categoryaliasactual", SeKUnsupported{}}, SeKwEntry{"sensitivityalias", SeKUnsupported{}}, SeKwEntry{"sensitivityaliasactual", SeKUnsupported{}}, SeKwEntry{"deny", SeKUnsupported{}}]

def SeCil.kw.hit(b: Bool, k: SeKw, rest: SeKw) -> SeKw:
  match b:
    case True{}:
      k
    case False{}:
      rest

def SeCil.kw.go(xs: List<&2, SeKwEntry>, +name: String) -> SeKw:
  match xs:
    case Nil{}:
      SeKUnknown{}
    case Con{e, t}:
      match e:
        case SeKwEntry{n, k}:
          SeCil.kw.hit(String.eq(n, name), k, SeCil.kw.go(t, name))

def SeCil.kw(+name: String) -> SeKw:
  SeCil.kw.go(SeCil.keywords(), name)

def SeKw.code(k: SeKw) -> Nat:
  match k:
    case SeKAllow{}:
      0n
    case SeKAuditAllow{}:
      1n
    case SeKBoolean{}:
      2n
    case SeKBooleanIf{}:
      3n
    case SeKCategory{}:
      4n
    case SeKCategoryOrder{}:
      5n
    case SeKClass{}:
      6n
    case SeKClassCommon{}:
      7n
    case SeKCommon{}:
      8n
    case SeKConstrain{}:
      9n
    case SeKContext{}:
      10n
    case SeKDontAudit{}:
      11n
    case SeKIgnore{}:
      12n
    case SeKLevel{}:
      13n
    case SeKLevelRange{}:
      14n
    case SeKMls{}:
      15n
    case SeKMlsConstrain{}:
      16n
    case SeKNeverAllow{}:
      17n
    case SeKRole{}:
      18n
    case SeKRoleAllow{}:
      19n
    case SeKRoleTransition{}:
      20n
    case SeKRoleType{}:
      21n
    case SeKSensitivity{}:
      22n
    case SeKSensitivityCategory{}:
      23n
    case SeKSensitivityOrder{}:
      24n
    case SeKType{}:
      25n
    case SeKTypeAlias{}:
      26n
    case SeKTypeAliasActual{}:
      27n
    case SeKTypeAttribute{}:
      28n
    case SeKTypeAttributeSet{}:
      29n
    case SeKTypeChange{}:
      30n
    case SeKTypeMember{}:
      31n
    case SeKTypePermissive{}:
      32n
    case SeKTypeTransition{}:
      33n
    case SeKUser{}:
      34n
    case SeKUserLevel{}:
      35n
    case SeKUserRange{}:
      36n
    case SeKUserRole{}:
      37n
    case SeKUnsupported{}:
      38n
    case SeKUnknown{}:
      39n

type SeStmt is Data:
  SeStmt{kw: SeKw, name: String, args: List<&2, SeSexp>}

def SeStmt.kw(x: SeStmt) -> SeKw:
  match x:
    case SeStmt{v, _, _}:
      v

def SeStmt.name(x: SeStmt) -> String:
  match x:
    case SeStmt{_, v, _}:
      v

def SeStmt.args(x: SeStmt) -> List<&2, SeSexp>:
  match x:
    case SeStmt{_, _, v}:
      v

def SeCil.stmt(e: SeSexp) -> SeStmt:
  match e:
    case SeAtom{n}:
      SeStmt{SeKUnknown{}, n, Nil{}}
    case SeList{xs}:
      match xs:
        case Nil{}:
          SeStmt{SeKUnknown{}, "()", Nil{}}
        case Con{h, t}:
          match h:
            case SeAtom{+n}:
              SeStmt{SeCil.kw(n), n, t}
            case SeList{ys}:
              SeStmt{SeKUnknown{}, "(", Nil{}}

def SeCil.stmts(xs: List<&2, SeSexp>) -> List<&2, SeStmt>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{SeCil.stmt(h), SeCil.stmts(t)}

def SeCil.select.put(b: Bool, s: SeStmt, rest: List<&2, SeStmt>) -> List<&2, SeStmt>:
  match b:
    case True{}:
      Con{s, rest}
    case False{}:
      rest

# the statements with one keyword, in order
def SeCil.select(xs: List<&2, SeStmt>, +k: SeKw) -> List<&2, SeStmt>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      SeCil.select.put(Nat.is_eq(SeKw.code(SeStmt.kw(s)), SeKw.code(k)), s, SeCil.select(t, k))

# the statements with either of two keywords, in order
def SeCil.select2(xs: List<&2, SeStmt>, +k1: SeKw, +k2: SeKw) -> List<&2, SeStmt>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      SeCil.select.put(Bool.or(Nat.is_eq(SeKw.code(SeStmt.kw(s)), SeKw.code(k1)), Nat.is_eq(SeKw.code(SeStmt.kw(s)), SeKw.code(k2))), s, SeCil.select2(t, k1, k2))

# Result helpers

def SeCil.bad(name: String) -> P.SeError:
  P.SeErrBadStatement{name}

def SeCil.atoms(xs: List<&2, SeSexp>, +what: String) -> Result<&2, &2, P.SeError, List<&2, String>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{h, t}:
      match h:
        case SeAtom{n}:
          do Result<&2, &2, P.SeError, List<&2, String>>:
            r : List<&2, String> <- SeCil.atoms(t, what)
            return Con{n, r}
        case SeList{ys}:
          Fail{SeCil.bad(what)}

# (kw name)
def SeCil.arg1(s: SeStmt) -> Result<&2, &2, P.SeError, String>:
  match s:
    case SeStmt{k, n, args}:
      match args:
        case Con{SeAtom{a}, Nil{}}:
          Done{a}
        case o:
          Fail{SeCil.bad(n)}

# (kw name name)
type SeTwoNames is Data:
  SeTwoNames{a: String, b: String}

def SeTwoNames.a(x: SeTwoNames) -> String:
  match x:
    case SeTwoNames{v, _}:
      v

def SeTwoNames.b(x: SeTwoNames) -> String:
  match x:
    case SeTwoNames{_, v}:
      v

def SeCil.arg2(s: SeStmt) -> Result<&2, &2, P.SeError, SeTwoNames>:
  match s:
    case SeStmt{k, n, args}:
      match args:
        case Con{SeAtom{a}, Con{SeAtom{b}, Nil{}}}:
          Done{SeTwoNames{a, b}}
        case o:
          Fail{SeCil.bad(n)}

# (kw name expr)
type SeNamed is Data:
  SeNamed{name: String, e: SeSexp}

def SeNamed.name(x: SeNamed) -> String:
  match x:
    case SeNamed{v, _}:
      v

def SeNamed.e(x: SeNamed) -> SeSexp:
  match x:
    case SeNamed{_, v}:
      v

def SeCil.arg_named(s: SeStmt) -> Result<&2, &2, P.SeError, SeNamed>:
  match s:
    case SeStmt{k, n, args}:
      match args:
        case Con{SeAtom{a}, Con{e, Nil{}}}:
          Done{SeNamed{a, e}}
        case o:
          Fail{SeCil.bad(n)}

# (kw (name ...))
def SeCil.arg_list(s: SeStmt) -> Result<&2, &2, P.SeError, List<&2, String>>:
  match s:
    case SeStmt{k, +n, args}:
      match args:
        case Con{SeList{xs}, Nil{}}:
          SeCil.atoms(xs, n)
        case o:
          Fail{SeCil.bad(n)}

def SeCil.each1(xs: List<&2, SeStmt>) -> Result<&2, &2, P.SeError, List<&2, String>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{s, t}:
      do Result<&2, &2, P.SeError, List<&2, String>>:
        a : String <- SeCil.arg1(s)
        r : List<&2, String> <- SeCil.each1(t)
        return Con{a, r}

def SeCil.each2(xs: List<&2, SeStmt>) -> Result<&2, &2, P.SeError, List<&2, SeTwoNames>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{s, t}:
      do Result<&2, &2, P.SeError, List<&2, SeTwoNames>>:
        a : SeTwoNames <- SeCil.arg2(s)
        r : List<&2, SeTwoNames> <- SeCil.each2(t)
        return Con{a, r}

def SeCil.each_named(xs: List<&2, SeStmt>) -> Result<&2, &2, P.SeError, List<&2, SeNamed>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{s, t}:
      do Result<&2, &2, P.SeError, List<&2, SeNamed>>:
        a : SeNamed <- SeCil.arg_named(s)
        r : List<&2, SeNamed> <- SeCil.each_named(t)
        return Con{a, r}

# the list of the first statement with keyword k, or none
def SeCil.order(xs: List<&2, SeStmt>) -> Result<&2, &2, P.SeError, List<&2, String>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{s, t}:
      SeCil.arg_list(s)

# The symbol table

def SeCil.declare.go(has: Bool, m: Map<&2, P.SeSym>, key: String, v: P.SeSym) -> Result<&2, &2, P.SeError, Map<&2, P.SeSym>>:
  match has:
    case True{}:
      Fail{P.SeErrDuplicate{key}}
    case False{}:
      Done{Map.set(&2, P.SeSym, m, key, v)}

def SeCil.declare(+m: Map<&2, P.SeSym>, +key: String, v: P.SeSym) -> Result<&2, &2, P.SeError, Map<&2, P.SeSym>>:
  SeCil.declare.go(Pair.snd(Map<&2, P.SeSym>, Bool, Map.has(&2, P.SeSym, m, key)), m, key, v)

def SeCil.declare_all(xs: List<&2, String>, +prefix: String, +i: Nat, r: Result<&2, &2, P.SeError, Map<&2, P.SeSym>>) -> Result<&2, &2, P.SeError, Map<&2, P.SeSym>>:
  match xs:
    case Nil{}:
      r
    case Con{n, t}:
      SeCil.declare_all(t, prefix, 1n+i, Result.bind(&2, &2, P.SeError, Map<&2, P.SeSym>, Map<&2, P.SeSym>, r, m => SeCil.declare(m, prefix ++ n, P.SeSymId{i})))

def SeCil.lookup(+m: Map<&2, P.SeSym>, +key: String) -> P.SeSym:
  Pair.snd(Map<&2, P.SeSym>, P.SeSym, Map.get(P.SeSym, P.SeSymNone{}, m, key))

def SeCil.id.go(s: P.SeSym, key: String) -> Result<&2, &2, P.SeError, Nat>:
  match s:
    case P.SeSymNone{}:
      Fail{P.SeErrUndeclared{key}}
    case P.SeSymId{i}:
      Done{i}
    case P.SeSymAttr{i}:
      Done{i}

# the number of a declared name
def SeCil.id(+m: Map<&2, P.SeSym>, +key: String) -> Result<&2, &2, P.SeError, Nat>:
  SeCil.id.go(SeCil.lookup(m, key), key)

# a type, not an attribute
def SeCil.type_id.go(s: P.SeSym, key: String) -> Result<&2, &2, P.SeError, Nat>:
  match s:
    case P.SeSymId{i}:
      Done{i}
    case o:
      Fail{P.SeErrUndeclared{key}}

def SeCil.type_id(+m: Map<&2, P.SeSym>, name: String) -> Result<&2, &2, P.SeError, Nat>:
  +key = "t:" ++ name
  SeCil.type_id.go(SeCil.lookup(m, key), key)

# The compile environment: names, the named levels, ranges and contexts, the
# type and attribute sets, the classes

type SeEnv is Data:
  SeEnv{syms: Map<&2, P.SeSym>, defs: Map<&2, SeSexp>, tsets: List<&2, List<&2, Bool>>, real: List<&2, Bool>, classes: List<&2, P.SeClass>, ncats: Nat, nroles: Nat, nusers: Nat}

def SeEnv.syms(x: SeEnv) -> Map<&2, P.SeSym>:
  match x:
    case SeEnv{v, _, _, _, _, _, _, _}:
      v

def SeEnv.defs(x: SeEnv) -> Map<&2, SeSexp>:
  match x:
    case SeEnv{_, v, _, _, _, _, _, _}:
      v

def SeEnv.tsets(x: SeEnv) -> List<&2, List<&2, Bool>>:
  match x:
    case SeEnv{_, _, v, _, _, _, _, _}:
      v

def SeEnv.real(x: SeEnv) -> List<&2, Bool>:
  match x:
    case SeEnv{_, _, _, v, _, _, _, _}:
      v

def SeEnv.classes(x: SeEnv) -> List<&2, P.SeClass>:
  match x:
    case SeEnv{_, _, _, _, v, _, _, _}:
      v

def SeEnv.ncats(x: SeEnv) -> Nat:
  match x:
    case SeEnv{_, _, _, _, _, v, _, _}:
      v

def SeEnv.nroles(x: SeEnv) -> Nat:
  match x:
    case SeEnv{_, _, _, _, _, _, v, _}:
      v

def SeEnv.nusers(x: SeEnv) -> Nat:
  match x:
    case SeEnv{_, _, _, _, _, _, _, v}:
      v

# Expressions: sets of types, permissions, categories, roles and users

type SeOp is Data:
  SeOpAnd{}
  SeOpOr{}
  SeOpXor{}
  SeOpNot{}
  SeOpAll{}
  SeOpRange{}
  SeOpEq{}
  SeOpNeq{}
  SeOpDom{}
  SeOpDomby{}
  SeOpIncomp{}
  SeOpName{}

type SeOpEntry is Data:
  SeOpEntry{name: String, op: SeOp}

def SeCil.op.hit(b: Bool, k: SeOp, rest: SeOp) -> SeOp:
  match b:
    case True{}:
      k
    case False{}:
      rest

def SeCil.op.go(xs: List<&2, SeOpEntry>, +name: String) -> SeOp:
  match xs:
    case Nil{}:
      SeOpName{}
    case Con{e, t}:
      match e:
        case SeOpEntry{n, k}:
          SeCil.op.hit(String.eq(n, name), k, SeCil.op.go(t, name))

def SeCil.op(+name: String) -> SeOp:
  SeCil.op.go([SeOpEntry{"and", SeOpAnd{}}, SeOpEntry{"or", SeOpOr{}}, SeOpEntry{"xor", SeOpXor{}}, SeOpEntry{"not", SeOpNot{}}, SeOpEntry{"all", SeOpAll{}}, SeOpEntry{"range", SeOpRange{}}, SeOpEntry{"eq", SeOpEq{}}, SeOpEntry{"neq", SeOpNeq{}}, SeOpEntry{"dom", SeOpDom{}}, SeOpEntry{"domby", SeOpDomby{}}, SeOpEntry{"incomp", SeOpIncomp{}}], name)

type SeSetKind is Data:
  SeSetTypes{}
  SeSetPerms{cls: String}
  SeSetCats{}
  SeSetRoles{}
  SeSetUsers{}

def SeCil.nth_bits(xs: List<&2, List<&2, Bool>>, i: Nat) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          SeCil.nth_bits(t, p)

def SeCil.class_by_name.hit(b: Bool, x: List<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      x
    case False{}:
      rest

def SeCil.class_by_name(xs: List<&2, P.SeClass>, +name: String) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      match c:
        case P.SeClass{n, ps}:
          SeCil.class_by_name.hit(String.eq(n, name), ps, SeCil.class_by_name(t, name))

def SeCil.set.universe(kind: SeSetKind, +env: SeEnv) -> List<&2, Bool>:
  match kind:
    case SeSetTypes{}:
      SeEnv.real(env)
    case SeSetPerms{c}:
      Bits.SeBits.full(List.length(&2, String, SeCil.class_by_name(SeEnv.classes(env), c)))
    case SeSetCats{}:
      Bits.SeBits.full(SeEnv.ncats(env))
    case SeSetRoles{}:
      Bits.SeBits.full(SeEnv.nroles(env))
    case SeSetUsers{}:
      Bits.SeBits.full(SeEnv.nusers(env))

def SeCil.single(r: Result<&2, &2, P.SeError, Nat>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{i}:
      Done{Bits.SeBits.single(i)}

def SeCil.set.type_sym(s: P.SeSym, +tsets: List<&2, List<&2, Bool>>, key: String) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match s:
    case P.SeSymNone{}:
      Fail{P.SeErrUndeclared{key}}
    case P.SeSymId{i}:
      Done{SeCil.nth_bits(tsets, i)}
    case P.SeSymAttr{i}:
      Done{SeCil.nth_bits(tsets, i)}

def SeCil.set.name(kind: SeSetKind, +env: SeEnv, n: String) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match kind:
    case SeSetTypes{}:
      +key = "t:" ++ n
      SeCil.set.type_sym(SeCil.lookup(SeEnv.syms(env), key), SeEnv.tsets(env), key)
    case SeSetPerms{c}:
      SeCil.single(SeCil.id(SeEnv.syms(env), "p:" ++ c ++ ":" ++ n))
    case SeSetCats{}:
      SeCil.single(SeCil.id(SeEnv.syms(env), "g:" ++ n))
    case SeSetRoles{}:
      SeCil.single(SeCil.id(SeEnv.syms(env), "r:" ++ n))
    case SeSetUsers{}:
      SeCil.single(SeCil.id(SeEnv.syms(env), "u:" ++ n))

def SeCil.set.atom.go(all: Bool, kind: SeSetKind, +env: SeEnv, n: String) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match all:
    case True{}:
      Done{SeCil.set.universe(kind, env)}
    case False{}:
      SeCil.set.name(kind, env, n)

def SeCil.set.atom(kind: SeSetKind, +env: SeEnv, +n: String) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  SeCil.set.atom.go(String.eq(n, "all"), kind, env, n)

type SeTwo<-A: Data> is Data:
  SeTwo{a: A, b: A}

def SeTwo.a(-A: Data, x: SeTwo<A>) -> A:
  match x:
    case SeTwo{v, _}:
      v

def SeTwo.b(-A: Data, x: SeTwo<A>) -> A:
  match x:
    case SeTwo{_, v}:
      v

def SeCil.two(-A: Data, rs: List<&2, Result<&2, &2, P.SeError, A>>, what: String) -> Result<&2, &2, P.SeError, SeTwo<A>>:
  match rs:
    case Con{r1, Con{r2, Nil{}}}:
      do Result<&2, &2, P.SeError, SeTwo<A>>:
        a : A <- r1
        b : A <- r2
        return SeTwo{a, b}
    case o:
      Fail{SeCil.bad(what)}

def SeCil.one(-A: Data, rs: List<&2, Result<&2, &2, P.SeError, A>>, what: String) -> Result<&2, &2, P.SeError, A>:
  match rs:
    case Con{r1, Nil{}}:
      r1
    case o:
      Fail{SeCil.bad(what)}

def SeCil.union(rs: List<&2, Result<&2, &2, P.SeError, List<&2, Bool>>>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match rs:
    case Nil{}:
      Done{Nil{}}
    case Con{r, t}:
      do Result<&2, &2, P.SeError, List<&2, Bool>>:
        a : List<&2, Bool> <- r
        b : List<&2, Bool> <- SeCil.union(t)
        return Bits.SeBits.or(a, b)

def SeCil.first_index(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      h

# {lo, ..., hi}, from the sets {lo} and {hi}
def SeCil.range_bits(t: SeTwo<List<&2, Bool>>) -> List<&2, Bool>:
  match t:
    case SeTwo{a, b}:
      Bits.SeBits.andnot(Bits.SeBits.full(1n+SeCil.first_index(Bits.SeBits.to_list(b))), Bits.SeBits.full(SeCil.first_index(Bits.SeBits.to_list(a))))

def SeCil.set.bin(op: SeOp, +t: SeTwo<List<&2, Bool>>) -> List<&2, Bool>:
  match op:
    case SeOpAnd{}:
      Bits.SeBits.and(SeTwo.a(List<&2, Bool>, t), SeTwo.b(List<&2, Bool>, t))
    case SeOpXor{}:
      Bits.SeBits.xor(SeTwo.a(List<&2, Bool>, t), SeTwo.b(List<&2, Bool>, t))
    case o:
      Bits.SeBits.or(SeTwo.a(List<&2, Bool>, t), SeTwo.b(List<&2, Bool>, t))

def SeCil.set.not(u: List<&2, Bool>, r: Result<&2, &2, P.SeError, List<&2, Bool>>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{Bits.SeBits.andnot(u, a)}

def SeCil.set.map2(op: SeOp, r: Result<&2, &2, P.SeError, SeTwo<List<&2, Bool>>>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Done{SeCil.set.bin(op, t)}

def SeCil.set.range(r: Result<&2, &2, P.SeError, SeTwo<List<&2, Bool>>>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Done{SeCil.range_bits(t)}

def SeCil.set.or2(a: Result<&2, &2, P.SeError, List<&2, Bool>>, b: Result<&2, &2, P.SeError, List<&2, Bool>>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  do Result<&2, &2, P.SeError, List<&2, Bool>>:
    x : List<&2, Bool> <- a
    y : List<&2, Bool> <- b
    return Bits.SeBits.or(x, y)

# a list headed by o: an operator applied to the values of the rest, or, for
# a plain list of names, the union of o and the rest
def SeCil.set.apply(op: SeOp, +o: String, kind: SeSetKind, +env: SeEnv, rs: List<&2, Result<&2, &2, P.SeError, List<&2, Bool>>>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match op:
    case SeOpAnd{}:
      SeCil.set.map2(SeOpAnd{}, SeCil.two(List<&2, Bool>, rs, o))
    case SeOpXor{}:
      SeCil.set.map2(SeOpXor{}, SeCil.two(List<&2, Bool>, rs, o))
    case SeOpOr{}:
      SeCil.union(rs)
    case SeOpNot{}:
      SeCil.set.not(SeCil.set.universe(kind, env), SeCil.one(List<&2, Bool>, rs, o))
    case SeOpAll{}:
      SeCil.set.or2(Done{SeCil.set.universe(kind, env)}, SeCil.union(rs))
    case SeOpRange{}:
      SeCil.set.range(SeCil.two(List<&2, Bool>, rs, o))
    case SeOpName{}:
      SeCil.set.or2(SeCil.set.name(kind, env, o), SeCil.union(rs))
    case other:
      Fail{SeCil.bad(o)}

# the value of each item of a list
def SeCil.set.vals(xs: List<&2, SeSexp>, +kind: SeSetKind, +env: SeEnv) -> List<&2, Result<&2, &2, P.SeError, List<&2, Bool>>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case SeAtom{n}:
          Con{SeCil.set.atom(kind, env, n), SeCil.set.vals(t, kind, env)}
        case SeList{ys}:
          match ys:
            case Nil{}:
              Con{Done{Nil{}}, SeCil.set.vals(t, kind, env)}
            case Con{y, rest}:
              match y:
                case SeAtom{+o}:
                  Con{SeCil.set.apply(SeCil.op(o), o, kind, env, SeCil.set.vals(rest, kind, env)), SeCil.set.vals(t, kind, env)}
                case SeList{zs}:
                  Con{Fail{SeCil.bad("set expression")}, SeCil.set.vals(t, kind, env)}

def SeCil.set.eval(e: SeSexp, +kind: SeSetKind, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  SeCil.one(List<&2, Bool>, SeCil.set.vals(Con{e, Nil{}}, kind, env), "set expression")

# Conditions over booleans (booleanif)

def SeCil.bool.var(r: Result<&2, &2, P.SeError, Nat>) -> Result<&2, &2, P.SeError, P.SeBexpr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{i}:
      Done{P.SeBVar{i}}

def SeCil.bool.bin(r: Result<&2, &2, P.SeError, SeTwo<P.SeBexpr>>, op: SeOp, +o: String) -> Result<&2, &2, P.SeError, P.SeBexpr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      match t:
        case SeTwo{a, b}:
          match op:
            case SeOpAnd{}:
              Done{P.SeBAnd{a, b}}
            case SeOpOr{}:
              Done{P.SeBOr{a, b}}
            case SeOpXor{}:
              Done{P.SeBXor{a, b}}
            case SeOpEq{}:
              Done{P.SeBEq{a, b}}
            case SeOpNeq{}:
              Done{P.SeBNeq{a, b}}
            case other:
              Fail{SeCil.bad(o)}

def SeCil.bool.not(r: Result<&2, &2, P.SeError, P.SeBexpr>) -> Result<&2, &2, P.SeError, P.SeBexpr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{P.SeBNot{a}}

def SeCil.bool.apply(op: SeOp, +o: String, rs: List<&2, Result<&2, &2, P.SeError, P.SeBexpr>>) -> Result<&2, &2, P.SeError, P.SeBexpr>:
  match op:
    case SeOpNot{}:
      SeCil.bool.not(SeCil.one(P.SeBexpr, rs, o))
    case other:
      SeCil.bool.bin(SeCil.two(P.SeBexpr, rs, o), other, o)

def SeCil.bool.vals(xs: List<&2, SeSexp>, +syms: Map<&2, P.SeSym>) -> List<&2, Result<&2, &2, P.SeError, P.SeBexpr>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case SeAtom{n}:
          Con{SeCil.bool.var(SeCil.id(syms, "b:" ++ n)), SeCil.bool.vals(t, syms)}
        case SeList{ys}:
          match ys:
            case Con{SeAtom{+o}, rest}:
              Con{SeCil.bool.apply(SeCil.op(o), o, SeCil.bool.vals(rest, syms)), SeCil.bool.vals(t, syms)}
            case other:
              Con{Fail{SeCil.bad("boolean expression")}, SeCil.bool.vals(t, syms)}

def SeCil.bool.eval(e: SeSexp, +syms: Map<&2, P.SeSym>) -> Result<&2, &2, P.SeError, P.SeBexpr>:
  SeCil.one(P.SeBexpr, SeCil.bool.vals(Con{e, Nil{}}, syms), "boolean expression")

# Constraint expressions

# u1 u2 r1 r2 t1 t2 l1 l2 h1 h2
type SeSel is Data:
  SeSelAttr{attr: K.SeCattr, side: K.SeCside}
  SeSelLevel{l: K.SeLsel}
  SeSelNone{}

type SeSelEntry is Data:
  SeSelEntry{name: String, sel: SeSel}

def SeCil.sel.hit(b: Bool, k: SeSel, rest: SeSel) -> SeSel:
  match b:
    case True{}:
      k
    case False{}:
      rest

def SeCil.sel.go(xs: List<&2, SeSelEntry>, +name: String) -> SeSel:
  match xs:
    case Nil{}:
      SeSelNone{}
    case Con{e, t}:
      match e:
        case SeSelEntry{n, k}:
          SeCil.sel.hit(String.eq(n, name), k, SeCil.sel.go(t, name))

def SeCil.sel(+name: String) -> SeSel:
  SeCil.sel.go([SeSelEntry{"u1", SeSelAttr{K.SeCUser{}, K.SeCSource{}}}, SeSelEntry{"u2", SeSelAttr{K.SeCUser{}, K.SeCTarget{}}}, SeSelEntry{"r1", SeSelAttr{K.SeCRole{}, K.SeCSource{}}}, SeSelEntry{"r2", SeSelAttr{K.SeCRole{}, K.SeCTarget{}}}, SeSelEntry{"t1", SeSelAttr{K.SeCType{}, K.SeCSource{}}}, SeSelEntry{"t2", SeSelAttr{K.SeCType{}, K.SeCTarget{}}}, SeSelEntry{"l1", SeSelLevel{K.SeL1{}}}, SeSelEntry{"h1", SeSelLevel{K.SeH1{}}}, SeSelEntry{"l2", SeSelLevel{K.SeL2{}}}, SeSelEntry{"h2", SeSelLevel{K.SeH2{}}}], name)


# eq and neq compare users, roles or types; all five compare levels
def SeCil.cons.eqop(op: SeOp) -> Maybe<&2, Bool>:
  match op:
    case SeOpEq{}:
      Some{True{}}
    case SeOpNeq{}:
      Some{False{}}
    case other:
      None{}

def SeCil.cons.lop(op: SeOp) -> Maybe<&2, K.SeLop>:
  match op:
    case SeOpEq{}:
      Some{K.SeLEq{}}
    case SeOpNeq{}:
      Some{K.SeLNeq{}}
    case SeOpDom{}:
      Some{K.SeLDom{}}
    case SeOpDomby{}:
      Some{K.SeLDomby{}}
    case SeOpIncomp{}:
      Some{K.SeLIncomp{}}
    case other:
      None{}

def SeCattr.code(a: K.SeCattr) -> Nat:
  match a:
    case K.SeCUser{}:
      0n
    case K.SeCRole{}:
      1n
    case K.SeCType{}:
      2n

def SeCattr.kind(a: K.SeCattr) -> SeSetKind:
  match a:
    case K.SeCUser{}:
      SeSetUsers{}
    case K.SeCRole{}:
      SeSetRoles{}
    case K.SeCType{}:
      SeSetTypes{}

def SeCside.is_source(s: K.SeCside) -> Bool:
  match s:
    case K.SeCSource{}:
      True{}
    case K.SeCTarget{}:
      False{}

# y is the partner of x: u2 for u1, r2 for r1, t2 for t1
def SeCil.cons.partner(attr: K.SeCattr, side: K.SeCside, y: SeSel) -> Bool:
  match y:
    case SeSelAttr{a2, s2}:
      Bool.and(Nat.is_eq(SeCattr.code(attr), SeCattr.code(a2)), Bool.and(SeCside.is_source(side), Bool.not(SeCside.is_source(s2))))
    case other:
      False{}

def SeCil.cons.y_sel(y: SeSexp) -> SeSel:
  match y:
    case SeAtom{+n}:
      SeCil.sel(n)
    case SeList{ys}:
      SeSelNone{}

def SeCil.cons.names(attr: K.SeCattr, side: K.SeCside, eq: Bool, r: Result<&2, &2, P.SeError, List<&2, Bool>>) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{set}:
      Done{K.SeCSet{attr, side, eq, set}}

def SeCil.cons.pair.go(pair: Bool, +attr: K.SeCattr, side: K.SeCside, eq: Bool, y: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match pair:
    case True{}:
      Done{K.SeCPair{attr, eq}}
    case False{}:
      SeCil.cons.names(attr, side, eq, SeCil.set.eval(y, SeCattr.kind(attr), env))

def SeCil.cons.attr(eq: Maybe<&2, Bool>, +attr: K.SeCattr, +side: K.SeCside, +y: SeSexp, +env: SeEnv, o: String) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match eq:
    case None{}:
      Fail{P.SeErrUnsupported{o}}
    case Some{e}:
      SeCil.cons.pair.go(SeCil.cons.partner(attr, side, SeCil.cons.y_sel(y)), attr, side, e, y, env)

def SeCil.cons.level(lop: Maybe<&2, K.SeLop>, l: K.SeLsel, ysel: SeSel, o: String) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match lop:
    case None{}:
      Fail{SeCil.bad(o)}
    case Some{op}:
      match ysel:
        case SeSelLevel{r}:
          Done{K.SeCLevel{op, l, r}}
        case other:
          Fail{SeCil.bad(o)}

def SeCil.cons.leaf.go(xsel: SeSel, +op: SeOp, +o: String, +y: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match xsel:
    case SeSelAttr{attr, side}:
      SeCil.cons.attr(SeCil.cons.eqop(op), attr, side, y, env, o)
    case SeSelLevel{l}:
      SeCil.cons.level(SeCil.cons.lop(op), l, SeCil.cons.y_sel(y), o)
    case SeSelNone{}:
      Fail{SeCil.bad(o)}

def SeCil.cons.leaf(op: SeOp, +o: String, args: List<&2, SeSexp>, +env: SeEnv) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match args:
    case Con{SeAtom{+x}, Con{y, Nil{}}}:
      SeCil.cons.leaf.go(SeCil.sel(x), op, o, y, env)
    case other:
      Fail{SeCil.bad(o)}

def SeCil.cons.bin(r: Result<&2, &2, P.SeError, SeTwo<K.SeCexpr>>, op: SeOp) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      match t:
        case SeTwo{a, b}:
          match op:
            case SeOpAnd{}:
              Done{K.SeCAnd{a, b}}
            case other:
              Done{K.SeCOr{a, b}}

def SeCil.cons.not(r: Result<&2, &2, P.SeError, K.SeCexpr>) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{K.SeCNot{a}}

def SeCil.cons.apply(op: SeOp, +o: String, args: List<&2, SeSexp>, +env: SeEnv, rs: List<&2, Result<&2, &2, P.SeError, K.SeCexpr>>) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  match op:
    case SeOpAnd{}:
      SeCil.cons.bin(SeCil.two(K.SeCexpr, rs, o), SeOpAnd{})
    case SeOpOr{}:
      SeCil.cons.bin(SeCil.two(K.SeCexpr, rs, o), SeOpOr{})
    case SeOpNot{}:
      SeCil.cons.not(SeCil.one(K.SeCexpr, rs, o))
    case other:
      SeCil.cons.leaf(other, o, args, env)

def SeCil.cons.vals(xs: List<&2, SeSexp>, +env: SeEnv) -> List<&2, Result<&2, &2, P.SeError, K.SeCexpr>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case SeAtom{n}:
          Con{Fail{SeCil.bad("constraint expression")}, SeCil.cons.vals(t, env)}
        case SeList{ys}:
          match ys:
            case Con{SeAtom{+o}, +rest}:
              Con{SeCil.cons.apply(SeCil.op(o), o, rest, env, SeCil.cons.vals(rest, env)), SeCil.cons.vals(t, env)}
            case other:
              Con{Fail{SeCil.bad("constraint expression")}, SeCil.cons.vals(t, env)}

def SeCil.cons.eval(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, K.SeCexpr>:
  SeCil.one(K.SeCexpr, SeCil.cons.vals(Con{e, Nil{}}, env), "constraint expression")

# Levels, ranges and contexts, anonymous or named

def SeCil.def_of.go(has: Bool, +defs: Map<&2, SeSexp>, +key: String) -> Result<&2, &2, P.SeError, SeSexp>:
  match has:
    case True{}:
      Done{Pair.snd(Map<&2, SeSexp>, SeSexp, Map.get(SeSexp, SeAtom{""}, defs, key))}
    case False{}:
      Fail{P.SeErrUndeclared{key}}

def SeCil.def_of(+defs: Map<&2, SeSexp>, +key: String) -> Result<&2, &2, P.SeError, SeSexp>:
  SeCil.def_of.go(Pair.snd(Map<&2, SeSexp>, Bool, Map.has(&2, SeSexp, defs, key)), defs, key)

def SeCil.level.cats(rest: List<&2, SeSexp>, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match rest:
    case Nil{}:
      Done{Nil{}}
    case Con{c, Nil{}}:
      SeCil.set.eval(c, SeSetCats{}, env)
    case other:
      Fail{SeCil.bad("level")}

def SeCil.level.anon(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, M.SeLevel>:
  match e:
    case SeList{Con{SeAtom{s}, rest}}:
      do Result<&2, &2, P.SeError, M.SeLevel>:
        r : Nat <- SeCil.id(SeEnv.syms(env), "s:" ++ s)
        cs : List<&2, Bool> <- SeCil.level.cats(rest, env)
        return M.SeLevel.make(r, cs)
    case other:
      Fail{SeCil.bad("level")}

def SeCil.level(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, M.SeLevel>:
  match e:
    case SeAtom{n}:
      do Result<&2, &2, P.SeError, M.SeLevel>:
        d : SeSexp <- SeCil.def_of(SeEnv.defs(env), "l:" ++ n)
        SeCil.level.anon(d, env)
    case SeList{xs}:
      SeCil.level.anon(SeList{xs}, env)

def SeCil.range.anon(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, M.SeRange>:
  match e:
    case SeList{Con{lo, Con{hi, Nil{}}}}:
      do Result<&2, &2, P.SeError, M.SeRange>:
        l : M.SeLevel <- SeCil.level(lo, env)
        h : M.SeLevel <- SeCil.level(hi, env)
        return M.SeRange{l, h}
    case other:
      Fail{SeCil.bad("levelrange")}

def SeCil.range(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, M.SeRange>:
  match e:
    case SeAtom{n}:
      do Result<&2, &2, P.SeError, M.SeRange>:
        d : SeSexp <- SeCil.def_of(SeEnv.defs(env), "n:" ++ n)
        SeCil.range.anon(d, env)
    case SeList{xs}:
      SeCil.range.anon(SeList{xs}, env)

def SeCil.context.anon(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, C.SeContext>:
  match e:
    case SeList{Con{SeAtom{u}, Con{SeAtom{r}, Con{SeAtom{t}, Con{rg, Nil{}}}}}}:
      do Result<&2, &2, P.SeError, C.SeContext>:
        ui : Nat <- SeCil.id(SeEnv.syms(env), "u:" ++ u)
        ri : Nat <- SeCil.id(SeEnv.syms(env), "r:" ++ r)
        ti : Nat <- SeCil.type_id(SeEnv.syms(env), t)
        g : M.SeRange <- SeCil.range(rg, env)
        return C.SeContext{ui, ri, ti, g}
    case other:
      Fail{SeCil.bad("context")}

def SeCil.context(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, C.SeContext>:
  match e:
    case SeAtom{n}:
      do Result<&2, &2, P.SeError, C.SeContext>:
        d : SeSexp <- SeCil.def_of(SeEnv.defs(env), "x:" ++ n)
        SeCil.context.anon(d, env)
    case SeList{xs}:
      SeCil.context.anon(SeList{xs}, env)

# Rules

type SeCP is Data:
  SeCP{cls: Nat, perms: List<&2, Bool>}

def SeCP.cls(x: SeCP) -> Nat:
  match x:
    case SeCP{v, _}:
      v

def SeCP.perms(x: SeCP) -> List<&2, Bool>:
  match x:
    case SeCP{_, v}:
      v

type SeTgt is Data:
  SeTgt{set: List<&2, Bool>, self: Bool}

def SeTgt.set(x: SeTgt) -> List<&2, Bool>:
  match x:
    case SeTgt{v, _}:
      v

def SeTgt.self(x: SeTgt) -> Bool:
  match x:
    case SeTgt{_, v}:
      v

# (class (permission expression))
def SeCil.classperms(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, SeCP>:
  match e:
    case SeList{Con{SeAtom{+c}, Con{pe, Nil{}}}}:
      do Result<&2, &2, P.SeError, SeCP>:
        i : Nat <- SeCil.id(SeEnv.syms(env), "c:" ++ c)
        ps : List<&2, Bool> <- SeCil.set.eval(pe, SeSetPerms{c}, env)
        return SeCP{i, ps}
    case other:
      Fail{P.SeErrUnsupported{"named classpermission"}}

def SeCil.target.go(is_self: Bool, e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, SeTgt>:
  match is_self:
    case True{}:
      Done{SeTgt{Nil{}, True{}}}
    case False{}:
      do Result<&2, &2, P.SeError, SeTgt>:
        s : List<&2, Bool> <- SeCil.set.eval(e, SeSetTypes{}, env)
        return SeTgt{s, False{}}

# a target: self, or a set of types
def SeCil.target(e: SeSexp, +env: SeEnv) -> Result<&2, &2, P.SeError, SeTgt>:
  match e:
    case SeAtom{+n}:
      SeCil.target.go(String.eq(n, "self"), SeAtom{n}, env)
    case SeList{xs}:
      SeCil.target.go(False{}, SeList{xs}, env)

def SeCil.mk_av(kind: P.SeAvKind, src: List<&2, Bool>, tg: SeTgt, cp: SeCP) -> P.SeAvRule:
  match tg:
    case SeTgt{tgt, self}:
      match cp:
        case SeCP{cls, perms}:
          P.SeAvRule{kind, src, tgt, self, cls, perms}

# (allow source target (class (permissions))), and auditallow, dontaudit,
# neverallow
def SeCil.avrule(kind: P.SeAvKind, s: SeStmt, +env: SeEnv) -> Result<&2, &2, P.SeError, P.SeAvRule>:
  match s:
    case SeStmt{k, n, args}:
      match args:
        case Con{a, Con{b, Con{cp, Nil{}}}}:
          do Result<&2, &2, P.SeError, P.SeAvRule>:
            src : List<&2, Bool> <- SeCil.set.eval(a, SeSetTypes{}, env)
            tg : SeTgt <- SeCil.target(b, env)
            c : SeCP <- SeCil.classperms(cp, env)
            return SeCil.mk_av(kind, src, tg, c)
        case other:
          Fail{SeCil.bad(n)}

type SeTyTail is Data:
  SeTyTail{name: Maybe<&2, String>, result: String}

def SeTyTail.name(x: SeTyTail) -> Maybe<&2, String>:
  match x:
    case SeTyTail{v, _}:
      v

def SeTyTail.result(x: SeTyTail) -> String:
  match x:
    case SeTyTail{_, v}:
      v

def SeCil.ty_tail(rest: List<&2, SeSexp>, +n: String) -> Result<&2, &2, P.SeError, SeTyTail>:
  match rest:
    case Con{SeAtom{r}, Nil{}}:
      Done{SeTyTail{None{}, r}}
    case Con{SeAtom{o}, Con{SeAtom{r}, Nil{}}}:
      Done{SeTyTail{Some{o}, r}}
    case other:
      Fail{SeCil.bad(n)}

def SeCil.mk_ty(kind: P.SeTyKind, src: List<&2, Bool>, tg: SeTgt, cls: Nat, nm: Maybe<&2, String>, res: Nat) -> P.SeTyRule:
  match tg:
    case SeTgt{tgt, self}:
      P.SeTyRule{kind, src, tgt, self, cls, nm, res}

# (typetransition source target class [object name] result), and
# typechange, typemember (without an object name)
def SeCil.tyrule(kind: P.SeTyKind, s: SeStmt, +env: SeEnv) -> Result<&2, &2, P.SeError, P.SeTyRule>:
  match s:
    case SeStmt{k, +n, args}:
      match args:
        case Con{a, Con{b, Con{SeAtom{c}, rest}}}:
          do Result<&2, &2, P.SeError, P.SeTyRule>:
            src : List<&2, Bool> <- SeCil.set.eval(a, SeSetTypes{}, env)
            tg : SeTgt <- SeCil.target(b, env)
            ci : Nat <- SeCil.id(SeEnv.syms(env), "c:" ++ c)
            +tl : SeTyTail <- SeCil.ty_tail(rest, n)
            ri : Nat <- SeCil.type_id(SeEnv.syms(env), SeTyTail.result(tl))
            return SeCil.mk_ty(kind, src, tg, ci, SeTyTail.name(tl), ri)
        case other:
          Fail{SeCil.bad(n)}

# booleanif: the rules of each branch (reversed while they are collected)

type SeBr is Data:
  SeBr{av: List<&2, P.SeAvRule>, ty: List<&2, P.SeTyRule>}

def SeCil.br.av(r: Result<&2, &2, P.SeError, P.SeAvRule>, acc: SeBr) -> Result<&2, &2, P.SeError, SeBr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeBr{av, ty}:
          Done{SeBr{Con{x, av}, ty}}

def SeCil.br.ty(r: Result<&2, &2, P.SeError, P.SeTyRule>, acc: SeBr) -> Result<&2, &2, P.SeError, SeBr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeBr{av, ty}:
          Done{SeBr{av, Con{x, ty}}}

# a statement of a branch: an access vector rule or a type rule
def SeCil.br.stmt(k: SeKw, +s: SeStmt, +env: SeEnv, acc: SeBr) -> Result<&2, &2, P.SeError, SeBr>:
  match k:
    case SeKAllow{}:
      SeCil.br.av(SeCil.avrule(P.SeAllow{}, s, env), acc)
    case SeKAuditAllow{}:
      SeCil.br.av(SeCil.avrule(P.SeAuditallow{}, s, env), acc)
    case SeKDontAudit{}:
      SeCil.br.av(SeCil.avrule(P.SeDontaudit{}, s, env), acc)
    case SeKTypeTransition{}:
      SeCil.br.ty(SeCil.tyrule(P.SeTyTransition{}, s, env), acc)
    case SeKTypeChange{}:
      SeCil.br.ty(SeCil.tyrule(P.SeTyChange{}, s, env), acc)
    case SeKTypeMember{}:
      SeCil.br.ty(SeCil.tyrule(P.SeTyMember{}, s, env), acc)
    case other:
      Fail{SeCil.bad("booleanif: " ++ SeStmt.name(s))}

def SeCil.br.go(xs: List<&2, SeSexp>, +env: SeEnv, acc: Result<&2, &2, P.SeError, SeBr>) -> Result<&2, &2, P.SeError, SeBr>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      +s = SeCil.stmt(h)
      SeCil.br.go(t, env, Result.bind(&2, &2, P.SeError, SeBr, SeBr, acc, a => SeCil.br.stmt(SeStmt.kw(s), s, env, a)))

def SeCil.if.put(is_t: Bool, is_f: Bool, body: List<&2, SeSexp>, +env: SeEnv, +two: SeTwo<SeBr>) -> Result<&2, &2, P.SeError, SeTwo<SeBr>>:
  match is_t:
    case True{}:
      do Result<&2, &2, P.SeError, SeTwo<SeBr>>:
        nb : SeBr <- SeCil.br.go(body, env, Done{SeTwo.a(SeBr, two)})
        return SeTwo{nb, SeTwo.b(SeBr, two)}
    case False{}:
      match is_f:
        case True{}:
          do Result<&2, &2, P.SeError, SeTwo<SeBr>>:
            nb : SeBr <- SeCil.br.go(body, env, Done{SeTwo.b(SeBr, two)})
            return SeTwo{SeTwo.a(SeBr, two), nb}
        case False{}:
          Fail{SeCil.bad("booleanif")}

# (true statements...) or (false statements...)
def SeCil.if.one(b: SeSexp, +env: SeEnv, two: SeTwo<SeBr>) -> Result<&2, &2, P.SeError, SeTwo<SeBr>>:
  match b:
    case SeList{Con{SeAtom{+tf}, body}}:
      SeCil.if.put(String.eq(tf, "true"), String.eq(tf, "false"), body, env, two)
    case other:
      Fail{SeCil.bad("booleanif")}

def SeCil.if.go(bs: List<&2, SeSexp>, +env: SeEnv, r: Result<&2, &2, P.SeError, SeTwo<SeBr>>) -> Result<&2, &2, P.SeError, SeTwo<SeBr>>:
  match bs:
    case Nil{}:
      r
    case Con{b, t}:
      SeCil.if.go(t, env, Result.bind(&2, &2, P.SeError, SeTwo<SeBr>, SeTwo<SeBr>, r, two => SeCil.if.one(b, env, two)))

def SeCil.mk_cond(e: P.SeBexpr, two: SeTwo<SeBr>) -> P.SeCond:
  match two:
    case SeTwo{t, f}:
      match t:
        case SeBr{tav, tty}:
          match f:
            case SeBr{fav, fty}:
              P.SeCond{e, List.reverse(&2, P.SeAvRule, tav), List.reverse(&2, P.SeTyRule, tty), List.reverse(&2, P.SeAvRule, fav), List.reverse(&2, P.SeTyRule, fty)}

# (booleanif condition (true ...) (false ...))
def SeCil.booleanif(s: SeStmt, +env: SeEnv) -> Result<&2, &2, P.SeError, P.SeCond>:
  match s:
    case SeStmt{k, n, args}:
      match args:
        case Con{e, bs}:
          do Result<&2, &2, P.SeError, P.SeCond>:
            c : P.SeBexpr <- SeCil.bool.eval(e, SeEnv.syms(env))
            two : SeTwo<SeBr> <- SeCil.if.go(bs, env, Done{SeTwo{SeBr{Nil{}, Nil{}}, SeBr{Nil{}, Nil{}}}})
            return SeCil.mk_cond(c, two)
        case Nil{}:
          Fail{SeCil.bad(n)}

# roleallow, roletransition, constraints, typepermissive

def SeCil.roleallow(s: SeStmt, +env: SeEnv) -> Result<&2, &2, P.SeError, P.SeRoleAllow>:
  do Result<&2, &2, P.SeError, P.SeRoleAllow>:
    +two : SeTwoNames <- SeCil.arg2(s)
    a : List<&2, Bool> <- SeCil.set.name(SeSetRoles{}, env, SeTwoNames.a(two))
    b : List<&2, Bool> <- SeCil.set.name(SeSetRoles{}, env, SeTwoNames.b(two))
    return P.SeRoleAllow{a, b}

# (roletransition role type class new_role)
def SeCil.roletrans(s: SeStmt, +env: SeEnv) -> Result<&2, &2, P.SeError, P.SeRoleTrans>:
  match s:
    case SeStmt{k, n, args}:
      match args:
        case Con{SeAtom{r}, Con{t, Con{SeAtom{c}, Con{SeAtom{r2}, Nil{}}}}}:
          do Result<&2, &2, P.SeError, P.SeRoleTrans>:
            ri : List<&2, Bool> <- SeCil.set.name(SeSetRoles{}, env, r)
            ts : List<&2, Bool> <- SeCil.set.eval(t, SeSetTypes{}, env)
            ci : Nat <- SeCil.id(SeEnv.syms(env), "c:" ++ c)
            ni : Nat <- SeCil.id(SeEnv.syms(env), "r:" ++ r2)
            return P.SeRoleTrans{ri, ts, ci, ni}
        case other:
          Fail{SeCil.bad(n)}

def SeCil.mk_cons(mls: Bool, cp: SeCP, e: K.SeCexpr) -> K.SeConstraint:
  match cp:
    case SeCP{cls, perms}:
      K.SeConstraint{mls, cls, perms, e}

# (constrain (class (permissions)) expression), and mlsconstrain
def SeCil.constraint(mls: Bool, s: SeStmt, +env: SeEnv) -> Result<&2, &2, P.SeError, K.SeConstraint>:
  match s:
    case SeStmt{k, n, args}:
      match args:
        case Con{cp, Con{e, Nil{}}}:
          do Result<&2, &2, P.SeError, K.SeConstraint>:
            c : SeCP <- SeCil.classperms(cp, env)
            x : K.SeCexpr <- SeCil.cons.eval(e, env)
            return SeCil.mk_cons(mls, c, x)
        case other:
          Fail{SeCil.bad(n)}

# The rules, collected (reversed) in one pass

type SeRA is Data:
  SeRA{av: List<&2, P.SeAvRule>, ty: List<&2, P.SeTyRule>, conds: List<&2, P.SeCond>, ra: List<&2, P.SeRoleAllow>, rt: List<&2, P.SeRoleTrans>, cons: List<&2, K.SeConstraint>, perm: List<&2, Bool>}

def SeCil.ra.av(r: Result<&2, &2, P.SeError, P.SeAvRule>, acc: SeRA) -> Result<&2, &2, P.SeError, SeRA>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeRA{av, ty, cd, ra, rt, cs, pm}:
          Done{SeRA{Con{x, av}, ty, cd, ra, rt, cs, pm}}

def SeCil.ra.ty(r: Result<&2, &2, P.SeError, P.SeTyRule>, acc: SeRA) -> Result<&2, &2, P.SeError, SeRA>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeRA{av, ty, cd, ra, rt, cs, pm}:
          Done{SeRA{av, Con{x, ty}, cd, ra, rt, cs, pm}}

def SeCil.ra.cond(r: Result<&2, &2, P.SeError, P.SeCond>, acc: SeRA) -> Result<&2, &2, P.SeError, SeRA>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeRA{av, ty, cd, ra, rt, cs, pm}:
          Done{SeRA{av, ty, Con{x, cd}, ra, rt, cs, pm}}

def SeCil.ra.ra(r: Result<&2, &2, P.SeError, P.SeRoleAllow>, acc: SeRA) -> Result<&2, &2, P.SeError, SeRA>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeRA{av, ty, cd, ra, rt, cs, pm}:
          Done{SeRA{av, ty, cd, Con{x, ra}, rt, cs, pm}}

def SeCil.ra.rt(r: Result<&2, &2, P.SeError, P.SeRoleTrans>, acc: SeRA) -> Result<&2, &2, P.SeError, SeRA>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeRA{av, ty, cd, ra, rt, cs, pm}:
          Done{SeRA{av, ty, cd, ra, Con{x, rt}, cs, pm}}

def SeCil.ra.cons(r: Result<&2, &2, P.SeError, K.SeConstraint>, acc: SeRA) -> Result<&2, &2, P.SeError, SeRA>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeRA{av, ty, cd, ra, rt, cs, pm}:
          Done{SeRA{av, ty, cd, ra, rt, Con{x, cs}, pm}}

def SeCil.ra.perm(r: Result<&2, &2, P.SeError, Nat>, acc: SeRA) -> Result<&2, &2, P.SeError, SeRA>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match acc:
        case SeRA{av, ty, cd, ra, rt, cs, pm}:
          Done{SeRA{av, ty, cd, ra, rt, cs, Bits.SeBits.or(pm, Bits.SeBits.single(x))}}

def SeCil.permissive_type(s: SeStmt, +env: SeEnv) -> Result<&2, &2, P.SeError, Nat>:
  do Result<&2, &2, P.SeError, Nat>:
    n : String <- SeCil.arg1(s)
    SeCil.type_id(SeEnv.syms(env), n)

def SeCil.rule.step(k: SeKw, +s: SeStmt, +env: SeEnv, acc: SeRA) -> Result<&2, &2, P.SeError, SeRA>:
  match k:
    case SeKAllow{}:
      SeCil.ra.av(SeCil.avrule(P.SeAllow{}, s, env), acc)
    case SeKAuditAllow{}:
      SeCil.ra.av(SeCil.avrule(P.SeAuditallow{}, s, env), acc)
    case SeKDontAudit{}:
      SeCil.ra.av(SeCil.avrule(P.SeDontaudit{}, s, env), acc)
    case SeKNeverAllow{}:
      SeCil.ra.av(SeCil.avrule(P.SeNeverallow{}, s, env), acc)
    case SeKTypeTransition{}:
      SeCil.ra.ty(SeCil.tyrule(P.SeTyTransition{}, s, env), acc)
    case SeKTypeChange{}:
      SeCil.ra.ty(SeCil.tyrule(P.SeTyChange{}, s, env), acc)
    case SeKTypeMember{}:
      SeCil.ra.ty(SeCil.tyrule(P.SeTyMember{}, s, env), acc)
    case SeKBooleanIf{}:
      SeCil.ra.cond(SeCil.booleanif(s, env), acc)
    case SeKRoleAllow{}:
      SeCil.ra.ra(SeCil.roleallow(s, env), acc)
    case SeKRoleTransition{}:
      SeCil.ra.rt(SeCil.roletrans(s, env), acc)
    case SeKConstrain{}:
      SeCil.ra.cons(SeCil.constraint(False{}, s, env), acc)
    case SeKMlsConstrain{}:
      SeCil.ra.cons(SeCil.constraint(True{}, s, env), acc)
    case SeKTypePermissive{}:
      SeCil.ra.perm(SeCil.permissive_type(s, env), acc)
    case other:
      Done{acc}

def SeCil.rules.go(xs: List<&2, SeStmt>, +env: SeEnv, acc: Result<&2, &2, P.SeError, SeRA>) -> Result<&2, &2, P.SeError, SeRA>:
  match xs:
    case Nil{}:
      acc
    case Con{+s, t}:
      SeCil.rules.go(t, env, Result.bind(&2, &2, P.SeError, SeRA, SeRA, acc, a => SeCil.rule.step(SeStmt.kw(s), s, env, a)))

def SeCil.mk_rules(acc: SeRA) -> P.SeRules:
  match acc:
    case SeRA{av, ty, cd, ra, rt, cs, pm}:
      P.SeRules{List.reverse(&2, P.SeAvRule, av), List.reverse(&2, P.SeTyRule, ty), List.reverse(&2, P.SeCond, cd), List.reverse(&2, P.SeRoleAllow, ra), List.reverse(&2, P.SeRoleTrans, rt), List.reverse(&2, K.SeConstraint, cs), pm}

# the rules of the statements
def SeCil.rules(xs: List<&2, SeStmt>, +env: SeEnv) -> Result<&2, &2, P.SeError, P.SeRules>:
  do Result<&2, &2, P.SeError, P.SeRules>:
    acc : SeRA <- SeCil.rules.go(xs, env, Done{SeRA{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}})
    return SeCil.mk_rules(acc)

def SeCil.pick(-A: Data, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

# Declarations

def SeCil.is_attr(k: SeKw) -> Bool:
  match k:
    case SeKTypeAttribute{}:
      True{}
    case other:
      False{}

def SeCil.typedefs(xs: List<&2, SeStmt>) -> Result<&2, &2, P.SeError, List<&2, P.SeTypeDef>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{+s, t}:
      do Result<&2, &2, P.SeError, List<&2, P.SeTypeDef>>:
        n : String <- SeCil.arg1(s)
        r : List<&2, P.SeTypeDef> <- SeCil.typedefs(t)
        return Con{P.SeTypeDef{n, SeCil.is_attr(SeStmt.kw(s)), Nil{}}, r}

# (class name (permissions)), and common
def SeCil.classdecl(s: SeStmt) -> Result<&2, &2, P.SeError, P.SeClass>:
  match s:
    case SeStmt{k, +n, args}:
      match args:
        case Con{SeAtom{c}, Con{SeList{ps}, Nil{}}}:
          do Result<&2, &2, P.SeError, P.SeClass>:
            xs : List<&2, String> <- SeCil.atoms(ps, n)
            return P.SeClass{c, xs}
        case other:
          Fail{SeCil.bad(n)}

def SeCil.classdecls(xs: List<&2, SeStmt>) -> Result<&2, &2, P.SeError, List<&2, P.SeClass>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{s, t}:
      do Result<&2, &2, P.SeError, List<&2, P.SeClass>>:
        c : P.SeClass <- SeCil.classdecl(s)
        r : List<&2, P.SeClass> <- SeCil.classdecls(t)
        return Con{c, r}

def SeCil.common_of.hit(b: Bool, x: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

def SeCil.common_of(ccs: List<&2, SeTwoNames>, +c: String) -> Maybe<&2, String>:
  match ccs:
    case Nil{}:
      None{}
    case Con{p, t}:
      match p:
        case SeTwoNames{a, b}:
          SeCil.common_of.hit(String.eq(a, c), b, SeCil.common_of(t, c))

def SeCil.common_perms(m: Maybe<&2, String>, +commons: List<&2, P.SeClass>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{n}:
      SeCil.class_by_name(commons, n)

# a class's permissions: its common's first, then its own
def SeCil.full_classes(cs: List<&2, P.SeClass>, +commons: List<&2, P.SeClass>, +ccs: List<&2, SeTwoNames>) -> List<&2, P.SeClass>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      match c:
        case P.SeClass{+n, own}:
          Con{P.SeClass{n, List.append(&2, String, SeCil.common_perms(SeCil.common_of(ccs, n), commons), own)}, SeCil.full_classes(t, commons, ccs)}

def SeCil.bool_value.go(t: Bool, f: Bool) -> Result<&2, &2, P.SeError, Bool>:
  match t:
    case True{}:
      Done{True{}}
    case False{}:
      match f:
        case True{}:
          Done{False{}}
        case False{}:
          Fail{SeCil.bad("boolean")}

def SeCil.bool_value(e: SeSexp) -> Result<&2, &2, P.SeError, Bool>:
  match e:
    case SeAtom{+v}:
      SeCil.bool_value.go(String.eq(v, "true"), String.eq(v, "false"))
    case SeList{xs}:
      Fail{SeCil.bad("boolean")}

def SeCil.bool_values(xs: List<&2, SeNamed>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{b, t}:
      match b:
        case SeNamed{n, e}:
          do Result<&2, &2, P.SeError, List<&2, Bool>>:
            v : Bool <- SeCil.bool_value(e)
            r : List<&2, Bool> <- SeCil.bool_values(t)
            return Con{v, r}

def SeCil.named_names(xs: List<&2, SeNamed>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{SeNamed.name(b), SeCil.named_names(t)}

def SeCil.mls_on(xs: List<&2, SeStmt>) -> Result<&2, &2, P.SeError, Bool>:
  match xs:
    case Nil{}:
      Done{False{}}
    case Con{s, t}:
      do Result<&2, &2, P.SeError, Bool>:
        a : String <- SeCil.arg1(s)
        SeCil.bool_value(SeAtom{a})

def SeCil.drop_object_r.put(b: Bool, x: String, rest: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{x, rest}

# the roles declared, less object_r (always role 0)
def SeCil.drop_object_r(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      SeCil.drop_object_r.put(String.eq(x, "object_r"), x, SeCil.drop_object_r(t))

# The symbol table

def SeCil.type_sym(attr: Bool, i: Nat) -> P.SeSym:
  match attr:
    case True{}:
      P.SeSymAttr{i}
    case False{}:
      P.SeSymId{i}

def SeCil.declare_types(xs: List<&2, P.SeTypeDef>, +i: Nat, r: Result<&2, &2, P.SeError, Map<&2, P.SeSym>>) -> Result<&2, &2, P.SeError, Map<&2, P.SeSym>>:
  match xs:
    case Nil{}:
      r
    case Con{d, t}:
      match d:
        case P.SeTypeDef{n, attr, ms}:
          SeCil.declare_types(t, 1n+i, Result.bind(&2, &2, P.SeError, Map<&2, P.SeSym>, Map<&2, P.SeSym>, r, m => SeCil.declare(m, "t:" ++ n, SeCil.type_sym(attr, i))))

def SeCil.declare_classes(xs: List<&2, P.SeClass>, +i: Nat, r: Result<&2, &2, P.SeError, Map<&2, P.SeSym>>) -> Result<&2, &2, P.SeError, Map<&2, P.SeSym>>:
  match xs:
    case Nil{}:
      r
    case Con{c, t}:
      match c:
        case P.SeClass{+n, ps}:
          SeCil.declare_classes(t, 1n+i, SeCil.declare_all(ps, "p:" ++ n ++ ":", 0n, Result.bind(&2, &2, P.SeError, Map<&2, P.SeSym>, Map<&2, P.SeSym>, r, m => SeCil.declare(m, "c:" ++ n, P.SeSymId{i}))))

def SeCil.alias.one(s: P.SeSym, +m: Map<&2, P.SeSym>, a: String, actual: String) -> Result<&2, &2, P.SeError, Map<&2, P.SeSym>>:
  match s:
    case P.SeSymId{i}:
      SeCil.declare(m, "t:" ++ a, P.SeSymId{i})
    case other:
      Fail{P.SeErrUndeclared{"t:" ++ actual}}

# (typealiasactual alias type)
def SeCil.aliases(xs: List<&2, SeTwoNames>, r: Result<&2, &2, P.SeError, Map<&2, P.SeSym>>) -> Result<&2, &2, P.SeError, Map<&2, P.SeSym>>:
  match xs:
    case Nil{}:
      r
    case Con{p, t}:
      match p:
        case SeTwoNames{a, +b}:
          SeCil.aliases(t, Result.bind(&2, &2, P.SeError, Map<&2, P.SeSym>, Map<&2, P.SeSym>, r, +m => SeCil.alias.one(SeCil.lookup(m, "t:" ++ b), m, a, b)))

def SeCil.defs(xs: List<&2, SeNamed>, +prefix: String, m: Map<&2, SeSexp>) -> Map<&2, SeSexp>:
  match xs:
    case Nil{}:
      m
    case Con{d, t}:
      match d:
        case SeNamed{n, e}:
          SeCil.defs(t, prefix, Map.set(&2, SeSexp, m, prefix ++ n, e))

# Attributes: the members of each, by rounds (an attribute may name others)

def SeCil.init_tsets(xs: List<&2, P.SeTypeDef>, +i: Nat) -> List<&2, List<&2, Bool>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case P.SeTypeDef{n, attr, ms}:
          Con{SeCil.pick(List<&2, Bool>, attr, Nil{}, Bits.SeBits.single(i)), SeCil.init_tsets(t, 1n+i)}

def SeCil.real(xs: List<&2, P.SeTypeDef>, +i: Nat) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case P.SeTypeDef{n, attr, ms}:
          Bits.SeBits.or(SeCil.pick(List<&2, Bool>, attr, Nil{}, Bits.SeBits.single(i)), SeCil.real(t, 1n+i))

def SeCil.count_attrs(xs: List<&2, P.SeTypeDef>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{d, t}:
      match d:
        case P.SeTypeDef{n, attr, ms}:
          Nat.add(SeCil.pick(Nat, attr, 1n, 0n), SeCil.count_attrs(t))

type SeFact is Data:
  SeFact{id: Nat, e: SeSexp}

def SeFact.id(x: SeFact) -> Nat:
  match x:
    case SeFact{v, _}:
      v

def SeFact.e(x: SeFact) -> SeSexp:
  match x:
    case SeFact{_, v}:
      v

def SeCil.fact.sym(s: P.SeSym, e: SeSexp, key: String) -> Result<&2, &2, P.SeError, SeFact>:
  match s:
    case P.SeSymAttr{i}:
      Done{SeFact{i, e}}
    case other:
      Fail{P.SeErrUndeclared{key}}

# (typeattributeset attribute expression)
def SeCil.facts(xs: List<&2, SeNamed>, +syms: Map<&2, P.SeSym>) -> Result<&2, &2, P.SeError, List<&2, SeFact>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{d, t}:
      match d:
        case SeNamed{n, e}:
          +key = "t:" ++ n
          do Result<&2, &2, P.SeError, List<&2, SeFact>>:
            f : SeFact <- SeCil.fact.sym(SeCil.lookup(syms, key), e, key)
            r : List<&2, SeFact> <- SeCil.facts(t, syms)
            return Con{f, r}

def SeCil.fact.hit(b: Bool, e: SeSexp, +env: SeEnv, rest: Result<&2, &2, P.SeError, List<&2, Bool>>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match b:
    case True{}:
      SeCil.set.or2(SeCil.set.eval(e, SeSetTypes{}, env), rest)
    case False{}:
      rest

def SeCil.fact_union(fs: List<&2, SeFact>, +i: Nat, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match fs:
    case Nil{}:
      Done{Nil{}}
    case Con{f, t}:
      match f:
        case SeFact{j, e}:
          SeCil.fact.hit(Nat.is_eq(i, j), e, env, SeCil.fact_union(t, i, env))

def SeCil.round.one(attr: Bool, +i: Nat, +facts: List<&2, SeFact>, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match attr:
    case True{}:
      SeCil.fact_union(facts, i, env)
    case False{}:
      Done{Bits.SeBits.single(i)}

def SeCil.round(xs: List<&2, P.SeTypeDef>, +i: Nat, +facts: List<&2, SeFact>, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, List<&2, Bool>>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{d, t}:
      match d:
        case P.SeTypeDef{n, attr, ms}:
          do Result<&2, &2, P.SeError, List<&2, List<&2, Bool>>>:
            v : List<&2, Bool> <- SeCil.round.one(attr, i, facts, env)
            r : List<&2, List<&2, Bool>> <- SeCil.round(t, 1n+i, facts, env)
            return Con{v, r}

def SeEnv.with_tsets(env: SeEnv, ts: List<&2, List<&2, Bool>>) -> SeEnv:
  match env:
    case SeEnv{sy, df, old, re, cl, nc, nr, nu}:
      SeEnv{sy, df, ts, re, cl, nc, nr, nu}

def SeCil.iterate(fuel: Nat, +types: List<&2, P.SeTypeDef>, +facts: List<&2, SeFact>, +env: SeEnv) -> Result<&2, &2, P.SeError, SeEnv>:
  match fuel:
    case 0n:
      Done{env}
    case 1n+p:
      do Result<&2, &2, P.SeError, SeEnv>:
        ts : List<&2, List<&2, Bool>> <- SeCil.round(types, 0n, facts, env)
        SeCil.iterate(p, types, facts, SeEnv.with_tsets(env, ts))

def SeCil.blist_eq(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case Con{y, ys}:
          False{}
    case Con{x, xs}:
      match b:
        case Nil{}:
          False{}
        case Con{y, ys}:
          Bool.and(Bool.not(Bool.xor(x, y)), SeCil.blist_eq(xs, ys))

def SeCil.tables_eq(a: List<&2, List<&2, Bool>>, b: List<&2, List<&2, Bool>>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case Con{y, ys}:
          False{}
    case Con{x, xs}:
      match b:
        case Nil{}:
          False{}
        case Con{y, ys}:
          Bool.and(SeCil.blist_eq(Bits.SeBits.norm(x), Bits.SeBits.norm(y)), SeCil.tables_eq(xs, ys))

def SeCil.stable(eq: Bool, env: SeEnv) -> Result<&2, &2, P.SeError, SeEnv>:
  match eq:
    case True{}:
      Done{env}
    case False{}:
      Fail{P.SeErrAttributeCycle{"typeattributeset"}}

type SeIdBits is Data:
  SeIdBits{id: Nat, set: List<&2, Bool>}

# Attribute cycles: R holds every attribute at first; each step keeps the
# attributes that the attributes in R name. Without a cycle, R is empty
# after one step per attribute (and one more).

def SeCil.ref_sym(s: P.SeSym) -> List<&2, Bool>:
  match s:
    case P.SeSymAttr{i}:
      Bits.SeBits.single(i)
    case other:
      Nil{}

# the attributes an expression names
def SeCil.refs_of(xs: List<&2, SeSexp>, +syms: Map<&2, P.SeSym>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case SeAtom{n}:
          Bits.SeBits.or(SeCil.ref_sym(SeCil.lookup(syms, "t:" ++ n)), SeCil.refs_of(t, syms))
        case SeList{ys}:
          Bits.SeBits.or(SeCil.refs_of(ys, syms), SeCil.refs_of(t, syms))

def SeCil.fact_refs(fs: List<&2, SeFact>, +syms: Map<&2, P.SeSym>) -> List<&2, SeIdBits>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case SeFact{i, e}:
          Con{SeIdBits{i, SeCil.refs_of(Con{e, Nil{}}, syms)}, SeCil.fact_refs(t, syms)}

def SeCil.step_refs(xs: List<&2, SeIdBits>, +r: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case SeIdBits{i, b}:
          Bits.SeBits.or(SeCil.pick(List<&2, Bool>, Bits.SeBits.has(r, i), b, Nil{}), SeCil.step_refs(t, r))

def SeCil.acyclic.end(left: Bool) -> Result<&2, &2, P.SeError, Unit>:
  match left:
    case True{}:
      Fail{P.SeErrAttributeCycle{"typeattributeset"}}
    case False{}:
      Done{Unit{}}

def SeCil.acyclic(fuel: Nat, +xs: List<&2, SeIdBits>, r: List<&2, Bool>) -> Result<&2, &2, P.SeError, Unit>:
  match fuel:
    case 0n:
      SeCil.acyclic.end(Bits.SeBits.any(r))
    case 1n+p:
      SeCil.acyclic(p, xs, SeCil.step_refs(xs, r))

def SeCil.all_attrs(xs: List<&2, P.SeTypeDef>, +i: Nat) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case P.SeTypeDef{n, attr, ms}:
          Bits.SeBits.or(SeCil.pick(List<&2, Bool>, attr, Bits.SeBits.single(i), Nil{}), SeCil.all_attrs(t, 1n+i))

# Every attribute's members, after one round per attribute and one more (an
# attribute's set is exact once the attributes it names are), once no
# attributes name each other in a cycle (secilc refuses those too).
def SeCil.attributes(+types: List<&2, P.SeTypeDef>, +facts: List<&2, SeFact>, +env: SeEnv) -> Result<&2, &2, P.SeError, SeEnv>:
  do Result<&2, &2, P.SeError, SeEnv>:
    ok : Unit <- SeCil.acyclic(1n+SeCil.count_attrs(types), SeCil.fact_refs(facts, SeEnv.syms(env)), SeCil.all_attrs(types, 0n))
    +e2 : SeEnv <- SeCil.iterate(1n+SeCil.count_attrs(types), types, facts, env)
    ts : List<&2, List<&2, Bool>> <- SeCil.round(types, 0n, facts, e2)
    SeCil.stable(SeCil.tables_eq(ts, SeEnv.tsets(e2)), e2)

def SeCil.with_members(xs: List<&2, P.SeTypeDef>, ts: List<&2, List<&2, Bool>>) -> List<&2, P.SeTypeDef>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case P.SeTypeDef{n, attr, old}:
          match ts:
            case Nil{}:
              Con{P.SeTypeDef{n, attr, old}, SeCil.with_members(t, Nil{})}
            case Con{m, us}:
              Con{P.SeTypeDef{n, attr, m}, SeCil.with_members(t, us)}

# Roles, users, sensitivities

type SeIdLevel is Data:
  SeIdLevel{id: Nat, level: M.SeLevel}

type SeIdRange is Data:
  SeIdRange{id: Nat, range: M.SeRange}

# (roletype role types), and (sensitivitycategory sensitivity categories)
def SeCil.id_sets(xs: List<&2, SeNamed>, +prefix: String, +kind: SeSetKind, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, SeIdBits>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{d, t}:
      match d:
        case SeNamed{n, e}:
          do Result<&2, &2, P.SeError, List<&2, SeIdBits>>:
            i : Nat <- SeCil.id(SeEnv.syms(env), prefix ++ n)
            b : List<&2, Bool> <- SeCil.set.eval(e, kind, env)
            r : List<&2, SeIdBits> <- SeCil.id_sets(t, prefix, kind, env)
            return Con{SeIdBits{i, b}, r}

# (userrole user role)
def SeCil.userroles(xs: List<&2, SeTwoNames>, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, SeIdBits>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{d, t}:
      match d:
        case SeTwoNames{u, r}:
          do Result<&2, &2, P.SeError, List<&2, SeIdBits>>:
            i : Nat <- SeCil.id(SeEnv.syms(env), "u:" ++ u)
            b : List<&2, Bool> <- SeCil.set.name(SeSetRoles{}, env, r)
            rest : List<&2, SeIdBits> <- SeCil.userroles(t, env)
            return Con{SeIdBits{i, b}, rest}

def SeCil.userlevels(xs: List<&2, SeNamed>, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, SeIdLevel>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{d, t}:
      match d:
        case SeNamed{n, e}:
          do Result<&2, &2, P.SeError, List<&2, SeIdLevel>>:
            i : Nat <- SeCil.id(SeEnv.syms(env), "u:" ++ n)
            l : M.SeLevel <- SeCil.level(e, env)
            r : List<&2, SeIdLevel> <- SeCil.userlevels(t, env)
            return Con{SeIdLevel{i, l}, r}

def SeCil.userranges(xs: List<&2, SeNamed>, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, SeIdRange>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{d, t}:
      match d:
        case SeNamed{n, e}:
          do Result<&2, &2, P.SeError, List<&2, SeIdRange>>:
            i : Nat <- SeCil.id(SeEnv.syms(env), "u:" ++ n)
            g : M.SeRange <- SeCil.range(e, env)
            r : List<&2, SeIdRange> <- SeCil.userranges(t, env)
            return Con{SeIdRange{i, g}, r}

def SeCil.or_for(xs: List<&2, SeIdBits>, +i: Nat) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case SeIdBits{j, b}:
          Bits.SeBits.or(SeCil.pick(List<&2, Bool>, Nat.is_eq(i, j), b, Nil{}), SeCil.or_for(t, i))

def SeCil.level_for.hit(b: Bool, l: M.SeLevel, rest: M.SeLevel) -> M.SeLevel:
  match b:
    case True{}:
      l
    case False{}:
      rest

def SeCil.level_for(xs: List<&2, SeIdLevel>, +i: Nat) -> M.SeLevel:
  match xs:
    case Nil{}:
      M.SeLevel{0n, Nil{}}
    case Con{d, t}:
      match d:
        case SeIdLevel{j, l}:
          SeCil.level_for.hit(Nat.is_eq(i, j), l, SeCil.level_for(t, i))

def SeCil.range_for.hit(b: Bool, l: M.SeRange, rest: M.SeRange) -> M.SeRange:
  match b:
    case True{}:
      l
    case False{}:
      rest

def SeCil.range_for(xs: List<&2, SeIdRange>, +i: Nat) -> M.SeRange:
  match xs:
    case Nil{}:
      M.SeRange{M.SeLevel{0n, Nil{}}, M.SeLevel{0n, Nil{}}}
    case Con{d, t}:
      match d:
        case SeIdRange{j, g}:
          SeCil.range_for.hit(Nat.is_eq(i, j), g, SeCil.range_for(t, i))

def SeCil.mk_roles(xs: List<&2, String>, +i: Nat, +facts: List<&2, SeIdBits>) -> List<&2, P.SeRole>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{P.SeRole{n, SeCil.or_for(facts, i)}, SeCil.mk_roles(t, 1n+i, facts)}

def SeCil.mk_users(xs: List<&2, String>, +i: Nat, +roles: List<&2, SeIdBits>, +levels: List<&2, SeIdLevel>, +ranges: List<&2, SeIdRange>) -> List<&2, P.SeUser>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{P.SeUser{n, SeCil.or_for(roles, i), SeCil.level_for(levels, i), SeCil.range_for(ranges, i)}, SeCil.mk_users(t, 1n+i, roles, levels, ranges)}

def SeCil.mk_senscats(xs: List<&2, String>, +i: Nat, +facts: List<&2, SeIdBits>) -> List<&2, List<&2, Bool>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{SeCil.or_for(facts, i), SeCil.mk_senscats(t, 1n+i, facts)}

def SeCil.contexts(xs: List<&2, SeNamed>, +env: SeEnv) -> Result<&2, &2, P.SeError, List<&2, P.SeCtxDef>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{d, t}:
      match d:
        case SeNamed{n, e}:
          do Result<&2, &2, P.SeError, List<&2, P.SeCtxDef>>:
            c : C.SeContext <- SeCil.context(e, env)
            r : List<&2, P.SeCtxDef> <- SeCil.contexts(t, env)
            return Con{P.SeCtxDef{n, c}, r}

# Every statement is in the subset (or read and ignored)

def SeCil.check.one(k: SeKw, n: String) -> Result<&2, &2, P.SeError, Unit>:
  match k:
    case SeKUnknown{}:
      Fail{P.SeErrUnknownStatement{n}}
    case SeKUnsupported{}:
      Fail{P.SeErrUnsupported{n}}
    case other:
      Done{Unit{}}

def SeCil.check(xs: List<&2, SeStmt>) -> Result<&2, &2, P.SeError, Unit>:
  match xs:
    case Nil{}:
      Done{Unit{}}
    case Con{s, t}:
      match s:
        case SeStmt{k, n, a}:
          do Result<&2, &2, P.SeError, Unit>:
            u : Unit <- SeCil.check.one(k, n)
            SeCil.check(t)

def SeCil.decl_syms(+tys: List<&2, P.SeTypeDef>, +rnames: List<&2, String>, +unames: List<&2, String>, +classes: List<&2, P.SeClass>, +bnames: List<&2, String>, +sens: List<&2, String>, +cats: List<&2, String>) -> Result<&2, &2, P.SeError, Map<&2, P.SeSym>>:
  SeCil.declare_all(cats, "g:", 0n, SeCil.declare_all(sens, "s:", 0n, SeCil.declare_all(bnames, "b:", 0n, SeCil.declare_classes(classes, 0n, SeCil.declare_all(unames, "u:", 0n, SeCil.declare_all(rnames, "r:", 0n, SeCil.declare_types(tys, 0n, Done{Map.new(&2, P.SeSym)})))))))

# the policy of a list of CIL statements
def SeCil.compile(ss: List<&2, SeSexp>) -> Result<&2, &2, P.SeError, P.SePolicy>:
  +st = SeCil.stmts(ss)
  do Result<&2, &2, P.SeError, P.SePolicy>:
    ok : Unit <- SeCil.check(st)
    +tys : List<&2, P.SeTypeDef> <- SeCil.typedefs(SeCil.select2(st, SeKType{}, SeKTypeAttribute{}))
    rn : List<&2, String> <- SeCil.each1(SeCil.select(st, SeKRole{}))
    +rnames : List<&2, String> = Con{"object_r", SeCil.drop_object_r(rn)}
    +unames : List<&2, String> <- SeCil.each1(SeCil.select(st, SeKUser{}))
    cls0 : List<&2, P.SeClass> <- SeCil.classdecls(SeCil.select(st, SeKClass{}))
    coms : List<&2, P.SeClass> <- SeCil.classdecls(SeCil.select(st, SeKCommon{}))
    ccs : List<&2, SeTwoNames> <- SeCil.each2(SeCil.select(st, SeKClassCommon{}))
    +classes : List<&2, P.SeClass> = SeCil.full_classes(cls0, coms, ccs)
    +bls : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKBoolean{}))
    bvals : List<&2, Bool> <- SeCil.bool_values(bls)
    +sens : List<&2, String> <- SeCil.order(SeCil.select(st, SeKSensitivityOrder{}))
    +cats : List<&2, String> <- SeCil.order(SeCil.select(st, SeKCategoryOrder{}))
    mls : Bool <- SeCil.mls_on(SeCil.select(st, SeKMls{}))
    syms0 : Map<&2, P.SeSym> <- SeCil.decl_syms(tys, rnames, unames, classes, SeCil.named_names(bls), sens, cats)
    al : List<&2, SeTwoNames> <- SeCil.each2(SeCil.select(st, SeKTypeAliasActual{}))
    +syms : Map<&2, P.SeSym> <- SeCil.aliases(al, Done{syms0})
    lv : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKLevel{}))
    lr : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKLevelRange{}))
    +cx : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKContext{}))
    defs : Map<&2, SeSexp> = SeCil.defs(lv, "l:", SeCil.defs(lr, "n:", SeCil.defs(cx, "x:", Map.new(&2, SeSexp))))
    env0 : SeEnv = SeEnv{syms, defs, SeCil.init_tsets(tys, 0n), SeCil.real(tys, 0n), classes, List.length(&2, String, cats), List.length(&2, String, rnames), List.length(&2, String, unames)}
    tas : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKTypeAttributeSet{}))
    facts : List<&2, SeFact> <- SeCil.facts(tas, syms)
    +env : SeEnv <- SeCil.attributes(tys, facts, env0)
    rts : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKRoleType{}))
    rfacts : List<&2, SeIdBits> <- SeCil.id_sets(rts, "r:", SeSetTypes{}, env)
    urs : List<&2, SeTwoNames> <- SeCil.each2(SeCil.select(st, SeKUserRole{}))
    ufacts : List<&2, SeIdBits> <- SeCil.userroles(urs, env)
    uls : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKUserLevel{}))
    ulev : List<&2, SeIdLevel> <- SeCil.userlevels(uls, env)
    ugs : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKUserRange{}))
    urng : List<&2, SeIdRange> <- SeCil.userranges(ugs, env)
    scs : List<&2, SeNamed> <- SeCil.each_named(SeCil.select(st, SeKSensitivityCategory{}))
    sfacts : List<&2, SeIdBits> <- SeCil.id_sets(scs, "s:", SeSetCats{}, env)
    ctxs : List<&2, P.SeCtxDef> <- SeCil.contexts(cx, env)
    rules : P.SeRules <- SeCil.rules(st, env)
    return P.SePolicy{P.SeDecl{SeCil.with_members(tys, SeEnv.tsets(env)), SeCil.mk_roles(rnames, 0n, Con{SeIdBits{0n, SeEnv.real(env)}, rfacts}), SeCil.mk_users(unames, 0n, ufacts, ulev, urng), classes, SeCil.named_names(bls), sens, cats, SeCil.mk_senscats(sens, 0n, sfacts), syms, ctxs}, rules, mls, bvals}

# the policy of a CIL text
def SeCil.load(o: B.Octets) -> Result<&2, &2, P.SeError, P.SePolicy>:
  do Result<&2, &2, P.SeError, P.SePolicy>:
    ss : List<&2, SeSexp> <- SeCil.read(o)
    SeCil.compile(ss)
