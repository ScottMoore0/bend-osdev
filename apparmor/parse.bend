# bend-osdev-apparmor: loading policy text (apparmor.d(5), "FORMAT").
#
# 1. Each file's text is split into tokens (token.bend), and the tokens into
#    items: statements ending at a comma, variable assignments (which end at
#    the end of their line), includes, and block openings and closings.
# 2. Includes are replaced by the items of the included file, taken from the
#    file map: <name> and "name" both look up name. An include is expanded
#    at most once in each block (the file's top level, each profile, hat or
#    qualifier block), so including a file twice is including it once and
#    include cycles end (apparmor_parser 4.0.1 does the same; see the
#    README, "Experiments"). A missing file fails unless the include says
#    `if exists`.
# 3. The preamble (before the first profile) assigns variables, @{NAME} =
#    values or += values, and declares aliases, alias /from/ -> /to/,; abi
#    statements are accepted and ignored.
# 4. Profiles are built: headers, flags, rules (with variables expanded:
#    one value as itself, several as {v1,v2}; a value's trailing '/' is
#    dropped before a '/'; @{profile_name} is the profile's full name),
#    child profiles and hats, and qualifier blocks. An alias adds, for each
#    file rule whose pattern starts with its source, a copy starting with
#    its target. Two rules on the same literal path with different exec
#    modes fail.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./options.bend as O
import ./profile.bend as PR
import ./rule.bend as R
import ./rule_file.bend as F
import ./rule_capability.bend as RC
import ./rule_network.bend as RN
import ./rule_signal.bend as RS
import ./rule_ptrace.bend as RP
import ./rule_mount.bend as RM
import ./rule_dbus.bend as RD
import ./rule_change_profile.bend as RX

# a file of the file map: its name (as includes name it) and its text
type AaSrcFile is Data:
  AaSrcFile{name: List<&2, U32>, text: List<&2, U32>}

# Items

type AaItem is Data:
  AaIStmt{toks: List<&2, T.AaTok>, src: E.AaSrc}
  AaIVar{toks: List<&2, T.AaTok>, src: E.AaSrc}
  AaIInclude{name: List<&2, U32>, optional: Bool, src: E.AaSrc}
  AaIOpen{toks: List<&2, T.AaTok>, src: E.AaSrc}
  AaIClose{src: E.AaSrc}
  AaIError{err: E.AaError}

def AaItem.rev_onto(xs: List<&2, AaItem>, acc: List<&2, AaItem>) -> List<&2, AaItem>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      AaItem.rev_onto(t, Con{h, acc})

# The itemizer. Modes: normal; a candidate variable assignment (the word
# @{NAME} alone, waiting to see = or +=); a variable assignment on a line;
# an include waiting for its path (stage 0), after `if` (1), after `if exists` (2).
type AaItMode is Data:
  AaImNorm{}
  AaImVarCand{line: U32}
  AaImVar{line: U32}
  AaImInc{stage: Nat, line: U32}

type AaItB is Data:
  AaItB{file: List<&2, U32>, mode: AaItMode, pend: List<&2, T.AaTok>, pdepth: Nat, out: List<&2, AaItem>}

def AaItB.src(+file: List<&2, U32>, line: U32) -> E.AaSrc:
  E.AaSrc{file, line}

def AaItB.emit(b: AaItB, it: AaItem) -> AaItB:
  match b:
    case AaItB{f, m, pe, pd, out}:
      AaItB{f, AaImNorm{}, Nil{}, pd, Con{it, out}}

def AaItB.err(b: AaItB, e: E.AaError) -> AaItB:
  AaItB.emit(b, AaIError{e})

def AaItB.push(b: AaItB, t: T.AaTok) -> AaItB:
  match b:
    case AaItB{f, m, pe, pd, out}:
      AaItB{f, m, Con{t, pe}, pd, out}

def AaItB.mode(b: AaItB, m: AaItMode) -> AaItB:
  match b:
    case AaItB{f, m0, pe, pd, out}:
      AaItB{f, m, pe, pd, out}

def AaItB.file(b: AaItB) -> List<&2, U32>:
  match b:
    case AaItB{f, m, pe, pd, out}:
      f

def AaItB.pend_empty(b: AaItB) -> Bool:
  match b:
    case AaItB{f, m, pe, pd, out}:
      match pe:
        case Nil{}:
          True{}
        case Con{h, t}:
          False{}

def AaItB.pdepth(b: AaItB) -> Nat:
  match b:
    case AaItB{f, m, pe, pd, out}:
      pd

def AaItB.paren(b: AaItB, up: Bool, t: T.AaTok) -> AaItB:
  match b:
    case AaItB{f, m, pe, pd, out}:
      match up:
        case True{}:
          AaItB{f, m, Con{t, pe}, 1n+pd, out}
        case False{}:
          AaItB{f, m, Con{t, pe}, Nat.sub(pd, 1n), out}

def AaItB.flush.item(kind: Nat, ts: List<&2, T.AaTok>, src: E.AaSrc) -> AaItem:
  match kind:
    case 0n:
      AaIStmt{ts, src}
    case 1n+k:
      match k:
        case 0n:
          AaIOpen{ts, src}
        case 1n+j:
          AaIVar{ts, src}

# the pending tokens become an item: 0 a statement, 1 a block opening, 2 an assignment
def AaItB.flush(b: AaItB, kind: Nat, line: U32) -> AaItB:
  match b:
    case AaItB{+f, m, pe, pd, out}:
      AaItB{f, AaImNorm{}, Nil{}, pd, Con{AaItB.flush.item(kind, T.AaTok.rev_onto(pe, Nil{}), E.AaSrc{f, line}), out}}

# a word starting @{: 0 not a variable word, 1 exactly @{NAME}, 2 @{NAME}= or @{NAME}+= with more
def AaIt.var_kind.rest(+r: List<&2, U32>) -> Nat:
  match r:
    case Nil{}:
      1n
    case Con{h, t}:
      Bool.pick(Nat, Bool.or(X.AaText.starts(r, "="), X.AaText.starts(r, "+=")), 2n, 0n)

def AaIt.after_close(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, +t}:
      Bool.pick(Maybe<&2, List<&2, U32>>, U32.is_eq(h, 125), Some{t}, AaIt.after_close(t))

def AaIt.var_kind.go(m: Maybe<&2, List<&2, U32>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{r}:
      AaIt.var_kind.rest(r)

def AaIt.var_kind(+w: List<&2, U32>) -> Nat:
  Bool.pick(Nat, X.AaText.starts(w, "@{"), AaIt.var_kind.go(AaIt.after_close(w)), 0n)

def AaIt.is_include(t: T.AaTok) -> Bool:
  match t:
    case T.AaTWord{+w, l}:
      Bool.or(X.AaText.is(w, "#include"), X.AaText.is(w, "include"))
    case _:
      False{}

# a token in normal mode
def AaItB.norm.word(k: Nat, +b: AaItB, t: T.AaTok, +line: U32) -> AaItB:
  match k:
    case 0n:
      AaItB.push(b, t)
    case 1n+k1:
      match k1:
        case 0n:
          AaItB.mode(AaItB.push(b, t), AaImVarCand{line})
        case 1n+k2:
          AaItB.mode(AaItB.push(b, t), AaImVar{line})

def AaItB.norm.first(t: T.AaTok, +b: AaItB) -> AaItB:
  match t:
    case T.AaTWord{+w, +l}:
      Bool.pick(AaItB, AaIt.is_include(T.AaTWord{w, l}), AaItB.mode(b, AaImInc{0n, l}), AaItB.norm.word(AaIt.var_kind(w), b, T.AaTWord{w, l}, l))
    case _:
      AaItB.push(b, t)

def AaItB.norm.open(depth0: Bool, +b: AaItB, t: T.AaTok, +l: U32) -> AaItB:
  match depth0:
    case True{}:
      AaItB.flush(b, 1n, l)
    case False{}:
      AaItB.push(b, t)

def AaItB.norm.close(depth0: Bool, empty: Bool, +b: AaItB, t: T.AaTok, +l: U32) -> AaItB:
  match depth0:
    case True{}:
      match empty:
        case True{}:
          AaItB.emit(b, AaIClose{E.AaSrc{AaItB.file(b), l}})
        case False{}:
          AaItB.err(b, E.AaErrSyntax{AaItB.file(b), l})
    case False{}:
      AaItB.push(b, t)

def AaItB.norm.comma(depth0: Bool, empty: Bool, +b: AaItB, t: T.AaTok, +l: U32) -> AaItB:
  match depth0:
    case True{}:
      match empty:
        case True{}:
          AaItB.err(b, E.AaErrSyntax{AaItB.file(b), l})
        case False{}:
          AaItB.flush(b, 0n, l)
    case False{}:
      AaItB.push(b, t)

def AaItB.norm.go(t: T.AaTok, +d0: Bool, +empty: Bool, +b: AaItB) -> AaItB:
  match t:
    case T.AaTOpen{+l}:
      AaItB.norm.open(d0, b, T.AaTOpen{l}, l)
    case T.AaTClose{+l}:
      AaItB.norm.close(d0, empty, b, T.AaTClose{l}, l)
    case T.AaTComma{+l}:
      AaItB.norm.comma(d0, empty, b, T.AaTComma{l}, l)
    case T.AaTLParen{l}:
      AaItB.paren(b, True{}, T.AaTLParen{l})
    case T.AaTRParen{l}:
      AaItB.paren(b, False{}, T.AaTRParen{l})
    case T.AaTWord{+w, +l}:
      Bool.pick(AaItB, Bool.and(d0, empty), AaItB.norm.first(T.AaTWord{w, l}, b), AaItB.push(b, T.AaTWord{w, l}))
    case T.AaTQuoted{q, l}:
      AaItB.push(b, T.AaTQuoted{q, l})

def AaItB.norm(+b: AaItB, t: T.AaTok) -> AaItB:
  AaItB.norm.go(t, Nat.is_eq(AaItB.pdepth(b), 0n), AaItB.pend_empty(b), b)

# after @{NAME}: = or += makes it an assignment; anything else a rule
def AaItB.varcand(+b: AaItB, t: T.AaTok, +line: U32) -> AaItB:
  match t:
    case T.AaTWord{+w, +l}:
      Bool.pick(AaItB, Bool.or(X.AaText.starts(w, "="), X.AaText.starts(w, "+=")), AaItB.mode(AaItB.push(b, T.AaTWord{w, l}), AaImVar{line}), AaItB.norm(AaItB.mode(b, AaImNorm{}), T.AaTWord{w, l}))
    case _:
      AaItB.norm(AaItB.mode(b, AaImNorm{}), t)

# an assignment takes the tokens of its line; a comma there is an error
def AaItB.var.same(same: Bool, +b: AaItB, t: T.AaTok, +line: U32) -> AaItB:
  match same:
    case True{}:
      match t:
        case T.AaTWord{w, l}:
          AaItB.push(b, T.AaTWord{w, l})
        case T.AaTQuoted{q, l}:
          AaItB.push(b, T.AaTQuoted{q, l})
        case _:
          AaItB.err(b, E.AaErrSyntax{AaItB.file(b), line})
    case False{}:
      AaItB.norm(AaItB.flush(b, 2n, line), t)

def AaItB.var(+b: AaItB, +t: T.AaTok, +line: U32) -> AaItB:
  AaItB.var.same(U32.is_eq(T.AaTok.line(t), line), b, t, line)

# the name inside <...>
def AaIt.magic(+w: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(U32.is_eq(X.AaText.head(w), 60), U32.is_eq(X.AaText.last(w, 0), 62)), Some{X.AaText.init(X.AaText.tail(w))}, None{})

def AaItB.inc.magic(m: Maybe<&2, List<&2, U32>>, +b: AaItB, opt: Bool, +line: U32) -> AaItB:
  match m:
    case None{}:
      AaItB.err(b, E.AaErrSyntax{AaItB.file(b), line})
    case Some{n}:
      AaItB.emit(b, AaIInclude{n, opt, E.AaSrc{AaItB.file(b), line}})

def AaItB.inc.path(+b: AaItB, t: T.AaTok, +opt: Bool, +line: U32) -> AaItB:
  match t:
    case T.AaTWord{w, l}:
      AaItB.inc.magic(AaIt.magic(w), b, opt, line)
    case T.AaTQuoted{q, l}:
      AaItB.emit(b, AaIInclude{q, opt, E.AaSrc{AaItB.file(b), line}})
    case _:
      AaItB.err(b, E.AaErrSyntax{AaItB.file(b), line})

def AaItB.inc(stage: Nat, +b: AaItB, +t: T.AaTok, +line: U32) -> AaItB:
  match stage:
    case 0n:
      Bool.pick(AaItB, T.AaTok.is(t, "if"), AaItB.mode(b, AaImInc{1n, line}), AaItB.inc.path(b, t, False{}, line))
    case 1n+s:
      match s:
        case 0n:
          Bool.pick(AaItB, T.AaTok.is(t, "exists"), AaItB.mode(b, AaImInc{2n, line}), AaItB.err(b, E.AaErrSyntax{AaItB.file(b), line}))
        case 1n+r:
          AaItB.inc.path(b, t, True{}, line)

def AaItB.step(b: AaItB, +t: T.AaTok) -> AaItB:
  match b:
    case AaItB{f, m, pe, pd, out}:
      match m:
        case AaImNorm{}:
          AaItB.norm(AaItB{f, AaImNorm{}, pe, pd, out}, t)
        case AaImVarCand{+l}:
          AaItB.varcand(AaItB{f, AaImVarCand{l}, pe, pd, out}, t, l)
        case AaImVar{+l}:
          AaItB.var(AaItB{f, AaImVar{l}, pe, pd, out}, t, l)
        case AaImInc{+s, +l}:
          AaItB.inc(s, AaItB{f, AaImInc{s, l}, pe, pd, out}, t, l)

def AaItB.run(ts: List<&2, T.AaTok>, b: AaItB) -> AaItB:
  match ts:
    case Nil{}:
      b
    case Con{t, rest}:
      AaItB.run(rest, AaItB.step(b, t))

def AaItB.finish(b: AaItB) -> List<&2, AaItem>:
  match b:
    case AaItB{+f, m, pe, pd, out}:
      match m:
        case AaImNorm{}:
          match pe:
            case Nil{}:
              AaItem.rev_onto(out, Nil{})
            case Con{h, t}:
              AaItem.rev_onto(Con{AaIError{E.AaErrSyntax{f, T.AaTok.line(h)}}, out}, Nil{})
        case AaImVarCand{+l}:
          AaItem.rev_onto(Con{AaIError{E.AaErrSyntax{f, l}}, out}, Nil{})
        case AaImVar{+l}:
          AaItem.rev_onto(Con{AaIVar{T.AaTok.rev_onto(pe, Nil{}), E.AaSrc{f, l}}, out}, Nil{})
        case AaImInc{+s, +l}:
          AaItem.rev_onto(Con{AaIError{E.AaErrSyntax{f, l}}, out}, Nil{})

def AaIt.of_lex(r: Result<&2, &2, U32, List<&2, T.AaTok>>, +file: List<&2, U32>) -> List<&2, AaItem>:
  match r:
    case Fail{l}:
      [AaIError{E.AaErrLex{file, l}}]
    case Done{ts}:
      AaItB.finish(AaItB.run(ts, AaItB{file, AaImNorm{}, Nil{}, 0n, Nil{}}))

# the items of a file's text; a fault becomes an error item
def AaParse.items(+file: List<&2, U32>, text: List<&2, U32>) -> List<&2, AaItem>:
  AaIt.of_lex(T.AaTok.lex(text), file)

# Includes

type AaExpOut is Data:
  AaExpOut{items: List<&2, AaItem>, scopes: List<&2, List<&2, List<&2, U32>>>}

def AaExpOut.items(o: AaExpOut) -> List<&2, AaItem>:
  match o:
    case AaExpOut{i, s}:
      i

def AaExpOut.scopes(o: AaExpOut) -> List<&2, List<&2, List<&2, U32>>>:
  match o:
    case AaExpOut{i, s}:
      s

def AaParse.find_file(fs: List<&2, AaSrcFile>, +name: List<&2, U32>) -> Maybe<&2, AaSrcFile>:
  match fs:
    case Nil{}:
      None{}
    case Con{+f, t}:
      match f:
        case AaSrcFile{n, x}:
          Bool.pick(Maybe<&2, AaSrcFile>, X.AaText.eq(n, name), Some{f}, AaParse.find_file(t, name))

# the file is already included in the innermost block
def AaParse.seen(scopes: List<&2, List<&2, List<&2, U32>>>, +name: List<&2, U32>) -> Bool:
  match scopes:
    case Nil{}:
      False{}
    case Con{s, t}:
      X.AaText.member(s, name)

def AaParse.mark(scopes: List<&2, List<&2, List<&2, U32>>>, name: List<&2, U32>) -> List<&2, List<&2, List<&2, U32>>>:
  match scopes:
    case Nil{}:
      [[name]]
    case Con{s, t}:
      Con{Con{name, s}, t}

def AaParse.pop(scopes: List<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, List<&2, U32>>>:
  match scopes:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      t

# the items an include brings in
def AaParse.inc_items(m: Maybe<&2, AaSrcFile>, opt: Bool, src: E.AaSrc) -> List<&2, AaItem>:
  match m:
    case None{}:
      match opt:
        case True{}:
          Nil{}
        case False{}:
          [AaIError{E.AaSrc.include(src)}]
    case Some{f}:
      match f:
        case AaSrcFile{+n, x}:
          AaParse.items(n, x)

# includes nested too deep
def AaParse.expand0(items: List<&2, AaItem>, +scopes: List<&2, List<&2, List<&2, U32>>>, +acc: List<&2, AaItem>) -> AaExpOut:
  match items:
    case Nil{}:
      AaExpOut{AaItem.rev_onto(acc, Nil{}), scopes}
    case Con{it, rest}:
      match it:
        case AaIOpen{ts, src}:
          AaParse.expand0(rest, Con{Nil{}, scopes}, Con{AaIOpen{ts, src}, acc})
        case AaIClose{src}:
          AaParse.expand0(rest, AaParse.pop(scopes), Con{AaIClose{src}, acc})
        case AaIInclude{+name, opt, src}:
          AaParse.expand0(rest, scopes, Bool.pick(List<&2, AaItem>, AaParse.seen(scopes, name), acc, Con{AaIError{E.AaSrc.include_depth(src)}, acc}))
        case AaIStmt{ts, src}:
          AaParse.expand0(rest, scopes, Con{AaIStmt{ts, src}, acc})
        case AaIVar{ts, src}:
          AaParse.expand0(rest, scopes, Con{AaIVar{ts, src}, acc})
        case AaIError{e}:
          AaParse.expand0(rest, scopes, Con{AaIError{e}, acc})

# the items with every include replaced by the included file's items;
# scopes: the files included so far in each open block, innermost first
def AaParse.expand(+fuel: Nat, items: List<&2, AaItem>, +files: List<&2, AaSrcFile>, +scopes: List<&2, List<&2, List<&2, U32>>>, +acc: List<&2, AaItem>) -> AaExpOut:
  match fuel:
    case 0n:
      AaParse.expand0(items, scopes, acc)
    case 1n+f:
      match items:
        case Nil{}:
          AaExpOut{AaItem.rev_onto(acc, Nil{}), scopes}
        case Con{it, +rest}:
          match it:
            case AaIOpen{ts, src}:
              AaParse.expand(fuel, rest, files, Con{Nil{}, scopes}, Con{AaIOpen{ts, src}, acc})
            case AaIClose{src}:
              AaParse.expand(fuel, rest, files, AaParse.pop(scopes), Con{AaIClose{src}, acc})
            case AaIInclude{+name, opt, +src}:
              # Bend evaluates both arms of a Bool.pick, so the recursion is
              # one call whose arguments depend on whether the file is seen
              +seen = AaParse.seen(scopes, name)
              +sub = AaParse.expand(f, AaParse.inc_items(Bool.pick(Maybe<&2, AaSrcFile>, seen, None{}, AaParse.find_file(files, name)), Bool.or(seen, opt), src), files, AaParse.mark(scopes, name), Nil{})
              AaParse.expand(fuel, rest, files, Bool.pick(List<&2, List<&2, List<&2, U32>>>, seen, scopes, AaExpOut.scopes(sub)), Bool.pick(List<&2, AaItem>, seen, acc, AaItem.rev_onto(AaExpOut.items(sub), acc)))
            case AaIStmt{ts, src}:
              AaParse.expand(fuel, rest, files, scopes, Con{AaIStmt{ts, src}, acc})
            case AaIVar{ts, src}:
              AaParse.expand(fuel, rest, files, scopes, Con{AaIVar{ts, src}, acc})
            case AaIError{e}:
              AaParse.expand(fuel, rest, files, scopes, Con{AaIError{e}, acc})

def AaParse.first_error(items: List<&2, AaItem>) -> Maybe<&2, E.AaError>:
  match items:
    case Nil{}:
      None{}
    case Con{it, rest}:
      match it:
        case AaIError{e}:
          Some{e}
        case _:
          AaParse.first_error(rest)

# Variables

def AaVars.find(env: List<&2, O.AaVar>, +name: List<&2, U32>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match env:
    case Nil{}:
      None{}
    case Con{v, t}:
      match v:
        case O.AaVar{n, +vals}:
          Bool.pick(Maybe<&2, List<&2, List<&2, U32>>>, X.AaText.eq(n, name), Some{vals}, AaVars.find(t, name))

def AaVars.is_some(m: Maybe<&2, List<&2, List<&2, U32>>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# values added to a variable's
def AaVars.extend(env: List<&2, O.AaVar>, +name: List<&2, U32>, +more: List<&2, List<&2, U32>>) -> List<&2, O.AaVar>:
  match env:
    case Nil{}:
      Nil{}
    case Con{v, t}:
      match v:
        case O.AaVar{+n, +vals}:
          Con{Bool.pick(O.AaVar, X.AaText.eq(n, name), O.AaVar{n, X.AaText.lappend(vals, more)}, O.AaVar{n, vals}), AaVars.extend(t, name, more)}

# a variable name: a letter, then letters, digits and '_'
def AaVars.name_ok.go(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.or(T.AaTerm.letter(h), Bool.or(Bool.and(U32.is_ge(h, 48), U32.is_le(h, 57)), U32.is_eq(h, 95))), AaVars.name_ok.go(t))

def AaVars.name_ok(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.and(T.AaTerm.letter(h), AaVars.name_ok.go(t))

# @{NAME} at the start of a word: the name and what follows the '}'
type AaVRef is Data:
  AaVRef{name: List<&2, U32>, rest: List<&2, U32>}

def AaVars.ref.go(xs: List<&2, U32>, +acc: List<&2, U32>) -> Maybe<&2, AaVRef>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, +t}:
      Bool.pick(Maybe<&2, AaVRef>, U32.is_eq(h, 125), Some{AaVRef{X.AaText.rev(acc), t}}, AaVars.ref.go(t, Con{h, acc}))

def AaVars.ref(+w: List<&2, U32>) -> Maybe<&2, AaVRef>:
  Bool.pick(Maybe<&2, AaVRef>, X.AaText.starts(w, "@{"), AaVars.ref.go(X.AaText.drop(2n, w), Nil{}), None{})

def AaVars.values.cons(x: List<&2, U32>, r: Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>) -> Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{xs}:
      Done{Con{x, xs}}

# the text of each word or string
def AaVars.values(ts: List<&2, T.AaTok>, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
  match ts:
    case Nil{}:
      Done{Nil{}}
    case Con{t, rest}:
      match t:
        case T.AaTWord{w, l}:
          AaVars.values.cons(w, AaVars.values(rest, src))
        case T.AaTQuoted{q, l}:
          AaVars.values.cons(q, AaVars.values(rest, src))
        case _:
          Fail{E.AaSrc.syntax(src)}

# an assignment: name, whether it is +=, the values
type AaAssign is Data:
  AaAssign{name: List<&2, U32>, append: Bool, values: List<&2, List<&2, U32>>}

# the operator at the start of x: += (True) or = (False), and what follows it
def AaVars.op(+x: List<&2, U32>) -> Maybe<&2, AaVRef>:
  Bool.pick(Maybe<&2, AaVRef>, X.AaText.starts(x, "+="), Some{AaVRef{[1], X.AaText.drop(2n, x)}}, Bool.pick(Maybe<&2, AaVRef>, X.AaText.starts(x, "="), Some{AaVRef{Nil{}, X.AaText.drop(1n, x)}}, None{}))

def AaVars.first(rem: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match rem:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      [Con{h, t}]

def AaVars.assign.op(m: Maybe<&2, AaVRef>, name: List<&2, U32>, rest: List<&2, T.AaTok>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaAssign>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{o}:
      match o:
        case AaVRef{tag, rem}:
          do Result<&2, &2, E.AaError, AaAssign>:
            vs : List<&2, List<&2, U32>> <- AaVars.values(rest, src)
            return AaAssign{name, Bool.not(X.AaText.is_nil(tag)), X.AaText.lappend(AaVars.first(rem), vs)}

# @{NAME} then a separate = or += word
def AaVars.assign.next(ts: List<&2, T.AaTok>, name: List<&2, U32>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaAssign>:
  match ts:
    case Nil{}:
      Fail{E.AaSrc.syntax(src)}
    case Con{t, rest}:
      match t:
        case T.AaTWord{+w, l}:
          AaVars.assign.op(AaVars.op(w), name, rest, src)
        case _:
          Fail{E.AaSrc.syntax(src)}

def AaVars.assign.ref(m: Maybe<&2, AaVRef>, +rest: List<&2, T.AaTok>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaAssign>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{r}:
      match r:
        case AaVRef{+name, +after}:
          Bool.pick(Result<&2, &2, E.AaError, AaAssign>, AaVars.name_ok(name), Bool.pick(Result<&2, &2, E.AaError, AaAssign>, X.AaText.is_nil(after), AaVars.assign.next(rest, name, src), AaVars.assign.op(AaVars.op(after), name, rest, src)), Fail{E.AaSrc.syntax(src)})

def AaVars.assign.parse(ts: List<&2, T.AaTok>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaAssign>:
  match ts:
    case Nil{}:
      Fail{E.AaSrc.syntax(src)}
    case Con{t, rest}:
      match t:
        case T.AaTWord{+w, l}:
          AaVars.assign.ref(AaVars.ref(w), rest, src)
        case _:
          Fail{E.AaSrc.syntax(src)}

# the environment after an assignment
def AaVars.apply.go(ap: Bool, known: Bool, env: List<&2, O.AaVar>, name: List<&2, U32>, vs: List<&2, List<&2, U32>>, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, O.AaVar>>:
  match ap:
    case True{}:
      match known:
        case True{}:
          Done{AaVars.extend(env, name, vs)}
        case False{}:
          Fail{E.AaSrc.var_redefined(src)}
    case False{}:
      match known:
        case True{}:
          Fail{E.AaSrc.var_redefined(src)}
        case False{}:
          Done{Con{O.AaVar{name, vs}, env}}

def AaVars.apply(a: AaAssign, +env: List<&2, O.AaVar>, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, O.AaVar>>:
  match a:
    case AaAssign{+name, ap, vs}:
      AaVars.apply.go(ap, AaVars.is_some(AaVars.find(env, name)), env, name, vs, src)

# Expanding variables in a text

def AaVars.unslash(+v: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_eq(X.AaText.last(v, 0), 47), X.AaText.init(v), v)

def AaVars.value(strip: Bool, +v: List<&2, U32>) -> List<&2, U32>:
  match strip:
    case True{}:
      AaVars.unslash(v)
    case False{}:
      v

# the values, separated by commas, last character first, onto acc
def AaVars.join(vs: List<&2, List<&2, U32>>, +strip: Bool, +first: Bool, +acc: List<&2, U32>) -> List<&2, U32>:
  match vs:
    case Nil{}:
      acc
    case Con{v, t}:
      AaVars.join(t, strip, False{}, X.AaText.rev_onto(AaVars.value(strip, v), Bool.pick(List<&2, U32>, first, acc, Con{44, acc})))

# the expansion of one reference (last character first, onto out)
def AaVars.emit(m: Maybe<&2, List<&2, List<&2, U32>>>, +strip: Bool, out: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      match vs:
        case Nil{}:
          None{}
        case Con{v, rest}:
          match rest:
            case Nil{}:
              Some{X.AaText.rev_onto(AaVars.value(strip, v), out)}
            case Con{w, more}:
              Some{Con{125, AaVars.join(Con{v, Con{w, more}}, strip, True{}, Con{123, out})}}

def AaVars.lookup(+env: List<&2, O.AaVar>, pname: Maybe<&2, List<&2, U32>>, +name: List<&2, U32>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match pname:
    case None{}:
      AaVars.find(env, name)
    case Some{p}:
      Bool.pick(Maybe<&2, List<&2, List<&2, U32>>>, X.AaText.is(name, "profile_name"), Some{[p]}, AaVars.find(env, name))

# the substitution: mode (0 text, 1 after an at sign, 2 inside a reference),
# the name read so far, the output (both last character first), still well formed
type AaSb is Data:
  AaSb{mode: Nat, name: List<&2, U32>, out: List<&2, U32>, ok: Bool}

def AaSb.close(r: Maybe<&2, List<&2, U32>>, ok: Bool) -> AaSb:
  match r:
    case None{}:
      AaSb{0n, Nil{}, Nil{}, False{}}
    case Some{out}:
      AaSb{0n, Nil{}, out, ok}

def AaSb.text(+h: U32, +out: List<&2, U32>, +ok: Bool) -> AaSb:
  Bool.pick(AaSb, U32.is_eq(h, 64), AaSb{1n, Nil{}, out, ok}, AaSb{0n, Nil{}, Con{h, out}, ok})

def AaSb.step(st: AaSb, +h: U32, +next: U32, +env: List<&2, O.AaVar>, +pname: Maybe<&2, List<&2, U32>>) -> AaSb:
  match st:
    case AaSb{m, +nm, +out, +ok}:
      match m:
        case 0n:
          AaSb.text(h, out, ok)
        case 1n+m1:
          match m1:
            case 0n:
              Bool.pick(AaSb, U32.is_eq(h, 123), AaSb{2n, Nil{}, out, ok}, AaSb.text(h, Con{64, out}, ok))
            case 1n+m2:
              Bool.pick(AaSb, U32.is_eq(h, 125), AaSb.close(AaVars.emit(AaVars.lookup(env, pname, X.AaText.rev(nm)), U32.is_eq(next, 47), out), ok), AaSb{2n, Con{h, nm}, out, ok})

def AaSb.run(xs: List<&2, U32>, st: AaSb, +env: List<&2, O.AaVar>, +pname: Maybe<&2, List<&2, U32>>) -> AaSb:
  match xs:
    case Nil{}:
      st
    case Con{+h, +t}:
      AaSb.run(t, AaSb.step(st, h, X.AaText.head(t), env, pname), env, pname)

def AaSb.result(st: AaSb) -> Maybe<&2, List<&2, U32>>:
  match st:
    case AaSb{m, nm, out, ok}:
      match m:
        case 0n:
          match ok:
            case False{}:
              None{}
            case True{}:
              Some{X.AaText.rev(out)}
        case 1n+m1:
          match m1:
            case 0n:
              match ok:
                case False{}:
                  None{}
                case True{}:
                  Some{X.AaText.rev(Con{64, out})}
            case 1n+m2:
              None{}

# one round: every reference replaced by its values
def AaVars.subst(xs: List<&2, U32>, +env: List<&2, O.AaVar>, +pname: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  AaSb.result(AaSb.run(xs, AaSb{0n, Nil{}, Nil{}, True{}}, env, pname))

# a reference remains: an at sign before an opening brace
def AaVars.has_ref(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, +t}:
      Bool.or(Bool.and(U32.is_eq(h, 64), U32.is_eq(X.AaText.head(t), 123)), AaVars.has_ref(t))

# whether a text still holds a reference; None stays None
def AaVars.more(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{t}:
      AaVars.has_ref(t)

# more: m still holds a reference (computed by the caller, so that a text
# without one is not substituted again)
def AaVars.expand.go(fuel: Nat, +more: Bool, m: Maybe<&2, List<&2, U32>>, +env: List<&2, O.AaVar>, +pname: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      match more:
        case True{}:
          None{}
        case False{}:
          m
    case 1n+f:
      match more:
        case False{}:
          m
        case True{}:
          match m:
            case None{}:
              None{}
            case Some{t}:
              +n = AaVars.subst(t, env, pname)
              AaVars.expand.go(f, AaVars.more(n), n, env, pname)

# xs with its variables expanded (values may refer to variables, to a depth
# of eight); None if a variable is not assigned
def AaVars.expand(+xs: List<&2, U32>, +env: List<&2, O.AaVar>, +pname: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  AaVars.expand.go(8n, AaVars.has_ref(xs), Some{xs}, env, pname)

def AaVars.tok.go(m: Maybe<&2, List<&2, U32>>, quoted: Bool, l: U32, src: E.AaSrc) -> Result<&2, &2, E.AaError, T.AaTok>:
  match m:
    case None{}:
      Fail{E.AaSrc.var_undefined(src)}
    case Some{x}:
      match quoted:
        case True{}:
          Done{T.AaTQuoted{x, l}}
        case False{}:
          Done{T.AaTWord{x, l}}

def AaVars.tok(t: T.AaTok, +env: List<&2, O.AaVar>, +pname: Maybe<&2, List<&2, U32>>, src: E.AaSrc) -> Result<&2, &2, E.AaError, T.AaTok>:
  match t:
    case T.AaTWord{w, l}:
      AaVars.tok.go(AaVars.expand(w, env, pname), False{}, l, src)
    case T.AaTQuoted{q, l}:
      AaVars.tok.go(AaVars.expand(q, env, pname), True{}, l, src)
    case T.AaTOpen{l}:
      Done{T.AaTOpen{l}}
    case T.AaTClose{l}:
      Done{T.AaTClose{l}}
    case T.AaTLParen{l}:
      Done{T.AaTLParen{l}}
    case T.AaTRParen{l}:
      Done{T.AaTRParen{l}}
    case T.AaTComma{l}:
      Done{T.AaTComma{l}}

# a statement's tokens with variables expanded
def AaVars.toks(ts: List<&2, T.AaTok>, +env: List<&2, O.AaVar>, +pname: Maybe<&2, List<&2, U32>>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, T.AaTok>>:
  match ts:
    case Nil{}:
      Done{Nil{}}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, List<&2, T.AaTok>>:
        x : T.AaTok <- AaVars.tok(t, env, pname, src)
        xs : List<&2, T.AaTok> <- AaVars.toks(rest, env, pname, src)
        return Con{x, xs}

# The preamble: variables and aliases

type AaAlias is Data:
  AaAlias{from: List<&2, U32>, to: List<&2, U32>}

type AaPre is Data:
  AaPre{env: List<&2, O.AaVar>, aliases: List<&2, AaAlias>, depth: Nat, started: Bool, err: Maybe<&2, E.AaError>}

def AaPre.fail(p: AaPre, e: E.AaError) -> AaPre:
  match p:
    case AaPre{v, a, d, s, err}:
      match err:
        case None{}:
          AaPre{v, a, d, s, Some{e}}
        case Some{e0}:
          AaPre{v, a, d, s, Some{e0}}

def AaPre.env(r: Result<&2, &2, E.AaError, List<&2, O.AaVar>>, p: AaPre) -> AaPre:
  match r:
    case Fail{e}:
      AaPre.fail(p, e)
    case Done{v}:
      match p:
        case AaPre{v0, a, d, s, err}:
          AaPre{v, a, d, s, err}

def AaPre.assign(r: Result<&2, &2, E.AaError, AaAssign>, +p: AaPre, src: E.AaSrc) -> AaPre:
  match r:
    case Fail{e}:
      AaPre.fail(p, e)
    case Done{a}:
      match p:
        case AaPre{+v, al, d, s, err}:
          AaPre.env(AaVars.apply(a, v, src), AaPre{v, al, d, s, err})

def AaPre.text(t: T.AaTok) -> Maybe<&2, List<&2, U32>>:
  match t:
    case T.AaTWord{w, l}:
      Some{w}
    case T.AaTQuoted{q, l}:
      Some{q}
    case _:
      None{}

# alias FROM -> TO
def AaPre.alias.go(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>, p: AaPre, src: E.AaSrc) -> AaPre:
  match a:
    case None{}:
      AaPre.fail(p, E.AaSrc.syntax(src))
    case Some{x}:
      match b:
        case None{}:
          AaPre.fail(p, E.AaSrc.syntax(src))
        case Some{y}:
          match p:
            case AaPre{v, al, d, s, err}:
              AaPre{v, Con{AaAlias{x, y}, al}, d, s, err}

def AaPre.alias(ts: List<&2, T.AaTok>, +p: AaPre, +src: E.AaSrc) -> AaPre:
  match ts:
    case Con{a, r1}:
      match r1:
        case Con{arrow, r2}:
          match r2:
            case Con{b, r3}:
              match r3:
                case Nil{}:
                  Bool.pick(AaPre, T.AaTok.is(arrow, "->"), AaPre.alias.go(AaPre.text(a), AaPre.text(b), p, src), AaPre.fail(p, E.AaSrc.syntax(src)))
                case Con{x, r4}:
                  AaPre.fail(p, E.AaSrc.syntax(src))
            case Nil{}:
              AaPre.fail(p, E.AaSrc.syntax(src))
        case Nil{}:
          AaPre.fail(p, E.AaSrc.syntax(src))
    case Nil{}:
      AaPre.fail(p, E.AaSrc.syntax(src))

def AaPre.depth(p: AaPre) -> Nat:
  match p:
    case AaPre{v, a, d, s, err}:
      d

def AaPre.started(p: AaPre) -> Bool:
  match p:
    case AaPre{v, a, d, s, err}:
      s

# a statement at the top level: alias (before the first profile), abi, or an error
def AaPre.top(ts: List<&2, T.AaTok>, +p: AaPre, +src: E.AaSrc) -> AaPre:
  match ts:
    case Nil{}:
      AaPre.fail(p, E.AaSrc.syntax(src))
    case Con{+t, rest}:
      Bool.pick(AaPre, T.AaTok.is(t, "alias"), Bool.pick(AaPre, AaPre.started(p), AaPre.fail(p, E.AaSrc.preamble(src)), AaPre.alias(rest, p, src)), Bool.pick(AaPre, T.AaTok.is(t, "abi"), p, AaPre.fail(p, E.AaSrc.syntax(src))))

def AaPre.stmt(d: Nat, ts: List<&2, T.AaTok>, +p: AaPre, +src: E.AaSrc) -> AaPre:
  match d:
    case 0n:
      AaPre.top(ts, p, src)
    case 1n+e:
      p

def AaPre.var(ok: Bool, ts: List<&2, T.AaTok>, +p: AaPre, +src: E.AaSrc) -> AaPre:
  match ok:
    case True{}:
      AaPre.assign(AaVars.assign.parse(ts, src), p, src)
    case False{}:
      AaPre.fail(p, E.AaSrc.preamble(src))

def AaPre.open(p: AaPre) -> AaPre:
  match p:
    case AaPre{v, a, d, s, err}:
      AaPre{v, a, 1n+d, True{}, err}

def AaPre.close(p: AaPre, src: E.AaSrc) -> AaPre:
  match p:
    case AaPre{v, a, d, s, err}:
      match d:
        case 0n:
          AaPre.fail(AaPre{v, a, 0n, s, err}, E.AaSrc.syntax(src))
        case 1n+e:
          AaPre{v, a, e, s, err}

def AaPre.step(+p: AaPre, it: AaItem) -> AaPre:
  match it:
    case AaIVar{ts, src}:
      AaPre.var(Bool.and(Nat.is_eq(AaPre.depth(p), 0n), Bool.not(AaPre.started(p))), ts, p, src)
    case AaIStmt{ts, src}:
      AaPre.stmt(AaPre.depth(p), ts, p, src)
    case AaIOpen{ts, src}:
      AaPre.open(p)
    case AaIClose{src}:
      AaPre.close(p, src)
    case AaIInclude{n, o, src}:
      p
    case AaIError{e}:
      AaPre.fail(p, e)

def AaPre.run(items: List<&2, AaItem>, p: AaPre) -> AaPre:
  match items:
    case Nil{}:
      p
    case Con{it, rest}:
      AaPre.run(rest, AaPre.step(p, it))

# Qualifiers: [audit] [allow | deny] [owner], in that order; a block's
# qualifiers apply to the rules inside it. access: 0 neither, 1 allow, 2 deny

type AaBQ is Data:
  AaBQ{audit: Bool, access: Nat, owner: Bool}

def AaBQ.none() -> AaBQ:
  AaBQ{False{}, 0n, False{}}

# what a term is as a qualifier: 1 audit, 2 allow, 3 deny, 4 owner, 0 none
def AaQ.kind(+t: T.AaTerm) -> Nat:
  Bool.pick(Nat, T.AaTerm.is(t, "audit"), 1n, Bool.pick(Nat, T.AaTerm.is(t, "allow"), 2n, Bool.pick(Nat, T.AaTerm.is(t, "deny"), 3n, Bool.pick(Nat, T.AaTerm.is(t, "owner"), 4n, 0n))))

# the qualifier k may come at stage s (0 start, 1 after audit, 2 after allow
# or deny, 3 after owner), and the stage after it
def AaQ.allowed(k: Nat, s: Nat) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+k1:
      match k1:
        case 0n:
          Nat.is_eq(s, 0n)
        case 1n+k2:
          match k2:
            case 0n:
              Nat.is_le(s, 1n)
            case 1n+k3:
              match k3:
                case 0n:
                  Nat.is_le(s, 1n)
                case 1n+k4:
                  Nat.is_le(s, 2n)

def AaQ.stage(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+k1:
      match k1:
        case 0n:
          1n
        case 1n+k2:
          match k2:
            case 0n:
              2n
            case 1n+k3:
              match k3:
                case 0n:
                  2n
                case 1n+k4:
                  3n

def AaQ.add(q: AaBQ, k: Nat) -> AaBQ:
  match q:
    case AaBQ{a, c, o}:
      match k:
        case 0n:
          AaBQ{a, c, o}
        case 1n+k1:
          match k1:
            case 0n:
              AaBQ{True{}, c, o}
            case 1n+k2:
              match k2:
                case 0n:
                  AaBQ{a, 1n, o}
                case 1n+k3:
                  match k3:
                    case 0n:
                      AaBQ{a, 2n, o}
                    case 1n+k4:
                      AaBQ{a, c, True{}}

type AaQP is Data:
  AaQP{q: AaBQ, rest: List<&2, T.AaTerm>}

def AaQ.parse.go(+k: Nat, +t: T.AaTerm, +rest: List<&2, T.AaTerm>, +stage: Nat, +q: AaBQ, more: AaQP) -> AaQP:
  Bool.pick(AaQP, AaQ.allowed(k, stage), more, AaQP{q, Con{t, rest}})

# the leading qualifiers of a rule's terms, and the terms after them
def AaQ.parse(ts: List<&2, T.AaTerm>, +stage: Nat, +q: AaBQ) -> AaQP:
  match ts:
    case Nil{}:
      AaQP{q, Nil{}}
    case Con{+t, +rest}:
      +k = AaQ.kind(t)
      AaQ.parse.go(k, t, rest, stage, q, AaQ.parse(rest, AaQ.stage(k), AaQ.add(q, k)))

# a block's qualifiers with a rule's (or an inner block's): allow and deny conflict
def AaQ.combine(b: AaBQ, r: AaBQ, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaBQ>:
  match b:
    case AaBQ{a1, +c1, o1}:
      match r:
        case AaBQ{a2, +c2, o2}:
          Bool.pick(Result<&2, &2, E.AaError, AaBQ>, Bool.and(Bool.and(Nat.is_gt(c1, 0n), Nat.is_gt(c2, 0n)), Bool.not(Nat.is_eq(c1, c2))), Fail{E.AaSrc.syntax(src)}, Done{AaBQ{Bool.or(a1, a2), Nat.max(c1, c2), Bool.or(o1, o2)}})

def AaBQ.qual(q: AaBQ) -> P.AaQual:
  match q:
    case AaBQ{a, c, o}:
      P.AaQual{a, Nat.is_eq(c, 2n), o}

# Rules

type AaCtx is Data:
  AaCtx{env: List<&2, O.AaVar>, aliases: List<&2, AaAlias>}

def AaCtx.env(c: AaCtx) -> List<&2, O.AaVar>:
  match c:
    case AaCtx{e, a}:
      e

def AaCtx.aliases(c: AaCtx) -> List<&2, AaAlias>:
  match c:
    case AaCtx{e, a}:
      a

def AaParse.unsupported() -> List<&2, String>:
  ["link", "unix", "pivot_root", "set", "mqueue", "io_uring", "userns", "all", "rlimit"]

# the keyword of a rule: 1 capability, 2 network, 3 signal, 4 ptrace, 5
# mount, 6 remount, 7 umount, 8 dbus, 9 change_profile, 10 file, 11 a rule
# kind outside the model, 12 a statement that belongs in the preamble, 0 none
# (a file rule without the keyword)
def AaParse.keyword(+t: T.AaTerm) -> Nat:
  Bool.pick(Nat, T.AaTerm.is(t, "capability"), 1n, Bool.pick(Nat, T.AaTerm.is(t, "network"), 2n, Bool.pick(Nat, T.AaTerm.is(t, "signal"), 3n, Bool.pick(Nat, T.AaTerm.is(t, "ptrace"), 4n, Bool.pick(Nat, T.AaTerm.is(t, "mount"), 5n, Bool.pick(Nat, T.AaTerm.is(t, "remount"), 6n, Bool.pick(Nat, T.AaTerm.is(t, "umount"), 7n, Bool.pick(Nat, T.AaTerm.is(t, "dbus"), 8n, Bool.pick(Nat, T.AaTerm.is(t, "change_profile"), 9n, Bool.pick(Nat, T.AaTerm.is(t, "file"), 10n, Bool.pick(Nat, T.AaTerm.is_one_of(t, AaParse.unsupported()), 11n, Bool.pick(Nat, Bool.or(T.AaTerm.is(t, "alias"), T.AaTerm.is(t, "abi")), 12n, 0n))))))))))))

def AaParse.wrap.cap(r: Result<&2, &2, E.AaError, RC.AaCapRule>) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{PR.AaRules.cap(x)}

def AaParse.wrap.net(r: Result<&2, &2, E.AaError, RN.AaNetRule>) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{PR.AaRules.net(x)}

def AaParse.wrap.signal(r: Result<&2, &2, E.AaError, RS.AaSignalRule>) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{PR.AaRules.signal(x)}

def AaParse.wrap.ptrace(r: Result<&2, &2, E.AaError, RP.AaPtraceRule>) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{PR.AaRules.ptrace(x)}

def AaParse.wrap.mount(r: Result<&2, &2, E.AaError, RM.AaMountRule>) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{PR.AaRules.mount(x)}

def AaParse.wrap.dbus(r: Result<&2, &2, E.AaError, RD.AaDbusRule>) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{PR.AaRules.dbus_rule(x)}

def AaParse.wrap.change(r: Result<&2, &2, E.AaError, RX.AaChangeRule>) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{PR.AaRules.change(x)}

def AaParse.alias.glob(m: Maybe<&2, G.AaGlob>, r: F.AaFileRule) -> List<&2, F.AaFileRule>:
  match m:
    case None{}:
      Nil{}
    case Some{g}:
      match r:
        case F.AaFileRule{q, text, g0, p, e, tg}:
          [F.AaFileRule{q, text, g, p, e, tg}]

# a file rule copied under an alias whose source starts its pattern
def AaParse.alias.one(a: AaAlias, r: F.AaFileRule) -> List<&2, F.AaFileRule>:
  match a:
    case AaAlias{+from, +to}:
      match r:
        case F.AaFileRule{q, +text, g, p, e, tg}:
          Bool.pick(List<&2, F.AaFileRule>, Bool.and(Bool.not(X.AaText.is_nil(text)), X.AaText.prefix(text, from)), AaParse.alias.glob(G.AaGlob.parse(X.AaText.append(to, X.AaText.drop(X.AaText.len(from), text))), F.AaFileRule{q, X.AaText.append(to, X.AaText.drop(X.AaText.len(from), text)), g, p, e, tg}), Nil{})

def AaParse.alias.all(als: List<&2, AaAlias>, +r: F.AaFileRule) -> List<&2, F.AaFileRule>:
  match als:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      F.AaFileRule.append(AaParse.alias.one(a, r), AaParse.alias.all(t, r))

def AaParse.wrap.file(r: Result<&2, &2, E.AaError, F.AaFileRule>, als: List<&2, AaAlias>) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+x}:
      Done{PR.AaRules.with_files(PR.AaRules.empty(), Con{x, AaParse.alias.all(als, x)})}

def AaParse.dispatch(k: Nat, +t: T.AaTerm, +rest: List<&2, T.AaTerm>, +q: P.AaQual, +als: List<&2, AaAlias>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match k:
    case 0n:
      AaParse.wrap.file(F.AaFile.parse(Con{t, rest}, q, src), als)
    case 1n+k1:
      match k1:
        case 0n:
          AaParse.wrap.cap(RC.AaCap.parse(rest, q, src))
        case 1n+k2:
          match k2:
            case 0n:
              AaParse.wrap.net(RN.AaNet.parse(rest, q, src))
            case 1n+k3:
              match k3:
                case 0n:
                  AaParse.wrap.signal(RS.AaSignal.parse(rest, q, src))
                case 1n+k4:
                  match k4:
                    case 0n:
                      AaParse.wrap.ptrace(RP.AaPtrace.parse(rest, q, src))
                    case 1n+k5:
                      match k5:
                        case 0n:
                          AaParse.wrap.mount(RM.AaMount.parse(RM.AaMountOpMount{}, rest, q, src))
                        case 1n+k6:
                          match k6:
                            case 0n:
                              AaParse.wrap.mount(RM.AaMount.parse(RM.AaMountOpRemount{}, rest, q, src))
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  AaParse.wrap.mount(RM.AaMount.parse(RM.AaMountOpUmount{}, rest, q, src))
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      AaParse.wrap.dbus(RD.AaDbus.parse(rest, q, src))
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          AaParse.wrap.change(RX.AaChange.parse(rest, q, src))
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              AaParse.wrap.file(F.AaFile.parse(rest, q, src), als)
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  Fail{E.AaSrc.unsupported(src)}
                                                case 1n+k12:
                                                  Fail{E.AaSrc.preamble(src)}

# a rule's terms (after the qualifiers), with the qualifiers in force
def AaParse.rule(ts: List<&2, T.AaTerm>, +q: P.AaQual, +als: List<&2, AaAlias>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match ts:
    case Nil{}:
      Fail{E.AaSrc.syntax(src)}
    case Con{+t, rest}:
      AaParse.dispatch(AaParse.keyword(t), t, rest, q, als, src)

def AaParse.terms(m: Maybe<&2, List<&2, T.AaTerm>>, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, T.AaTerm>>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{ts}:
      Done{ts}

def AaParse.rule.qual(qp: AaQP, +block: AaBQ, +als: List<&2, AaAlias>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaRules>:
  match qp:
    case AaQP{q, rest}:
      do Result<&2, &2, E.AaError, PR.AaRules>:
        c : AaBQ <- AaQ.combine(block, q, src)
        AaParse.rule(rest, AaBQ.qual(c), als, src)

# a statement inside a profile: its rules
def AaParse.stmt(ts: List<&2, T.AaTok>, +block: AaBQ, +pname: List<&2, U32>, +ctx: AaCtx, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaRules>:
  do Result<&2, &2, E.AaError, PR.AaRules>:
    xs : List<&2, T.AaTok> <- AaVars.toks(ts, AaCtx.env(ctx), Some{pname}, src)
    terms : List<&2, T.AaTerm> <- AaParse.terms(T.AaTerm.of_toks(xs), src)
    AaParse.rule.qual(AaQ.parse(terms, 0n, AaBQ.none()), block, AaCtx.aliases(ctx), src)

# Profile heads: profile NAME [ATTACHMENT] [FLAGS], PATH [FLAGS], ^HAT
# [FLAGS], hat NAME [FLAGS], or the qualifiers of a qualifier block.
# kind: 0 a profile, 1 a hat, 2 a qualifier block

type AaHead is Data:
  AaHead{kind: Nat, name: List<&2, U32>, attach: Maybe<&2, G.AaGlob>, flags: PR.AaFlags, q: AaBQ}

# Flags: the mode seen (if any) and the audit flag
type AaFlB is Data:
  AaFlB{mode: Maybe<&2, PR.AaMode>, audit: Bool}

def AaFl.mode_of(+w: List<&2, U32>) -> Maybe<&2, PR.AaMode>:
  Bool.pick(Maybe<&2, PR.AaMode>, X.AaText.is(w, "enforce"), Some{PR.AaModeEnforce{}}, Bool.pick(Maybe<&2, PR.AaMode>, X.AaText.is(w, "complain"), Some{PR.AaModeComplain{}}, Bool.pick(Maybe<&2, PR.AaMode>, X.AaText.is(w, "kill"), Some{PR.AaModeKill{}}, Bool.pick(Maybe<&2, PR.AaMode>, X.AaText.is(w, "unconfined"), Some{PR.AaModeUnconfined{}}, Bool.pick(Maybe<&2, PR.AaMode>, X.AaText.is(w, "default_allow"), Some{PR.AaModeDefaultAllow{}}, Bool.pick(Maybe<&2, PR.AaMode>, X.AaText.is(w, "prompt"), Some{PR.AaModePrompt{}}, None{}))))))

def AaFl.misc() -> List<&2, String>:
  ["mediate_deleted", "attach_disconnected", "chroot_relative", "debug", "interruptible"]

def AaFl.mode_eq(a: PR.AaMode, b: PR.AaMode) -> Bool:
  X.AaText.eq(X.AaText.of_string(PR.AaMode.show(a)), X.AaText.of_string(PR.AaMode.show(b)))

def AaFl.set_mode(b: AaFlB, m: PR.AaMode, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFlB>:
  match b:
    case AaFlB{old, a}:
      match old:
        case None{}:
          Done{AaFlB{Some{m}, a}}
        case Some{+o}:
          Bool.pick(Result<&2, &2, E.AaError, AaFlB>, AaFl.mode_eq(o, m), Done{AaFlB{Some{o}, a}}, Fail{E.AaSrc.flag(src)})

def AaFl.word.mode(m: Maybe<&2, PR.AaMode>, +w: List<&2, U32>, +b: AaFlB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFlB>:
  match m:
    case Some{x}:
      AaFl.set_mode(b, x, src)
    case None{}:
      match b:
        case AaFlB{+mo, +a}:
          Bool.pick(Result<&2, &2, E.AaError, AaFlB>, X.AaText.is(w, "audit"), Done{AaFlB{mo, True{}}}, Bool.pick(Result<&2, &2, E.AaError, AaFlB>, X.AaText.one_of(AaFl.misc(), w), Done{AaFlB{mo, a}}, Fail{E.AaSrc.flag(src)}))

# kill.signal=SIGNAL and attach_disconnected.path=PATH are accepted and not modelled
def AaFl.step(t: T.AaTerm, +b: AaFlB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFlB>:
  match t:
    case T.AaTmWord{+w}:
      AaFl.word.mode(AaFl.mode_of(w), w, b, src)
    case T.AaTmCond{+k, v}:
      Bool.pick(Result<&2, &2, E.AaError, AaFlB>, Bool.or(X.AaText.is(k, "kill.signal"), X.AaText.is(k, "attach_disconnected.path")), Done{b}, Fail{E.AaSrc.flag(src)})
    case _:
      Fail{E.AaSrc.flag(src)}

def AaFl.run(ts: List<&2, T.AaTerm>, b: AaFlB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFlB>:
  match ts:
    case Nil{}:
      Done{b}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, AaFlB>:
        b2 : AaFlB <- AaFl.step(t, b, src)
        AaFl.run(rest, b2, src)

def AaFl.finish(b: AaFlB) -> PR.AaFlags:
  match b:
    case AaFlB{m, a}:
      PR.AaFlags{Maybe.default(&2, PR.AaMode, m, PR.AaModeEnforce{}), a}

def AaFl.list(xs: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaFlags>:
  do Result<&2, &2, E.AaError, PR.AaFlags>:
    b : AaFlB <- AaFl.run(xs, AaFlB{None{}, False{}}, src)
    return AaFl.finish(b)

# the flags term: flags=(...) or (...)
def AaFl.term(t: T.AaTerm, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaFlags>:
  match t:
    case T.AaTmList{xs}:
      AaFl.list(xs, src)
    case T.AaTmCond{+k, v}:
      match v:
        case T.AaTmList{xs}:
          Bool.pick(Result<&2, &2, E.AaError, PR.AaFlags>, X.AaText.is(k, "flags"), AaFl.list(xs, src), Fail{E.AaSrc.syntax(src)})
        case _:
          Fail{E.AaSrc.syntax(src)}
    case _:
      Fail{E.AaSrc.syntax(src)}

# optional flags, and nothing after them
def AaFl.opt(ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaFlags>:
  match ts:
    case Nil{}:
      Done{PR.AaFlags.default()}
    case Con{t, rest}:
      match rest:
        case Nil{}:
          AaFl.term(t, src)
        case Con{x, more}:
          Fail{E.AaSrc.syntax(src)}

def AaParse.alnum(+c: U32) -> Bool:
  Bool.or(T.AaTerm.letter(c), Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)))

# a profile name: a quoted string, or a word starting with a letter, a digit or '/'
def AaParse.name(t: T.AaTerm, +src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, U32>>:
  match t:
    case T.AaTmWord{+w}:
      Bool.pick(Result<&2, &2, E.AaError, List<&2, U32>>, Bool.or(AaParse.alnum(X.AaText.head(w)), U32.is_eq(X.AaText.head(w), 47)), Done{w}, Fail{E.AaSrc.syntax(src)})
    case T.AaTmQuoted{+q}:
      Bool.pick(Result<&2, &2, E.AaError, List<&2, U32>>, X.AaText.is_nil(q), Fail{E.AaSrc.syntax(src)}, Done{q})
    case _:
      Fail{E.AaSrc.syntax(src)}

def AaParse.attach.glob(r: Result<&2, &2, E.AaError, G.AaGlob>, src: E.AaSrc) -> Result<&2, &2, E.AaError, Maybe<&2, G.AaGlob>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+g}:
      Bool.pick(Result<&2, &2, E.AaError, Maybe<&2, G.AaGlob>>, F.AaFile.rooted(g), Done{Some{g}}, Fail{E.AaSrc.syntax(src)})

# a name that is an absolute path is also the attachment
def AaParse.self_attach(+name: List<&2, U32>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, Maybe<&2, G.AaGlob>>:
  Bool.pick(Result<&2, &2, E.AaError, Maybe<&2, G.AaGlob>>, U32.is_eq(X.AaText.head(name), 47), AaParse.attach.glob(R.AaRule.glob_text(name, src), src), Done{None{}})

def AaParse.head.make(kind: Nat, name: List<&2, U32>, attach: Maybe<&2, G.AaGlob>, r: Result<&2, &2, E.AaError, PR.AaFlags>) -> Result<&2, &2, E.AaError, AaHead>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Done{AaHead{kind, name, attach, f, AaBQ.none()}}

def AaParse.head.flags_only(ts: List<&2, T.AaTerm>, +name: List<&2, U32>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  do Result<&2, &2, E.AaError, AaHead>:
    a : Maybe<&2, G.AaGlob> <- AaParse.self_attach(name, src)
    AaParse.head.make(0n, name, a, AaFl.opt(ts, src))

def AaParse.head.attached(t: T.AaTerm, rest: List<&2, T.AaTerm>, name: List<&2, U32>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  do Result<&2, &2, E.AaError, AaHead>:
    g : G.AaGlob <- R.AaRule.glob(t, src)
    a : Maybe<&2, G.AaGlob> <- AaParse.attach.glob(Done{g}, src)
    AaParse.head.make(0n, name, a, AaFl.opt(rest, src))

# after `profile NAME`: an attachment, then flags
def AaParse.head.profile.rest(ts: List<&2, T.AaTerm>, +name: List<&2, U32>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  match ts:
    case Nil{}:
      do Result<&2, &2, E.AaError, AaHead>:
        a : Maybe<&2, G.AaGlob> <- AaParse.self_attach(name, src)
        return AaHead{0n, name, a, PR.AaFlags.default(), AaBQ.none()}
    case Con{+t, +rest}:
      Bool.pick(Result<&2, &2, E.AaError, AaHead>, F.AaFile.is_path(t), AaParse.head.attached(t, rest, name, src), AaParse.head.flags_only(Con{t, rest}, name, src))

def AaParse.head.profile(ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  match ts:
    case Nil{}:
      Fail{E.AaSrc.syntax(src)}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, AaHead>:
        n : List<&2, U32> <- AaParse.name(t, src)
        AaParse.head.profile.rest(rest, n, src)

def AaParse.head.hat.name(+n: List<&2, U32>, rest: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  Bool.pick(Result<&2, &2, E.AaError, AaHead>, AaParse.alnum(X.AaText.head(n)), AaParse.head.make(1n, n, None{}, AaFl.opt(rest, src)), Fail{E.AaSrc.syntax(src)})

# hat NAME [FLAGS]
def AaParse.head.hat(ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  match ts:
    case Nil{}:
      Fail{E.AaSrc.syntax(src)}
    case Con{t, rest}:
      match t:
        case T.AaTmWord{w}:
          AaParse.head.hat.name(w, rest, src)
        case _:
          Fail{E.AaSrc.syntax(src)}

def AaParse.head.qual(qp: AaQP, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  match qp:
    case AaQP{q, rest}:
      match rest:
        case Nil{}:
          Done{AaHead{2n, Nil{}, None{}, PR.AaFlags.default(), q}}
        case Con{x, more}:
          Fail{E.AaSrc.syntax(src)}

# a path as the head: its name and its attachment
def AaParse.head.path(t: T.AaTerm, rest: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  do Result<&2, &2, E.AaError, AaHead>:
    n : List<&2, U32> <- AaParse.name(t, src)
    AaParse.head.flags_only(rest, n, src)

def AaParse.head.word(+w: List<&2, U32>, +t: T.AaTerm, +rest: List<&2, T.AaTerm>, +top: Bool, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  Bool.pick(Result<&2, &2, E.AaError, AaHead>, X.AaText.is(w, "profile"), AaParse.head.profile(rest, src), Bool.pick(Result<&2, &2, E.AaError, AaHead>, Bool.and(Bool.not(top), X.AaText.is(w, "hat")), AaParse.head.hat(rest, src), Bool.pick(Result<&2, &2, E.AaError, AaHead>, Bool.and(Bool.not(top), U32.is_eq(X.AaText.head(w), 94)), AaParse.head.hat.name(X.AaText.tail(w), rest, src), Bool.pick(Result<&2, &2, E.AaError, AaHead>, Bool.and(top, F.AaFile.is_path(t)), AaParse.head.path(t, rest, src), Bool.pick(Result<&2, &2, E.AaError, AaHead>, Bool.not(top), AaParse.head.qual(AaQ.parse(Con{t, rest}, 0n, AaBQ.none()), src), Fail{E.AaSrc.syntax(src)})))))

# the head of a block, at the top level or inside a profile
def AaParse.head(ts: List<&2, T.AaTerm>, +top: Bool, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  match ts:
    case Nil{}:
      Fail{E.AaSrc.syntax(src)}
    case Con{t, rest}:
      match t:
        case T.AaTmWord{+w}:
          AaParse.head.word(w, T.AaTmWord{w}, rest, top, src)
        case T.AaTmQuoted{+q}:
          Bool.pick(Result<&2, &2, E.AaError, AaHead>, top, AaParse.head.path(T.AaTmQuoted{q}, rest, src), Fail{E.AaSrc.syntax(src)})
        case _:
          Fail{E.AaSrc.syntax(src)}

# Exec conflicts: two rules on the same literal path with different exec modes

def AaParse.target_eq(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      X.AaText.eq(x, y)
    case _ _:
      False{}

def AaParse.xconf(a: F.AaFileRule, b: F.AaFileRule) -> Bool:
  match a:
    case F.AaFileRule{q1, t1, g1, p1, e1, tg1}:
      match e1:
        case None{}:
          False{}
        case Some{m1}:
          match b:
            case F.AaFileRule{q2, t2, g2, p2, e2, tg2}:
              match e2:
                case None{}:
                  False{}
                case Some{m2}:
                  Bool.and(Bool.and(G.AaGlob.is_literal(g1), G.AaGlob.is_literal(g2)), Bool.and(X.AaText.eq(t1, t2), Bool.not(Bool.and(F.AaXMode.eq(m1, m2), AaParse.target_eq(tg1, tg2)))))

def AaParse.xconf.any(+r: F.AaFileRule, rs: List<&2, F.AaFileRule>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{s, t}:
      Bool.or(AaParse.xconf(r, s), AaParse.xconf.any(r, t))

def AaParse.conflicts.go(rs: List<&2, F.AaFileRule>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{+r, +t}:
      Bool.or(AaParse.xconf.any(r, t), AaParse.conflicts.go(t))

# the allow rules with an exec mode on a literal pattern: the only ones that can conflict
def AaParse.exec_literal(r: F.AaFileRule) -> Bool:
  match r:
    case F.AaFileRule{q, t, g, p, e, tg}:
      match e:
        case None{}:
          False{}
        case Some{m}:
          Bool.and(G.AaGlob.is_literal(g), Bool.not(P.AaQual.deny(q)))

def AaParse.exec_rules(rs: List<&2, F.AaFileRule>) -> List<&2, F.AaFileRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      F.AaFileRule.matching.go(AaParse.exec_literal(r), r, AaParse.exec_rules(t))

def AaParse.conflicts(rs: List<&2, F.AaFileRule>) -> Bool:
  AaParse.conflicts.go(AaParse.exec_rules(rs))

# change_profile rules with exec conditions must agree on safe and unsafe
# (apparmor_parser 4.0.1 refuses overlapping ones that differ; the package,
# which does not intersect patterns, refuses any allow rules that differ)
def AaParse.cp_applies(r: RX.AaChangeRule) -> Bool:
  match r:
    case RX.AaChangeRule{q, e, s, tg}:
      match e:
        case None{}:
          False{}
        case Some{g}:
          Bool.not(P.AaQual.deny(q))

def AaParse.cp_safe(r: RX.AaChangeRule) -> Bool:
  match r:
    case RX.AaChangeRule{q, e, s, tg}:
      s

def AaParse.cp_clash(applies: Bool, +s: Bool, seen: Maybe<&2, Bool>) -> Bool:
  match applies:
    case False{}:
      False{}
    case True{}:
      match seen:
        case None{}:
          False{}
        case Some{x}:
          Bool.xor(x, s)

def AaParse.cp_next(applies: Bool, s: Bool, +seen: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match applies:
    case False{}:
      seen
    case True{}:
      match seen:
        case None{}:
          Some{s}
        case Some{x}:
          Some{x}

def AaParse.safe_clash(rs: List<&2, RX.AaChangeRule>, +seen: Maybe<&2, Bool>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{+r, t}:
      Bool.or(AaParse.cp_clash(AaParse.cp_applies(r), AaParse.cp_safe(r), seen), AaParse.safe_clash(t, AaParse.cp_next(AaParse.cp_applies(r), AaParse.cp_safe(r), seen)))

# Building: a stack of open blocks, innermost first. A profile frame holds
# the profile being built, whether it is a hat, its full name; every frame
# holds the qualifiers in force.

type AaFrame is Data:
  AaFrame{prof: Maybe<&2, PR.AaProfile>, hat: Bool, full: List<&2, U32>, qual: AaBQ, src: E.AaSrc}

type AaBuild is Data:
  AaBuild{frames: List<&2, AaFrame>, top: List<&2, PR.AaProfile>, err: Maybe<&2, E.AaError>}

def AaBuild.fail(b: AaBuild, e: E.AaError) -> AaBuild:
  match b:
    case AaBuild{fs, top, err}:
      match err:
        case None{}:
          AaBuild{fs, top, Some{e}}
        case Some{e0}:
          AaBuild{fs, top, Some{e0}}

# the innermost profile frame's full name
def AaFrames.full(fs: List<&2, AaFrame>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case AaFrame{p, h, full, q, s}:
          match p:
            case None{}:
              AaFrames.full(t)
            case Some{x}:
              full

def AaFrames.qual(fs: List<&2, AaFrame>) -> AaBQ:
  match fs:
    case Nil{}:
      AaBQ.none()
    case Con{f, t}:
      match f:
        case AaFrame{p, h, full, q, s}:
          q

# the rules added to the innermost profile
def AaFrames.add_rules(fs: List<&2, AaFrame>, rs: PR.AaRules) -> List<&2, AaFrame>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case AaFrame{p, h, full, q, s}:
          match p:
            case None{}:
              Con{AaFrame{None{}, h, full, q, s}, AaFrames.add_rules(t, rs)}
            case Some{x}:
              Con{AaFrame{Some{PR.AaProfile.prepend(x, rs)}, h, full, q, s}, t}

def AaFrames.names.go(ps: List<&2, PR.AaProfile>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{PR.AaProfile.name(p), AaFrames.names.go(t)}

def AaFrames.names(+p: PR.AaProfile) -> List<&2, List<&2, U32>>:
  AaFrames.names.go(PR.AaProfile.list_append(PR.AaProfile.children(p), PR.AaProfile.hats(p)))

def AaFrames.add_sub.go(dup: Bool, +x: PR.AaProfile, k: PR.AaProfile, hat: Bool) -> Maybe<&2, PR.AaProfile>:
  match dup:
    case True{}:
      None{}
    case False{}:
      match hat:
        case True{}:
          Some{PR.AaProfile.add_hat(x, k)}
        case False{}:
          Some{PR.AaProfile.add_child(x, k)}

def AaFrames.add_sub.put(m: Maybe<&2, PR.AaProfile>, h: Bool, full: List<&2, U32>, q: AaBQ, s: E.AaSrc, t: List<&2, AaFrame>) -> Maybe<&2, List<&2, AaFrame>>:
  match m:
    case None{}:
      None{}
    case Some{y}:
      Some{Con{AaFrame{Some{y}, h, full, q, s}, t}}

def AaFrames.add_sub.cons(f: AaFrame, m: Maybe<&2, List<&2, AaFrame>>) -> Maybe<&2, List<&2, AaFrame>>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{Con{f, t}}

# a finished child or hat added to the innermost profile; None if the name is taken
def AaFrames.add_sub(fs: List<&2, AaFrame>, +k: PR.AaProfile, +hat: Bool) -> Maybe<&2, List<&2, AaFrame>>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, t}:
      match f:
        case AaFrame{p, h, full, q, s}:
          match p:
            case None{}:
              AaFrames.add_sub.cons(AaFrame{None{}, h, full, q, s}, AaFrames.add_sub(t, k, hat))
            case Some{+x}:
              AaFrames.add_sub.put(AaFrames.add_sub.go(X.AaText.member(AaFrames.names(x), PR.AaProfile.name(k)), x, k, hat), h, full, q, s, t)

def AaFrames.has_profile(fs: List<&2, AaFrame>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{f, t}:
      match f:
        case AaFrame{p, h, full, q, s}:
          match p:
            case None{}:
              AaFrames.has_profile(t)
            case Some{x}:
              True{}

def AaBuild.top_names(ps: List<&2, PR.AaProfile>) -> List<&2, List<&2, U32>>:
  AaFrames.names.go(ps)

# a finished profile: checked, and added to its parent or to the top level
def AaBuild.finish.sub(m: Maybe<&2, List<&2, AaFrame>>, top: List<&2, PR.AaProfile>, err: Maybe<&2, E.AaError>, src: E.AaSrc) -> AaBuild:
  match m:
    case None{}:
      AaBuild.fail(AaBuild{Nil{}, top, err}, E.AaSrc.duplicate(src))
    case Some{fs}:
      AaBuild{fs, top, err}

def AaBuild.finish.top(+p: PR.AaProfile, +top: List<&2, PR.AaProfile>, +err: Maybe<&2, E.AaError>, +src: E.AaSrc) -> AaBuild:
  Bool.pick(AaBuild, X.AaText.member(AaBuild.top_names(top), PR.AaProfile.name(p)), AaBuild.fail(AaBuild{Nil{}, top, err}, E.AaSrc.duplicate(src)), AaBuild{Nil{}, PR.AaProfile.list_append(top, [p]), err})

def AaBuild.finish.place(nested: Bool, +p: PR.AaProfile, hat: Bool, +fs: List<&2, AaFrame>, +top: List<&2, PR.AaProfile>, +err: Maybe<&2, E.AaError>, +src: E.AaSrc) -> AaBuild:
  match nested:
    case True{}:
      AaBuild.finish.sub(AaFrames.add_sub(fs, p, hat), top, err, src)
    case False{}:
      AaBuild.finish.top(p, top, err, src)

def AaBuild.finish(+p: PR.AaProfile, +hat: Bool, +fs: List<&2, AaFrame>, +top: List<&2, PR.AaProfile>, +err: Maybe<&2, E.AaError>, +src: E.AaSrc) -> AaBuild:
  Bool.pick(AaBuild, Bool.or(AaParse.conflicts(PR.AaRules.files(PR.AaProfile.rules(p))), AaParse.safe_clash(PR.AaRules.changes(PR.AaProfile.rules(p)), None{})), AaBuild.fail(AaBuild{fs, top, err}, E.AaSrc.exec_conflict(src)), AaBuild.finish.place(AaFrames.has_profile(fs), p, hat, fs, top, err, src))

def AaBuild.close(b: AaBuild, src: E.AaSrc) -> AaBuild:
  match b:
    case AaBuild{fs, top, err}:
      match fs:
        case Nil{}:
          AaBuild.fail(AaBuild{Nil{}, top, err}, E.AaSrc.syntax(src))
        case Con{f, rest}:
          match f:
            case AaFrame{p, h, full, q, s}:
              match p:
                case None{}:
                  AaBuild{rest, top, err}
                case Some{x}:
                  AaBuild.finish(x, h, rest, top, err, s)

def AaBuild.push.qual(r: Result<&2, &2, E.AaError, AaBQ>, fs: List<&2, AaFrame>, top: List<&2, PR.AaProfile>, err: Maybe<&2, E.AaError>, src: E.AaSrc) -> AaBuild:
  match r:
    case Fail{e}:
      AaBuild.fail(AaBuild{fs, top, err}, e)
    case Done{q}:
      AaBuild{Con{AaFrame{None{}, False{}, Nil{}, q, src}, fs}, top, err}

def AaBuild.push.kind(kind: Nat, +fs: List<&2, AaFrame>, top: List<&2, PR.AaProfile>, err: Maybe<&2, E.AaError>, name: List<&2, U32>, attach: Maybe<&2, G.AaGlob>, flags: PR.AaFlags, q: AaBQ, full: List<&2, U32>, +src: E.AaSrc) -> AaBuild:
  match kind:
    case 0n:
      AaBuild{Con{AaFrame{Some{PR.AaProfile.new(name, attach, flags)}, False{}, full, AaBQ.none(), src}, fs}, top, err}
    case 1n+k:
      match k:
        case 0n:
          AaBuild{Con{AaFrame{Some{PR.AaProfile.new(name, attach, flags)}, True{}, full, AaBQ.none(), src}, fs}, top, err}
        case 1n+j:
          AaBuild.push.qual(AaQ.combine(AaFrames.qual(fs), q, src), fs, top, err, src)

# a block opens
def AaBuild.push(r: Result<&2, &2, E.AaError, AaHead>, b: AaBuild, +src: E.AaSrc) -> AaBuild:
  match r:
    case Fail{e}:
      AaBuild.fail(b, e)
    case Done{hd}:
      match hd:
        case AaHead{kind, +name, attach, flags, q}:
          match b:
            case AaBuild{+fs, top, err}:
              +outer = AaFrames.full(fs)
              +full = Bool.pick(List<&2, U32>, X.AaText.is_nil(outer), name, X.AaText.append(outer, X.AaText.append(X.AaText.of_string("//"), name)))
              AaBuild.push.kind(kind, fs, top, err, name, attach, flags, q, full, src)

def AaBuild.frames(b: AaBuild) -> List<&2, AaFrame>:
  match b:
    case AaBuild{fs, top, err}:
      fs

def AaParse.head.of(ts: List<&2, T.AaTok>, +top: Bool, +pname: Maybe<&2, List<&2, U32>>, +ctx: AaCtx, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaHead>:
  do Result<&2, &2, E.AaError, AaHead>:
    xs : List<&2, T.AaTok> <- AaVars.toks(ts, AaCtx.env(ctx), pname, src)
    terms : List<&2, T.AaTerm> <- AaParse.terms(T.AaTerm.of_toks(xs), src)
    AaParse.head(terms, top, src)

def AaBuild.open(+b: AaBuild, ts: List<&2, T.AaTok>, +ctx: AaCtx, +src: E.AaSrc) -> AaBuild:
  +inside = AaFrames.has_profile(AaBuild.frames(b))
  +pname = Bool.pick(Maybe<&2, List<&2, U32>>, inside, Some{AaFrames.full(AaBuild.frames(b))}, None{})
  AaBuild.push(AaParse.head.of(ts, Bool.not(inside), pname, ctx, src), b, src)

def AaBuild.rules(r: Result<&2, &2, E.AaError, PR.AaRules>, b: AaBuild) -> AaBuild:
  match r:
    case Fail{e}:
      AaBuild.fail(b, e)
    case Done{rs}:
      match b:
        case AaBuild{fs, top, err}:
          AaBuild{AaFrames.add_rules(fs, rs), top, err}

# a statement: a rule inside a profile; at the top level the preamble pass has checked it
def AaBuild.stmt(+b: AaBuild, ts: List<&2, T.AaTok>, +ctx: AaCtx, +src: E.AaSrc) -> AaBuild:
  +fs = AaBuild.frames(b)
  Bool.pick(AaBuild, AaFrames.has_profile(fs), AaBuild.rules(AaParse.stmt(ts, AaFrames.qual(fs), AaFrames.full(fs), ctx, src), b), b)

def AaBuild.ok(b: AaBuild) -> Bool:
  match b:
    case AaBuild{fs, top, err}:
      match err:
        case None{}:
          True{}
        case Some{e}:
          False{}

def AaBuild.step(+b: AaBuild, it: AaItem, +ctx: AaCtx) -> AaBuild:
  match it:
    case AaIOpen{ts, src}:
      Bool.pick(AaBuild, AaBuild.ok(b), AaBuild.open(b, ts, ctx, src), b)
    case AaIClose{src}:
      Bool.pick(AaBuild, AaBuild.ok(b), AaBuild.close(b, src), b)
    case AaIStmt{ts, src}:
      Bool.pick(AaBuild, AaBuild.ok(b), AaBuild.stmt(b, ts, ctx, src), b)
    case AaIVar{ts, src}:
      b
    case AaIInclude{n, o, src}:
      b
    case AaIError{e}:
      AaBuild.fail(b, e)

def AaBuild.run(items: List<&2, AaItem>, b: AaBuild, +ctx: AaCtx) -> AaBuild:
  match items:
    case Nil{}:
      b
    case Con{it, rest}:
      AaBuild.run(rest, AaBuild.step(b, it, ctx), ctx)

def AaBuild.result(b: AaBuild, src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaPolicy>:
  match b:
    case AaBuild{fs, top, err}:
      match fs:
        case Nil{}:
          match err:
            case Some{e}:
              Fail{e}
            case None{}:
              Done{PR.AaPolicy{top}}
        case Con{f, rest}:
          match err:
            case Some{e}:
              Fail{e}
            case None{}:
              Fail{E.AaSrc.syntax(src)}

# Loading

def AaParse.pre.result(p: AaPre, items: List<&2, AaItem>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaPolicy>:
  match p:
    case AaPre{env, als, d, s, err}:
      match d:
        case 0n:
          match err:
            case Some{e}:
              Fail{e}
            case None{}:
              AaBuild.result(AaBuild.run(items, AaBuild{Nil{}, Nil{}, None{}}, AaCtx{env, als}), src)
        case 1n+x:
          match err:
            case Some{e}:
              Fail{e}
            case None{}:
              Fail{E.AaSrc.syntax(src)}

def AaParse.load.items(m: Maybe<&2, E.AaError>, +items: List<&2, AaItem>, +opts: O.AaOptions, +src: E.AaSrc) -> Result<&2, &2, E.AaError, PR.AaPolicy>:
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      AaParse.pre.result(AaPre.run(items, AaPre{O.AaOptions.vars(opts), Nil{}, 0n, False{}, None{}}), items, src)

def AaParse.load.file(m: Maybe<&2, AaSrcFile>, +opts: O.AaOptions, +files: List<&2, AaSrcFile>, +main: List<&2, U32>) -> Result<&2, &2, E.AaError, PR.AaPolicy>:
  match m:
    case None{}:
      Fail{E.AaErrInclude{main, 0}}
    case Some{f}:
      match f:
        case AaSrcFile{n, text}:
          +items = AaExpOut.items(AaParse.expand(O.AaOptions.depth(opts), AaParse.items(main, text), files, [[main]], Nil{}))
          AaParse.load.items(AaParse.first_error(items), items, opts, E.AaSrc{main, 0})

# the policy the file named main defines, reading includes from the file map
def AaParse.load(+opts: O.AaOptions, +files: List<&2, AaSrcFile>, +main: List<&2, U32>) -> Result<&2, &2, E.AaError, PR.AaPolicy>:
  AaParse.load.file(AaParse.find_file(files, main), opts, files, main)
