# bend-osdev-apparmor: what the rule kinds share when they read their terms:
# patterns from words, strings and conditions, and checked name lists.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./token.bend as T
import ./error.bend as E
import ./perm.bend as P

def AaRule.of_maybe(m: Maybe<&2, G.AaGlob>, e: E.AaError) -> Result<&2, &2, E.AaError, G.AaGlob>:
  match m:
    case None{}:
      Fail{e}
    case Some{g}:
      Done{g}

# the pattern written as xs
def AaRule.glob_text(xs: List<&2, U32>, src: E.AaSrc) -> Result<&2, &2, E.AaError, G.AaGlob>:
  AaRule.of_maybe(G.AaGlob.parse(xs), E.AaSrc.glob(src))

def AaRule.glob.go(m: Maybe<&2, List<&2, U32>>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, G.AaGlob>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{xs}:
      AaRule.glob_text(xs, src)

# the pattern a word or quoted string writes
def AaRule.glob(t: T.AaTerm, src: E.AaSrc) -> Result<&2, &2, E.AaError, G.AaGlob>:
  AaRule.glob.go(T.AaTerm.text(t), src)

def AaRule.one.go(xs: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, G.AaGlob>:
  match xs:
    case Nil{}:
      Fail{E.AaSrc.syntax(src)}
    case Con{x, rest}:
      match rest:
        case Nil{}:
          AaRule.glob(x, src)
        case Con{y, more}:
          Fail{E.AaSrc.syntax(src)}

# the pattern of a condition's value: a word, a quoted string, or one of
# them in parentheses
def AaRule.value_glob(v: T.AaTerm, +src: E.AaSrc) -> Result<&2, &2, E.AaError, G.AaGlob>:
  match v:
    case T.AaTmWord{w}:
      AaRule.glob_text(w, src)
    case T.AaTmQuoted{q}:
      AaRule.glob_text(q, src)
    case T.AaTmList{xs}:
      AaRule.one.go(xs, src)
    case T.AaTmCond{k, x}:
      Fail{E.AaSrc.syntax(src)}
    case T.AaTmArrow{}:
      Fail{E.AaSrc.syntax(src)}

# the patterns of a value: one, or a parenthesised list
def AaRule.value_globs.go(xs: List<&2, List<&2, U32>>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, G.AaGlob>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{x, rest}:
      do Result<&2, &2, E.AaError, List<&2, G.AaGlob>>:
        g : G.AaGlob <- AaRule.glob_text(x, src)
        gs : List<&2, G.AaGlob> <- AaRule.value_globs.go(rest, src)
        return Con{g, gs}

def AaRule.texts(m: Maybe<&2, List<&2, List<&2, U32>>>, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{xs}:
      Done{xs}

def AaRule.value_globs(v: T.AaTerm, +src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, G.AaGlob>>:
  do Result<&2, &2, E.AaError, List<&2, G.AaGlob>>:
    xs : List<&2, List<&2, U32>> <- AaRule.texts(T.AaTerm.texts(v), src)
    AaRule.value_globs.go(xs, src)

# the names of a value, each one of the allowed names
def AaRule.check_names.go(hit: Bool, x: List<&2, U32>, r: Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
  match hit:
    case False{}:
      Fail{E.AaSrc.name(src)}
    case True{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{xs}:
          Done{Con{x, xs}}

def AaRule.check_names(xs: List<&2, List<&2, U32>>, +ok: List<&2, String>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{+x, rest}:
      AaRule.check_names.go(X.AaText.one_of(ok, x), x, AaRule.check_names(rest, ok, src), src)

def AaRule.names(v: T.AaTerm, +ok: List<&2, String>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
  do Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
    xs : List<&2, List<&2, U32>> <- AaRule.texts(T.AaTerm.texts(v), src)
    AaRule.check_names(xs, ok, src)

# Matching helpers

def AaRule.opt_match(m: Maybe<&2, G.AaGlob>, +s: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{g}:
      G.AaGlob.matches(g, s)

# some pattern of the list matches s
def AaRule.any_match(gs: List<&2, G.AaGlob>, +s: List<&2, U32>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{g, t}:
      Bool.or(G.AaGlob.matches(g, s), AaRule.any_match(t, s))

def AaRule.opt_any(m: Maybe<&2, List<&2, G.AaGlob>>, +s: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{gs}:
      AaRule.any_match(gs, s)

def AaRule.glob_append(xs: List<&2, G.AaGlob>, ys: List<&2, G.AaGlob>) -> List<&2, G.AaGlob>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaRule.glob_append(t, ys)}

def AaRule.add_globs(m: Maybe<&2, List<&2, G.AaGlob>>, gs: List<&2, G.AaGlob>) -> Maybe<&2, List<&2, G.AaGlob>>:
  match m:
    case None{}:
      Some{gs}
    case Some{hs}:
      Some{AaRule.glob_append(hs, gs)}

# the qualifiers of a rule kind that does not take owner
def AaRule.no_owner(q: P.AaQual, src: E.AaSrc) -> Result<&2, &2, E.AaError, P.AaQual>:
  match q:
    case P.AaQual{a, d, o}:
      match o:
        case True{}:
          Fail{E.AaSrc.syntax(src)}
        case False{}:
          Done{P.AaQual{a, d, False{}}}
