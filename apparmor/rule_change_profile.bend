# bend-osdev-apparmor: change_profile rules (apparmor.d(5), "CHANGE_PROFILE
# RULE", "change_profile rules"): `change_profile [[safe|unsafe] EXEC_COND]
# [-> PROFILE NAME]`, which profiles a task may move to through the
# change_profile API, optionally only when it executes a matching program.
# safe (the default) and unsafe say whether the environment is scrubbed; an
# exec mode needs an exec condition. One permission bit: change.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./rule.bend as R

# exec: None for any (or no) exec; target: None for every profile
type AaChangeRule is Data:
  AaChangeRule{qual: P.AaQual, exec: Maybe<&2, G.AaGlob>, safe: Bool, target: Maybe<&2, G.AaGlob>}

# a change to the profile named target, now (exec None) or when the program
# exec is executed
type AaChangeQuery is Data:
  AaChangeQuery{exec: Maybe<&2, List<&2, U32>>, target: List<&2, U32>}

# the builder: mode word seen (0 none, 1 safe, 2 unsafe), exec condition,
# arrow seen, target
type AaChB is Data:
  AaChB{mode: Nat, exec: Maybe<&2, G.AaGlob>, arrow: Bool, target: Maybe<&2, G.AaGlob>}

def AaChange.is_path(t: T.AaTerm) -> Bool:
  match t:
    case T.AaTmWord{+w}:
      Bool.or(U32.is_eq(X.AaText.head(w), 47), U32.is_eq(X.AaText.head(w), 123))
    case T.AaTmQuoted{q}:
      True{}
    case _:
      False{}

def AaChB.set_target(b: AaChB, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChB>:
  match b:
    case AaChB{m, e, ar, tg}:
      match ar:
        case False{}:
          Fail{E.AaSrc.syntax(src)}
        case True{}:
          match tg:
            case None{}:
              Done{AaChB{m, e, True{}, Some{g}}}
            case Some{h}:
              Fail{E.AaSrc.syntax(src)}

def AaChB.set_exec(b: AaChB, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChB>:
  match b:
    case AaChB{m, e, ar, tg}:
      match e:
        case None{}:
          match ar:
            case False{}:
              Done{AaChB{m, Some{g}, False{}, tg}}
            case True{}:
              Fail{E.AaSrc.syntax(src)}
        case Some{h}:
          Fail{E.AaSrc.syntax(src)}

# a pattern: the target after the arrow, else the exec condition
def AaChB.glob(b: AaChB, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChB>:
  match b:
    case AaChB{m, e, +ar, tg}:
      match ar:
        case True{}:
          AaChB.set_target(AaChB{m, e, ar, tg}, g, src)
        case False{}:
          AaChB.set_exec(AaChB{m, e, ar, tg}, g, src)

def AaChB.arrow(b: AaChB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChB>:
  match b:
    case AaChB{m, e, ar, tg}:
      match ar:
        case True{}:
          Fail{E.AaSrc.syntax(src)}
        case False{}:
          Done{AaChB{m, e, True{}, tg}}

# safe or unsafe, before anything else
def AaChB.mode(b: AaChB, n: Nat, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChB>:
  match b:
    case AaChB{m, e, ar, tg}:
      match m:
        case 0n:
          match e:
            case None{}:
              match ar:
                case False{}:
                  Done{AaChB{n, None{}, False{}, tg}}
                case True{}:
                  Fail{E.AaSrc.syntax(src)}
            case Some{h}:
              Fail{E.AaSrc.syntax(src)}
        case 1n+k:
          Fail{E.AaSrc.syntax(src)}

def AaChB.term.glob(r: Result<&2, &2, E.AaError, G.AaGlob>, b: AaChB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChB>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{g}:
      AaChB.glob(b, g, src)

def AaChB.step(t: T.AaTerm, +b: AaChB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChB>:
  match t:
    case T.AaTmWord{+w}:
      Bool.pick(Result<&2, &2, E.AaError, AaChB>, X.AaText.is(w, "safe"), AaChB.mode(b, 1n, src), Bool.pick(Result<&2, &2, E.AaError, AaChB>, X.AaText.is(w, "unsafe"), AaChB.mode(b, 2n, src), AaChB.term.glob(R.AaRule.glob_text(w, src), b, src)))
    case T.AaTmQuoted{q}:
      AaChB.term.glob(R.AaRule.glob_text(q, src), b, src)
    case T.AaTmArrow{}:
      AaChB.arrow(b, src)
    case _:
      Fail{E.AaSrc.syntax(src)}

def AaChB.run(ts: List<&2, T.AaTerm>, b: AaChB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChB>:
  match ts:
    case Nil{}:
      Done{b}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, AaChB>:
        b2 : AaChB <- AaChB.step(t, b, src)
        AaChB.run(rest, b2, src)

def AaChange.is_some(m: Maybe<&2, G.AaGlob>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{g}:
      True{}

# an exec mode needs an exec condition; an arrow needs a target
def AaChB.finish(q: P.AaQual, b: AaChB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChangeRule>:
  match b:
    case AaChB{+m, +e, ar, +tg}:
      +bad = Bool.or(Bool.and(Nat.is_gt(m, 0n), Bool.not(AaChange.is_some(e))), Bool.and(ar, Bool.not(AaChange.is_some(tg))))
      Bool.pick(Result<&2, &2, E.AaError, AaChangeRule>, bad, Fail{E.AaSrc.syntax(src)}, Done{AaChangeRule{q, e, Bool.not(Nat.is_eq(m, 2n)), tg}})

def AaChange.parse.q(r: Result<&2, &2, E.AaError, P.AaQual>, ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChangeRule>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{q}:
      do Result<&2, &2, E.AaError, AaChangeRule>:
        b : AaChB <- AaChB.run(ts, AaChB{0n, None{}, False{}, None{}}, src)
        AaChB.finish(q, b, src)

# the terms after `change_profile`
def AaChange.parse(ts: List<&2, T.AaTerm>, q: P.AaQual, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaChangeRule>:
  AaChange.parse.q(R.AaRule.no_owner(q, src), ts, src)

# Matching: the target matches, and a rule with an exec condition applies
# only to a change at the exec of a matching program

def AaChange.exec_ok(m: Maybe<&2, G.AaGlob>, x: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{g}:
      match x:
        case None{}:
          False{}
        case Some{p}:
          G.AaGlob.matches(g, p)

def AaChangeRule.matches(r: AaChangeRule, q: AaChangeQuery) -> Bool:
  match r:
    case AaChangeRule{qu, e, s, tg}:
      match q:
        case AaChangeQuery{qe, qt}:
          Bool.and(AaChange.exec_ok(e, qe), R.AaRule.opt_match(tg, qt))

def AaChangeRule.matching.go(hit: Bool, r: AaChangeRule, rest: List<&2, AaChangeRule>) -> List<&2, AaChangeRule>:
  match hit:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

def AaChangeRule.matching(rs: List<&2, AaChangeRule>, +q: AaChangeQuery) -> List<&2, AaChangeRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      AaChangeRule.matching.go(AaChangeRule.matches(r, q), r, AaChangeRule.matching(t, q))

def AaChangeRule.grants.of(rs: List<&2, AaChangeRule>) -> List<&2, P.AaGrant>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case AaChangeRule{qu, e, s, tg}:
          Con{P.AaGrant.of(qu, P.AaPerms.bit(0n)), AaChangeRule.grants.of(t)}

def AaChangeRule.grants(rs: List<&2, AaChangeRule>, +q: AaChangeQuery) -> List<&2, P.AaGrant>:
  AaChangeRule.grants.of(AaChangeRule.matching(rs, q))

def AaChangeRule.append(xs: List<&2, AaChangeRule>, ys: List<&2, AaChangeRule>) -> List<&2, AaChangeRule>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaChangeRule.append(t, ys)}

def AaChangeQuery.req() -> P.AaPerms:
  P.AaPerms.bit(0n)
