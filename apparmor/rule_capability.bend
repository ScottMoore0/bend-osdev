# bend-osdev-apparmor: capability rules (apparmor.d(5), "CAPABILITY RULE"):
# `capability` alone (every capability) or a list of lower-case capability
# names without the CAP_ prefix (capabilities(7)). Names and numbers come
# from bend-osdev-caps. One permission bit: use.
import Base
import ../caps/caps.bend as C
import ./text.bend as X
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./rule.bend as R

# caps: None for every capability
type AaCapRule is Data:
  AaCapRule{qual: P.AaQual, caps: Maybe<&2, List<&2, U32>>}

# a request to use capability number cap (CAP_CHOWN is 0)
type AaCapQuery is Data:
  AaCapQuery{cap: U32}

def AaCap.upper(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{Bool.pick(U32, Bool.and(U32.is_ge(h, 97), U32.is_le(h, 122)), U32.sub(h, 32), h), AaCap.upper(t)}

# no upper-case letter
def AaCap.lower(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(Bool.and(U32.is_ge(h, 65), U32.is_le(h, 90))), AaCap.lower(t))

# the number of the capability named w (lower case, no CAP_ prefix)
def AaCap.of_name(+w: List<&2, U32>) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, AaCap.lower(w), C.Cap.of_name(X.AaText.to_string(X.AaText.append(X.AaText.of_string("CAP_"), AaCap.upper(w)))), None{})

def AaCap.name.go(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "?"
    case Some{s}:
      s

def AaCap.name(k: U32) -> String:
  AaCap.name.go(C.Cap.name(k))

def AaCap.parse.one(m: Maybe<&2, U32>, r: Result<&2, &2, E.AaError, List<&2, U32>>, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, U32>>:
  match m:
    case None{}:
      Fail{E.AaSrc.name(src)}
    case Some{k}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{ks}:
          Done{Con{k, ks}}

def AaCap.parse.names(ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, U32>>:
  match ts:
    case Nil{}:
      Done{Nil{}}
    case Con{t, rest}:
      match t:
        case T.AaTmWord{w}:
          AaCap.parse.one(AaCap.of_name(w), AaCap.parse.names(rest, src), src)
        case _:
          Fail{E.AaSrc.syntax(src)}

def AaCap.parse.go(r: Result<&2, &2, E.AaError, List<&2, U32>>, q: P.AaQual) -> Result<&2, &2, E.AaError, AaCapRule>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ks}:
      Done{AaCapRule{q, Some{ks}}}

def AaCap.parse.q(r: Result<&2, &2, E.AaError, P.AaQual>, ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaCapRule>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{q}:
      match ts:
        case Nil{}:
          Done{AaCapRule{q, None{}}}
        case Con{t, rest}:
          AaCap.parse.go(AaCap.parse.names(Con{t, rest}, src), q)

# the terms after `capability`; the owner qualifier is not allowed
def AaCap.parse(ts: List<&2, T.AaTerm>, q: P.AaQual, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaCapRule>:
  AaCap.parse.q(R.AaRule.no_owner(q, src), ts, src)

# Matching

def AaCap.member(ks: List<&2, U32>, +k: U32) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(U32.is_eq(h, k), AaCap.member(t, k))

def AaCapRule.matches(r: AaCapRule, q: AaCapQuery) -> Bool:
  match r:
    case AaCapRule{qu, ks}:
      match ks:
        case None{}:
          True{}
        case Some{xs}:
          match q:
            case AaCapQuery{k}:
              AaCap.member(xs, k)

def AaCapRule.matching.go(hit: Bool, r: AaCapRule, rest: List<&2, AaCapRule>) -> List<&2, AaCapRule>:
  match hit:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

def AaCapRule.matching(rs: List<&2, AaCapRule>, +q: AaCapQuery) -> List<&2, AaCapRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      AaCapRule.matching.go(AaCapRule.matches(r, q), r, AaCapRule.matching(t, q))

def AaCapRule.grants.of(rs: List<&2, AaCapRule>) -> List<&2, P.AaGrant>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case AaCapRule{qu, ks}:
          Con{P.AaGrant.of(qu, P.AaPerms.bit(0n)), AaCapRule.grants.of(t)}

def AaCapRule.grants(rs: List<&2, AaCapRule>, +q: AaCapQuery) -> List<&2, P.AaGrant>:
  AaCapRule.grants.of(AaCapRule.matching(rs, q))

def AaCapRule.append(xs: List<&2, AaCapRule>, ys: List<&2, AaCapRule>) -> List<&2, AaCapRule>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaCapRule.append(t, ys)}

# the request's permission: use
def AaCapQuery.req() -> P.AaPerms:
  P.AaPerms.bit(0n)
