# bend-osdev-apparmor: ptrace rules (apparmor.d(5), "PTRACE RULE", "PTrace
# rules"): `ptrace [ACCESS] [peer=AARE]`. Permission bits: read 0, trace 1,
# readby 2, tracedby 3; with no access list all four are implied. The page
# lists r, w and rw without saying what they stand for; the package reads r
# as read, w as trace and rw as both (a stated choice; see the README).
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./rule.bend as R

type AaPtraceRule is Data:
  AaPtraceRule{qual: P.AaQual, perms: P.AaPerms, peer: Maybe<&2, G.AaGlob>}

# req: read, trace (of the peer) or readby, tracedby (by the peer)
type AaPtraceQuery is Data:
  AaPtraceQuery{req: P.AaPerms, peer: List<&2, U32>}

def AaPtrace.read() -> Nat:
  0n

def AaPtrace.trace() -> Nat:
  1n

def AaPtrace.readby() -> Nat:
  2n

def AaPtrace.tracedby() -> Nat:
  3n

def AaPtrace.access(+w: List<&2, U32>) -> Maybe<&2, P.AaPerms>:
  Bool.pick(Maybe<&2, P.AaPerms>, Bool.or(X.AaText.is(w, "read"), X.AaText.is(w, "r")), Some{P.AaPerms.bit(0n)}, Bool.pick(Maybe<&2, P.AaPerms>, Bool.or(X.AaText.is(w, "trace"), X.AaText.is(w, "w")), Some{P.AaPerms.bit(1n)}, Bool.pick(Maybe<&2, P.AaPerms>, X.AaText.is(w, "readby"), Some{P.AaPerms.bit(2n)}, Bool.pick(Maybe<&2, P.AaPerms>, X.AaText.is(w, "tracedby"), Some{P.AaPerms.bit(3n)}, Bool.pick(Maybe<&2, P.AaPerms>, X.AaText.is(w, "rw"), Some{P.AaPerms.of_bits([True{}, True{}])}, None{})))))

type AaPtB is Data:
  AaPtB{perms: Maybe<&2, P.AaPerms>, peer: Maybe<&2, G.AaGlob>}

def AaPtB.perms(m: Maybe<&2, P.AaPerms>, b: AaPtB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtB>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{p}:
      match b:
        case AaPtB{bp, pe}:
          match bp:
            case None{}:
              Done{AaPtB{Some{p}, pe}}
            case Some{q}:
              Done{AaPtB{Some{P.AaPerms.union(q, p)}, pe}}

def AaPtB.access_list(xs: List<&2, T.AaTerm>, b: AaPtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtB>:
  match xs:
    case Nil{}:
      Done{b}
    case Con{x, rest}:
      match x:
        case T.AaTmWord{w}:
          do Result<&2, &2, E.AaError, AaPtB>:
            b2 : AaPtB <- AaPtB.perms(AaPtrace.access(w), b, src)
            AaPtB.access_list(rest, b2, src)
        case _:
          Fail{E.AaSrc.syntax(src)}

def AaPtB.set_peer(b: AaPtB, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtB>:
  match b:
    case AaPtB{p, pe}:
      match pe:
        case None{}:
          Done{AaPtB{p, Some{g}}}
        case Some{h}:
          Fail{E.AaSrc.syntax(src)}

def AaPtB.cond.peer(v: T.AaTerm, b: AaPtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtB>:
  do Result<&2, &2, E.AaError, AaPtB>:
    g : G.AaGlob <- R.AaRule.value_glob(v, src)
    AaPtB.set_peer(b, g, src)

def AaPtB.cond(+k: List<&2, U32>, +v: T.AaTerm, +b: AaPtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtB>:
  Bool.pick(Result<&2, &2, E.AaError, AaPtB>, X.AaText.is(k, "peer"), AaPtB.cond.peer(v, b, src), Fail{E.AaSrc.syntax(src)})

def AaPtB.step(t: T.AaTerm, b: AaPtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtB>:
  match t:
    case T.AaTmWord{w}:
      AaPtB.perms(AaPtrace.access(w), b, src)
    case T.AaTmList{xs}:
      AaPtB.access_list(xs, b, src)
    case T.AaTmCond{k, v}:
      AaPtB.cond(k, v, b, src)
    case _:
      Fail{E.AaSrc.syntax(src)}

def AaPtB.run(ts: List<&2, T.AaTerm>, b: AaPtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtB>:
  match ts:
    case Nil{}:
      Done{b}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, AaPtB>:
        b2 : AaPtB <- AaPtB.step(t, b, src)
        AaPtB.run(rest, b2, src)

def AaPtB.finish(q: P.AaQual, b: AaPtB) -> AaPtraceRule:
  match b:
    case AaPtB{p, pe}:
      AaPtraceRule{q, Maybe.default(&2, P.AaPerms, p, P.AaPerms.of_bits([True{}, True{}, True{}, True{}])), pe}

def AaPtrace.parse.q(r: Result<&2, &2, E.AaError, P.AaQual>, ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtraceRule>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{q}:
      do Result<&2, &2, E.AaError, AaPtraceRule>:
        b : AaPtB <- AaPtB.run(ts, AaPtB{None{}, None{}}, src)
        return AaPtB.finish(q, b)

# the terms after `ptrace`
def AaPtrace.parse(ts: List<&2, T.AaTerm>, q: P.AaQual, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaPtraceRule>:
  AaPtrace.parse.q(R.AaRule.no_owner(q, src), ts, src)

# Matching

def AaPtraceRule.matches(r: AaPtraceRule, q: AaPtraceQuery) -> Bool:
  match r:
    case AaPtraceRule{qu, p, pe}:
      match q:
        case AaPtraceQuery{req, peer}:
          R.AaRule.opt_match(pe, peer)

def AaPtraceRule.matching.go(hit: Bool, r: AaPtraceRule, rest: List<&2, AaPtraceRule>) -> List<&2, AaPtraceRule>:
  match hit:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

def AaPtraceRule.matching(rs: List<&2, AaPtraceRule>, +q: AaPtraceQuery) -> List<&2, AaPtraceRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      AaPtraceRule.matching.go(AaPtraceRule.matches(r, q), r, AaPtraceRule.matching(t, q))

def AaPtraceRule.grants.of(rs: List<&2, AaPtraceRule>) -> List<&2, P.AaGrant>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case AaPtraceRule{qu, p, pe}:
          Con{P.AaGrant.of(qu, p), AaPtraceRule.grants.of(t)}

def AaPtraceRule.grants(rs: List<&2, AaPtraceRule>, +q: AaPtraceQuery) -> List<&2, P.AaGrant>:
  AaPtraceRule.grants.of(AaPtraceRule.matching(rs, q))

def AaPtraceRule.append(xs: List<&2, AaPtraceRule>, ys: List<&2, AaPtraceRule>) -> List<&2, AaPtraceRule>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaPtraceRule.append(t, ys)}

def AaPtraceQuery.req(q: AaPtraceQuery) -> P.AaPerms:
  match q:
    case AaPtraceQuery{r, p}:
      r
