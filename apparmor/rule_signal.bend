# bend-osdev-apparmor: signal rules (apparmor.d(5), "SIGNAL RULE", "Signal
# rules"): `signal [ACCESS] [set=(SIGNALS)] [peer=AARE]`, the conditions in
# any order. Permission bits: send 0, receive 1; with no access list both
# are implied. r and read are receive, w and write send, rw both (the page
# gives these synonyms for dbus; the package reads signal's the same way).
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./rule.bend as R

# signals: None for every signal; peer: None for every peer
type AaSignalRule is Data:
  AaSignalRule{qual: P.AaQual, perms: P.AaPerms, signals: Maybe<&2, List<&2, List<&2, U32>>>, peer: Maybe<&2, G.AaGlob>}

# a signal sent or received (req: send and/or receive), by name (hup, int,
# ..., rtmin+N) and the peer's profile name
type AaSignalQuery is Data:
  AaSignalQuery{req: P.AaPerms, signal: List<&2, U32>, peer: List<&2, U32>}

def AaSignal.send() -> Nat:
  0n

def AaSignal.receive() -> Nat:
  1n

def AaSignal.names() -> List<&2, String>:
  ["hup", "int", "quit", "ill", "trap", "abrt", "bus", "fpe", "kill", "usr1", "segv", "usr2", "pipe", "alrm", "term", "stkflt", "chld", "cont", "stop", "stp", "ttin", "ttou", "urg", "xcpu", "xfsz", "vtalrm", "prof", "winch", "io", "pwr", "sys", "emt", "exists"]

# the digits of xs as a number, if every character is a digit (at most 3)
def AaSignal.num.go(xs: List<&2, U32>, +acc: U32, +n: Nat) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      Bool.pick(Maybe<&2, U32>, Nat.is_eq(n, 0n), None{}, Some{acc})
    case Con{+h, t}:
      Bool.pick(Maybe<&2, U32>, Bool.and(Bool.and(U32.is_ge(h, 48), U32.is_le(h, 57)), Nat.is_lt(n, 3n)), AaSignal.num.go(t, U32.add(U32.mul(acc, 10), U32.sub(h, 48)), 1n+n), None{})

def AaSignal.rt.go(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      U32.is_le(v, 32)

# rtmin+0 ... rtmin+32
def AaSignal.is_rt(+w: List<&2, U32>) -> Bool:
  Bool.and(X.AaText.starts(w, "rtmin+"), AaSignal.rt.go(AaSignal.num.go(X.AaText.drop(6n, w), 0, 0n)))

def AaSignal.valid(+w: List<&2, U32>) -> Bool:
  Bool.or(X.AaText.one_of(AaSignal.names(), w), AaSignal.is_rt(w))

def AaSignal.check(xs: List<&2, List<&2, U32>>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{+x, rest}:
      R.AaRule.check_names.go(AaSignal.valid(x), x, AaSignal.check(rest, src), src)

# the bits of an access word
def AaSignal.access(+w: List<&2, U32>) -> Maybe<&2, P.AaPerms>:
  Bool.pick(Maybe<&2, P.AaPerms>, Bool.or(X.AaText.is(w, "send"), Bool.or(X.AaText.is(w, "w"), X.AaText.is(w, "write"))), Some{P.AaPerms.bit(0n)}, Bool.pick(Maybe<&2, P.AaPerms>, Bool.or(X.AaText.is(w, "receive"), Bool.or(X.AaText.is(w, "r"), X.AaText.is(w, "read"))), Some{P.AaPerms.bit(1n)}, Bool.pick(Maybe<&2, P.AaPerms>, X.AaText.is(w, "rw"), Some{P.AaPerms.of_bits([True{}, True{}])}, None{})))

# Reading the conditions: the permissions so far (None: none given yet)

type AaSigB is Data:
  AaSigB{perms: Maybe<&2, P.AaPerms>, signals: Maybe<&2, List<&2, List<&2, U32>>>, peer: Maybe<&2, G.AaGlob>}

def AaSigB.perms(m: Maybe<&2, P.AaPerms>, b: AaSigB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSigB>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{p}:
      match b:
        case AaSigB{bp, s, pe}:
          match bp:
            case None{}:
              Done{AaSigB{Some{p}, s, pe}}
            case Some{q}:
              Done{AaSigB{Some{P.AaPerms.union(q, p)}, s, pe}}

def AaSigB.access_list(xs: List<&2, T.AaTerm>, b: AaSigB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSigB>:
  match xs:
    case Nil{}:
      Done{b}
    case Con{x, rest}:
      match x:
        case T.AaTmWord{w}:
          do Result<&2, &2, E.AaError, AaSigB>:
            b2 : AaSigB <- AaSigB.perms(AaSignal.access(w), b, src)
            AaSigB.access_list(rest, b2, src)
        case _:
          Fail{E.AaSrc.syntax(src)}

def AaSigB.add_signals(b: AaSigB, xs: List<&2, List<&2, U32>>) -> AaSigB:
  match b:
    case AaSigB{p, s, pe}:
      match s:
        case None{}:
          AaSigB{p, Some{xs}, pe}
        case Some{ys}:
          AaSigB{p, Some{X.AaText.lappend(ys, xs)}, pe}

def AaSigB.set_peer(b: AaSigB, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSigB>:
  match b:
    case AaSigB{p, s, pe}:
      match pe:
        case None{}:
          Done{AaSigB{p, s, Some{g}}}
        case Some{h}:
          Fail{E.AaSrc.syntax(src)}

def AaSigB.cond.set(v: T.AaTerm, b: AaSigB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSigB>:
  do Result<&2, &2, E.AaError, AaSigB>:
    xs : List<&2, List<&2, U32>> <- R.AaRule.texts(T.AaTerm.texts(v), src)
    ys : List<&2, List<&2, U32>> <- AaSignal.check(xs, src)
    return AaSigB.add_signals(b, ys)

def AaSigB.cond.peer(v: T.AaTerm, b: AaSigB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSigB>:
  do Result<&2, &2, E.AaError, AaSigB>:
    g : G.AaGlob <- R.AaRule.value_glob(v, src)
    AaSigB.set_peer(b, g, src)

def AaSigB.cond(+k: List<&2, U32>, +v: T.AaTerm, +b: AaSigB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSigB>:
  Bool.pick(Result<&2, &2, E.AaError, AaSigB>, X.AaText.is(k, "set"), AaSigB.cond.set(v, b, src), Bool.pick(Result<&2, &2, E.AaError, AaSigB>, X.AaText.is(k, "peer"), AaSigB.cond.peer(v, b, src), Fail{E.AaSrc.syntax(src)}))

def AaSigB.step(t: T.AaTerm, b: AaSigB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSigB>:
  match t:
    case T.AaTmWord{w}:
      AaSigB.perms(AaSignal.access(w), b, src)
    case T.AaTmList{xs}:
      AaSigB.access_list(xs, b, src)
    case T.AaTmCond{k, v}:
      AaSigB.cond(k, v, b, src)
    case _:
      Fail{E.AaSrc.syntax(src)}

def AaSigB.run(ts: List<&2, T.AaTerm>, b: AaSigB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSigB>:
  match ts:
    case Nil{}:
      Done{b}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, AaSigB>:
        b2 : AaSigB <- AaSigB.step(t, b, src)
        AaSigB.run(rest, b2, src)

def AaSigB.finish(q: P.AaQual, b: AaSigB) -> AaSignalRule:
  match b:
    case AaSigB{p, s, pe}:
      AaSignalRule{q, Maybe.default(&2, P.AaPerms, p, P.AaPerms.of_bits([True{}, True{}])), s, pe}

def AaSignal.parse.q(r: Result<&2, &2, E.AaError, P.AaQual>, ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSignalRule>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{q}:
      do Result<&2, &2, E.AaError, AaSignalRule>:
        b : AaSigB <- AaSigB.run(ts, AaSigB{None{}, None{}, None{}}, src)
        return AaSigB.finish(q, b)

# the terms after `signal`
def AaSignal.parse(ts: List<&2, T.AaTerm>, q: P.AaQual, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaSignalRule>:
  AaSignal.parse.q(R.AaRule.no_owner(q, src), ts, src)

# Matching

def AaSignal.opt_member(m: Maybe<&2, List<&2, List<&2, U32>>>, +x: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{xs}:
      X.AaText.member(xs, x)

def AaSignalRule.matches(r: AaSignalRule, q: AaSignalQuery) -> Bool:
  match r:
    case AaSignalRule{qu, p, s, pe}:
      match q:
        case AaSignalQuery{req, sig, peer}:
          Bool.and(AaSignal.opt_member(s, sig), R.AaRule.opt_match(pe, peer))

def AaSignalRule.matching.go(hit: Bool, r: AaSignalRule, rest: List<&2, AaSignalRule>) -> List<&2, AaSignalRule>:
  match hit:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

def AaSignalRule.matching(rs: List<&2, AaSignalRule>, +q: AaSignalQuery) -> List<&2, AaSignalRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      AaSignalRule.matching.go(AaSignalRule.matches(r, q), r, AaSignalRule.matching(t, q))

def AaSignalRule.grants.of(rs: List<&2, AaSignalRule>) -> List<&2, P.AaGrant>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case AaSignalRule{qu, p, s, pe}:
          Con{P.AaGrant.of(qu, p), AaSignalRule.grants.of(t)}

def AaSignalRule.grants(rs: List<&2, AaSignalRule>, +q: AaSignalQuery) -> List<&2, P.AaGrant>:
  AaSignalRule.grants.of(AaSignalRule.matching(rs, q))

def AaSignalRule.append(xs: List<&2, AaSignalRule>, ys: List<&2, AaSignalRule>) -> List<&2, AaSignalRule>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaSignalRule.append(t, ys)}

def AaSignalQuery.req(q: AaSignalQuery) -> P.AaPerms:
  match q:
    case AaSignalQuery{r, s, p}:
      r
