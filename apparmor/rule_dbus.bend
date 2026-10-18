# bend-osdev-apparmor: dbus rules (apparmor.d(5), "DBUS RULE", "DBus
# rules"): message rules (path, interface, member, peer=(name label)),
# service rules (name) and eavesdrop rules (bus only), each with an
# optional bus=. Permission bits: send 0, receive 1, bind 2, eavesdrop 3.
# r and read are receive, w and write send, rw both. bind is not allowed in
# message rules, send and receive not in service rules, eavesdrop only with
# a bus condition. With no access list a message rule implies send and
# receive, a service rule bind, and a rule with neither kind of condition
# all four.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./rule.bend as R

type AaDbusRule is Data:
  AaDbusRule{qual: P.AaQual, perms: P.AaPerms, bus: Maybe<&2, G.AaGlob>, path: Maybe<&2, G.AaGlob>, iface: Maybe<&2, G.AaGlob>, member: Maybe<&2, G.AaGlob>, name: Maybe<&2, G.AaGlob>, peer_name: Maybe<&2, G.AaGlob>, peer_label: Maybe<&2, G.AaGlob>}

# a dbus operation: req (send, receive, bind, eavesdrop), the bus (system,
# session, ...), the object path, interface and member, the name bound (for
# bind), and the peer's bus name and profile name
type AaDbusQuery is Data:
  AaDbusQuery{req: P.AaPerms, bus: List<&2, U32>, path: List<&2, U32>, iface: List<&2, U32>, member: List<&2, U32>, name: List<&2, U32>, peer_name: List<&2, U32>, peer_label: List<&2, U32>}

def AaDbus.send() -> Nat:
  0n

def AaDbus.receive() -> Nat:
  1n

def AaDbus.bind() -> Nat:
  2n

def AaDbus.eavesdrop() -> Nat:
  3n

def AaDbus.access(+w: List<&2, U32>) -> Maybe<&2, P.AaPerms>:
  Bool.pick(Maybe<&2, P.AaPerms>, Bool.or(X.AaText.is(w, "send"), Bool.or(X.AaText.is(w, "w"), X.AaText.is(w, "write"))), Some{P.AaPerms.bit(0n)}, Bool.pick(Maybe<&2, P.AaPerms>, Bool.or(X.AaText.is(w, "receive"), Bool.or(X.AaText.is(w, "r"), X.AaText.is(w, "read"))), Some{P.AaPerms.bit(1n)}, Bool.pick(Maybe<&2, P.AaPerms>, X.AaText.is(w, "bind"), Some{P.AaPerms.bit(2n)}, Bool.pick(Maybe<&2, P.AaPerms>, X.AaText.is(w, "eavesdrop"), Some{P.AaPerms.bit(3n)}, Bool.pick(Maybe<&2, P.AaPerms>, X.AaText.is(w, "rw"), Some{P.AaPerms.of_bits([True{}, True{}])}, None{})))))

# The builder: one slot per condition, each set at most once
type AaDbB is Data:
  AaDbB{perms: Maybe<&2, P.AaPerms>, slots: List<&2, Maybe<&2, G.AaGlob>>}

def AaDbB.empty() -> AaDbB:
  AaDbB{None{}, [None{}, None{}, None{}, None{}, None{}, None{}, None{}]}

# the slot of a condition key: bus 0, path 1, interface 2, member 3, name 4
def AaDbus.slot(+k: List<&2, U32>) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, X.AaText.is(k, "bus"), Some{0n}, Bool.pick(Maybe<&2, Nat>, X.AaText.is(k, "path"), Some{1n}, Bool.pick(Maybe<&2, Nat>, X.AaText.is(k, "interface"), Some{2n}, Bool.pick(Maybe<&2, Nat>, X.AaText.is(k, "member"), Some{3n}, Bool.pick(Maybe<&2, Nat>, X.AaText.is(k, "name"), Some{4n}, None{})))))

# a peer condition's key: name 5, label 6
def AaDbus.peer_slot(+k: List<&2, U32>) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, X.AaText.is(k, "name"), Some{5n}, Bool.pick(Maybe<&2, Nat>, X.AaText.is(k, "label"), Some{6n}, None{}))

def AaDbus.set.cons(x: Maybe<&2, G.AaGlob>, r: Maybe<&2, List<&2, Maybe<&2, G.AaGlob>>>) -> Maybe<&2, List<&2, Maybe<&2, G.AaGlob>>>:
  match r:
    case None{}:
      None{}
    case Some{xs}:
      Some{Con{x, xs}}

# slot i of the list set to g; None if it is set already
def AaDbus.set(n: Nat, xs: List<&2, Maybe<&2, G.AaGlob>>, g: G.AaGlob) -> Maybe<&2, List<&2, Maybe<&2, G.AaGlob>>>:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          None{}
        case Con{x, rest}:
          match x:
            case None{}:
              Some{Con{Some{g}, rest}}
            case Some{h}:
              None{}
    case 1n+m:
      match xs:
        case Nil{}:
          None{}
        case Con{x, rest}:
          AaDbus.set.cons(x, AaDbus.set(m, rest, g))

def AaDbB.put.go(r: Maybe<&2, List<&2, Maybe<&2, G.AaGlob>>>, p: Maybe<&2, P.AaPerms>, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  match r:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{xs}:
      Done{AaDbB{p, xs}}

def AaDbB.put(m: Maybe<&2, Nat>, b: AaDbB, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{n}:
      match b:
        case AaDbB{p, xs}:
          AaDbB.put.go(AaDbus.set(n, xs, g), p, src)

def AaDbB.perms(m: Maybe<&2, P.AaPerms>, b: AaDbB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  match m:
    case None{}:
      Fail{E.AaSrc.syntax(src)}
    case Some{p}:
      match b:
        case AaDbB{bp, xs}:
          match bp:
            case None{}:
              Done{AaDbB{Some{p}, xs}}
            case Some{q}:
              Done{AaDbB{Some{P.AaPerms.union(q, p)}, xs}}

def AaDbB.access_list(xs: List<&2, T.AaTerm>, b: AaDbB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  match xs:
    case Nil{}:
      Done{b}
    case Con{x, rest}:
      match x:
        case T.AaTmWord{w}:
          do Result<&2, &2, E.AaError, AaDbB>:
            b2 : AaDbB <- AaDbB.perms(AaDbus.access(w), b, src)
            AaDbB.access_list(rest, b2, src)
        case _:
          Fail{E.AaSrc.syntax(src)}

def AaDbB.cond.one(m: Maybe<&2, Nat>, v: T.AaTerm, b: AaDbB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  do Result<&2, &2, E.AaError, AaDbB>:
    g : G.AaGlob <- R.AaRule.value_glob(v, src)
    AaDbB.put(m, b, g, src)

# the conditions inside peer=( ... )
def AaDbB.peer(xs: List<&2, T.AaTerm>, b: AaDbB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  match xs:
    case Nil{}:
      Done{b}
    case Con{x, rest}:
      match x:
        case T.AaTmCond{k, v}:
          do Result<&2, &2, E.AaError, AaDbB>:
            b2 : AaDbB <- AaDbB.cond.one(AaDbus.peer_slot(k), v, b, src)
            AaDbB.peer(rest, b2, src)
        case _:
          Fail{E.AaSrc.syntax(src)}

def AaDbB.cond.peer(v: T.AaTerm, b: AaDbB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  match v:
    case T.AaTmList{xs}:
      AaDbB.peer(xs, b, src)
    case _:
      Fail{E.AaSrc.syntax(src)}

def AaDbB.cond(+k: List<&2, U32>, +v: T.AaTerm, +b: AaDbB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  Bool.pick(Result<&2, &2, E.AaError, AaDbB>, X.AaText.is(k, "peer"), AaDbB.cond.peer(v, b, src), AaDbB.cond.one(AaDbus.slot(k), v, b, src))

def AaDbB.step(t: T.AaTerm, b: AaDbB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  match t:
    case T.AaTmWord{w}:
      AaDbB.perms(AaDbus.access(w), b, src)
    case T.AaTmList{xs}:
      AaDbB.access_list(xs, b, src)
    case T.AaTmCond{k, v}:
      AaDbB.cond(k, v, b, src)
    case _:
      Fail{E.AaSrc.syntax(src)}

def AaDbB.run(ts: List<&2, T.AaTerm>, b: AaDbB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbB>:
  match ts:
    case Nil{}:
      Done{b}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, AaDbB>:
        b2 : AaDbB <- AaDbB.step(t, b, src)
        AaDbB.run(rest, b2, src)

def AaDbus.is_some(m: Maybe<&2, G.AaGlob>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{g}:
      True{}

def AaDbus.nth(n: Nat, xs: List<&2, Maybe<&2, G.AaGlob>>) -> Maybe<&2, G.AaGlob>:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          None{}
        case Con{x, rest}:
          x
    case 1n+m:
      match xs:
        case Nil{}:
          None{}
        case Con{x, rest}:
          AaDbus.nth(m, rest)

# the permissions given, checked against the kind of rule, or the implied ones
def AaDbus.perms(m: Maybe<&2, P.AaPerms>, +msg: Bool, +svc: Bool, src: E.AaSrc) -> Result<&2, &2, E.AaError, P.AaPerms>:
  match m:
    case None{}:
      Done{Bool.pick(P.AaPerms, msg, P.AaPerms.of_bits([True{}, True{}]), Bool.pick(P.AaPerms, svc, P.AaPerms.bit(2n), P.AaPerms.of_bits([True{}, True{}, True{}, True{}])))}
    case Some{+p}:
      +bad = Bool.or(Bool.and(msg, svc), Bool.or(Bool.and(msg, P.AaPerms.has(p, 2n)), Bool.or(Bool.and(svc, Bool.or(P.AaPerms.has(p, 0n), P.AaPerms.has(p, 1n))), Bool.and(Bool.or(msg, svc), P.AaPerms.has(p, 3n)))))
      Bool.pick(Result<&2, &2, E.AaError, P.AaPerms>, bad, Fail{E.AaSrc.syntax(src)}, Done{p})

def AaDbB.finish(q: P.AaQual, b: AaDbB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbusRule>:
  match b:
    case AaDbB{p, +xs}:
      +msg = Bool.or(AaDbus.is_some(AaDbus.nth(1n, xs)), Bool.or(AaDbus.is_some(AaDbus.nth(2n, xs)), Bool.or(AaDbus.is_some(AaDbus.nth(3n, xs)), Bool.or(AaDbus.is_some(AaDbus.nth(5n, xs)), AaDbus.is_some(AaDbus.nth(6n, xs))))))
      +svc = AaDbus.is_some(AaDbus.nth(4n, xs))
      do Result<&2, &2, E.AaError, AaDbusRule>:
        ps : P.AaPerms <- AaDbus.perms(p, msg, svc, src)
        return AaDbusRule{q, ps, AaDbus.nth(0n, xs), AaDbus.nth(1n, xs), AaDbus.nth(2n, xs), AaDbus.nth(3n, xs), AaDbus.nth(4n, xs), AaDbus.nth(5n, xs), AaDbus.nth(6n, xs)}

def AaDbus.parse.q(r: Result<&2, &2, E.AaError, P.AaQual>, ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbusRule>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{q}:
      do Result<&2, &2, E.AaError, AaDbusRule>:
        b : AaDbB <- AaDbB.run(ts, AaDbB.empty(), src)
        AaDbB.finish(q, b, src)

# the terms after `dbus`
def AaDbus.parse(ts: List<&2, T.AaTerm>, q: P.AaQual, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaDbusRule>:
  AaDbus.parse.q(R.AaRule.no_owner(q, src), ts, src)

# Matching

def AaDbusRule.matches(r: AaDbusRule, q: AaDbusQuery) -> Bool:
  match r:
    case AaDbusRule{qu, p, bus, path, iface, member, name, pn, pl}:
      match q:
        case AaDbusQuery{req, qbus, qpath, qiface, qmember, qname, qpn, qpl}:
          Bool.and(R.AaRule.opt_match(bus, qbus), Bool.and(R.AaRule.opt_match(path, qpath), Bool.and(R.AaRule.opt_match(iface, qiface), Bool.and(R.AaRule.opt_match(member, qmember), Bool.and(R.AaRule.opt_match(name, qname), Bool.and(R.AaRule.opt_match(pn, qpn), R.AaRule.opt_match(pl, qpl)))))))

def AaDbusRule.matching.go(hit: Bool, r: AaDbusRule, rest: List<&2, AaDbusRule>) -> List<&2, AaDbusRule>:
  match hit:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

def AaDbusRule.matching(rs: List<&2, AaDbusRule>, +q: AaDbusQuery) -> List<&2, AaDbusRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      AaDbusRule.matching.go(AaDbusRule.matches(r, q), r, AaDbusRule.matching(t, q))

def AaDbusRule.grants.of(rs: List<&2, AaDbusRule>) -> List<&2, P.AaGrant>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case AaDbusRule{qu, p, bus, path, iface, member, name, pn, pl}:
          Con{P.AaGrant.of(qu, p), AaDbusRule.grants.of(t)}

def AaDbusRule.grants(rs: List<&2, AaDbusRule>, +q: AaDbusQuery) -> List<&2, P.AaGrant>:
  AaDbusRule.grants.of(AaDbusRule.matching(rs, q))

def AaDbusRule.append(xs: List<&2, AaDbusRule>, ys: List<&2, AaDbusRule>) -> List<&2, AaDbusRule>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaDbusRule.append(t, ys)}

def AaDbusQuery.req(q: AaDbusQuery) -> P.AaPerms:
  match q:
    case AaDbusQuery{r, b, p, i, m, n, pn, pl}:
      r
