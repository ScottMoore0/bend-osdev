# bend-osdev-apparmor: network rules (apparmor.d(5), "NETWORK RULE",
# "Network Rules"): `network [DOMAIN] [TYPE | PROTOCOL]`, coarse-grained
# mediation by address family, socket type and protocol. Rules become more
# restrictive as more is given and accumulate as a union. Access lists and
# the ip, port and peer conditions (fine-grained inet mediation) are outside
# the model. One permission bit: use.
import Base
import ./text.bend as X
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./rule.bend as R

type AaNetRule is Data:
  AaNetRule{qual: P.AaQual, domain: Maybe<&2, List<&2, U32>>, stype: Maybe<&2, List<&2, U32>>, proto: Maybe<&2, List<&2, U32>>}

# a socket: its domain (inet, unix, ...), type (stream, dgram, ...) and
# protocol (tcp, udp, icmp, or empty)
type AaNetQuery is Data:
  AaNetQuery{domain: List<&2, U32>, stype: List<&2, U32>, proto: List<&2, U32>}

def AaNet.domains() -> List<&2, String>:
  ["unix", "inet", "ax25", "ipx", "appletalk", "netrom", "bridge", "atmpvc", "x25", "inet6", "rose", "netbeui", "security", "key", "netlink", "packet", "ash", "econet", "atmsvc", "rds", "sna", "irda", "pppox", "wanpipe", "llc", "ib", "mpls", "can", "tipc", "bluetooth", "iucv", "rxrpc", "isdn", "phonet", "ieee802154", "caif", "alg", "nfc", "vsock", "kcm", "qipcrtr", "smc", "xdp", "mctp"]

def AaNet.types() -> List<&2, String>:
  ["stream", "dgram", "seqpacket", "rdm", "raw", "packet"]

def AaNet.protos() -> List<&2, String>:
  ["tcp", "udp", "icmp"]

# the access permissions of fine-grained rules (not modelled)
def AaNet.accesses() -> List<&2, String>:
  ["create", "bind", "listen", "accept", "connect", "shutdown", "getattr", "setattr", "getopt", "setopt", "send", "receive", "r", "w", "rw"]

# what a word of a network rule is: 0 a domain, 1 a type, 2 a protocol, 3 an access (unsupported), 4 unknown
def AaNet.kind(+w: List<&2, U32>) -> Nat:
  Bool.pick(Nat, X.AaText.one_of(AaNet.domains(), w), 0n, Bool.pick(Nat, X.AaText.one_of(AaNet.types(), w), 1n, Bool.pick(Nat, X.AaText.one_of(AaNet.protos(), w), 2n, Bool.pick(Nat, X.AaText.one_of(AaNet.accesses(), w), 3n, 4n))))

def AaNet.word(t: T.AaTerm, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, U32>>:
  match t:
    case T.AaTmWord{w}:
      Done{w}
    case T.AaTmQuoted{q}:
      Fail{E.AaSrc.syntax(src)}
    case T.AaTmList{xs}:
      Fail{E.AaSrc.unsupported(src)}
    case T.AaTmCond{k, v}:
      Fail{E.AaSrc.unsupported(src)}
    case T.AaTmArrow{}:
      Fail{E.AaSrc.syntax(src)}

def AaNet.add.kind(ty: Maybe<&2, List<&2, U32>>, pr: Maybe<&2, List<&2, U32>>, r: AaNetRule, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  match ty:
    case Some{x}:
      Fail{E.AaSrc.syntax(src)}
    case None{}:
      match pr:
        case Some{y}:
          Fail{E.AaSrc.syntax(src)}
        case None{}:
          Done{r}

def AaNet.set_type(r: AaNetRule, w: List<&2, U32>, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  match r:
    case AaNetRule{q, d, +ty, +pr}:
      AaNet.add.kind(ty, pr, AaNetRule{q, d, Some{w}, pr}, src)

def AaNet.set_proto(r: AaNetRule, w: List<&2, U32>, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  match r:
    case AaNetRule{q, d, +ty, +pr}:
      AaNet.add.kind(ty, pr, AaNetRule{q, d, ty, Some{w}}, src)

def AaNet.set_domain(first: Bool, r: AaNetRule, w: List<&2, U32>, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  match first:
    case True{}:
      match r:
        case AaNetRule{q, d, ty, pr}:
          Done{AaNetRule{q, Some{w}, ty, pr}}
    case False{}:
      Fail{E.AaSrc.syntax(src)}

# the rule so far and the next word: a domain only first, then at most one type or protocol
def AaNet.add(k: Nat, first: Bool, r: AaNetRule, w: List<&2, U32>, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  match k:
    case 0n:
      AaNet.set_domain(first, r, w, src)
    case 1n+k1:
      match k1:
        case 0n:
          AaNet.set_type(r, w, src)
        case 1n+k2:
          match k2:
            case 0n:
              AaNet.set_proto(r, w, src)
            case 1n+k3:
              match k3:
                case 0n:
                  Fail{E.AaSrc.unsupported(src)}
                case 1n+k4:
                  Fail{E.AaSrc.name(src)}

def AaNet.add.word(+w: List<&2, U32>, first: Bool, r: AaNetRule, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  AaNet.add(AaNet.kind(w), first, r, w, src)

def AaNet.parse.go(ts: List<&2, T.AaTerm>, r: AaNetRule, +first: Bool, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  match ts:
    case Nil{}:
      Done{r}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, AaNetRule>:
        w : List<&2, U32> <- AaNet.word(t, src)
        r2 : AaNetRule <- AaNet.add.word(w, first, r, src)
        AaNet.parse.go(rest, r2, False{}, src)

# a protocol needs the inet or inet6 domain, or none, and icmp is not inet6's
# (apparmor_parser 4.0.1: "Invalid network entry" otherwise)
def AaNet.proto_ok(d: Maybe<&2, List<&2, U32>>, pr: Maybe<&2, List<&2, U32>>) -> Bool:
  match d:
    case None{}:
      True{}
    case Some{+x}:
      match pr:
        case None{}:
          True{}
        case Some{+y}:
          Bool.or(X.AaText.is(x, "inet"), Bool.and(X.AaText.is(x, "inet6"), Bool.not(X.AaText.is(y, "icmp"))))

def AaNet.check(r: AaNetRule, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  match r:
    case AaNetRule{q, +d, ty, +pr}:
      Bool.pick(Result<&2, &2, E.AaError, AaNetRule>, AaNet.proto_ok(d, pr), Done{AaNetRule{q, d, ty, pr}}, Fail{E.AaSrc.name(src)})

def AaNet.parse.q(r: Result<&2, &2, E.AaError, P.AaQual>, ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{q}:
      do Result<&2, &2, E.AaError, AaNetRule>:
        x : AaNetRule <- AaNet.parse.go(ts, AaNetRule{q, None{}, None{}, None{}}, True{}, src)
        AaNet.check(x, src)

# the terms after `network`
def AaNet.parse(ts: List<&2, T.AaTerm>, q: P.AaQual, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaNetRule>:
  AaNet.parse.q(R.AaRule.no_owner(q, src), ts, src)

# Matching

def AaNet.opt_eq(m: Maybe<&2, List<&2, U32>>, x: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{y}:
      X.AaText.eq(y, x)

def AaNetRule.matches(r: AaNetRule, q: AaNetQuery) -> Bool:
  match r:
    case AaNetRule{qu, d, ty, pr}:
      match q:
        case AaNetQuery{qd, qt, qp}:
          Bool.and(AaNet.opt_eq(d, qd), Bool.and(AaNet.opt_eq(ty, qt), AaNet.opt_eq(pr, qp)))

def AaNetRule.matching.go(hit: Bool, r: AaNetRule, rest: List<&2, AaNetRule>) -> List<&2, AaNetRule>:
  match hit:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

def AaNetRule.matching(rs: List<&2, AaNetRule>, +q: AaNetQuery) -> List<&2, AaNetRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      AaNetRule.matching.go(AaNetRule.matches(r, q), r, AaNetRule.matching(t, q))

def AaNetRule.grants.of(rs: List<&2, AaNetRule>) -> List<&2, P.AaGrant>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case AaNetRule{qu, d, ty, pr}:
          Con{P.AaGrant.of(qu, P.AaPerms.bit(0n)), AaNetRule.grants.of(t)}

def AaNetRule.grants(rs: List<&2, AaNetRule>, +q: AaNetQuery) -> List<&2, P.AaGrant>:
  AaNetRule.grants.of(AaNetRule.matching(rs, q))

def AaNetRule.append(xs: List<&2, AaNetRule>, ys: List<&2, AaNetRule>) -> List<&2, AaNetRule>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaNetRule.append(t, ys)}

def AaNetQuery.req() -> P.AaPerms:
  P.AaPerms.bit(0n)
