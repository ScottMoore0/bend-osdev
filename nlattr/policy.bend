# bend-osdev-nlattr, validation against a policy (the kernel's struct
# nla_policy and nla_validate, as its netlink documentation describes them).
#
# A policy gives a rule per attribute type (rule t for type t); a set of
# policies is a list, and a nested attribute's rule names the policy of its
# payload by its index in the set, so policies may refer to each other
# (and to themselves) without a recursive type.
import Base
import ../bytes/bytes.bend as B
import ./header.bend as H
import ./nlattr.bend as N

type NlRule is Data:
  NlUnspec{min: Nat}
  NlU8{}
  NlU16{}
  NlU32{}
  NlU64{}
  NlString{max: Nat}
  NlNulString{max: Nat}
  NlFlag{}
  NlBinary{min: Nat, max: Nat}
  NlNested{policy: Nat}
  NlReject{}

type NlPolicy is Data:
  NlPolicy{rules: List<&2, NlRule>}

# How to validate: how to parse nested payloads, whether integer payloads
# must have exactly their size (else at least it), whether a type with no
# rule is an error (else ignored), whether a nested attribute must carry
# NLA_F_NESTED, and how deep nesting may go
type NlCheck is Data:
  NlCheck{parse: N.NlOpts, exact: Bool, unknown: Bool, nested_flag: Bool, depth: Nat}

# the kernel's strict validation (NL_VALIDATE_STRICT), and its liberal one
def nla.check_strict(+o: H.NlOrder) -> NlCheck:
  NlCheck{N.NlOpts{o, True{}}, True{}, True{}, True{}, 10n}

def nla.check_liberal(+o: H.NlOrder) -> NlCheck:
  NlCheck{N.NlOpts{o, False{}}, False{}, False{}, False{}, 10n}

def nla.check_default() -> NlCheck:
  nla.check_strict(H.NlLittle{})

def nla.check.parse(c: NlCheck) -> N.NlOpts:
  match c:
    case NlCheck{p, e, u, nf, d}:
      p

# work left: attributes to validate against a policy, at a nesting depth
type NlWork is Data:
  NlWork{depth: Nat, policy: Nat, attrs: List<&2, N.NlAttr>}

def nla.rule.at(m: Maybe<&2, NlPolicy>, +t: Nat) -> Maybe<&2, NlRule>:
  match m:
    case None{}:
      None{}
    case Some{NlPolicy{rs}}:
      List.get(&2, NlRule, rs, t)

# the rule for type t in policy pol of the set
def nla.rule(set: List<&2, NlPolicy>, pol: Nat, +t: Nat) -> Maybe<&2, NlRule>:
  nla.rule.at(List.get(&2, NlPolicy, set, pol), t)

def nla.ok() -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  Done{None{}}

def nla.need(ok: Bool, e: N.NlError) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match ok:
    case True{}:
      nla.ok()
    case False{}:
      Fail{e}

def nla.int.exact(short: Bool, long: Bool, +t: Nat) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match short long:
    case True{} _:
      Fail{N.NlTooShort{t}}
    case False{} True{}:
      Fail{N.NlTooLarge{t}}
    case False{} False{}:
      nla.ok()

# an integer payload of size bytes: exactly (exact) or at least
def nla.int(exact: Bool, +t: Nat, +l: Nat, +size: Nat) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match exact:
    case True{}:
      nla.int.exact(Nat.is_lt(l, size), Nat.is_lt(size, l), t)
    case False{}:
      nla.need(Nat.is_le(size, l), N.NlTooShort{t})

# at most max bytes (max 0: no limit)
def nla.atmost(+max: Nat, +l: Nat, +t: Nat) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match max:
    case 0n:
      nla.ok()
    case 1n+m:
      nla.need(Nat.is_le(l, 1n+m), N.NlTooLarge{t})

def nla.then(r: Result<&2, &2, N.NlError, Maybe<&2, NlWork>>, s: Result<&2, &2, N.NlError, Maybe<&2, NlWork>>) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{w}:
      s

# the payload's length, not counting a final NUL
def nla.strlen.go(+l: Nat, last: Maybe<&2, U32>) -> Nat:
  match last:
    case Some{+b}:
      Bool.pick(Nat, U32.is_eq(b, 0), Nat.sub(l, 1n), l)
    case None{}:
      l

def nla.ends_nul(last: Maybe<&2, U32>) -> Bool:
  match last:
    case Some{+b}:
      U32.is_eq(b, 0)
    case None{}:
      False{}

def nla.nested.parsed(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, +d: Nat, +sub: Nat) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{as}:
      Done{Some{NlWork{d, sub, as}}}

def nla.nested.flag(ok: Bool, +t: Nat, +p: N.NlOpts, payload: B.Octets, d: Nat, +sub: Nat) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match ok d:
    case False{} _:
      Fail{N.NlNoNestedFlag{t}}
    case True{} 0n:
      Fail{N.NlTooDeep{}}
    case True{} 1n+e:
      nla.nested.parsed(N.nla.parse(p, payload), e, sub)

# one attribute against its rule: a failure, nothing left, or its nested
# attributes to validate next
def nla.step.kind(m: Maybe<&2, NlRule>, +p: N.NlOpts, +exact: Bool, +unknown: Bool, +nf: Bool, +d: Nat, +t: Nat, +nd: Bool, +pl: B.Octets, +l: Nat, +last: Maybe<&2, U32>) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match m:
    case None{}:
      nla.need(Bool.not(unknown), N.NlUnknown{t})
    case Some{NlUnspec{+min}}:
      nla.need(Nat.is_le(min, l), N.NlTooShort{t})
    case Some{NlU8{}}:
      nla.int(exact, t, l, 1n)
    case Some{NlU16{}}:
      nla.int(exact, t, l, 2n)
    case Some{NlU32{}}:
      nla.int(exact, t, l, 4n)
    case Some{NlU64{}}:
      nla.int(exact, t, l, 8n)
    case Some{NlString{+max}}:
      nla.atmost(max, nla.strlen.go(l, last), t)
    case Some{NlNulString{+max}}:
      nla.then(nla.need(nla.ends_nul(last), N.NlNoNul{t}), nla.atmost(max, Nat.sub(l, 1n), t))
    case Some{NlFlag{}}:
      nla.need(Nat.is_eq(l, 0n), N.NlNotFlag{t})
    case Some{NlBinary{+min, +max}}:
      nla.then(nla.need(Nat.is_le(min, l), N.NlTooShort{t}), nla.atmost(max, l, t))
    case Some{NlNested{+sub}}:
      nla.nested.flag(Bool.or(Bool.not(nf), nd), t, p, pl, d, sub)
    case Some{NlReject{}}:
      Fail{N.NlUnknown{t}}

def nla.step.rule(m: Maybe<&2, NlRule>, c: NlCheck, +d: Nat, a: N.NlAttr) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  match m c a:
    case r NlCheck{+p, +exact, +unknown, +nf, dmax} N.NlAttr{+t, +nd, nb, +pl}:
      +l = B.Octets.len(pl)
      nla.step.kind(r, p, exact, unknown, nf, d, t, nd, pl, l, B.Octets.at(pl, Nat.sub(l, 1n)))

def nla.step(+c: NlCheck, set: List<&2, NlPolicy>, +pol: Nat, +d: Nat, +a: N.NlAttr) -> Result<&2, &2, N.NlError, Maybe<&2, NlWork>>:
  nla.step.rule(nla.rule(set, pol, N.nla.type(a)), c, d, a)

def nla.push(m: Maybe<&2, NlWork>, rest: List<&2, NlWork>) -> List<&2, NlWork>:
  match m:
    case None{}:
      rest
    case Some{w}:
      Con{w, rest}

# the work list, one attribute at a time; fuel bounds the steps
def nla.validate.go(fuel: Nat, +c: NlCheck, +set: List<&2, NlPolicy>, work: List<&2, NlWork>) -> Result<&2, &2, N.NlError, Unit>:
  match fuel work:
    case _ Nil{}:
      Done{Unit{}}
    case 0n Con{w, t}:
      Fail{N.NlTooDeep{}}
    case 1n+f Con{NlWork{d, pol, Nil{}}, t}:
      nla.validate.go(f, c, set, t)
    case 1n+f Con{NlWork{+d, +pol, Con{+a, as}}, t}:
      Result.bind(&2, &2, N.NlError, Maybe<&2, NlWork>, Unit, nla.step(c, set, pol, d, a), m => nla.validate.go(f, c, set, nla.push(m, Con{NlWork{d, pol, as}, t})))

# the attributes valid against policy pol of the set (nla_validate)
def nla.validate(+c: NlCheck, +set: List<&2, NlPolicy>, +pol: Nat, +fuel: Nat, as: List<&2, N.NlAttr>) -> Result<&2, &2, N.NlError, Unit>:
  match c:
    case NlCheck{p, e, u, nf, +depth}:
      nla.validate.go(fuel, c, set, [NlWork{depth, pol, as}])

# a parse's attributes, when they are valid against policy pol of the set
def nla.parse_policy.go(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, +c: NlCheck, +set: List<&2, NlPolicy>, +pol: Nat, +fuel: Nat) -> Result<&2, &2, N.NlError, List<&2, N.NlAttr>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+as}:
      Result.map(&2, &2, N.NlError, Unit, List<&2, N.NlAttr>, u2 => as, nla.validate(c, set, pol, fuel, as))

# the attributes of buf, parsed and valid against policy pol of the set
# (nla_parse with a policy); the steps are bounded by the buffer's size
def nla.parse_policy(+c: NlCheck, +set: List<&2, NlPolicy>, +pol: Nat, +buf: B.Octets) -> Result<&2, &2, N.NlError, List<&2, N.NlAttr>>:
  +fuel = Nat.add(Nat.mul(2n, B.Octets.len(buf)), 2n)
  nla.parse_policy.go(N.nla.parse(nla.check.parse(c), buf), c, set, pol, fuel)
