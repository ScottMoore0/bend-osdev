# Validation and the readers, for every input.
#
# Validation: an attribute NlAttr{t, nd, nb, pl} validated on its own
# against policy pol of a set, whose rule for type t is R, answers exactly
# what R describes (one law per kind of rule), for every check
# NlCheck{p, exact, unknown, nf, depth}. The answer is written below as a
# plain Result over the payload's length l = Octets.len(pl) and its last
# byte. The fuel is any number of steps from 2 (one for the attribute, one
# for the end of its list); nla.parse_policy gives far more.
#
# The readers: each reads back the integer its maker wrote, in either byte
# order, and nla.find answers the first attribute of the type.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./header.bend as H
import ./nlattr.bend as N
import ./policy.bend as P

# The answers, as the netlink documentation describes each rule

def nllaw.need(ok: Bool, e: N.NlError) -> Result<&2, &2, N.NlError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

def nllaw.then(r: Result<&2, &2, N.NlError, Unit>, s: Result<&2, &2, N.NlError, Unit>) -> Result<&2, &2, N.NlError, Unit>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      s

# an integer of size bytes: with exact, fewer bytes are too short and more
# too large; without it, only fewer are refused
def nllaw.int(exact: Bool, +t: Nat, +l: Nat, +size: Nat) -> Result<&2, &2, N.NlError, Unit>:
  match exact:
    case True{}:
      nllaw.then(nllaw.need(Bool.not(Nat.is_lt(l, size)), N.NlTooShort{t}), nllaw.need(Bool.not(Nat.is_lt(size, l)), N.NlTooLarge{t}))
    case False{}:
      nllaw.need(Nat.is_le(size, l), N.NlTooShort{t})

# at most max bytes, max 0 being no limit
def nllaw.atmost(+max: Nat, l: Nat, t: Nat) -> Result<&2, &2, N.NlError, Unit>:
  nllaw.need(Bool.or(Nat.is_eq(max, 0n), Nat.is_le(l, max)), N.NlTooLarge{t})

def nllaw.nul_at(m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{b}:
      U32.is_eq(b, 0)
    case None{}:
      False{}

# the payload's last byte is a NUL
def nllaw.ends_nul(+pl: B.Octets) -> Bool:
  nllaw.nul_at(B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n)))

# the payload's length, a final NUL not counted
def nllaw.strlen(+pl: B.Octets) -> Nat:
  Bool.pick(Nat, nllaw.ends_nul(pl), Nat.sub(B.Octets.len(pl), 1n), B.Octets.len(pl))

# A type with no rule: refused when the check refuses unknown types

law validate_no_rule:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +hr: {List.get(&2, P.NlRule, rs, t) == None{} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.need(Bool.not(unknown), N.NlUnknown{t}) : Result<&2, &2, N.NlError, Unit>}

law validate_unspec:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +min: Nat
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlUnspec{min}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.need(Nat.is_le(min, B.Octets.len(pl)), N.NlTooShort{t}) : Result<&2, &2, N.NlError, Unit>}

law validate_u8:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlU8{}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.int(exact, t, B.Octets.len(pl), 1n) : Result<&2, &2, N.NlError, Unit>}

law validate_u16:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlU16{}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.int(exact, t, B.Octets.len(pl), 2n) : Result<&2, &2, N.NlError, Unit>}

law validate_u32:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlU32{}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.int(exact, t, B.Octets.len(pl), 4n) : Result<&2, &2, N.NlError, Unit>}

law validate_u64:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlU64{}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.int(exact, t, B.Octets.len(pl), 8n) : Result<&2, &2, N.NlError, Unit>}

law validate_string:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +max: Nat
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlString{max}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.atmost(max, nllaw.strlen(pl), t) : Result<&2, &2, N.NlError, Unit>}

law validate_nul_string:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +max: Nat
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlNulString{max}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.then(nllaw.need(nllaw.ends_nul(pl), N.NlNoNul{t}), nllaw.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t)) : Result<&2, &2, N.NlError, Unit>}

law validate_flag:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlFlag{}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.need(Nat.is_eq(B.Octets.len(pl), 0n), N.NlNotFlag{t}) : Result<&2, &2, N.NlError, Unit>}

law validate_binary:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +min: Nat
  for +max: Nat
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlBinary{min, max}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == nllaw.then(nllaw.need(Nat.is_le(min, B.Octets.len(pl)), N.NlTooShort{t}), nllaw.atmost(max, B.Octets.len(pl), t)) : Result<&2, &2, N.NlError, Unit>}

law validate_reject:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlReject{}} : Maybe<&2, P.NlRule>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == Fail{N.NlUnknown{t}} : Result<&2, &2, N.NlError, Unit>}

# A nested rule: refused without NLA_F_NESTED when the check asks for it,
# refused at depth 0, refused with the payload's parse error, and accepted
# when the payload's attributes are valid against the nested policy one
# level deeper (with the fuel f that validation took)

law validate_nested_no_flag:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +depth: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +sub: Nat
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlNested{sub}} : Maybe<&2, P.NlRule>}
  for +hf: {Bool.or(Bool.not(nf), nd) == False{} : Bool}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == Fail{N.NlNoNestedFlag{t}} : Result<&2, &2, N.NlError, Unit>}

law validate_nested_too_deep:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +sub: Nat
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlNested{sub}} : Maybe<&2, P.NlRule>}
  for +hf: {Bool.or(Bool.not(nf), nd) == True{} : Bool}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, 0n}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == Fail{N.NlTooDeep{}} : Result<&2, &2, N.NlError, Unit>}

law validate_nested_bad:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +d: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +sub: Nat
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlNested{sub}} : Maybe<&2, P.NlRule>}
  for +hf: {Bool.or(Bool.not(nf), nd) == True{} : Bool}
  for +e: N.NlError
  for +hp: {N.nla.parse(p, pl) == Fail{e} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  for +f: Nat
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, 1n+d}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == Fail{e} : Result<&2, &2, N.NlError, Unit>}

law validate_nested_valid:
  for +p: N.NlOpts
  for +exact: Bool
  for +unknown: Bool
  for +nf: Bool
  for +d: Nat
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +rs: List<&2, P.NlRule>
  for +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}
  for +t: Nat
  for +nd: Bool
  for +nb: Bool
  for +pl: B.Octets
  for +sub: Nat
  for +hr: {List.get(&2, P.NlRule, rs, t) == Some{P.NlNested{sub}} : Maybe<&2, P.NlRule>}
  for +hf: {Bool.or(Bool.not(nf), nd) == True{} : Bool}
  for +as: List<&2, N.NlAttr>
  for +hp: {N.nla.parse(p, pl) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  for +f: Nat
  for +u: Unit
  for +hv: {P.nla.validate(P.NlCheck{p, exact, unknown, nf, d}, set, sub, f, as) == Done{u} : Result<&2, &2, N.NlError, Unit>}
  {P.nla.validate(P.NlCheck{p, exact, unknown, nf, 1n+d}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}

# The readers

law get_u8_round_trip:
  for +t: Nat
  for +v: U32
  {N.nla.get_u8(N.nla.u8(t, v)) == Some{B.byte(v)} : Maybe<&2, U32>}

law get_u16_round_trip:
  for +o: H.NlOrder
  for +t: Nat
  for +v: U32
  {N.nla.get_u16(o, N.nla.u16(o, t, v)) == Some{B.low16(v)} : Maybe<&2, U32>}

law get_u32_round_trip:
  for +o: H.NlOrder
  for +t: Nat
  for +v: U32
  {N.nla.get_u32(o, N.nla.u32(o, t, v)) == Some{v} : Maybe<&2, U32>}

# a network-order value reads back in either host order
law get_u32_be_round_trip:
  for +o: H.NlOrder
  for +t: Nat
  for +v: U32
  {N.nla.get_u32(o, N.nla.u32_be(t, v)) == Some{v} : Maybe<&2, U32>}

law get_u64_round_trip:
  for +o: H.NlOrder
  for +t: Nat
  for +v: W.W64
  {N.nla.get_u64(o, N.nla.u64(o, t, v)) == Some{v} : Maybe<&2, W.W64>}

# nla.find: the first attribute of the type; others before it are skipped

law find_head:
  for +a: N.NlAttr
  for +as: List<&2, N.NlAttr>
  {N.nla.find(Con{a, as}, N.nla.type(a)) == Some{a} : Maybe<&2, N.NlAttr>}

law find_skip:
  for +a: N.NlAttr
  for +as: List<&2, N.NlAttr>
  for +t: Nat
  for +ne: {Nat.is_eq(N.nla.type(a), t) == False{} : Bool}
  {N.nla.find(Con{a, as}, t) == N.nla.find(as, t) : Maybe<&2, N.NlAttr>}

law find_nil:
  for +t: Nat
  {N.nla.find(Nil{}, t) == None{} : Maybe<&2, N.NlAttr>}

# The hypotheses of the nested laws are satisfiable: a nested attribute of
# one u32, valid against a set of two policies

law validate_nested_example:
  {P.nla.validate(P.nla.check_strict(H.NlLittle{}), [P.NlPolicy{[P.NlReject{}, P.NlNested{1n}]}, P.NlPolicy{[P.NlReject{}, P.NlU32{}]}], 0n, 4n, [N.NlAttr{1n, True{}, False{}, B.Octets.of_list([8, 0, 1, 0, 1, 0, 0, 0])}]) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}
