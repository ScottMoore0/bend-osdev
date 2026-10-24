import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./header.bend as H
import ./nlattr.bend as N
import ./policy.bend as P
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS_validate.bend as Laws

# Lemmas are mostly stated as {value == expression}, the direction a rewrite
# needs: %e : P replaces the expression (marked _ in P) by the value.

def nlv.rdisc(r: Result<&2, &2, N.NlError, Unit>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{u}:
      Empty

def nlv.fd_absurd(+e: N.NlError, +u: Unit, +h: {Fail{e} == Done{u} : Result<&2, &2, N.NlError, Unit>}) -> Empty:
  %h : nlv.rdisc(_)
  Unit{}

def nlv.nrefl(+n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nlv.nrefl(p)

def nlv.byte_idem(+v: U32) -> {B.byte(v) == B.byte(B.byte(v)) : U32}:
  match v:
    case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
      {==}

# A step's answer, for the rules that leave no nested work: the answer of
# the specification, with Done carrying no work

def nlv.lift(s: Result<&2, &2, N.NlError, Unit>) -> Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>:
  match s:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{None{}}

def nlv.need_l(+ok: Bool, +e: N.NlError) -> {nlv.lift(Laws.nllaw.need(ok, e)) == P.nla.need(ok, e) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def nlv.then_l(+x: Result<&2, &2, N.NlError, Unit>, +y: Result<&2, &2, N.NlError, Unit>) -> {nlv.lift(Laws.nllaw.then(x, y)) == P.nla.then(nlv.lift(x), nlv.lift(y)) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  match x:
    case Fail{e}:
      {==}
    case Done{u}:
      {==}

def nlv.atmost_l(+max: Nat, +l: Nat, +t: Nat) -> {nlv.lift(Laws.nllaw.atmost(max, l, t)) == P.nla.atmost(max, l, t) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  match max:
    case 0n:
      {==}
    case 1n+m:
      nlv.need_l(Nat.is_le(l, 1n+m), N.NlTooLarge{t})

def nlv.ie(+s: Bool, +lg: Bool, +t: Nat) -> {nlv.lift(Laws.nllaw.then(Laws.nllaw.need(Bool.not(s), N.NlTooShort{t}), Laws.nllaw.need(Bool.not(lg), N.NlTooLarge{t}))) == P.nla.int.exact(s, lg, t) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  match s lg:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def nlv.int_l(+exact: Bool, +t: Nat, +l: Nat, +size: Nat) -> {nlv.lift(Laws.nllaw.int(exact, t, l, size)) == P.nla.int(exact, t, l, size) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  match exact:
    case True{}:
      nlv.ie(Nat.is_lt(l, size), Nat.is_lt(size, l), t)
    case False{}:
      nlv.need_l(Nat.is_le(size, l), N.NlTooShort{t})

def nlv.sl(+l: Nat, +m: Maybe<&2, U32>) -> {Bool.pick(Nat, Laws.nllaw.nul_at(m), Nat.sub(l, 1n), l) == P.nla.strlen.go(l, m) : Nat}:
  match m:
    case Some{b}:
      {==}
    case None{}:
      {==}

def nlv.en(+m: Maybe<&2, U32>) -> {Laws.nllaw.nul_at(m) == P.nla.ends_nul(m) : Bool}:
  match m:
    case Some{b}:
      {==}
    case None{}:
      {==}

# One attribute alone: the step for its rule, then the end of the list

def nlv.one(+p: N.NlOpts, +exact: Bool, +unknown: Bool, +nf: Bool, +depth: Nat, +set: List<&2, P.NlPolicy>, +pol: Nat, +rs: List<&2, P.NlRule>, +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}, +t: Nat, +nd: Bool, +nb: Bool, +pl: B.Octets, +m: Maybe<&2, P.NlRule>, +hr: {List.get(&2, P.NlRule, rs, t) == m : Maybe<&2, P.NlRule>}, +f: Nat) -> {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.step.kind(m, p, exact, unknown, nf, depth, t, nd, pl, B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, depth}, set, P.nla.push(w, [P.NlWork{depth, pol, Nil{}}]))) : Result<&2, &2, N.NlError, Unit>}:
  %Equal.sym(Maybe<&2, P.NlPolicy>, List.get(&2, P.NlPolicy, set, pol), Some{P.NlPolicy{rs}}, hs) : {Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.step.rule(P.nla.rule.at(_, t), P.NlCheck{p, exact, unknown, nf, depth}, depth, N.NlAttr{t, nd, nb, pl}), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, depth}, set, P.nla.push(w, [P.NlWork{depth, pol, Nil{}}]))) == Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.step.kind(m, p, exact, unknown, nf, depth, t, nd, pl, B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, depth}, set, P.nla.push(w, [P.NlWork{depth, pol, Nil{}}]))) : Result<&2, &2, N.NlError, Unit>}
  %Equal.sym(Maybe<&2, P.NlRule>, List.get(&2, P.NlRule, rs, t), m, hr) : {Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.step.rule(_, P.NlCheck{p, exact, unknown, nf, depth}, depth, N.NlAttr{t, nd, nb, pl}), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, depth}, set, P.nla.push(w, [P.NlWork{depth, pol, Nil{}}]))) == Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.step.kind(m, p, exact, unknown, nf, depth, t, nd, pl, B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, depth}, set, P.nla.push(w, [P.NlWork{depth, pol, Nil{}}]))) : Result<&2, &2, N.NlError, Unit>}
  {==}

# the end of the list: nothing left but the attribute's empty remainder
def nlv.bl(+s: Result<&2, &2, N.NlError, Unit>, +c: P.NlCheck, +set: List<&2, P.NlPolicy>, +pol: Nat, +depth: Nat, +f: Nat) -> {Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, nlv.lift(s), w => P.nla.validate.go(1n+f, c, set, P.nla.push(w, [P.NlWork{depth, pol, Nil{}}]))) == s : Result<&2, &2, N.NlError, Unit>}:
  match s:
    case Fail{e}:
      {==}
    case Done{u}:
      match u:
        case Unit{}:
          match f:
            case 0n:
              {==}
            case 1n+g:
              {==}

def nlv.fin(+p: N.NlOpts, +exact: Bool, +unknown: Bool, +nf: Bool, +depth: Nat, +set: List<&2, P.NlPolicy>, +pol: Nat, +rs: List<&2, P.NlRule>, +hs: {List.get(&2, P.NlPolicy, set, pol) == Some{P.NlPolicy{rs}} : Maybe<&2, P.NlPolicy>}, +t: Nat, +nd: Bool, +nb: Bool, +pl: B.Octets, +m: Maybe<&2, P.NlRule>, +hr: {List.get(&2, P.NlRule, rs, t) == m : Maybe<&2, P.NlRule>}, +f: Nat, +s: Result<&2, &2, N.NlError, Unit>, +hk: {nlv.lift(s) == P.nla.step.kind(m, p, exact, unknown, nf, depth, t, nd, pl, B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}) -> {P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]) == s : Result<&2, &2, N.NlError, Unit>}:
  %Equal.sym(Result<&2, &2, N.NlError, Unit>, P.nla.validate(P.NlCheck{p, exact, unknown, nf, depth}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]), Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.step.kind(m, p, exact, unknown, nf, depth, t, nd, pl, B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, depth}, set, P.nla.push(w, [P.NlWork{depth, pol, Nil{}}]))), nlv.one(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, m, hr, f)) : {_ == s : Result<&2, &2, N.NlError, Unit>}
  %hk : {Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, _, w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, depth}, set, P.nla.push(w, [P.NlWork{depth, pol, Nil{}}]))) == s : Result<&2, &2, N.NlError, Unit>}
  nlv.bl(s, P.NlCheck{p, exact, unknown, nf, depth}, set, pol, depth, f)

def Laws.validate_no_rule(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, None{}, hr, f, Laws.nllaw.need(Bool.not(unknown), N.NlUnknown{t}), nlv.need_l(Bool.not(unknown), N.NlUnknown{t}))

def Laws.validate_unspec(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, min, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlUnspec{min}}, hr, f, Laws.nllaw.need(Nat.is_le(min, B.Octets.len(pl)), N.NlTooShort{t}), nlv.need_l(Nat.is_le(min, B.Octets.len(pl)), N.NlTooShort{t}))

def Laws.validate_u8(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlU8{}}, hr, f, Laws.nllaw.int(exact, t, B.Octets.len(pl), 1n), nlv.int_l(exact, t, B.Octets.len(pl), 1n))

def Laws.validate_u16(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlU16{}}, hr, f, Laws.nllaw.int(exact, t, B.Octets.len(pl), 2n), nlv.int_l(exact, t, B.Octets.len(pl), 2n))

def Laws.validate_u32(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlU32{}}, hr, f, Laws.nllaw.int(exact, t, B.Octets.len(pl), 4n), nlv.int_l(exact, t, B.Octets.len(pl), 4n))

def Laws.validate_u64(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlU64{}}, hr, f, Laws.nllaw.int(exact, t, B.Octets.len(pl), 8n), nlv.int_l(exact, t, B.Octets.len(pl), 8n))

def nlv.str_k(+max: Nat, +pl: B.Octets, +t: Nat) -> {nlv.lift(Laws.nllaw.atmost(max, Laws.nllaw.strlen(pl), t)) == P.nla.atmost(max, P.nla.strlen.go(B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))), t) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  %nlv.sl(B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))) : {nlv.lift(Laws.nllaw.atmost(max, Laws.nllaw.strlen(pl), t)) == P.nla.atmost(max, _, t) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  nlv.atmost_l(max, Laws.nllaw.strlen(pl), t)

def Laws.validate_string(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, max, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlString{max}}, hr, f, Laws.nllaw.atmost(max, Laws.nllaw.strlen(pl), t), nlv.str_k(max, pl, t))

def nlv.nul_k(+max: Nat, +pl: B.Octets, +t: Nat) -> {nlv.lift(Laws.nllaw.then(Laws.nllaw.need(Laws.nllaw.ends_nul(pl), N.NlNoNul{t}), Laws.nllaw.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t))) == P.nla.then(P.nla.need(P.nla.ends_nul(B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))), N.NlNoNul{t}), P.nla.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t)) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  %nlv.en(B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))) : {nlv.lift(Laws.nllaw.then(Laws.nllaw.need(Laws.nllaw.ends_nul(pl), N.NlNoNul{t}), Laws.nllaw.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t))) == P.nla.then(P.nla.need(_, N.NlNoNul{t}), P.nla.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t)) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  %nlv.need_l(Laws.nllaw.ends_nul(pl), N.NlNoNul{t}) : {nlv.lift(Laws.nllaw.then(Laws.nllaw.need(Laws.nllaw.ends_nul(pl), N.NlNoNul{t}), Laws.nllaw.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t))) == P.nla.then(_, P.nla.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t)) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  %nlv.atmost_l(max, Nat.sub(B.Octets.len(pl), 1n), t) : {nlv.lift(Laws.nllaw.then(Laws.nllaw.need(Laws.nllaw.ends_nul(pl), N.NlNoNul{t}), Laws.nllaw.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t))) == P.nla.then(nlv.lift(Laws.nllaw.need(Laws.nllaw.ends_nul(pl), N.NlNoNul{t})), _) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  nlv.then_l(Laws.nllaw.need(Laws.nllaw.ends_nul(pl), N.NlNoNul{t}), Laws.nllaw.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t))

def Laws.validate_nul_string(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, max, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlNulString{max}}, hr, f, Laws.nllaw.then(Laws.nllaw.need(Laws.nllaw.ends_nul(pl), N.NlNoNul{t}), Laws.nllaw.atmost(max, Nat.sub(B.Octets.len(pl), 1n), t)), nlv.nul_k(max, pl, t))

def Laws.validate_flag(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlFlag{}}, hr, f, Laws.nllaw.need(Nat.is_eq(B.Octets.len(pl), 0n), N.NlNotFlag{t}), nlv.need_l(Nat.is_eq(B.Octets.len(pl), 0n), N.NlNotFlag{t}))

def nlv.bin_k(+min: Nat, +max: Nat, +l: Nat, +t: Nat) -> {nlv.lift(Laws.nllaw.then(Laws.nllaw.need(Nat.is_le(min, l), N.NlTooShort{t}), Laws.nllaw.atmost(max, l, t))) == P.nla.then(P.nla.need(Nat.is_le(min, l), N.NlTooShort{t}), P.nla.atmost(max, l, t)) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  %nlv.need_l(Nat.is_le(min, l), N.NlTooShort{t}) : {nlv.lift(Laws.nllaw.then(Laws.nllaw.need(Nat.is_le(min, l), N.NlTooShort{t}), Laws.nllaw.atmost(max, l, t))) == P.nla.then(_, P.nla.atmost(max, l, t)) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  %nlv.atmost_l(max, l, t) : {nlv.lift(Laws.nllaw.then(Laws.nllaw.need(Nat.is_le(min, l), N.NlTooShort{t}), Laws.nllaw.atmost(max, l, t))) == P.nla.then(nlv.lift(Laws.nllaw.need(Nat.is_le(min, l), N.NlTooShort{t})), _) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  nlv.then_l(Laws.nllaw.need(Nat.is_le(min, l), N.NlTooShort{t}), Laws.nllaw.atmost(max, l, t))

def Laws.validate_binary(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, min, max, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlBinary{min, max}}, hr, f, Laws.nllaw.then(Laws.nllaw.need(Nat.is_le(min, B.Octets.len(pl)), N.NlTooShort{t}), Laws.nllaw.atmost(max, B.Octets.len(pl), t)), nlv.bin_k(min, max, B.Octets.len(pl), t))

def Laws.validate_reject(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, hr, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlReject{}}, hr, f, Fail{N.NlUnknown{t}}, {==})

# Nested rules

def nlv.noflag_k(+nf: Bool, +nd: Bool, +hf: {Bool.or(Bool.not(nf), nd) == False{} : Bool}, +t: Nat, +p: N.NlOpts, +pl: B.Octets, +depth: Nat, +sub: Nat) -> {nlv.lift(Fail{N.NlNoNestedFlag{t}}) == P.nla.nested.flag(Bool.or(Bool.not(nf), nd), t, p, pl, depth, sub) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  %Equal.sym(Bool, Bool.or(Bool.not(nf), nd), False{}, hf) : {nlv.lift(Fail{N.NlNoNestedFlag{t}}) == P.nla.nested.flag(_, t, p, pl, depth, sub) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  {==}

def Laws.validate_nested_no_flag(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, sub, hr, hf, f):
  nlv.fin(p, exact, unknown, nf, depth, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlNested{sub}}, hr, f, Fail{N.NlNoNestedFlag{t}}, nlv.noflag_k(nf, nd, hf, t, p, pl, depth, sub))

def nlv.deep_k(+nf: Bool, +nd: Bool, +hf: {Bool.or(Bool.not(nf), nd) == True{} : Bool}, +t: Nat, +p: N.NlOpts, +pl: B.Octets, +sub: Nat) -> {nlv.lift(Fail{N.NlTooDeep{}}) == P.nla.nested.flag(Bool.or(Bool.not(nf), nd), t, p, pl, 0n, sub) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  %Equal.sym(Bool, Bool.or(Bool.not(nf), nd), True{}, hf) : {nlv.lift(Fail{N.NlTooDeep{}}) == P.nla.nested.flag(_, t, p, pl, 0n, sub) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  {==}

def Laws.validate_nested_too_deep(p, exact, unknown, nf, set, pol, rs, hs, t, nd, nb, pl, sub, hr, hf, f):
  nlv.fin(p, exact, unknown, nf, 0n, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlNested{sub}}, hr, f, Fail{N.NlTooDeep{}}, nlv.deep_k(nf, nd, hf, t, p, pl, sub))

def nlv.bad_k(+nf: Bool, +nd: Bool, +hf: {Bool.or(Bool.not(nf), nd) == True{} : Bool}, +t: Nat, +p: N.NlOpts, +pl: B.Octets, +d: Nat, +sub: Nat, +e: N.NlError, +hp: {N.nla.parse(p, pl) == Fail{e} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {nlv.lift(Fail{e}) == P.nla.nested.flag(Bool.or(Bool.not(nf), nd), t, p, pl, 1n+d, sub) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}:
  %Equal.sym(Bool, Bool.or(Bool.not(nf), nd), True{}, hf) : {nlv.lift(Fail{e}) == P.nla.nested.flag(_, t, p, pl, 1n+d, sub) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  %Equal.sym(Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, N.nla.parse(p, pl), Fail{e}, hp) : {nlv.lift(Fail{e}) == P.nla.nested.parsed(_, d, sub) : Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>}
  {==}

def Laws.validate_nested_bad(p, exact, unknown, nf, d, set, pol, rs, hs, t, nd, nb, pl, sub, hr, hf, e, hp, f):
  nlv.fin(p, exact, unknown, nf, 1n+d, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlNested{sub}}, hr, f, Fail{e}, nlv.bad_k(nf, nd, hf, t, p, pl, d, sub, e, hp))

# A nested payload validated within f steps: with one step more, the
# attribute's empty remainder after it is validated too. The check's depth
# field is not read by the steps (only by nla.validate, to start), so it
# may differ between the two.

def nlv.push_app(+m: Maybe<&2, P.NlWork>, +w: P.NlWork, +t: List<&2, P.NlWork>, +e: P.NlWork) -> {List.append(&2, P.NlWork, P.nla.push(m, Con{w, t}), [e]) == P.nla.push(m, Con{w, List.append(&2, P.NlWork, t, [e])}) : List<&2, P.NlWork>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def nlv.H(+r: Result<&2, &2, N.NlError, Maybe<&2, P.NlWork>>, +p: N.NlOpts, +exact: Bool, +unknown: Bool, +nf: Bool, +D: Nat, +D2: Nat, +set: List<&2, P.NlPolicy>, +g: Nat, +w: P.NlWork, +t: List<&2, P.NlWork>, +e0: P.NlWork, +u: Unit, +hh: {Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, r, m => P.nla.validate.go(g, P.NlCheck{p, exact, unknown, nf, D2}, set, P.nla.push(m, Con{w, t}))) == Done{u} : Result<&2, &2, N.NlError, Unit>}, ih: @m: Maybe<&2, P.NlWork> -> @hm: {P.nla.validate.go(g, P.NlCheck{p, exact, unknown, nf, D2}, set, P.nla.push(m, Con{w, t})) == Done{u} : Result<&2, &2, N.NlError, Unit>} -> {P.nla.validate.go(1n+g, P.NlCheck{p, exact, unknown, nf, D}, set, List.append(&2, P.NlWork, P.nla.push(m, Con{w, t}), [e0])) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}) -> {Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, r, m => P.nla.validate.go(1n+g, P.NlCheck{p, exact, unknown, nf, D}, set, P.nla.push(m, Con{w, List.append(&2, P.NlWork, t, [e0])}))) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}:
  match r:
    case Fail{e}:
      Empty.absurd({Fail{e} == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}, nlv.fd_absurd(e, u, hh))
    case Done{m}:
      %nlv.push_app(m, w, t, e0) : {P.nla.validate.go(1n+g, P.NlCheck{p, exact, unknown, nf, D}, set, _) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}
      ih(m, hh)

def nlv.L(+f: Nat, +ws: List<&2, P.NlWork>, +p: N.NlOpts, +exact: Bool, +unknown: Bool, +nf: Bool, +D: Nat, +D2: Nat, +set: List<&2, P.NlPolicy>, +d0: Nat, +q0: Nat, +u: Unit, +h: {P.nla.validate.go(f, P.NlCheck{p, exact, unknown, nf, D2}, set, ws) == Done{u} : Result<&2, &2, N.NlError, Unit>}) -> {P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, D}, set, List.append(&2, P.NlWork, ws, [P.NlWork{d0, q0, Nil{}}])) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}:
  match f:
    case 0n:
      match ws:
        case Nil{}:
          {==}
        case Con{w, t}:
          Empty.absurd({P.nla.validate.go(1n, P.NlCheck{p, exact, unknown, nf, D}, set, List.append(&2, P.NlWork, Con{w, t}, [P.NlWork{d0, q0, Nil{}}])) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}, nlv.fd_absurd(N.NlTooDeep{}, u, h))
    case 1n+g:
      match ws:
        case Nil{}:
          {==}
        case Con{w, t}:
          match w:
            case P.NlWork{+d, +q, as}:
              match as:
                case Nil{}:
                  nlv.L(g, t, p, exact, unknown, nf, D, D2, set, d0, q0, u, h)
                case Con{a, as2}:
                  match a:
                    case N.NlAttr{+ta, +nd, +nb, +pl}:
                      nlv.H(P.nla.step.kind(P.nla.rule(set, q, ta), p, exact, unknown, nf, d, ta, nd, pl, B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))), p, exact, unknown, nf, D, D2, set, g, P.NlWork{d, q, as2}, t, P.NlWork{d0, q0, Nil{}}, u, h, m => hm => nlv.L(g, P.nla.push(m, Con{P.NlWork{d, q, as2}, t}), p, exact, unknown, nf, D, D2, set, d0, q0, u, hm))

def Laws.validate_nested_valid(p, exact, unknown, nf, d, set, pol, rs, hs, t, nd, nb, pl, sub, hr, hf, as, hp, f, u, hv):
  %Equal.sym(Result<&2, &2, N.NlError, Unit>, P.nla.validate(P.NlCheck{p, exact, unknown, nf, 1n+d}, set, pol, 1n+1n+f, [N.NlAttr{t, nd, nb, pl}]), Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.step.kind(Some{P.NlNested{sub}}, p, exact, unknown, nf, 1n+d, t, nd, pl, B.Octets.len(pl), B.Octets.at(pl, Nat.sub(B.Octets.len(pl), 1n))), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, 1n+d}, set, P.nla.push(w, [P.NlWork{1n+d, pol, Nil{}}]))), nlv.one(p, exact, unknown, nf, 1n+d, set, pol, rs, hs, t, nd, nb, pl, Some{P.NlNested{sub}}, hr, f)) : {_ == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}
  %Equal.sym(Bool, Bool.or(Bool.not(nf), nd), True{}, hf) : {Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.nested.flag(_, t, p, pl, 1n+d, sub), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, 1n+d}, set, P.nla.push(w, [P.NlWork{1n+d, pol, Nil{}}]))) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}
  %Equal.sym(Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, N.nla.parse(p, pl), Done{as}, hp) : {Result.bind(&2, &2, N.NlError, Maybe<&2, P.NlWork>, Unit, P.nla.nested.parsed(_, d, sub), w => P.nla.validate.go(1n+f, P.NlCheck{p, exact, unknown, nf, 1n+d}, set, P.nla.push(w, [P.NlWork{1n+d, pol, Nil{}}]))) == Done{Unit{}} : Result<&2, &2, N.NlError, Unit>}
  nlv.L(f, [P.NlWork{d, sub, as}], p, exact, unknown, nf, 1n+d, d, set, 1n+d, pol, u, hv)

# The readers: bytes' round trips

def Laws.get_u8_round_trip(t, v):
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(B.Octets.of_list([v]), 0n), B.at(B.Octets.to_list(B.Octets.of_list([v])), 0n), BL.octets_at_list(B.Octets.of_list([v]), 0n)) : {_ == Some{B.byte(v)} : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([v])), B.mask([v]), BL.octets_to_of([v])) : {B.at(_, 0n) == Some{B.byte(v)} : Maybe<&2, U32>}
  %nlv.byte_idem(v) : {Some{_} == Some{B.byte(v)} : Maybe<&2, U32>}
  {==}

def Laws.get_u16_round_trip(o, t, v):
  match o:
    case H.NlLittle{}:
      BL.octets_le16_round_trip(v)
    case H.NlBig{}:
      BL.octets_be16_round_trip(v)

def Laws.get_u32_round_trip(o, t, v):
  match o:
    case H.NlLittle{}:
      BL.octets_le32_round_trip(v)
    case H.NlBig{}:
      BL.octets_be32_round_trip(v)

def Laws.get_u32_be_round_trip(o, t, v):
  match o:
    case H.NlLittle{}:
      BL.octets_be32_round_trip(v)
    case H.NlBig{}:
      BL.octets_be32_round_trip(v)

def Laws.get_u64_round_trip(o, t, v):
  match o:
    case H.NlLittle{}:
      BL.octets_le64_round_trip(v)
    case H.NlBig{}:
      BL.octets_be64_round_trip(v)

def Laws.find_head(a, as):
  %nlv.nrefl(N.nla.type(a)) : {N.nla.find.pick(_, a, N.nla.find(as, N.nla.type(a))) == Some{a} : Maybe<&2, N.NlAttr>}
  {==}

def Laws.find_skip(a, as, t, ne):
  %Equal.sym(Bool, Nat.is_eq(N.nla.type(a), t), False{}, ne) : {N.nla.find.pick(_, a, N.nla.find(as, t)) == N.nla.find(as, t) : Maybe<&2, N.NlAttr>}
  {==}

def Laws.find_nil(t):
  {==}

def Laws.validate_nested_example():
  {==}
