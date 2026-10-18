import Base
import ../word64/word64.bend as W
import ./dim.bend as D
import ./LAWS.bend as Laws

# Contradictions and Bool

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : ab.bool(_)
  Unit{}

def ab.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

def ab.some(m: Maybe<&2, Bool>) -> Type:
  match m:
    case Some{x}:
      Unit
    case None{}:
      Empty

def ab.none_some(-x: Bool, e: {None{} == Some{x} : Maybe<&2, Bool>}) -> Empty:
  %Equal.sym(Maybe<&2, Bool>, None{}, Some{x}, e) : ab.some(_)
  Unit{}

def ab.ft_some(e: {Some{False{}} == Some{True{}} : Maybe<&2, Bool>}) -> Empty:
  ab.ft(Equal.cong(Maybe<&2, Bool>, Bool, m => Maybe.default(&2, Bool, m, False{}), Some{False{}}, Some{True{}}, e))

def bo.and_l(x: Bool, -y: Bool, +e: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

def bo.and_r(x: Bool, -y: Bool, +e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == True{} : Bool}, ab.ft(e))

def bo.and_intro(-x: Bool, -y: Bool, +ex: {x == True{} : Bool}, +ey: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

def bo.or_still(a: Bool, -b: Bool, +e: {Bool.or(a, b) == True{} : Bool}, +u: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, ab.tf(u))
    case False{}:
      e

# Nat

def nat.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat.le_refl(p)

def nat.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat.eq_refl(p)

def nat.le_succ_self(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat.le_succ_self(p)

def nat.le_succ2(n: Nat) -> {Nat.is_le(n, 2n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat.le_succ2(p)

def nat.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.sub1_le(n: Nat) -> {Nat.is_le(Nat.sub(n, 1n), 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, nat.sub_zero(p)) : {Nat.is_le(_, 2n+p) == True{} : Bool}
      nat.le_succ2(p)

def nat.le_sub1(n: Nat) -> {Nat.is_le(n, 1n+Nat.sub(n, 1n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, nat.sub_zero(p)) : {Nat.is_le(1n+p, 1n+_) == True{} : Bool}
      nat.le_refl(p)

def nat.lt_le_trans(a: Nat, b: Nat, c: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}, +f: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n c:
      f
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.ft(f))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 0n c:
      Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool}, ab.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, ab.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nat.lt_le_trans(ap, bp, cp, e, f)

def nat.sub1_le_self(n: Nat) -> {Nat.is_le(Nat.sub(n, 1n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, nat.sub_zero(p)) : {Nat.is_le(_, 1n+p) == True{} : Bool}
      nat.le_succ_self(p)

def nat.lt_sub1(+ix: Nat, +n: Nat, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(ix, 1n), n) == True{} : Bool}:
  nat.lt_le_trans(Nat.sub(ix, 1n), ix, n, nat.sub1_le_self(ix), h)

def nat.eq_zero(n: Nat, +e: {Nat.is_eq(n, 0n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, ab.ft(e))

def nat.eq_of(a: Nat, b: Nat, +e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, ab.ft(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, ab.ft(e))
    case 1n+ +ap 1n+bp:
      %nat.eq_of(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

def nat.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.le_add(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      nat.le_zero(b)
    case 1n+p:
      nat.le_add(p, b)

def nat.le_succ(a: Nat, b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, ab.ft(e))
    case 1n+ap 1n+bp:
      nat.le_succ(ap, bp, e)

def nat.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), nat.add_succ(p, b)) : {1n+_ == 2n+Nat.add(p, b) : Nat}
      {==}

# U32: a word equals itself (Base's word order, bit by bit)

def wd.fin_refl(x: Bool) -> {Word.cmp.fin(x, x, EQ{}) == EQ{} : Cmp}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def wd.refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case WCon{+x, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, wd.refl(p, at)) : {Word.cmp.fin(x, x, _) == EQ{} : Cmp}
          wd.fin_refl(x)

def u.refl(a: U32) -> {U32.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case U32{+w}:
      wd.refl(32n, w)

def u.eq_refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, u.refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# An interval compares the same as itself

def rate.refl(+a: W.W64) -> {D.Dim.same_rate(a, a) == True{} : Bool}:
  bo.and_intro(U32.is_eq(W.W64.hi(a), W.W64.hi(a)), U32.is_eq(W.W64.lo(a), W.W64.lo(a)), u.eq_refl(W.W64.hi(a)), u.eq_refl(W.W64.lo(a)))

def cmp.same(cs: List<&2, D.DimCriterion>, +pct: U32, +a: D.DimRates) -> {D.Dim.compare.with(cs, pct, a, a) == D.DimSame{} : D.DimVerdict}:
  match cs:
    case Nil{}:
      {==}
    case Con{D.DimCriterion{+m, +hb}, +rest}:
      %Equal.sym(Bool, D.Dim.same_rate(D.Dim.metric(m, a), D.Dim.metric(m, a)), True{}, rate.refl(D.Dim.metric(m, a))) : {D.Dim.verdict(Con{D.DimCmp{D.Dim.compare.rate.go(_, pct, D.Dim.metric(m, a), D.Dim.metric(m, a)), hb}, D.Dim.compare.all(rest, pct, a, a)}) == D.DimSame{} : D.DimVerdict}
      cmp.same(rest, pct, a)

# More Nat

def nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nat.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def nat.le_add_r(a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      nat.le_refl(b)
    case 1n+ +p:
      nat.le_succ(b, Nat.add(p, b), nat.le_add_r(p, b))

def nat.lt0_false(n: Nat, +e: {Nat.is_lt(0n, n) == False{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, ab.tf(e))

def nat.pos_of(ix: Nat, +n: Nat, +hl: {Nat.is_lt(1n, n) == True{} : Bool}, +e: {Nat.is_lt(1n+ix, n) == False{} : Bool}) -> {Nat.is_lt(0n, ix) == True{} : Bool}:
  match ix:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.tf(Equal.trans(Bool, True{}, Nat.is_lt(1n, n), False{}, Equal.sym(Bool, Nat.is_lt(1n, n), True{}, hl), e)))
    case 1n+p:
      {==}

def nat.two_le(m: Nat, +h: {Nat.is_le(2n, m) == True{} : Bool}) -> {Nat.is_le(m, 1n) == False{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({Nat.is_le(0n, 1n) == False{} : Bool}, ab.ft(h))
    case 1n+q:
      match q:
        case 0n:
          Empty.absurd({Nat.is_le(1n, 1n) == False{} : Bool}, ab.ft(h))
        case 1n+u:
          {==}

# Family A: the index stays within a table of n profiles

def A.land(t: Bool, -right: Bool, -n: Nat, +ix: Nat, -rs: Nat, -ls: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.land(t, right, ix, rs, ls, r))), n) == True{} : Bool}:
  match t:
    case True{}:
      h
    case False{}:
      h

def A.wg(can: Bool, right: Bool, +rs: Nat, +ls: Nat, +mx: Nat, +n: Nat, +ix: Nat, -r: D.DimRates, +ecan: {D.Dim.can(n, right, ix) == can : Bool}, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.walk.go(can, right, rs, ls, mx, ix, r))), n) == True{} : Bool}:
  match can right:
    case True{} True{}:
      A.land(Nat.is_le(mx, 1n+rs), True{}, n, 1n+ix, 1n+rs, ls, r, ecan)
    case True{} False{}:
      A.land(Nat.is_le(mx, 1n+ls), False{}, n, Nat.sub(ix, 1n), rs, 1n+ls, r, nat.lt_sub1(ix, n, h))
    case False{} right:
      h

def A.going(c: D.DimVerdict, +right: Bool, +rs: Nat, +ls: Nat, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide.going(c, right, rs, ls, n, mx, ix, r))), n) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      h
    case D.DimBetter{}:
      A.wg(D.Dim.can(n, right, ix), right, rs, ls, mx, n, ix, r, {==}, h)
    case D.DimWorse{}:
      A.wg(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), rs, ls, mx, n, ix, r, {==}, h)

def A.top(c: D.DimVerdict, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide.top(c, n, mx, ix, r))), n) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      h
    case D.DimBetter{}:
      A.wg(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), 0n, 0n, mx, n, ix, r, {==}, h)
    case D.DimWorse{}:
      A.wg(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), 0n, 0n, mx, n, ix, r, {==}, h)

def A.tired(o: Bool, +right: Bool, -k: Nat, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide.tired(o, right, k, n, mx, ix, r))), n) == True{} : Bool}:
  match o:
    case True{}:
      A.wg(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), 0n, 0n, mx, n, ix, r, {==}, h)
    case False{}:
      h

def A.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide(m, c, n, lim, mx, ix, r))), n) == True{} : Bool}:
  match m:
    case D.DimGoing{+right, +rs, +ls}:
      A.going(c, right, rs, ls, n, mx, ix, r, h)
    case D.DimParkedTop{}:
      A.top(c, n, mx, ix, r, h)
    case D.DimParkedTired{+right, +k}:
      A.tired(Nat.is_le(lim, k), right, k, n, mx, ix, r, h)

def A.prev(pv: Maybe<&2, D.DimRates>, p: D.DimParams, +ix: Nat, +m: D.DimMode, +r: D.DimRates, +h: {Nat.is_lt(ix, List.length(&2, D.DimProfile, D.DimParams.profiles(p))) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.step.prev(pv, p, ix, m, r))), List.length(&2, D.DimProfile, D.DimParams.profiles(p))) == True{} : Bool}:
  match pv:
    case None{}:
      h
    case Some{+q}:
      match p:
        case D.DimParams{+ps, +sx, +pct, +lim, +mx, +cs}:
          A.decide(m, D.Dim.compare.with(cs, pct, r, q), List.length(&2, D.DimProfile, ps), lim, mx, ix, r, h)

def A.on(skip: Bool, +p: D.DimParams, st: D.Dim, +s: D.DimSample, +h: {D.Dim.valid(p, st) == True{} : Bool}) -> {D.Dim.valid(p, D.DimStep.state(D.Dim.step.on(skip, p, st, s))) == True{} : Bool}:
  match skip:
    case True{}:
      h
    case False{}:
      match st:
        case D.Dim{+ix, +m, +pv}:
          A.prev(pv, p, ix, m, D.Dim.rates(s), h)

# Family B: at most one step, and a step that says no change keeps the index

def dp.ns(+ix: Nat, +r: D.DimStep) -> Bool:
  Bool.and(Bool.and(Nat.is_le(D.Dim.index(D.DimStep.state(r)), 1n+ix), Nat.is_le(ix, 1n+D.Dim.index(D.DimStep.state(r)))), Bool.or(D.DimStep.changed(r), Nat.is_eq(D.Dim.index(D.DimStep.state(r)), ix)))

def ns.core(+i: Nat) -> {Bool.and(Bool.and(Nat.is_le(i, 1n+i), Nat.is_le(i, 1n+i)), Bool.or(False{}, Nat.is_eq(i, i))) == True{} : Bool}:
  bo.and_intro(Bool.and(Nat.is_le(i, 1n+i), Nat.is_le(i, 1n+i)), Bool.or(False{}, Nat.is_eq(i, i)), bo.and_intro(Nat.is_le(i, 1n+i), Nat.is_le(i, 1n+i), nat.le_succ_self(i), nat.le_succ_self(i)), nat.eq_refl(i))

def ns.same(+ix: Nat, -m: D.DimMode, -r: D.DimRates) -> {dp.ns(ix, D.Dim.mk(ix, m, r, False{})) == True{} : Bool}:
  ns.core(ix)

def ns.up(+ix: Nat, -m: D.DimMode, -r: D.DimRates) -> {dp.ns(ix, D.Dim.mk(1n+ix, m, r, True{})) == True{} : Bool}:
  bo.and_intro(Bool.and(Nat.is_le(1n+ix, 1n+ix), Nat.is_le(ix, 2n+ix)), Bool.or(True{}, Nat.is_eq(1n+ix, ix)), bo.and_intro(Nat.is_le(1n+ix, 1n+ix), Nat.is_le(ix, 2n+ix), nat.le_refl(1n+ix), nat.le_succ2(ix)), {==})

def ns.down(+ix: Nat, -m: D.DimMode, -r: D.DimRates) -> {dp.ns(ix, D.Dim.mk(Nat.sub(ix, 1n), m, r, True{})) == True{} : Bool}:
  bo.and_intro(Bool.and(Nat.is_le(Nat.sub(ix, 1n), 1n+ix), Nat.is_le(ix, 1n+Nat.sub(ix, 1n))), Bool.or(True{}, Nat.is_eq(Nat.sub(ix, 1n), ix)), bo.and_intro(Nat.is_le(Nat.sub(ix, 1n), 1n+ix), Nat.is_le(ix, 1n+Nat.sub(ix, 1n)), nat.sub1_le(ix), nat.le_sub1(ix)), {==})

def B.land_up(t: Bool, +right: Bool, +ix: Nat, +rs: Nat, +ls: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.land(t, right, 1n+ix, rs, ls, r)) == True{} : Bool}:
  match t:
    case True{}:
      ns.up(ix, D.DimParkedTired{right, 0n}, r)
    case False{}:
      ns.up(ix, D.DimGoing{right, rs, ls}, r)

def B.land_down(t: Bool, +right: Bool, +ix: Nat, +rs: Nat, +ls: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.land(t, right, Nat.sub(ix, 1n), rs, ls, r)) == True{} : Bool}:
  match t:
    case True{}:
      ns.down(ix, D.DimParkedTired{right, 0n}, r)
    case False{}:
      ns.down(ix, D.DimGoing{right, rs, ls}, r)

def B.wg(can: Bool, right: Bool, +rs: Nat, +ls: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.walk.go(can, right, rs, ls, mx, ix, r)) == True{} : Bool}:
  match can right:
    case True{} True{}:
      B.land_up(Nat.is_le(mx, 1n+rs), True{}, ix, 1n+rs, ls, r)
    case True{} False{}:
      B.land_down(Nat.is_le(mx, 1n+ls), False{}, ix, rs, 1n+ls, r)
    case False{} +right:
      ns.same(ix, D.DimParkedTired{right, 0n}, r)

def B.going(c: D.DimVerdict, +right: Bool, +rs: Nat, +ls: Nat, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide.going(c, right, rs, ls, n, mx, ix, r)) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      ns.same(ix, D.DimParkedTop{}, r)
    case D.DimBetter{}:
      B.wg(D.Dim.can(n, right, ix), right, rs, ls, mx, ix, r)
    case D.DimWorse{}:
      B.wg(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), rs, ls, mx, ix, r)

def B.top(c: D.DimVerdict, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide.top(c, n, mx, ix, r)) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      ns.same(ix, D.DimParkedTop{}, r)
    case D.DimBetter{}:
      B.wg(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), 0n, 0n, mx, ix, r)
    case D.DimWorse{}:
      B.wg(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), 0n, 0n, mx, ix, r)

def B.tired(o: Bool, +right: Bool, +k: Nat, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide.tired(o, right, k, n, mx, ix, r)) == True{} : Bool}:
  match o:
    case True{}:
      B.wg(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), 0n, 0n, mx, ix, r)
    case False{}:
      ns.same(ix, D.DimParkedTired{right, 1n+k}, r)

def B.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide(m, c, n, lim, mx, ix, r)) == True{} : Bool}:
  match m:
    case D.DimGoing{+right, +rs, +ls}:
      B.going(c, right, rs, ls, n, mx, ix, r)
    case D.DimParkedTop{}:
      B.top(c, n, mx, ix, r)
    case D.DimParkedTired{+right, +k}:
      B.tired(Nat.is_le(lim, k), right, k, n, mx, ix, r)

def B.prev(pv: Maybe<&2, D.DimRates>, p: D.DimParams, +ix: Nat, +m: D.DimMode, +r: D.DimRates) -> {dp.ns(ix, D.Dim.step.prev(pv, p, ix, m, r)) == True{} : Bool}:
  match pv:
    case None{}:
      ns.same(ix, m, r)
    case Some{+q}:
      match p:
        case D.DimParams{+ps, +sx, +pct, +lim, +mx, +cs}:
          B.decide(m, D.Dim.compare.with(cs, pct, r, q), List.length(&2, D.DimProfile, ps), lim, mx, ix, r)

def B.on(skip: Bool, +p: D.DimParams, +st: D.Dim, +s: D.DimSample) -> {dp.ns(D.Dim.index(st), D.Dim.step.on(skip, p, st, s)) == True{} : Bool}:
  match skip:
    case True{}:
      ns.core(D.Dim.index(st))
    case False{}:
      match st:
        case D.Dim{+ix, +m, +pv}:
          B.prev(pv, p, ix, m, D.Dim.rates(s))

# Family C: a step's state holds the sample's rates

def C.land(t: Bool, -right: Bool, -ix: Nat, -rs: Nat, -ls: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.land(t, right, ix, rs, ls, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match t:
    case True{}:
      {==}
    case False{}:
      {==}

def C.wg(can: Bool, right: Bool, +rs: Nat, +ls: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.walk.go(can, right, rs, ls, mx, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match can right:
    case True{} True{}:
      C.land(Nat.is_le(mx, 1n+rs), True{}, 1n+ix, 1n+rs, ls, r)
    case True{} False{}:
      C.land(Nat.is_le(mx, 1n+ls), False{}, Nat.sub(ix, 1n), rs, 1n+ls, r)
    case False{} right:
      {==}

def C.going(c: D.DimVerdict, +right: Bool, +rs: Nat, +ls: Nat, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide.going(c, right, rs, ls, n, mx, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match c:
    case D.DimSame{}:
      {==}
    case D.DimBetter{}:
      C.wg(D.Dim.can(n, right, ix), right, rs, ls, mx, ix, r)
    case D.DimWorse{}:
      C.wg(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), rs, ls, mx, ix, r)

def C.top(c: D.DimVerdict, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide.top(c, n, mx, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match c:
    case D.DimSame{}:
      {==}
    case D.DimBetter{}:
      C.wg(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), 0n, 0n, mx, ix, r)
    case D.DimWorse{}:
      C.wg(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), 0n, 0n, mx, ix, r)

def C.tired(o: Bool, +right: Bool, -k: Nat, +n: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide.tired(o, right, k, n, mx, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match o:
    case True{}:
      C.wg(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), 0n, 0n, mx, ix, r)
    case False{}:
      {==}

def C.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +mx: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide(m, c, n, lim, mx, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match m:
    case D.DimGoing{+right, +rs, +ls}:
      C.going(c, right, rs, ls, n, mx, ix, r)
    case D.DimParkedTop{}:
      C.top(c, n, mx, ix, r)
    case D.DimParkedTired{+right, +k}:
      C.tired(Nat.is_le(lim, k), right, k, n, mx, ix, r)

# Identical samples: one step with a sample of some time, from a state
# holding that sample's rates, decides on DimSame

def cv.step(+ix: Nat, +m: D.DimMode, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, m, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.decide(m, D.DimSame{}, List.length(&2, D.DimProfile, ps), lim, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}:
  %Equal.sym(Bool, U32.is_zero(el), False{}, nz) : {D.DimStep.state(D.Dim.step.on(_, D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, m, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.decide(m, D.DimSame{}, List.length(&2, D.DimProfile, ps), lim, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  %Equal.sym(D.DimVerdict, D.Dim.compare.with(cs, pct, D.Dim.rates(D.DimSample{pk, by, ev, co, el}), D.Dim.rates(D.DimSample{pk, by, ev, co, el})), D.DimSame{}, cmp.same(cs, pct, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : {D.DimStep.state(D.Dim.decide(m, _, List.length(&2, D.DimProfile, ps), lim, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.DimStep.state(D.Dim.decide(m, D.DimSame{}, List.length(&2, D.DimProfile, ps), lim, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  {==}

def cv.top(+ix: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  cv.step(ix, D.DimParkedTop{}, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz)

def cv.going(+ix: Nat, +d: Bool, +rs: Nat, +ls: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimGoing{d, rs, ls}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  cv.step(ix, D.DimGoing{d, rs, ls}, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz)

# a step of no time changes nothing

def cv.skip(+x: D.Dim, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +z: {U32.is_zero(el) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, x, D.DimSample{pk, by, ev, co, el})) == x : D.Dim}:
  %Equal.sym(Bool, U32.is_zero(el), True{}, z) : {D.DimStep.state(D.Dim.step.on(_, D.DimParams{ps, sx, pct, lim, mx, cs}, x, D.DimSample{pk, by, ev, co, el})) == x : D.Dim}
  {==}

# a fixed point stays

def cv.rest(n: Nat, +p: D.DimParams, +x: D.Dim, +s: D.DimSample, +f: {D.DimStep.state(D.Dim.step(p, x, s)) == x : D.Dim}) -> {D.Dim.run(p, x, List.replicate(D.DimSample, n, s)) == x : D.Dim}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(p, x, s)), x, f) : {D.Dim.run.go(List.replicate(D.DimSample, k, s), p, _) == x : D.Dim}
      cv.rest(k, p, x, s, f)

# rewriting a run that reaches a fixed point x, in both places of the goal

def cv.at(+y: D.Dim, +x: D.Dim, +k: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +e: {D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})) == x : D.Dim}, +f: {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, x, D.DimSample{pk, by, ev, co, el})) == x : D.Dim}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  %Equal.sym(D.Dim, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})), x, e) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, _, D.DimSample{pk, by, ev, co, el})) == _ : D.Dim}
  f

def cv.fixed_run(+y: D.Dim, +k: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +f: {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, y, D.DimSample{pk, by, ev, co, el})) == y : D.Dim}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  cv.at(y, y, k, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, cv.rest(k, D.DimParams{ps, sx, pct, lim, mx, cs}, y, D.DimSample{pk, by, ev, co, el}, f), f)

# Parked tired with the same interval: count, or verify

def cv.tired_count(+ix: Nat, +p: Bool, +k: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +eo: {Nat.is_le(lim, k) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.decide(D.DimParkedTired{p, k}, D.DimSame{}, List.length(&2, D.DimProfile, ps), lim, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), cv.step(ix, D.DimParkedTired{p, k}, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz)) : {_ == D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(Bool, Nat.is_le(lim, k), False{}, eo) : {D.DimStep.state(D.Dim.decide.tired(_, p, k, List.length(&2, D.DimProfile, ps), mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  {==}

def cv.tired_out(+ix: Nat, +p: Bool, +k: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +eo: {Nat.is_le(lim, k) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.walk(List.length(&2, D.DimProfile, ps), mx, Bool.not(p), 0n, 0n, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.decide(D.DimParkedTired{p, k}, D.DimSame{}, List.length(&2, D.DimProfile, ps), lim, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), cv.step(ix, D.DimParkedTired{p, k}, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz)) : {_ == D.DimStep.state(D.Dim.walk(List.length(&2, D.DimProfile, ps), mx, Bool.not(p), 0n, 0n, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  %Equal.sym(Bool, Nat.is_le(lim, k), True{}, eo) : {D.DimStep.state(D.Dim.decide.tired(_, p, k, List.length(&2, D.DimProfile, ps), mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.DimStep.state(D.Dim.walk(List.length(&2, D.DimProfile, ps), mx, Bool.not(p), 0n, 0n, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  {==}

# the verifying step, when it can be taken: one step, not too tired

def cv.walk_left(+ix: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +ec: {Nat.is_lt(0n, ix) == True{} : Bool}) -> {D.DimStep.state(D.Dim.walk(List.length(&2, D.DimProfile, ps), mx, False{}, 0n, 0n, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, 0n, 1n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(Bool, Nat.is_lt(0n, ix), True{}, ec) : {D.DimStep.state(D.Dim.walk.go(_, False{}, 0n, 0n, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, 0n, 1n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(Bool, Nat.is_le(mx, 1n), False{}, nat.two_le(mx, hm)) : {D.DimStep.state(D.Dim.land(_, False{}, Nat.sub(ix, 1n), 0n, 1n, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, 0n, 1n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  {==}

def cv.walk_right(+ix: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +ec: {Nat.is_lt(1n+ix, List.length(&2, D.DimProfile, ps)) == True{} : Bool}) -> {D.DimStep.state(D.Dim.walk(List.length(&2, D.DimProfile, ps), mx, True{}, 0n, 0n, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{1n+ix, D.DimGoing{True{}, 1n, 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(Bool, Nat.is_lt(1n+ix, List.length(&2, D.DimProfile, ps)), True{}, ec) : {D.DimStep.state(D.Dim.walk.go(_, True{}, 0n, 0n, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{1n+ix, D.DimGoing{True{}, 1n, 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(Bool, Nat.is_le(mx, 1n), False{}, nat.two_le(mx, hm)) : {D.DimStep.state(D.Dim.land(_, True{}, 1n+ix, 1n, 0n, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{1n+ix, D.DimGoing{True{}, 1n, 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  {==}

def cv.exit_t(+ix: Nat, +k: Nat, +e2: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +eo: {Nat.is_le(lim, k) == True{} : Bool}, +ec: {Nat.is_lt(0n, ix) == True{} : Bool}) -> {D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{True{}, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+e2, D.DimSample{pk, by, ev, co, el})) == D.Dim{Nat.sub(ix, 1n), D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{True{}, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, 0n, 1n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, Equal.trans(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{True{}, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.walk(List.length(&2, D.DimProfile, ps), mx, False{}, 0n, 0n, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, 0n, 1n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.tired_out(ix, True{}, k, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, eo), cv.walk_left(ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, hm, ec))) : {D.Dim.run.go(List.replicate(D.DimSample, 1n+e2, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _) == D.Dim{Nat.sub(ix, 1n), D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, 0n, 1n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{Nat.sub(ix, 1n), D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.going(Nat.sub(ix, 1n), False{}, 0n, 1n, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz)) : {D.Dim.run.go(List.replicate(D.DimSample, e2, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _) == D.Dim{Nat.sub(ix, 1n), D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  cv.rest(e2, D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{Nat.sub(ix, 1n), D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el}, cv.top(Nat.sub(ix, 1n), ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz))

def cv.exit_f(+ix: Nat, +k: Nat, +e2: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +eo: {Nat.is_le(lim, k) == True{} : Bool}, +ec: {Nat.is_lt(1n+ix, List.length(&2, D.DimProfile, ps)) == True{} : Bool}) -> {D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{False{}, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+e2, D.DimSample{pk, by, ev, co, el})) == D.Dim{1n+ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{False{}, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{1n+ix, D.DimGoing{True{}, 1n, 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, Equal.trans(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{False{}, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.walk(List.length(&2, D.DimProfile, ps), mx, True{}, 0n, 0n, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), D.Dim{1n+ix, D.DimGoing{True{}, 1n, 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.tired_out(ix, False{}, k, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, eo), cv.walk_right(ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, hm, ec))) : {D.Dim.run.go(List.replicate(D.DimSample, 1n+e2, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _) == D.Dim{1n+ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{1n+ix, D.DimGoing{True{}, 1n, 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{1n+ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.going(1n+ix, True{}, 1n, 0n, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz)) : {D.Dim.run.go(List.replicate(D.DimSample, e2, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _) == D.Dim{1n+ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  cv.rest(e2, D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{1n+ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el}, cv.top(1n+ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz))

def cv.exit(p: Bool, +k: Nat, +ix: Nat, +e2: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +eo: {Nat.is_le(lim, k) == True{} : Bool}, +ecan: {D.Dim.can(List.length(&2, D.DimProfile, ps), Bool.not(p), ix) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+e2, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+e2, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match p:
    case True{}:
      cv.at(D.Dim{ix, D.DimParkedTired{True{}, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.Dim{Nat.sub(ix, 1n), D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 2n+e2, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, cv.exit_t(ix, k, e2, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, eo, ecan), cv.top(Nat.sub(ix, 1n), ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz))
    case False{}:
      cv.at(D.Dim{ix, D.DimParkedTired{False{}, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.Dim{1n+ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 2n+e2, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, cv.exit_f(ix, k, e2, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, eo, ecan), cv.top(1n+ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz))

# the step the other way can be taken, when this way cannot (two profiles
# or more)

def cv.flip(p: Bool, +ix: Nat, +n: Nat, +hl: {Nat.is_lt(1n, n) == True{} : Bool}, +ec: {D.Dim.can(n, Bool.not(p), ix) == False{} : Bool}) -> {D.Dim.can(n, Bool.not(Bool.not(p)), ix) == True{} : Bool}:
  match p:
    case True{}:
      %Equal.sym(Nat, ix, 0n, nat.lt0_false(ix, ec)) : {Nat.is_lt(1n+_, n) == True{} : Bool}
      hl
    case False{}:
      nat.pos_of(ix, n, hl, ec)

def cv.h_next(+lim: Nat, +jp: Nat, +t: Nat, +h: {Nat.is_le(lim, 1n+Nat.add(jp, t)) == True{} : Bool}) -> {Nat.is_le(lim, Nat.add(jp, 1n+t)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(jp, 1n+t), 1n+Nat.add(jp, t), nat.add_succ(jp, t)) : {Nat.is_le(lim, _) == True{} : Bool}
  h

def cv.h2(+e: Nat, +lim: Nat) -> {Nat.is_le(lim, Nat.add(Nat.add(e, lim), 0n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(e, lim), 0n), Nat.add(e, lim), nat.add_zero(Nat.add(e, lim))) : {Nat.is_le(lim, _) == True{} : Bool}
  nat.le_add_r(e, lim)

# second phase: parked tired where the verifying step can be taken; at
# rest after 2 + e samples, when lim <= e + k

def cv.p2c(o: Bool, +k: Nat, +p: Bool, +ix: Nat, +e: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +eo: {Nat.is_le(lim, k) == o : Bool}, +ecan: {D.Dim.can(List.length(&2, D.DimProfile, ps), Bool.not(p), ix) == True{} : Bool}, next: {o == False{} : Bool} -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+e, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+e, D.DimSample{pk, by, ev, co, el})) : D.Dim}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+e, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+e, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match o:
    case True{}:
      cv.exit(p, k, ix, e, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, eo, ecan)
    case False{}:
      %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.tired_count(ix, p, k, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, eo)) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run.go(List.replicate(D.DimSample, 1n+e, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _), D.DimSample{pk, by, ev, co, el})) == D.Dim.run.go(List.replicate(D.DimSample, 1n+e, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _) : D.Dim}
      next({==})

def cv.p2(e: Nat, +k: Nat, +p: Bool, +ix: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +ecan: {D.Dim.can(List.length(&2, D.DimProfile, ps), Bool.not(p), ix) == True{} : Bool}, +h: {Nat.is_le(lim, Nat.add(e, k)) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+e, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+e, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match e:
    case 0n:
      cv.p2c(Nat.is_le(lim, k), k, p, ix, 0n, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, {==}, ecan, u => Empty.absurd({D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n, D.DimSample{pk, by, ev, co, el})) : D.Dim}, ab.tf(Equal.trans(Bool, True{}, Nat.is_le(lim, k), False{}, Equal.sym(Bool, Nat.is_le(lim, k), True{}, h), u))))
    case 1n+ +ep:
      cv.p2c(Nat.is_le(lim, k), k, p, ix, 1n+ep, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, {==}, ecan, u => cv.p2(ep, 1n+k, p, ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, ecan, cv.h_next(lim, ep, k, h)))

# first phase: parked tired anywhere; if the verifying step cannot be
# taken, it parks tired the other way and the second phase follows

def cv.p1y_step(+ix: Nat, +p: Bool, +k: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +eo: {Nat.is_le(lim, k) == True{} : Bool}, +ecn: {D.Dim.can(List.length(&2, D.DimProfile, ps), Bool.not(p), ix) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParkedTired{Bool.not(p), 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.walk(List.length(&2, D.DimProfile, ps), mx, Bool.not(p), 0n, 0n, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), cv.tired_out(ix, p, k, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, eo)) : {_ == D.Dim{ix, D.DimParkedTired{Bool.not(p), 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(Bool, D.Dim.can(List.length(&2, D.DimProfile, ps), Bool.not(p), ix), False{}, ecn) : {D.DimStep.state(D.Dim.walk.go(_, Bool.not(p), 0n, 0n, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{ix, D.DimParkedTired{Bool.not(p), 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  {==}

def cv.p1y(+p: Bool, +k: Nat, +ix: Nat, +e: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +hl: {Nat.is_lt(1n, List.length(&2, D.DimProfile, ps)) == True{} : Bool}, +eo: {Nat.is_le(lim, k) == True{} : Bool}, +ecn: {D.Dim.can(List.length(&2, D.DimProfile, ps), Bool.not(p), ix) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{ix, D.DimParkedTired{Bool.not(p), 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.p1y_step(ix, p, k, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, eo, ecn)) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run.go(List.replicate(D.DimSample, 1n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _), D.DimSample{pk, by, ev, co, el})) == D.Dim.run.go(List.replicate(D.DimSample, 1n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _) : D.Dim}
  %Equal.sym(Nat, Nat.add(e, 1n+lim), 1n+Nat.add(e, lim), nat.add_succ(e, lim)) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{Bool.not(p), 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+_, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{Bool.not(p), 0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+_, D.DimSample{pk, by, ev, co, el})) : D.Dim}
  cv.p2(Nat.add(e, lim), 0n, Bool.not(p), ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, cv.flip(p, ix, List.length(&2, D.DimProfile, ps), hl, ecn), cv.h2(e, lim))

def cv.p1x(cn: Bool, +k: Nat, +p: Bool, +ix: Nat, +e: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +hl: {Nat.is_lt(1n, List.length(&2, D.DimProfile, ps)) == True{} : Bool}, +eo: {Nat.is_le(lim, k) == True{} : Bool}, +ecn: {D.Dim.can(List.length(&2, D.DimProfile, ps), Bool.not(p), ix) == cn : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match cn:
    case True{}:
      cv.exit(p, k, ix, Nat.add(e, 1n+lim), ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, eo, ecn)
    case False{}:
      cv.p1y(p, k, ix, e, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, hl, eo, ecn)

def cv.p1c(o: Bool, +k: Nat, +p: Bool, +ix: Nat, +e: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +hl: {Nat.is_lt(1n, List.length(&2, D.DimProfile, ps)) == True{} : Bool}, +eo: {Nat.is_le(lim, k) == o : Bool}, next: {o == False{} : Bool} -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match o:
    case True{}:
      cv.p1x(D.Dim.can(List.length(&2, D.DimProfile, ps), Bool.not(p), ix), k, p, ix, e, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, hl, eo, {==})
    case False{}:
      %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.tired_count(ix, p, k, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, eo)) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run.go(List.replicate(D.DimSample, 1n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _), D.DimSample{pk, by, ev, co, el})) == D.Dim.run.go(List.replicate(D.DimSample, 1n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _) : D.Dim}
      next({==})

def cv.p1(e: Nat, +k: Nat, +p: Bool, +ix: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +hl: {Nat.is_lt(1n, List.length(&2, D.DimProfile, ps)) == True{} : Bool}, +h: {Nat.is_le(lim, Nat.add(e, k)) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(e, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match e:
    case 0n:
      cv.p1c(Nat.is_le(lim, k), k, p, ix, 0n, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, hl, {==}, u => Empty.absurd({D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+Nat.add(0n, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, 1n+k}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+Nat.add(0n, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}, ab.tf(Equal.trans(Bool, True{}, Nat.is_le(lim, k), False{}, Equal.sym(Bool, Nat.is_le(lim, k), True{}, h), u))))
    case 1n+ +ep:
      cv.p1c(Nat.is_le(lim, k), k, p, ix, 1n+ep, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, hl, {==}, u => cv.p1(ep, 1n+k, p, ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, hl, cv.h_next(lim, ep, k, h)))

# from a state holding the sample's rates, 2 + lim + (1 + lim) samples
# bring it to rest

def cv.going_eq(+ix: Nat, +d: Bool, +rs: Nat, +ls: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimGoing{d, rs, ls}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimGoing{d, rs, ls}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.going(ix, d, rs, ls, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz)) : {D.Dim.run.go(List.replicate(D.DimSample, 1n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, mx, cs}, _) == D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  cv.rest(1n+Nat.add(lim, 1n+lim), D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el}, cv.top(ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz))

def cv.primed(y: D.Dim, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +hl: {Nat.is_lt(1n, List.length(&2, D.DimProfile, ps)) == True{} : Bool}, +hp: {D.Dim.prev(y) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, y, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, y, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match y:
    case D.Dim{+ix, D.DimGoing{+d, +rs, +ls}, +pv}:
      %Equal.sym(Maybe<&2, D.DimRates>, pv, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}, hp) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimGoing{d, rs, ls}, _}, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimGoing{d, rs, ls}, _}, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}
      cv.at(D.Dim{ix, D.DimGoing{d, rs, ls}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 2n+Nat.add(lim, 1n+lim), ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, cv.going_eq(ix, d, rs, ls, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz), cv.top(ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz))
    case D.Dim{+ix, D.DimParkedTop{}, +pv}:
      %Equal.sym(Maybe<&2, D.DimRates>, pv, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}, hp) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTop{}, _}, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTop{}, _}, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}
      cv.fixed_run(D.Dim{ix, D.DimParkedTop{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 2n+Nat.add(lim, 1n+lim), ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, cv.top(ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz))
    case D.Dim{+ix, D.DimParkedTired{+p, +k}, +pv}:
      %Equal.sym(Maybe<&2, D.DimRates>, pv, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}, hp) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, _}, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, D.DimParkedTired{p, k}, _}, List.replicate(D.DimSample, 2n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}
      cv.p1(lim, k, p, ix, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz, hm, hl, nat.le_add(lim, k))

# one step with a sample of some time leaves the state holding its rates

def cv.primes.prev(pv: Maybe<&2, D.DimRates>, +ix: Nat, +m: D.DimMode, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.Dim.prev(D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, m, pv}, D.DimSample{pk, by, ev, co, el}))) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}:
  match pv:
    case None{}:
      %Equal.sym(Bool, U32.is_zero(el), False{}, nz) : {D.Dim.prev(D.DimStep.state(D.Dim.step.on(_, D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, m, None{}}, D.DimSample{pk, by, ev, co, el}))) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}
      {==}
    case Some{+q}:
      %Equal.sym(Bool, U32.is_zero(el), False{}, nz) : {D.Dim.prev(D.DimStep.state(D.Dim.step.on(_, D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim{ix, m, Some{q}}, D.DimSample{pk, by, ev, co, el}))) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}
      C.decide(m, D.Dim.compare.with(cs, pct, D.Dim.rates(D.DimSample{pk, by, ev, co, el}), q), List.length(&2, D.DimProfile, ps), lim, mx, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))

def cv.primes(st: D.Dim, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.Dim.prev(D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, st, D.DimSample{pk, by, ev, co, el}))) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}:
  match st:
    case D.Dim{+ix, +m, +pv}:
      cv.primes.prev(pv, ix, m, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, nz)

def cv.settle(z: Bool, +st: D.Dim, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +mx: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +hm: {Nat.is_le(2n, mx) == True{} : Bool}, +hl: {Nat.is_lt(1n, List.length(&2, D.DimProfile, ps)) == True{} : Bool}, +ez: {U32.is_zero(el) == z : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, st, List.replicate(D.DimSample, 3n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, st, List.replicate(D.DimSample, 3n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match z:
    case True{}:
      cv.skip(D.Dim.run(D.DimParams{ps, sx, pct, lim, mx, cs}, st, List.replicate(D.DimSample, 3n+Nat.add(lim, 1n+lim), D.DimSample{pk, by, ev, co, el})), ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, ez)
    case False{}:
      cv.primed(D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, mx, cs}, st, D.DimSample{pk, by, ev, co, el})), ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, ez, hm, hl, cv.primes(st, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, ez))

# Runs keep the index in the table

def bo.lt_zero(i: Nat, +h: {Nat.is_lt(i, 0n) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match i:
    case 0n:
      h
    case 1n+k:
      h

def new.valid(inside: Bool, +sx: Nat, +ps: List<&2, D.DimProfile>, +e: {Nat.is_lt(sx, List.length(&2, D.DimProfile, ps)) == inside : Bool}, +h: {Nat.is_lt(0n, List.length(&2, D.DimProfile, ps)) == True{} : Bool}) -> {Nat.is_lt(D.Dim.new.at(inside, sx), List.length(&2, D.DimProfile, ps)) == True{} : Bool}:
  match inside:
    case True{}:
      e
    case False{}:
      h

def run.valid(ss: List<&2, D.DimSample>, +p: D.DimParams, +st: D.Dim, +v: {D.Dim.valid(p, st) == True{} : Bool}) -> {D.Dim.valid(p, D.Dim.run.go(ss, p, st)) == True{} : Bool}:
  match ss:
    case Nil{}:
      v
    case Con{+s, +rest}:
      run.valid(rest, p, D.DimStep.state(D.Dim.step(p, st, s)), A.on(U32.is_zero(D.DimSample.elapsed(s)), p, st, s, v))

def get.some(xs: List<&2, D.DimProfile>, i: Nat, +h: {Nat.is_lt(i, List.length(&2, D.DimProfile, xs)) == True{} : Bool}) -> {Maybe.is_some(&2, D.DimProfile, List.get(&2, D.DimProfile, xs, i)) == True{} : Bool}:
  match xs i:
    case Nil{} i:
      Empty.absurd({Maybe.is_some(&2, D.DimProfile, List.get(&2, D.DimProfile, Nil{}, i)) == True{} : Bool}, ab.ft(bo.lt_zero(i, h)))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+k:
      get.some(t, k, h)

# The laws

def Laws.dim_new_valid(p, h):
  match p:
    case D.DimParams{+ps, +sx, pct, lim, mx, cs}:
      new.valid(Nat.is_lt(sx, List.length(&2, D.DimProfile, ps)), sx, ps, {==}, h)

def Laws.dim_step_valid(p, st, s, v):
  A.on(U32.is_zero(D.DimSample.elapsed(s)), p, st, s, v)

def Laws.dim_run_valid(p, st, ss, v):
  run.valid(ss, p, st, v)

def Laws.dim_profile_some(p, st, v):
  get.some(D.DimParams.profiles(p), D.Dim.index(st), v)

def Laws.dim_step_by_one(p, st, s):
  bo.and_l(Bool.and(Nat.is_le(D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))), 1n+D.Dim.index(st)), Nat.is_le(D.Dim.index(st), 1n+D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))))), Bool.or(D.DimStep.changed(D.Dim.step(p, st, s)), Nat.is_eq(D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))), D.Dim.index(st))), B.on(U32.is_zero(D.DimSample.elapsed(s)), p, st, s))

def Laws.dim_unchanged(p, st, s, u):
  nat.eq_of(D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))), D.Dim.index(st), bo.or_still(D.DimStep.changed(D.Dim.step(p, st, s)), Nat.is_eq(D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))), D.Dim.index(st)), bo.and_r(Bool.and(Nat.is_le(D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))), 1n+D.Dim.index(st)), Nat.is_le(D.Dim.index(st), 1n+D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))))), Bool.or(D.DimStep.changed(D.Dim.step(p, st, s)), Nat.is_eq(D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))), D.Dim.index(st))), B.on(U32.is_zero(D.DimSample.elapsed(s)), p, st, s)), u))

def Laws.dim_same_rates(p, s):
  match p:
    case D.DimParams{ps, sx, +pct, lim, mx, +cs}:
      cmp.same(cs, pct, D.Dim.rates(s))

def Laws.dim_settles(p, st, s, hl, hm):
  match p s:
    case D.DimParams{+ps, +sx, +pct, +lim, +mx, +cs} D.DimSample{+pk, +by, +ev, +co, +el}:
      cv.settle(U32.is_zero(el), st, ps, sx, pct, lim, mx, cs, pk, by, ev, co, el, hm, hl, {==})

def Laws.dim_rest(p, x, s, n, f):
  cv.rest(n, p, x, s, f)

def Laws.dim_wit():
  {==}

def Laws.dim_vec_climb_index():
  {==}

def Laws.dim_vec_climb_mode():
  {==}

def Laws.dim_vec_edge_index():
  {==}

def Laws.dim_vec_edge_mode():
  {==}

def Laws.dim_vec_interval():
  {==}
