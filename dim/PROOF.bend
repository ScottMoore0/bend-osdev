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

# The inward direction right is a step within the table

def iw.right(multi: Bool, left: Bool, right: Bool, +n: Nat, +ix: Nat, +em: {Nat.is_lt(1n, n) == multi : Bool}, +el: {Nat.is_eq(ix, 0n) == left : Bool}, +e: {D.Dim.inward.go(multi, left, right) == Some{True{}} : Maybe<&2, Bool>}) -> {Nat.is_lt(1n+ix, n) == True{} : Bool}:
  match multi left right:
    case False{} left right:
      Empty.absurd({Nat.is_lt(1n+ix, n) == True{} : Bool}, ab.none_some(True{}, e))
    case True{} True{} right:
      %Equal.sym(Nat, ix, 0n, nat.eq_zero(ix, el)) : {Nat.is_lt(1n+_, n) == True{} : Bool}
      em
    case True{} False{} True{}:
      Empty.absurd({Nat.is_lt(1n+ix, n) == True{} : Bool}, ab.ft_some(e))
    case True{} False{} False{}:
      Empty.absurd({Nat.is_lt(1n+ix, n) == True{} : Bool}, ab.none_some(True{}, e))

# Family A: the index stays within a table of n profiles

def A.mv(can: Bool, right: Bool, +n: Nat, +ix: Nat, -r: D.DimRates, +ecan: {D.Dim.can(n, right, ix) == can : Bool}, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.move.go(can, right, ix, r))), n) == True{} : Bool}:
  match can right:
    case True{} True{}:
      ecan
    case True{} False{}:
      nat.lt_sub1(ix, n, h)
    case False{} right:
      h

def A.pr(d: Bool, +n: Nat, +ix: Nat, -r: D.DimRates, +ee: {D.Dim.inward(n, ix) == Some{d} : Maybe<&2, Bool>}, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.probe(d, ix, r))), n) == True{} : Bool}:
  match d:
    case True{}:
      iw.right(Nat.is_lt(1n, n), Nat.is_eq(ix, 0n), Nat.is_eq(1n+ix, n), n, ix, {==}, {==}, ee)
    case False{}:
      nat.lt_sub1(ix, n, h)

def A.tg(off: Bool, tired: Bool, d: Bool, +n: Nat, +t: Nat, +ix: Nat, -r: D.DimRates, +ee: {D.Dim.inward(n, ix) == Some{d} : Maybe<&2, Bool>}, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.tire.go(off, tired, d, t, ix, r))), n) == True{} : Bool}:
  match off tired:
    case True{} tired:
      h
    case False{} True{}:
      A.pr(d, n, ix, r, ee, h)
    case False{} False{}:
      h

def A.tire(edge: Maybe<&2, Bool>, +n: Nat, +lim: Nat, +t: Nat, +ix: Nat, -r: D.DimRates, +ee: {D.Dim.inward(n, ix) == edge : Maybe<&2, Bool>}, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.tire(edge, lim, t, ix, r))), n) == True{} : Bool}:
  match edge:
    case None{}:
      h
    case Some{+d}:
      A.tg(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, n, t, ix, r, ee, h)

def A.park(pr: Bool, -n: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide.park(pr, ix, r))), n) == True{} : Bool}:
  match pr:
    case True{}:
      h
    case False{}:
      h

def A.going(c: D.DimVerdict, +right: Bool, pr: Bool, +n: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide.going(c, right, pr, n, ix, r))), n) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      A.park(pr, n, ix, r, h)
    case D.DimBetter{}:
      A.mv(D.Dim.can(n, right, ix), right, n, ix, r, {==}, h)
    case D.DimWorse{}:
      A.mv(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), n, ix, r, {==}, h)

def A.parked(c: D.DimVerdict, +t: Nat, +n: Nat, +lim: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide.parked(c, t, n, lim, ix, r))), n) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      A.tire(D.Dim.inward(n, ix), n, lim, t, ix, r, {==}, h)
    case D.DimBetter{}:
      A.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), n, ix, r, {==}, h)
    case D.DimWorse{}:
      A.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), n, ix, r, {==}, h)

def A.settled(c: D.DimVerdict, +n: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide.settled(c, n, ix, r))), n) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      h
    case D.DimBetter{}:
      A.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), n, ix, r, {==}, h)
    case D.DimWorse{}:
      A.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), n, ix, r, {==}, h)

def A.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +ix: Nat, -r: D.DimRates, +h: {Nat.is_lt(ix, n) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.decide(m, c, n, lim, ix, r))), n) == True{} : Bool}:
  match m:
    case D.DimGoing{+right, +pr}:
      A.going(c, right, pr, n, ix, r, h)
    case D.DimParked{+t}:
      A.parked(c, t, n, lim, ix, r, h)
    case D.DimSettled{}:
      A.settled(c, n, ix, r, h)

def A.prev(pv: Maybe<&2, D.DimRates>, p: D.DimParams, +ix: Nat, +m: D.DimMode, +r: D.DimRates, +h: {Nat.is_lt(ix, List.length(&2, D.DimProfile, D.DimParams.profiles(p))) == True{} : Bool}) -> {Nat.is_lt(D.Dim.index(D.DimStep.state(D.Dim.step.prev(pv, p, ix, m, r))), List.length(&2, D.DimProfile, D.DimParams.profiles(p))) == True{} : Bool}:
  match pv:
    case None{}:
      h
    case Some{+q}:
      match p:
        case D.DimParams{+ps, +sx, +pct, +lim, +cs}:
          A.decide(m, D.Dim.compare.with(cs, pct, r, q), List.length(&2, D.DimProfile, ps), lim, ix, r, h)

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

def B.mv(can: Bool, right: Bool, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.move.go(can, right, ix, r)) == True{} : Bool}:
  match can right:
    case True{} True{}:
      ns.up(ix, D.DimGoing{True{}, False{}}, r)
    case True{} False{}:
      ns.down(ix, D.DimGoing{False{}, False{}}, r)
    case False{} right:
      ns.same(ix, D.DimParked{0n}, r)

def B.pr(d: Bool, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.probe(d, ix, r)) == True{} : Bool}:
  match d:
    case True{}:
      ns.up(ix, D.DimGoing{True{}, True{}}, r)
    case False{}:
      ns.down(ix, D.DimGoing{False{}, True{}}, r)

def B.tg(off: Bool, tired: Bool, d: Bool, +t: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.tire.go(off, tired, d, t, ix, r)) == True{} : Bool}:
  match off tired:
    case True{} tired:
      ns.same(ix, D.DimParked{t}, r)
    case False{} True{}:
      B.pr(d, ix, r)
    case False{} False{}:
      ns.same(ix, D.DimParked{1n+t}, r)

def B.tire(edge: Maybe<&2, Bool>, +lim: Nat, +t: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.tire(edge, lim, t, ix, r)) == True{} : Bool}:
  match edge:
    case None{}:
      ns.same(ix, D.DimParked{t}, r)
    case Some{+d}:
      B.tg(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, r)

def B.park(pr: Bool, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide.park(pr, ix, r)) == True{} : Bool}:
  match pr:
    case True{}:
      ns.same(ix, D.DimSettled{}, r)
    case False{}:
      ns.same(ix, D.DimParked{0n}, r)

def B.going(c: D.DimVerdict, +right: Bool, pr: Bool, +n: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide.going(c, right, pr, n, ix, r)) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      B.park(pr, ix, r)
    case D.DimBetter{}:
      B.mv(D.Dim.can(n, right, ix), right, ix, r)
    case D.DimWorse{}:
      B.mv(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), ix, r)

def B.parked(c: D.DimVerdict, +t: Nat, +n: Nat, +lim: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide.parked(c, t, n, lim, ix, r)) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      B.tire(D.Dim.inward(n, ix), lim, t, ix, r)
    case D.DimBetter{}:
      B.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), ix, r)
    case D.DimWorse{}:
      B.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), ix, r)

def B.settled(c: D.DimVerdict, +n: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide.settled(c, n, ix, r)) == True{} : Bool}:
  match c:
    case D.DimSame{}:
      ns.same(ix, D.DimSettled{}, r)
    case D.DimBetter{}:
      B.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), ix, r)
    case D.DimWorse{}:
      B.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), ix, r)

def B.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +ix: Nat, -r: D.DimRates) -> {dp.ns(ix, D.Dim.decide(m, c, n, lim, ix, r)) == True{} : Bool}:
  match m:
    case D.DimGoing{+right, +pr}:
      B.going(c, right, pr, n, ix, r)
    case D.DimParked{+t}:
      B.parked(c, t, n, lim, ix, r)
    case D.DimSettled{}:
      B.settled(c, n, ix, r)

def B.prev(pv: Maybe<&2, D.DimRates>, p: D.DimParams, +ix: Nat, +m: D.DimMode, +r: D.DimRates) -> {dp.ns(ix, D.Dim.step.prev(pv, p, ix, m, r)) == True{} : Bool}:
  match pv:
    case None{}:
      ns.same(ix, m, r)
    case Some{+q}:
      match p:
        case D.DimParams{+ps, +sx, +pct, +lim, +cs}:
          B.decide(m, D.Dim.compare.with(cs, pct, r, q), List.length(&2, D.DimProfile, ps), lim, ix, r)

def B.on(skip: Bool, +p: D.DimParams, +st: D.Dim, +s: D.DimSample) -> {dp.ns(D.Dim.index(st), D.Dim.step.on(skip, p, st, s)) == True{} : Bool}:
  match skip:
    case True{}:
      ns.core(D.Dim.index(st))
    case False{}:
      match st:
        case D.Dim{+ix, +m, +pv}:
          B.prev(pv, p, ix, m, D.Dim.rates(s))

# Family C: a step's state holds the sample's rates

def C.mv(can: Bool, right: Bool, -ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.move.go(can, right, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match can right:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} right:
      {==}

def C.pr(d: Bool, -ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.probe(d, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

def C.tg(off: Bool, tired: Bool, d: Bool, -t: Nat, -ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.tire.go(off, tired, d, t, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match off tired:
    case True{} tired:
      {==}
    case False{} True{}:
      C.pr(d, ix, r)
    case False{} False{}:
      {==}

def C.tire(edge: Maybe<&2, Bool>, +lim: Nat, +t: Nat, -ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.tire(edge, lim, t, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match edge:
    case None{}:
      {==}
    case Some{+d}:
      C.tg(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, r)

def C.park(pr: Bool, -ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide.park(pr, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match pr:
    case True{}:
      {==}
    case False{}:
      {==}

def C.going(c: D.DimVerdict, +right: Bool, pr: Bool, +n: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide.going(c, right, pr, n, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match c:
    case D.DimSame{}:
      C.park(pr, ix, r)
    case D.DimBetter{}:
      C.mv(D.Dim.can(n, right, ix), right, ix, r)
    case D.DimWorse{}:
      C.mv(D.Dim.can(n, Bool.not(right), ix), Bool.not(right), ix, r)

def C.parked(c: D.DimVerdict, +t: Nat, +n: Nat, +lim: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide.parked(c, t, n, lim, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match c:
    case D.DimSame{}:
      C.tire(D.Dim.inward(n, ix), lim, t, ix, r)
    case D.DimBetter{}:
      C.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), ix, r)
    case D.DimWorse{}:
      C.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), ix, r)

def C.settled(c: D.DimVerdict, +n: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide.settled(c, n, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match c:
    case D.DimSame{}:
      {==}
    case D.DimBetter{}:
      C.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), ix, r)
    case D.DimWorse{}:
      C.mv(D.Dim.can(n, Nat.is_eq(ix, 0n), ix), Nat.is_eq(ix, 0n), ix, r)

def C.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +ix: Nat, -r: D.DimRates) -> {D.Dim.prev(D.DimStep.state(D.Dim.decide(m, c, n, lim, ix, r))) == Some{r} : Maybe<&2, D.DimRates>}:
  match m:
    case D.DimGoing{+right, +pr}:
      C.going(c, right, pr, n, ix, r)
    case D.DimParked{+t}:
      C.parked(c, t, n, lim, ix, r)
    case D.DimSettled{}:
      C.settled(c, n, ix, r)

# Identical samples: one step with a sample of some time, from a state
# holding that sample's rates, decides on DimSame

def cv.step(+ix: Nat, +m: D.DimMode, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, m, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.decide(m, D.DimSame{}, List.length(&2, D.DimProfile, ps), lim, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}:
  %Equal.sym(Bool, U32.is_zero(el), False{}, nz) : {D.DimStep.state(D.Dim.step.on(_, D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, m, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.decide(m, D.DimSame{}, List.length(&2, D.DimProfile, ps), lim, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  %Equal.sym(D.DimVerdict, D.Dim.compare.with(cs, pct, D.Dim.rates(D.DimSample{pk, by, ev, co, el}), D.Dim.rates(D.DimSample{pk, by, ev, co, el})), D.DimSame{}, cmp.same(cs, pct, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : {D.DimStep.state(D.Dim.decide(m, _, List.length(&2, D.DimProfile, ps), lim, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.DimStep.state(D.Dim.decide(m, D.DimSame{}, List.length(&2, D.DimProfile, ps), lim, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  {==}

def cv.settled(+ix: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  cv.step(ix, D.DimSettled{}, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)

def cv.probe(+ix: Nat, +d: Bool, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  cv.step(ix, D.DimGoing{d, True{}}, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)

def cv.going(+ix: Nat, +d: Bool, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, False{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParked{0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  cv.step(ix, D.DimGoing{d, False{}}, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)

# a step of no time changes nothing

def cv.skip(+x: D.Dim, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +z: {U32.is_zero(el) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, x, D.DimSample{pk, by, ev, co, el})) == x : D.Dim}:
  %Equal.sym(Bool, U32.is_zero(el), True{}, z) : {D.DimStep.state(D.Dim.step.on(_, D.DimParams{ps, sx, pct, lim, cs}, x, D.DimSample{pk, by, ev, co, el})) == x : D.Dim}
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

def cv.at(+y: D.Dim, +x: D.Dim, +k: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +e: {D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})) == x : D.Dim}, +f: {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, x, D.DimSample{pk, by, ev, co, el})) == x : D.Dim}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  %Equal.sym(D.Dim, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})), x, e) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, _, D.DimSample{pk, by, ev, co, el})) == _ : D.Dim}
  f

# Parked on an edge with the same interval: count, then probe

def cv.parked_step(+ix: Nat, +t: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.tire(D.Dim.inward(List.length(&2, D.DimProfile, ps), ix), lim, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}:
  cv.step(ix, D.DimParked{t}, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)

def cv.probe_eq.right(+ix: Nat, +t: Nat, +j: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +e: {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{1n+ix, D.DimGoing{True{}, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}) -> {D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+j, D.DimSample{pk, by, ev, co, el})) == D.Dim{1n+ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{1n+ix, D.DimGoing{True{}, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, e) : {D.Dim.run.go(List.replicate(D.DimSample, 1n+j, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, cs}, _) == D.Dim{1n+ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{1n+ix, D.DimGoing{True{}, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{1n+ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.probe(1n+ix, True{}, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)) : {D.Dim.run.go(List.replicate(D.DimSample, j, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, cs}, _) == D.Dim{1n+ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  cv.rest(j, D.DimParams{ps, sx, pct, lim, cs}, D.Dim{1n+ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el}, cv.settled(1n+ix, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz))

def cv.probe_eq.left(+ix: Nat, +t: Nat, +j: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +e: {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}) -> {D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+j, D.DimSample{pk, by, ev, co, el})) == D.Dim{Nat.sub(ix, 1n), D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, e) : {D.Dim.run.go(List.replicate(D.DimSample, 1n+j, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, cs}, _) == D.Dim{Nat.sub(ix, 1n), D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{Nat.sub(ix, 1n), D.DimGoing{False{}, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{Nat.sub(ix, 1n), D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.probe(Nat.sub(ix, 1n), False{}, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)) : {D.Dim.run.go(List.replicate(D.DimSample, j, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, cs}, _) == D.Dim{Nat.sub(ix, 1n), D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  cv.rest(j, D.DimParams{ps, sx, pct, lim, cs}, D.Dim{Nat.sub(ix, 1n), D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el}, cv.settled(Nat.sub(ix, 1n), ps, sx, pct, lim, cs, pk, by, ev, co, el, nz))

def cv.probe_run(d: Bool, +ix: Nat, +t: Nat, +j: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +e: {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.probe(d, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+j, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+j, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match d:
    case True{}:
      cv.at(D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.Dim{1n+ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 2n+j, ps, sx, pct, lim, cs, pk, by, ev, co, el, cv.probe_eq.right(ix, t, j, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, e), cv.settled(1n+ix, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz))
    case False{}:
      cv.at(D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.Dim{Nat.sub(ix, 1n), D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 2n+j, ps, sx, pct, lim, cs, pk, by, ev, co, el, cv.probe_eq.left(ix, t, j, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, e), cv.settled(Nat.sub(ix, 1n), ps, sx, pct, lim, cs, pk, by, ev, co, el, nz))

# The step of a parked state, by the edge and the tired count

def cv.pk_none(+ix: Nat, +t: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +ee: {D.Dim.inward(List.length(&2, D.DimProfile, ps), ix) == None{} : Maybe<&2, Bool>}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.tire(D.Dim.inward(List.length(&2, D.DimProfile, ps), ix), lim, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), cv.parked_step(ix, t, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)) : {_ == D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(Maybe<&2, Bool>, D.Dim.inward(List.length(&2, D.DimProfile, ps), ix), None{}, ee) : {D.DimStep.state(D.Dim.tire(_, lim, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  {==}

def cv.pk_go(+ix: Nat, +t: Nat, +d: Bool, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +ee: {D.Dim.inward(List.length(&2, D.DimProfile, ps), ix) == Some{d} : Maybe<&2, Bool>}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.tire.go(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.tire(D.Dim.inward(List.length(&2, D.DimProfile, ps), ix), lim, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), cv.parked_step(ix, t, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)) : {_ == D.DimStep.state(D.Dim.tire.go(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  %Equal.sym(Maybe<&2, Bool>, D.Dim.inward(List.length(&2, D.DimProfile, ps), ix), Some{d}, ee) : {D.DimStep.state(D.Dim.tire(_, lim, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.DimStep.state(D.Dim.tire.go(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  {==}

def cv.pk_off(+ix: Nat, +t: Nat, +d: Bool, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +ee: {D.Dim.inward(List.length(&2, D.DimProfile, ps), ix) == Some{d} : Maybe<&2, Bool>}, +eo: {Nat.is_eq(lim, 0n) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.tire.go(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), cv.pk_go(ix, t, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, ee)) : {_ == D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(Bool, Nat.is_eq(lim, 0n), True{}, eo) : {D.DimStep.state(D.Dim.tire.go(_, Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  {==}

def cv.pk_probe(+ix: Nat, +t: Nat, +d: Bool, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +ee: {D.Dim.inward(List.length(&2, D.DimProfile, ps), ix) == Some{d} : Maybe<&2, Bool>}, +eo: {Nat.is_eq(lim, 0n) == False{} : Bool}, +et: {Nat.is_le(lim, 1n+t) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.DimStep.state(D.Dim.probe(d, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.tire.go(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), cv.pk_go(ix, t, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, ee)) : {_ == D.DimStep.state(D.Dim.probe(d, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  %Equal.sym(Bool, Nat.is_eq(lim, 0n), False{}, eo) : {D.DimStep.state(D.Dim.tire.go(_, Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.DimStep.state(D.Dim.probe(d, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  %Equal.sym(Bool, Nat.is_le(lim, 1n+t), True{}, et) : {D.DimStep.state(D.Dim.tire.go(False{}, _, d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.DimStep.state(D.Dim.probe(d, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) : D.Dim}
  {==}

def cv.pk_count(+ix: Nat, +t: Nat, +d: Bool, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +ee: {D.Dim.inward(List.length(&2, D.DimProfile, ps), ix) == Some{d} : Maybe<&2, Bool>}, +eo: {Nat.is_eq(lim, 0n) == False{} : Bool}, +et: {Nat.is_le(lim, 1n+t) == False{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.DimStep.state(D.Dim.tire.go(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))), cv.pk_go(ix, t, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, ee)) : {_ == D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(Bool, Nat.is_eq(lim, 0n), False{}, eo) : {D.DimStep.state(D.Dim.tire.go(_, Nat.is_le(lim, 1n+t), d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  %Equal.sym(Bool, Nat.is_le(lim, 1n+t), False{}, et) : {D.DimStep.state(D.Dim.tire.go(False{}, _, d, t, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))) == D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  {==}

def cv.fixed_run(+y: D.Dim, +k: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +f: {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, y, D.DimSample{pk, by, ev, co, el})) == y : D.Dim}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, y, List.replicate(D.DimSample, k, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  cv.at(y, y, k, ps, sx, pct, lim, cs, pk, by, ev, co, el, cv.rest(k, D.DimParams{ps, sx, pct, lim, cs}, y, D.DimSample{pk, by, ev, co, el}, f), f)

# the cases of a parked state, by the edge, whether probing is off, and
# whether the count is up; next: the rest of the count, when it is not

def cv.pc(edge: Maybe<&2, Bool>, off: Bool, tired: Bool, +ix: Nat, +t: Nat, +j: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +ee: {D.Dim.inward(List.length(&2, D.DimProfile, ps), ix) == edge : Maybe<&2, Bool>}, +eo: {Nat.is_eq(lim, 0n) == off : Bool}, +et: {Nat.is_le(lim, 1n+t) == tired : Bool}, next: {tired == False{} : Bool} -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+j, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n+j, D.DimSample{pk, by, ev, co, el})) : D.Dim}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+j, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+j, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match edge:
    case None{}:
      cv.fixed_run(D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 2n+j, ps, sx, pct, lim, cs, pk, by, ev, co, el, cv.pk_none(ix, t, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, ee))
    case Some{+d}:
      match off:
        case True{}:
          cv.fixed_run(D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 2n+j, ps, sx, pct, lim, cs, pk, by, ev, co, el, cv.pk_off(ix, t, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, ee, eo))
        case False{}:
          match tired:
            case True{}:
              cv.probe_run(d, ix, t, j, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, cv.pk_probe(ix, t, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, ee, eo, et))
            case False{}:
              %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.pk_count(ix, t, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, ee, eo, et)) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run.go(List.replicate(D.DimSample, 1n+j, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, cs}, _), D.DimSample{pk, by, ev, co, el})) == D.Dim.run.go(List.replicate(D.DimSample, 1n+j, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, cs}, _) : D.Dim}
              next({==})

def cv.h_next(+lim: Nat, +jp: Nat, +t: Nat, +h: {Nat.is_le(lim, 1n+Nat.add(jp, 1n+t)) == True{} : Bool}) -> {Nat.is_le(lim, Nat.add(jp, 2n+t)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(jp, 2n+t), 1n+Nat.add(jp, 1n+t), nat.add_succ(jp, 1n+t)) : {Nat.is_le(lim, _) == True{} : Bool}
  h

# parked: after 2 + j identical samples at rest, when lim <= j + 1 + t

def cv.parked(j: Nat, +t: Nat, +ix: Nat, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +h: {Nat.is_le(lim, Nat.add(j, 1n+t)) == True{} : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+j, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+j, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match j:
    case 0n:
      cv.pc(D.Dim.inward(List.length(&2, D.DimProfile, ps), ix), Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), ix, t, 0n, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, {==}, {==}, {==}, u => Empty.absurd({D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{1n+t}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 1n, D.DimSample{pk, by, ev, co, el})) : D.Dim}, ab.tf(Equal.trans(Bool, True{}, Nat.is_le(lim, 1n+t), False{}, Equal.sym(Bool, Nat.is_le(lim, 1n+t), True{}, h), u))))
    case 1n+ +jp:
      cv.pc(D.Dim.inward(List.length(&2, D.DimProfile, ps), ix), Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), ix, t, 1n+jp, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, {==}, {==}, {==}, u => cv.parked(jp, 1n+t, ix, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, cv.h_next(lim, jp, t, h)))

# from a state holding the sample's rates, 3 + lim samples bring it to rest

def cv.going_eq(+ix: Nat, +d: Bool, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, False{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+lim, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, False{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{ix, D.DimParked{0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.going(ix, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)) : {D.Dim.run.go(List.replicate(D.DimSample, 2n+lim, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, cs}, _) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+lim, D.DimSample{pk, by, ev, co, el})) : D.Dim}
  {==}

def cv.probe_eq2(+ix: Nat, +d: Bool, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})) == D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}:
  %Equal.sym(D.Dim, D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el})), D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, cv.probe(ix, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)) : {D.Dim.run.go(List.replicate(D.DimSample, 2n+lim, D.DimSample{pk, by, ev, co, el}), D.DimParams{ps, sx, pct, lim, cs}, _) == D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}} : D.Dim}
  cv.rest(2n+lim, D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.DimSample{pk, by, ev, co, el}, cv.settled(ix, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz))

def cv.primed(y: D.Dim, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}, +hp: {D.Dim.prev(y) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, y, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, y, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match y:
    case D.Dim{+ix, D.DimGoing{+d, True{}}, +pv}:
      %Equal.sym(Maybe<&2, D.DimRates>, pv, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}, hp) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, True{}}, _}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, True{}}, _}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})) : D.Dim}
      cv.at(D.Dim{ix, D.DimGoing{d, True{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 3n+lim, ps, sx, pct, lim, cs, pk, by, ev, co, el, cv.probe_eq2(ix, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz), cv.settled(ix, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz))
    case D.Dim{+ix, D.DimGoing{+d, False{}}, +pv}:
      %Equal.sym(Maybe<&2, D.DimRates>, pv, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}, hp) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, False{}}, _}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, False{}}, _}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})) : D.Dim}
      %Equal.sym(D.Dim, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimGoing{d, False{}}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})), D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{0n}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, List.replicate(D.DimSample, 2n+lim, D.DimSample{pk, by, ev, co, el})), cv.going_eq(ix, d, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, _, D.DimSample{pk, by, ev, co, el})) == _ : D.Dim}
      cv.parked(lim, 0n, ix, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, nat.le_add(lim, 1n))
    case D.Dim{+ix, D.DimParked{+t}, +pv}:
      %Equal.sym(Maybe<&2, D.DimRates>, pv, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}, hp) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, _}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimParked{t}, _}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})) : D.Dim}
      cv.parked(1n+lim, t, ix, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz, nat.le_succ(lim, Nat.add(lim, 1n+t), nat.le_add(lim, 1n+t)))
    case D.Dim{+ix, D.DimSettled{}, +pv}:
      %Equal.sym(Maybe<&2, D.DimRates>, pv, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}, hp) : {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimSettled{}, _}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, D.DimSettled{}, _}, List.replicate(D.DimSample, 3n+lim, D.DimSample{pk, by, ev, co, el})) : D.Dim}
      cv.fixed_run(D.Dim{ix, D.DimSettled{}, Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})}}, 3n+lim, ps, sx, pct, lim, cs, pk, by, ev, co, el, cv.settled(ix, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz))

# one step with a sample of some time leaves the state holding its rates

def cv.primes.prev(pv: Maybe<&2, D.DimRates>, +ix: Nat, +m: D.DimMode, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.Dim.prev(D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, m, pv}, D.DimSample{pk, by, ev, co, el}))) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}:
  match pv:
    case None{}:
      %Equal.sym(Bool, U32.is_zero(el), False{}, nz) : {D.Dim.prev(D.DimStep.state(D.Dim.step.on(_, D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, m, None{}}, D.DimSample{pk, by, ev, co, el}))) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}
      {==}
    case Some{+q}:
      %Equal.sym(Bool, U32.is_zero(el), False{}, nz) : {D.Dim.prev(D.DimStep.state(D.Dim.step.on(_, D.DimParams{ps, sx, pct, lim, cs}, D.Dim{ix, m, Some{q}}, D.DimSample{pk, by, ev, co, el}))) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}
      C.decide(m, D.Dim.compare.with(cs, pct, D.Dim.rates(D.DimSample{pk, by, ev, co, el}), q), List.length(&2, D.DimProfile, ps), lim, ix, D.Dim.rates(D.DimSample{pk, by, ev, co, el}))

def cv.primes(st: D.Dim, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +nz: {U32.is_zero(el) == False{} : Bool}) -> {D.Dim.prev(D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, st, D.DimSample{pk, by, ev, co, el}))) == Some{D.Dim.rates(D.DimSample{pk, by, ev, co, el})} : Maybe<&2, D.DimRates>}:
  match st:
    case D.Dim{+ix, +m, +pv}:
      cv.primes.prev(pv, ix, m, ps, sx, pct, lim, cs, pk, by, ev, co, el, nz)

def cv.settle(z: Bool, +st: D.Dim, +ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32, +ez: {U32.is_zero(el) == z : Bool}) -> {D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, st, List.replicate(D.DimSample, 4n+lim, D.DimSample{pk, by, ev, co, el})), D.DimSample{pk, by, ev, co, el})) == D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, st, List.replicate(D.DimSample, 4n+lim, D.DimSample{pk, by, ev, co, el})) : D.Dim}:
  match z:
    case True{}:
      cv.skip(D.Dim.run(D.DimParams{ps, sx, pct, lim, cs}, st, List.replicate(D.DimSample, 4n+lim, D.DimSample{pk, by, ev, co, el})), ps, sx, pct, lim, cs, pk, by, ev, co, el, ez)
    case False{}:
      cv.primed(D.DimStep.state(D.Dim.step(D.DimParams{ps, sx, pct, lim, cs}, st, D.DimSample{pk, by, ev, co, el})), ps, sx, pct, lim, cs, pk, by, ev, co, el, ez, cv.primes(st, ps, sx, pct, lim, cs, pk, by, ev, co, el, ez))

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

# Runs keep the index in the table

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
    case D.DimParams{+ps, +sx, pct, lim, cs}:
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
    case D.DimParams{ps, sx, +pct, lim, +cs}:
      cmp.same(cs, pct, D.Dim.rates(s))

def Laws.dim_settles(p, st, s):
  match p s:
    case D.DimParams{+ps, +sx, +pct, +lim, +cs} D.DimSample{+pk, +by, +ev, +co, +el}:
      cv.settle(U32.is_zero(el), st, ps, sx, pct, lim, cs, pk, by, ev, co, el, {==})

def Laws.dim_rest(p, x, s, n, f):
  cv.rest(n, p, x, s, f)

def Laws.dim_wit():
  {==}

def Laws.dim_vec_climb_index():
  {==}

def Laws.dim_vec_climb_mode():
  {==}

def Laws.dim_vec_probe_index():
  {==}

def Laws.dim_vec_probe_mode():
  {==}
