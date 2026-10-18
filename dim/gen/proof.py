#!/usr/bin/env python3
"""Generates dim/PROOF.bend. Its lemmas follow every branch of a step three
times (the index stays in the table; it moves by at most one, and only when
the step says so; the previous rates are the sample's), and the convergence
proof follows identical samples through the parking and tired states; the
statements repeat long terms, which the shorthands below build.

Run from anywhere: python3 gen/proof.py rewrites ../PROOF.bend; with
--check it only reports whether the file is up to date (exit 1 if not).
"""
import os, sys
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "PROOF.bend")

def tt(x): return "{%s == True{} : Bool}" % x
def ff(x): return "{%s == False{} : Bool}" % x
def eqb(a, b): return "{%s == %s : Bool}" % (a, b)
def eqd(a, b): return "{%s == %s : D.Dim}" % (a, b)
LE = lambda a, b: "Nat.is_le(%s, %s)" % (a, b)
LTN = lambda a, b: "Nat.is_lt(%s, %s)" % (a, b)
EQN = lambda a, b: "Nat.is_eq(%s, %s)" % (a, b)
AND = lambda a, b: "Bool.and(%s, %s)" % (a, b)
OR = lambda a, b: "Bool.or(%s, %s)" % (a, b)
RAT = "D.DimRates"
MB = "Maybe<&2, D.DimRates>"
def MK(ix, m, r, ch): return "D.Dim.mk(%s, %s, %s, %s)" % (ix, m, r, ch)
def CAN(n, right, ix): return "D.Dim.can(%s, %s, %s)" % (n, right, ix)
def MOVEGO(can, right, ix, r): return "D.Dim.move.go(%s, %s, %s, %s)" % (can, right, ix, r)
def PROBE(d, ix, r): return "D.Dim.probe(%s, %s, %s)" % (d, ix, r)
def INWARD(n, ix): return "D.Dim.inward(%s, %s)" % (n, ix)
def TIREGO(off, tired, d, t, ix, r): return "D.Dim.tire.go(%s, %s, %s, %s, %s, %s)" % (off, tired, d, t, ix, r)
def TIRE(e, lim, t, ix, r): return "D.Dim.tire(%s, %s, %s, %s, %s)" % (e, lim, t, ix, r)
def PARK(pr, ix, r): return "D.Dim.decide.park(%s, %s, %s)" % (pr, ix, r)
def GOING(c, right, pr, n, ix, r): return "D.Dim.decide.going(%s, %s, %s, %s, %s, %s)" % (c, right, pr, n, ix, r)
def PARKED(c, t, n, lim, ix, r): return "D.Dim.decide.parked(%s, %s, %s, %s, %s, %s)" % (c, t, n, lim, ix, r)
def SETTLED(c, n, ix, r): return "D.Dim.decide.settled(%s, %s, %s, %s)" % (c, n, ix, r)
def DECIDE(m, c, n, lim, ix, r): return "D.Dim.decide(%s, %s, %s, %s, %s, %s)" % (m, c, n, lim, ix, r)
def PREV(pv, p, ix, m, r): return "D.Dim.step.prev(%s, %s, %s, %s, %s)" % (pv, p, ix, m, r)
def ON(sk, p, st, s): return "D.Dim.step.on(%s, %s, %s, %s)" % (sk, p, st, s)
def ST(x): return "D.DimStep.state(%s)" % x
def CH(x): return "D.DimStep.changed(%s)" % x
def IX(x): return "D.Dim.index(%s)" % x
def PRV(x): return "D.Dim.prev(%s)" % x
def LEN(ps): return "List.length(&2, D.DimProfile, %s)" % ps
def CMPW(cs, pct, a, b): return "D.Dim.compare.with(%s, %s, %s, %s)" % (cs, pct, a, b)
EQ0 = "Nat.is_eq(ix, 0n)"
NR = "Bool.not(right)"

# Family A: the index stays in a table of n profiles
def A(res): return tt(LTN(IX(ST(res)), "n"))
HA = "+h: " + tt(LTN("ix", "n"))
# Family B: at most one step, and none unless the step says so
def B(res): return tt("dp.ns(ix, %s)" % res)
# Family C: the new state holds the sample's rates
def C(res): return "{%s == Some{r} : %s}" % (PRV(ST(res)), MB)

# the default record and sample, matched
SIG = "+ps: List<&2, D.DimProfile>, +sx: Nat, +pct: U32, +lim: Nat, +cs: List<&2, D.DimCriterion>, +pk: U32, +by: U32, +ev: U32, +co: U32, +el: U32"
ARGS = "ps, sx, pct, lim, cs, pk, by, ev, co, el"
P = "D.DimParams{ps, sx, pct, lim, cs}"
S = "D.DimSample{pk, by, ev, co, el}"
R = "D.Dim.rates(%s)" % S
N = LEN("ps")
NZ = "+nz: " + ff("U32.is_zero(el)")
def STEP(y): return ST("D.Dim.step(%s, %s, %s)" % (P, y, S))
def REP(k): return "List.replicate(D.DimSample, %s, %s)" % (k, S)
def RUN(y, k): return "D.Dim.run(%s, %s, %s)" % (P, y, REP(k))
def RUNGO(k, y): return "D.Dim.run.go(%s, %s, %s)" % (REP(k), P, y)
def FIX(x): return eqd(STEP(x), x)
def PK(t, ix="ix"): return "D.Dim{%s, D.DimParked{%s}, Some{%s}}" % (ix, t, R)
def SE(ix="ix"): return "D.Dim{%s, D.DimSettled{}, Some{%s}}" % (ix, R)
def GOY(d, pr, ix="ix"): return "D.Dim{%s, D.DimGoing{%s, %s}, Some{%s}}" % (ix, d, pr, R)

text = f'''import Base
import ../word64/word64.bend as W
import ./dim.bend as D
import ./LAWS.bend as Laws

# Contradictions and Bool

def ab.bool(b: Bool) -> Type:
  match b:
    case True{{}}:
      Unit
    case False{{}}:
      Empty

def ab.tf(e: {{True{{}} == False{{}} : Bool}}) -> Empty:
  %e : ab.bool(_)
  Unit{{}}

def ab.ft(e: {{False{{}} == True{{}} : Bool}}) -> Empty:
  %Equal.sym(Bool, False{{}}, True{{}}, e) : ab.bool(_)
  Unit{{}}

def ab.some(m: Maybe<&2, Bool>) -> Type:
  match m:
    case Some{{x}}:
      Unit
    case None{{}}:
      Empty

def ab.none_some(-x: Bool, e: {{None{{}} == Some{{x}} : Maybe<&2, Bool>}}) -> Empty:
  %Equal.sym(Maybe<&2, Bool>, None{{}}, Some{{x}}, e) : ab.some(_)
  Unit{{}}

def ab.ft_some(e: {{Some{{False{{}}}} == Some{{True{{}}}} : Maybe<&2, Bool>}}) -> Empty:
  ab.ft(Equal.cong(Maybe<&2, Bool>, Bool, m => Maybe.default(&2, Bool, m, False{{}}), Some{{False{{}}}}, Some{{True{{}}}}, e))

def bo.and_l(x: Bool, -y: Bool, +e: {tt(AND("x", "y"))}) -> {tt("x")}:
  match x:
    case True{{}}:
      {{==}}
    case False{{}}:
      Empty.absurd({tt("False{}")}, ab.ft(e))

def bo.and_r(x: Bool, -y: Bool, +e: {tt(AND("x", "y"))}) -> {tt("y")}:
  match x:
    case True{{}}:
      e
    case False{{}}:
      Empty.absurd({tt("y")}, ab.ft(e))

def bo.and_intro(-x: Bool, -y: Bool, +ex: {tt("x")}, +ey: {tt("y")}) -> {tt(AND("x", "y"))}:
  %Equal.sym(Bool, x, True{{}}, ex) : {tt(AND("_", "y"))}
  ey

def bo.or_still(a: Bool, -b: Bool, +e: {tt(OR("a", "b"))}, +u: {ff("a")}) -> {tt("b")}:
  match a:
    case True{{}}:
      Empty.absurd({tt("b")}, ab.tf(u))
    case False{{}}:
      e

# Nat

def nat.le_refl(n: Nat) -> {tt(LE("n", "n"))}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      nat.le_refl(p)

def nat.eq_refl(n: Nat) -> {tt(EQN("n", "n"))}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      nat.eq_refl(p)

def nat.le_succ_self(n: Nat) -> {tt(LE("n", "1n+n"))}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      nat.le_succ_self(p)

def nat.le_succ2(n: Nat) -> {tt(LE("n", "2n+n"))}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      nat.le_succ2(p)

def nat.sub_zero(n: Nat) -> {{Nat.sub(n, 0n) == n : Nat}}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      {{==}}

def nat.sub1_le(n: Nat) -> {tt(LE("Nat.sub(n, 1n)", "1n+n"))}:
  match n:
    case 0n:
      {{==}}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, nat.sub_zero(p)) : {tt(LE("_", "2n+p"))}
      nat.le_succ2(p)

def nat.le_sub1(n: Nat) -> {tt(LE("n", "1n+Nat.sub(n, 1n)"))}:
  match n:
    case 0n:
      {{==}}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, nat.sub_zero(p)) : {tt(LE("1n+p", "1n+_"))}
      nat.le_refl(p)

def nat.lt_le_trans(a: Nat, b: Nat, c: Nat, +e: {tt(LE("a", "b"))}, +f: {tt(LTN("b", "c"))}) -> {tt(LTN("a", "c"))}:
  match a b c:
    case 0n 0n c:
      f
    case 0n 1n+bp 0n:
      Empty.absurd({tt(LTN("0n", "0n"))}, ab.ft(f))
    case 0n 1n+bp 1n+cp:
      {{==}}
    case 1n+ap 0n c:
      Empty.absurd({tt(LTN("1n+ap", "c"))}, ab.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({tt(LTN("1n+ap", "0n"))}, ab.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nat.lt_le_trans(ap, bp, cp, e, f)

def nat.sub1_le_self(n: Nat) -> {tt(LE("Nat.sub(n, 1n)", "n"))}:
  match n:
    case 0n:
      {{==}}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, nat.sub_zero(p)) : {tt(LE("_", "1n+p"))}
      nat.le_succ_self(p)

def nat.lt_sub1(+ix: Nat, +n: Nat, +h: {tt(LTN("ix", "n"))}) -> {tt(LTN("Nat.sub(ix, 1n)", "n"))}:
  nat.lt_le_trans(Nat.sub(ix, 1n), ix, n, nat.sub1_le_self(ix), h)

def nat.eq_zero(n: Nat, +e: {tt(EQN("n", "0n"))}) -> {{n == 0n : Nat}}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      Empty.absurd({{1n+p == 0n : Nat}}, ab.ft(e))

def nat.eq_of(a: Nat, b: Nat, +e: {tt(EQN("a", "b"))}) -> {{a == b : Nat}}:
  match a b:
    case 0n 0n:
      {{==}}
    case 0n 1n+bp:
      Empty.absurd({{0n == 1n+bp : Nat}}, ab.ft(e))
    case 1n+ap 0n:
      Empty.absurd({{1n+ap == 0n : Nat}}, ab.ft(e))
    case 1n+ +ap 1n+bp:
      %nat.eq_of(ap, bp, e) : {{1n+ap == 1n+_ : Nat}}
      {{==}}

def nat.le_zero(n: Nat) -> {tt(LE("0n", "n"))}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      {{==}}

def nat.le_add(a: Nat, b: Nat) -> {tt(LE("a", "Nat.add(a, b)"))}:
  match a:
    case 0n:
      nat.le_zero(b)
    case 1n+p:
      nat.le_add(p, b)

def nat.le_succ(a: Nat, b: Nat, +e: {tt(LE("a", "b"))}) -> {tt(LE("a", "1n+b"))}:
  match a b:
    case 0n _:
      {{==}}
    case 1n+ap 0n:
      Empty.absurd({tt(LE("1n+ap", "1n"))}, ab.ft(e))
    case 1n+ap 1n+bp:
      nat.le_succ(ap, bp, e)

def nat.add_succ(a: Nat, -b: Nat) -> {{Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}}:
  match a:
    case 0n:
      {{==}}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), nat.add_succ(p, b)) : {{1n+_ == 2n+Nat.add(p, b) : Nat}}
      {{==}}

# U32: a word equals itself (Base's word order, bit by bit)

def wd.fin_refl(x: Bool) -> {{Word.cmp.fin(x, x, EQ{{}}) == EQ{{}} : Cmp}}:
  match x:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def wd.refl(n: Nat, a: Word(n)) -> {{Word.cmp(n, a, a) == EQ{{}} : Cmp}}:
  match n:
    case 0n:
      {{==}}
    case 1n+ +p:
      match a:
        case WCon{{+x, +at}}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{{}}, wd.refl(p, at)) : {{Word.cmp.fin(x, x, _) == EQ{{}} : Cmp}}
          wd.fin_refl(x)

def u.refl(a: U32) -> {{U32.cmp(a, a) == EQ{{}} : Cmp}}:
  match a:
    case U32{{+w}}:
      wd.refl(32n, w)

def u.eq_refl(+a: U32) -> {tt("U32.is_eq(a, a)")}:
  %Equal.sym(Cmp, U32.cmp(a, a), EQ{{}}, u.refl(a)) : {tt("Cmp.is_eq(_)")}
  {{==}}

# An interval compares the same as itself

def rate.refl(+a: W.W64) -> {tt("D.Dim.same_rate(a, a)")}:
  bo.and_intro(U32.is_eq(W.W64.hi(a), W.W64.hi(a)), U32.is_eq(W.W64.lo(a), W.W64.lo(a)), u.eq_refl(W.W64.hi(a)), u.eq_refl(W.W64.lo(a)))

def cmp.same(cs: List<&2, D.DimCriterion>, +pct: U32, +a: {RAT}) -> {{{CMPW("cs", "pct", "a", "a")} == D.DimSame{{}} : D.DimVerdict}}:
  match cs:
    case Nil{{}}:
      {{==}}
    case Con{{D.DimCriterion{{+m, +hb}}, +rest}}:
      %Equal.sym(Bool, D.Dim.same_rate(D.Dim.metric(m, a), D.Dim.metric(m, a)), True{{}}, rate.refl(D.Dim.metric(m, a))) : {{D.Dim.verdict(Con{{D.DimCmp{{D.Dim.compare.rate.go(_, pct, D.Dim.metric(m, a), D.Dim.metric(m, a)), hb}}, D.Dim.compare.all(rest, pct, a, a)}}) == D.DimSame{{}} : D.DimVerdict}}
      cmp.same(rest, pct, a)

# The inward direction right is a step within the table

def iw.right(multi: Bool, left: Bool, right: Bool, +n: Nat, +ix: Nat, +em: {eqb(LTN("1n", "n"), "multi")}, +el: {eqb(EQN("ix", "0n"), "left")}, +e: {{D.Dim.inward.go(multi, left, right) == Some{{True{{}}}} : Maybe<&2, Bool>}}) -> {tt(LTN("1n+ix", "n"))}:
  match multi left right:
    case False{{}} left right:
      Empty.absurd({tt(LTN("1n+ix", "n"))}, ab.none_some(True{{}}, e))
    case True{{}} True{{}} right:
      %Equal.sym(Nat, ix, 0n, nat.eq_zero(ix, el)) : {tt(LTN("1n+_", "n"))}
      em
    case True{{}} False{{}} True{{}}:
      Empty.absurd({tt(LTN("1n+ix", "n"))}, ab.ft_some(e))
    case True{{}} False{{}} False{{}}:
      Empty.absurd({tt(LTN("1n+ix", "n"))}, ab.none_some(True{{}}, e))

# Family A: the index stays within a table of n profiles

def A.mv(can: Bool, right: Bool, +n: Nat, +ix: Nat, -r: {RAT}, +ecan: {eqb(CAN("n", "right", "ix"), "can")}, {HA}) -> {A(MOVEGO("can", "right", "ix", "r"))}:
  match can right:
    case True{{}} True{{}}:
      ecan
    case True{{}} False{{}}:
      nat.lt_sub1(ix, n, h)
    case False{{}} right:
      h

def A.pr(d: Bool, +n: Nat, +ix: Nat, -r: {RAT}, +ee: {{{INWARD("n", "ix")} == Some{{d}} : Maybe<&2, Bool>}}, {HA}) -> {A(PROBE("d", "ix", "r"))}:
  match d:
    case True{{}}:
      iw.right(Nat.is_lt(1n, n), Nat.is_eq(ix, 0n), Nat.is_eq(1n+ix, n), n, ix, {{==}}, {{==}}, ee)
    case False{{}}:
      nat.lt_sub1(ix, n, h)

def A.tg(off: Bool, tired: Bool, d: Bool, +n: Nat, +t: Nat, +ix: Nat, -r: {RAT}, +ee: {{{INWARD("n", "ix")} == Some{{d}} : Maybe<&2, Bool>}}, {HA}) -> {A(TIREGO("off", "tired", "d", "t", "ix", "r"))}:
  match off tired:
    case True{{}} tired:
      h
    case False{{}} True{{}}:
      A.pr(d, n, ix, r, ee, h)
    case False{{}} False{{}}:
      h

def A.tire(edge: Maybe<&2, Bool>, +n: Nat, +lim: Nat, +t: Nat, +ix: Nat, -r: {RAT}, +ee: {{{INWARD("n", "ix")} == edge : Maybe<&2, Bool>}}, {HA}) -> {A(TIRE("edge", "lim", "t", "ix", "r"))}:
  match edge:
    case None{{}}:
      h
    case Some{{+d}}:
      A.tg(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, n, t, ix, r, ee, h)

def A.park(pr: Bool, -n: Nat, +ix: Nat, -r: {RAT}, {HA}) -> {A(PARK("pr", "ix", "r"))}:
  match pr:
    case True{{}}:
      h
    case False{{}}:
      h

def A.going(c: D.DimVerdict, +right: Bool, pr: Bool, +n: Nat, +ix: Nat, -r: {RAT}, {HA}) -> {A(GOING("c", "right", "pr", "n", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      A.park(pr, n, ix, r, h)
    case D.DimBetter{{}}:
      A.mv({CAN("n", "right", "ix")}, right, n, ix, r, {{==}}, h)
    case D.DimWorse{{}}:
      A.mv({CAN("n", NR, "ix")}, {NR}, n, ix, r, {{==}}, h)

def A.parked(c: D.DimVerdict, +t: Nat, +n: Nat, +lim: Nat, +ix: Nat, -r: {RAT}, {HA}) -> {A(PARKED("c", "t", "n", "lim", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      A.tire({INWARD("n", "ix")}, n, lim, t, ix, r, {{==}}, h)
    case D.DimBetter{{}}:
      A.mv({CAN("n", EQ0, "ix")}, {EQ0}, n, ix, r, {{==}}, h)
    case D.DimWorse{{}}:
      A.mv({CAN("n", EQ0, "ix")}, {EQ0}, n, ix, r, {{==}}, h)

def A.settled(c: D.DimVerdict, +n: Nat, +ix: Nat, -r: {RAT}, {HA}) -> {A(SETTLED("c", "n", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      h
    case D.DimBetter{{}}:
      A.mv({CAN("n", EQ0, "ix")}, {EQ0}, n, ix, r, {{==}}, h)
    case D.DimWorse{{}}:
      A.mv({CAN("n", EQ0, "ix")}, {EQ0}, n, ix, r, {{==}}, h)

def A.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +ix: Nat, -r: {RAT}, {HA}) -> {A(DECIDE("m", "c", "n", "lim", "ix", "r"))}:
  match m:
    case D.DimGoing{{+right, +pr}}:
      A.going(c, right, pr, n, ix, r, h)
    case D.DimParked{{+t}}:
      A.parked(c, t, n, lim, ix, r, h)
    case D.DimSettled{{}}:
      A.settled(c, n, ix, r, h)

def A.prev(pv: {MB}, p: D.DimParams, +ix: Nat, +m: D.DimMode, +r: {RAT}, +h: {tt(LTN("ix", LEN("D.DimParams.profiles(p)")))}) -> {tt(LTN(IX(ST(PREV("pv", "p", "ix", "m", "r"))), LEN("D.DimParams.profiles(p)")))}:
  match pv:
    case None{{}}:
      h
    case Some{{+q}}:
      match p:
        case D.DimParams{{+ps, +sx, +pct, +lim, +cs}}:
          A.decide(m, {CMPW("cs", "pct", "r", "q")}, {LEN("ps")}, lim, ix, r, h)

def A.on(skip: Bool, +p: D.DimParams, st: D.Dim, +s: D.DimSample, +h: {tt("D.Dim.valid(p, st)")}) -> {tt("D.Dim.valid(p, " + ST(ON("skip", "p", "st", "s")) + ")")}:
  match skip:
    case True{{}}:
      h
    case False{{}}:
      match st:
        case D.Dim{{+ix, +m, +pv}}:
          A.prev(pv, p, ix, m, D.Dim.rates(s), h)

# Family B: at most one step, and a step that says no change keeps the index

def dp.ns(+ix: Nat, +r: D.DimStep) -> Bool:
  {AND(AND(LE(IX(ST("r")), "1n+ix"), LE("ix", "1n+" + IX(ST("r")))), OR(CH("r"), EQN(IX(ST("r")), "ix")))}

def ns.core(+i: Nat) -> {tt(AND(AND(LE("i", "1n+i"), LE("i", "1n+i")), OR("False{}", EQN("i", "i"))))}:
  bo.and_intro({AND(LE("i", "1n+i"), LE("i", "1n+i"))}, {OR("False{}", EQN("i", "i"))}, bo.and_intro({LE("i", "1n+i")}, {LE("i", "1n+i")}, nat.le_succ_self(i), nat.le_succ_self(i)), nat.eq_refl(i))

def ns.same(+ix: Nat, -m: D.DimMode, -r: {RAT}) -> {B(MK("ix", "m", "r", "False{}"))}:
  ns.core(ix)

def ns.up(+ix: Nat, -m: D.DimMode, -r: {RAT}) -> {B(MK("1n+ix", "m", "r", "True{}"))}:
  bo.and_intro({AND(LE("1n+ix", "1n+ix"), LE("ix", "2n+ix"))}, {OR("True{}", EQN("1n+ix", "ix"))}, bo.and_intro({LE("1n+ix", "1n+ix")}, {LE("ix", "2n+ix")}, nat.le_refl(1n+ix), nat.le_succ2(ix)), {{==}})

def ns.down(+ix: Nat, -m: D.DimMode, -r: {RAT}) -> {B(MK("Nat.sub(ix, 1n)", "m", "r", "True{}"))}:
  bo.and_intro({AND(LE("Nat.sub(ix, 1n)", "1n+ix"), LE("ix", "1n+Nat.sub(ix, 1n)"))}, {OR("True{}", EQN("Nat.sub(ix, 1n)", "ix"))}, bo.and_intro({LE("Nat.sub(ix, 1n)", "1n+ix")}, {LE("ix", "1n+Nat.sub(ix, 1n)")}, nat.sub1_le(ix), nat.le_sub1(ix)), {{==}})

def B.mv(can: Bool, right: Bool, +ix: Nat, -r: {RAT}) -> {B(MOVEGO("can", "right", "ix", "r"))}:
  match can right:
    case True{{}} True{{}}:
      ns.up(ix, D.DimGoing{{True{{}}, False{{}}}}, r)
    case True{{}} False{{}}:
      ns.down(ix, D.DimGoing{{False{{}}, False{{}}}}, r)
    case False{{}} right:
      ns.same(ix, D.DimParked{{0n}}, r)

def B.pr(d: Bool, +ix: Nat, -r: {RAT}) -> {B(PROBE("d", "ix", "r"))}:
  match d:
    case True{{}}:
      ns.up(ix, D.DimGoing{{True{{}}, True{{}}}}, r)
    case False{{}}:
      ns.down(ix, D.DimGoing{{False{{}}, True{{}}}}, r)

def B.tg(off: Bool, tired: Bool, d: Bool, +t: Nat, +ix: Nat, -r: {RAT}) -> {B(TIREGO("off", "tired", "d", "t", "ix", "r"))}:
  match off tired:
    case True{{}} tired:
      ns.same(ix, D.DimParked{{t}}, r)
    case False{{}} True{{}}:
      B.pr(d, ix, r)
    case False{{}} False{{}}:
      ns.same(ix, D.DimParked{{1n+t}}, r)

def B.tire(edge: Maybe<&2, Bool>, +lim: Nat, +t: Nat, +ix: Nat, -r: {RAT}) -> {B(TIRE("edge", "lim", "t", "ix", "r"))}:
  match edge:
    case None{{}}:
      ns.same(ix, D.DimParked{{t}}, r)
    case Some{{+d}}:
      B.tg(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, r)

def B.park(pr: Bool, +ix: Nat, -r: {RAT}) -> {B(PARK("pr", "ix", "r"))}:
  match pr:
    case True{{}}:
      ns.same(ix, D.DimSettled{{}}, r)
    case False{{}}:
      ns.same(ix, D.DimParked{{0n}}, r)

def B.going(c: D.DimVerdict, +right: Bool, pr: Bool, +n: Nat, +ix: Nat, -r: {RAT}) -> {B(GOING("c", "right", "pr", "n", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      B.park(pr, ix, r)
    case D.DimBetter{{}}:
      B.mv({CAN("n", "right", "ix")}, right, ix, r)
    case D.DimWorse{{}}:
      B.mv({CAN("n", NR, "ix")}, {NR}, ix, r)

def B.parked(c: D.DimVerdict, +t: Nat, +n: Nat, +lim: Nat, +ix: Nat, -r: {RAT}) -> {B(PARKED("c", "t", "n", "lim", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      B.tire({INWARD("n", "ix")}, lim, t, ix, r)
    case D.DimBetter{{}}:
      B.mv({CAN("n", EQ0, "ix")}, {EQ0}, ix, r)
    case D.DimWorse{{}}:
      B.mv({CAN("n", EQ0, "ix")}, {EQ0}, ix, r)

def B.settled(c: D.DimVerdict, +n: Nat, +ix: Nat, -r: {RAT}) -> {B(SETTLED("c", "n", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      ns.same(ix, D.DimSettled{{}}, r)
    case D.DimBetter{{}}:
      B.mv({CAN("n", EQ0, "ix")}, {EQ0}, ix, r)
    case D.DimWorse{{}}:
      B.mv({CAN("n", EQ0, "ix")}, {EQ0}, ix, r)

def B.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +ix: Nat, -r: {RAT}) -> {B(DECIDE("m", "c", "n", "lim", "ix", "r"))}:
  match m:
    case D.DimGoing{{+right, +pr}}:
      B.going(c, right, pr, n, ix, r)
    case D.DimParked{{+t}}:
      B.parked(c, t, n, lim, ix, r)
    case D.DimSettled{{}}:
      B.settled(c, n, ix, r)

def B.prev(pv: {MB}, p: D.DimParams, +ix: Nat, +m: D.DimMode, +r: {RAT}) -> {B(PREV("pv", "p", "ix", "m", "r"))}:
  match pv:
    case None{{}}:
      ns.same(ix, m, r)
    case Some{{+q}}:
      match p:
        case D.DimParams{{+ps, +sx, +pct, +lim, +cs}}:
          B.decide(m, {CMPW("cs", "pct", "r", "q")}, {LEN("ps")}, lim, ix, r)

def B.on(skip: Bool, +p: D.DimParams, +st: D.Dim, +s: D.DimSample) -> {tt("dp.ns(" + IX("st") + ", " + ON("skip", "p", "st", "s") + ")")}:
  match skip:
    case True{{}}:
      ns.core({IX("st")})
    case False{{}}:
      match st:
        case D.Dim{{+ix, +m, +pv}}:
          B.prev(pv, p, ix, m, D.Dim.rates(s))

# Family C: a step's state holds the sample's rates

def C.mv(can: Bool, right: Bool, -ix: Nat, -r: {RAT}) -> {C(MOVEGO("can", "right", "ix", "r"))}:
  match can right:
    case True{{}} True{{}}:
      {{==}}
    case True{{}} False{{}}:
      {{==}}
    case False{{}} right:
      {{==}}

def C.pr(d: Bool, -ix: Nat, -r: {RAT}) -> {C(PROBE("d", "ix", "r"))}:
  match d:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def C.tg(off: Bool, tired: Bool, d: Bool, -t: Nat, -ix: Nat, -r: {RAT}) -> {C(TIREGO("off", "tired", "d", "t", "ix", "r"))}:
  match off tired:
    case True{{}} tired:
      {{==}}
    case False{{}} True{{}}:
      C.pr(d, ix, r)
    case False{{}} False{{}}:
      {{==}}

def C.tire(edge: Maybe<&2, Bool>, +lim: Nat, +t: Nat, -ix: Nat, -r: {RAT}) -> {C(TIRE("edge", "lim", "t", "ix", "r"))}:
  match edge:
    case None{{}}:
      {{==}}
    case Some{{+d}}:
      C.tg(Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), d, t, ix, r)

def C.park(pr: Bool, -ix: Nat, -r: {RAT}) -> {C(PARK("pr", "ix", "r"))}:
  match pr:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def C.going(c: D.DimVerdict, +right: Bool, pr: Bool, +n: Nat, +ix: Nat, -r: {RAT}) -> {C(GOING("c", "right", "pr", "n", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      C.park(pr, ix, r)
    case D.DimBetter{{}}:
      C.mv({CAN("n", "right", "ix")}, right, ix, r)
    case D.DimWorse{{}}:
      C.mv({CAN("n", NR, "ix")}, {NR}, ix, r)

def C.parked(c: D.DimVerdict, +t: Nat, +n: Nat, +lim: Nat, +ix: Nat, -r: {RAT}) -> {C(PARKED("c", "t", "n", "lim", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      C.tire({INWARD("n", "ix")}, lim, t, ix, r)
    case D.DimBetter{{}}:
      C.mv({CAN("n", EQ0, "ix")}, {EQ0}, ix, r)
    case D.DimWorse{{}}:
      C.mv({CAN("n", EQ0, "ix")}, {EQ0}, ix, r)

def C.settled(c: D.DimVerdict, +n: Nat, +ix: Nat, -r: {RAT}) -> {C(SETTLED("c", "n", "ix", "r"))}:
  match c:
    case D.DimSame{{}}:
      {{==}}
    case D.DimBetter{{}}:
      C.mv({CAN("n", EQ0, "ix")}, {EQ0}, ix, r)
    case D.DimWorse{{}}:
      C.mv({CAN("n", EQ0, "ix")}, {EQ0}, ix, r)

def C.decide(m: D.DimMode, c: D.DimVerdict, +n: Nat, +lim: Nat, +ix: Nat, -r: {RAT}) -> {C(DECIDE("m", "c", "n", "lim", "ix", "r"))}:
  match m:
    case D.DimGoing{{+right, +pr}}:
      C.going(c, right, pr, n, ix, r)
    case D.DimParked{{+t}}:
      C.parked(c, t, n, lim, ix, r)
    case D.DimSettled{{}}:
      C.settled(c, n, ix, r)

# Identical samples: one step with a sample of some time, from a state
# holding that sample's rates, decides on DimSame

def cv.step(+ix: Nat, +m: D.DimMode, {SIG}, {NZ}) -> {eqd(STEP("D.Dim{ix, m, Some{" + R + "}}"), ST(DECIDE("m", "D.DimSame{}", N, "lim", "ix", R)))}:
  %Equal.sym(Bool, U32.is_zero(el), False{{}}, nz) : {eqd(ST(ON("_", P, "D.Dim{ix, m, Some{" + R + "}}", S)), ST(DECIDE("m", "D.DimSame{}", N, "lim", "ix", R)))}
  %Equal.sym(D.DimVerdict, {CMPW("cs", "pct", R, R)}, D.DimSame{{}}, cmp.same(cs, pct, {R})) : {eqd(ST(DECIDE("m", "_", N, "lim", "ix", R)), ST(DECIDE("m", "D.DimSame{}", N, "lim", "ix", R)))}
  {{==}}

def cv.settled(+ix: Nat, {SIG}, {NZ}) -> {FIX(SE())}:
  cv.step(ix, D.DimSettled{{}}, {ARGS}, nz)

def cv.probe(+ix: Nat, +d: Bool, {SIG}, {NZ}) -> {eqd(STEP(GOY("d", "True{}")), SE())}:
  cv.step(ix, D.DimGoing{{d, True{{}}}}, {ARGS}, nz)

def cv.going(+ix: Nat, +d: Bool, {SIG}, {NZ}) -> {eqd(STEP(GOY("d", "False{}")), PK("0n"))}:
  cv.step(ix, D.DimGoing{{d, False{{}}}}, {ARGS}, nz)

# a step of no time changes nothing

def cv.skip(+x: D.Dim, {SIG}, +z: {tt("U32.is_zero(el)")}) -> {FIX("x")}:
  %Equal.sym(Bool, U32.is_zero(el), True{{}}, z) : {eqd(ST(ON("_", P, "x", S)), "x")}
  {{==}}

# a fixed point stays

def cv.rest(n: Nat, +p: D.DimParams, +x: D.Dim, +s: D.DimSample, +f: {eqd(ST("D.Dim.step(p, x, s)"), "x")}) -> {eqd("D.Dim.run(p, x, List.replicate(D.DimSample, n, s))", "x")}:
  match n:
    case 0n:
      {{==}}
    case 1n+k:
      %Equal.sym(D.Dim, {ST("D.Dim.step(p, x, s)")}, x, f) : {eqd("D.Dim.run.go(List.replicate(D.DimSample, k, s), p, _)", "x")}
      cv.rest(k, p, x, s, f)

# rewriting a run that reaches a fixed point x, in both places of the goal

def cv.at(+y: D.Dim, +x: D.Dim, +k: Nat, {SIG}, +e: {eqd(RUN("y", "k"), "x")}, +f: {FIX("x")}) -> {FIX(RUN("y", "k"))}:
  %Equal.sym(D.Dim, {RUN("y", "k")}, x, e) : {eqd(STEP("_"), "_")}
  f

# Parked on an edge with the same interval: count, then probe

def cv.parked_step(+ix: Nat, +t: Nat, {SIG}, {NZ}) -> {eqd(STEP(PK("t")), ST(TIRE(INWARD(N, "ix"), "lim", "t", "ix", R)))}:
  cv.step(ix, D.DimParked{{t}}, {ARGS}, nz)

def cv.probe_run(d: Bool, +ix: Nat, +t: Nat, +j: Nat, {SIG}, {NZ}, +e: {eqd(STEP(PK("t")), ST(PROBE("d", "ix", R)))}) -> {FIX(RUN(PK("t"), "2n+j"))}:
  match d:
    case True{{}}:
      cv.at({PK("t")}, {SE("1n+ix")}, 2n+j, {ARGS}, cv.probe_eq(True{{}}, ix, t, j, {ARGS}, nz, e), cv.settled(1n+ix, {ARGS}, nz))
    case False{{}}:
      cv.at({PK("t")}, {SE("Nat.sub(ix, 1n)")}, 2n+j, {ARGS}, cv.probe_eq(False{{}}, ix, t, j, {ARGS}, nz, e), cv.settled(Nat.sub(ix, 1n), {ARGS}, nz))
'''

# simpler: one lemma per direction
def probe_eq_dir(dname, d, ix2):
    pr = GOY(d, "True{}", ix2)
    return f'''
def cv.probe_eq.{dname}(+ix: Nat, +t: Nat, +j: Nat, {SIG}, {NZ}, +e: {eqd(STEP(PK("t")), pr)}) -> {eqd(RUN(PK("t"), "2n+j"), SE(ix2))}:
  %Equal.sym(D.Dim, {STEP(PK("t"))}, {pr}, e) : {eqd(RUNGO("1n+j", "_"), SE(ix2))}
  %Equal.sym(D.Dim, {STEP(pr)}, {SE(ix2)}, cv.probe({ix2}, {d}, {ARGS}, nz)) : {eqd(RUNGO("j", "_"), SE(ix2))}
  cv.rest(j, {P}, {SE(ix2)}, {S}, cv.settled({ix2}, {ARGS}, nz))
'''

text = text.replace("cv.probe_eq(True{}, ix, t, j, %s, nz, e)" % ARGS, "cv.probe_eq.right(ix, t, j, %s, nz, e)" % ARGS)
text = text.replace("cv.probe_eq(False{}, ix, t, j, %s, nz, e)" % ARGS, "cv.probe_eq.left(ix, t, j, %s, nz, e)" % ARGS)
anchor = "def cv.probe_run("
text = text.replace(anchor, (probe_eq_dir("right", "True{}", "1n+ix") + probe_eq_dir("left", "False{}", "Nat.sub(ix, 1n)")).lstrip("\n") + "\n" + anchor)

TEQ = lambda e: "{%s == %s : Maybe<&2, Bool>}" % (INWARD(N, "ix"), e)
text += f'''
# The step of a parked state, by the edge and the tired count

def cv.pk_none(+ix: Nat, +t: Nat, {SIG}, {NZ}, +ee: {TEQ("None{}")}) -> {FIX(PK("t"))}:
  %Equal.sym(D.Dim, {STEP(PK("t"))}, {ST(TIRE(INWARD(N, "ix"), "lim", "t", "ix", R))}, cv.parked_step(ix, t, {ARGS}, nz)) : {eqd("_", PK("t"))}
  %Equal.sym(Maybe<&2, Bool>, {INWARD(N, "ix")}, None{{}}, ee) : {eqd(ST(TIRE("_", "lim", "t", "ix", R)), PK("t"))}
  {{==}}

def cv.pk_go(+ix: Nat, +t: Nat, +d: Bool, {SIG}, {NZ}, +ee: {TEQ("Some{d}")}) -> {eqd(STEP(PK("t")), ST(TIREGO("Nat.is_eq(lim, 0n)", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R)))}:
  %Equal.sym(D.Dim, {STEP(PK("t"))}, {ST(TIRE(INWARD(N, "ix"), "lim", "t", "ix", R))}, cv.parked_step(ix, t, {ARGS}, nz)) : {eqd("_", ST(TIREGO("Nat.is_eq(lim, 0n)", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R)))}
  %Equal.sym(Maybe<&2, Bool>, {INWARD(N, "ix")}, Some{{d}}, ee) : {eqd(ST(TIRE("_", "lim", "t", "ix", R)), ST(TIREGO("Nat.is_eq(lim, 0n)", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R)))}
  {{==}}

def cv.pk_off(+ix: Nat, +t: Nat, +d: Bool, {SIG}, {NZ}, +ee: {TEQ("Some{d}")}, +eo: {tt(EQN("lim", "0n"))}) -> {FIX(PK("t"))}:
  %Equal.sym(D.Dim, {STEP(PK("t"))}, {ST(TIREGO("Nat.is_eq(lim, 0n)", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R))}, cv.pk_go(ix, t, d, {ARGS}, nz, ee)) : {eqd("_", PK("t"))}
  %Equal.sym(Bool, Nat.is_eq(lim, 0n), True{{}}, eo) : {eqd(ST(TIREGO("_", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R)), PK("t"))}
  {{==}}

def cv.pk_probe(+ix: Nat, +t: Nat, +d: Bool, {SIG}, {NZ}, +ee: {TEQ("Some{d}")}, +eo: {ff(EQN("lim", "0n"))}, +et: {tt(LE("lim", "1n+t"))}) -> {eqd(STEP(PK("t")), ST(PROBE("d", "ix", R)))}:
  %Equal.sym(D.Dim, {STEP(PK("t"))}, {ST(TIREGO("Nat.is_eq(lim, 0n)", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R))}, cv.pk_go(ix, t, d, {ARGS}, nz, ee)) : {eqd("_", ST(PROBE("d", "ix", R)))}
  %Equal.sym(Bool, Nat.is_eq(lim, 0n), False{{}}, eo) : {eqd(ST(TIREGO("_", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R)), ST(PROBE("d", "ix", R)))}
  %Equal.sym(Bool, Nat.is_le(lim, 1n+t), True{{}}, et) : {eqd(ST(TIREGO("False{}", "_", "d", "t", "ix", R)), ST(PROBE("d", "ix", R)))}
  {{==}}

def cv.pk_count(+ix: Nat, +t: Nat, +d: Bool, {SIG}, {NZ}, +ee: {TEQ("Some{d}")}, +eo: {ff(EQN("lim", "0n"))}, +et: {ff(LE("lim", "1n+t"))}) -> {eqd(STEP(PK("t")), PK("1n+t"))}:
  %Equal.sym(D.Dim, {STEP(PK("t"))}, {ST(TIREGO("Nat.is_eq(lim, 0n)", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R))}, cv.pk_go(ix, t, d, {ARGS}, nz, ee)) : {eqd("_", PK("1n+t"))}
  %Equal.sym(Bool, Nat.is_eq(lim, 0n), False{{}}, eo) : {eqd(ST(TIREGO("_", "Nat.is_le(lim, 1n+t)", "d", "t", "ix", R)), PK("1n+t"))}
  %Equal.sym(Bool, Nat.is_le(lim, 1n+t), False{{}}, et) : {eqd(ST(TIREGO("False{}", "_", "d", "t", "ix", R)), PK("1n+t"))}
  {{==}}

def cv.fixed_run(+y: D.Dim, +k: Nat, {SIG}, +f: {FIX("y")}) -> {FIX(RUN("y", "k"))}:
  cv.at(y, y, k, {ARGS}, cv.rest(k, {P}, y, {S}, f), f)

# the cases of a parked state, by the edge, whether probing is off, and
# whether the count is up; next: the rest of the count, when it is not

def cv.pc(edge: Maybe<&2, Bool>, off: Bool, tired: Bool, +ix: Nat, +t: Nat, +j: Nat, {SIG}, {NZ}, +ee: {TEQ("edge")}, +eo: {eqb(EQN("lim", "0n"), "off")}, +et: {eqb(LE("lim", "1n+t"), "tired")}, next: {ff("tired")} -> {FIX(RUN(PK("1n+t"), "1n+j"))}) -> {FIX(RUN(PK("t"), "2n+j"))}:
  match edge:
    case None{{}}:
      cv.fixed_run({PK("t")}, 2n+j, {ARGS}, cv.pk_none(ix, t, {ARGS}, nz, ee))
    case Some{{+d}}:
      match off:
        case True{{}}:
          cv.fixed_run({PK("t")}, 2n+j, {ARGS}, cv.pk_off(ix, t, d, {ARGS}, nz, ee, eo))
        case False{{}}:
          match tired:
            case True{{}}:
              cv.probe_run(d, ix, t, j, {ARGS}, nz, cv.pk_probe(ix, t, d, {ARGS}, nz, ee, eo, et))
            case False{{}}:
              %Equal.sym(D.Dim, {STEP(PK("t"))}, {PK("1n+t")}, cv.pk_count(ix, t, d, {ARGS}, nz, ee, eo, et)) : {FIX(RUNGO("1n+j", "_"))}
              next({{==}})

def cv.h_next(+lim: Nat, +jp: Nat, +t: Nat, +h: {tt(LE("lim", "1n+Nat.add(jp, 1n+t)"))}) -> {tt(LE("lim", "Nat.add(jp, 2n+t)"))}:
  %Equal.sym(Nat, Nat.add(jp, 2n+t), 1n+Nat.add(jp, 1n+t), nat.add_succ(jp, 1n+t)) : {tt(LE("lim", "_"))}
  h

# parked: after 2 + j identical samples at rest, when lim <= j + 1 + t

def cv.parked(j: Nat, +t: Nat, +ix: Nat, {SIG}, {NZ}, +h: {tt(LE("lim", "Nat.add(j, 1n+t)"))}) -> {FIX(RUN(PK("t"), "2n+j"))}:
  match j:
    case 0n:
      cv.pc({INWARD(N, "ix")}, Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), ix, t, 0n, {ARGS}, nz, {{==}}, {{==}}, {{==}}, u => Empty.absurd({FIX(RUN(PK("1n+t"), "1n"))}, ab.tf(Equal.trans(Bool, True{{}}, Nat.is_le(lim, 1n+t), False{{}}, Equal.sym(Bool, Nat.is_le(lim, 1n+t), True{{}}, h), u))))
    case 1n+ +jp:
      cv.pc({INWARD(N, "ix")}, Nat.is_eq(lim, 0n), Nat.is_le(lim, 1n+t), ix, t, 1n+jp, {ARGS}, nz, {{==}}, {{==}}, {{==}}, u => cv.parked(jp, 1n+t, ix, {ARGS}, nz, cv.h_next(lim, jp, t, h)))

# from a state holding the sample's rates, 3 + lim samples bring it to rest

def cv.going_eq(+ix: Nat, +d: Bool, {SIG}, {NZ}) -> {eqd(RUN(GOY("d", "False{}"), "3n+lim"), RUN(PK("0n"), "2n+lim"))}:
  %Equal.sym(D.Dim, {STEP(GOY("d", "False{}"))}, {PK("0n")}, cv.going(ix, d, {ARGS}, nz)) : {eqd(RUNGO("2n+lim", "_"), RUN(PK("0n"), "2n+lim"))}
  {{==}}

def cv.probe_eq2(+ix: Nat, +d: Bool, {SIG}, {NZ}) -> {eqd(RUN(GOY("d", "True{}"), "3n+lim"), SE())}:
  %Equal.sym(D.Dim, {STEP(GOY("d", "True{}"))}, {SE()}, cv.probe(ix, d, {ARGS}, nz)) : {eqd(RUNGO("2n+lim", "_"), SE())}
  cv.rest(2n+lim, {P}, {SE()}, {S}, cv.settled(ix, {ARGS}, nz))

def cv.primed(y: D.Dim, {SIG}, {NZ}, +hp: {{{PRV("y")} == Some{{{R}}} : {MB}}}) -> {FIX(RUN("y", "3n+lim"))}:
  match y:
    case D.Dim{{+ix, D.DimGoing{{+d, True{{}}}}, +pv}}:
      %Equal.sym({MB}, pv, Some{{{R}}}, hp) : {FIX(RUN("D.Dim{ix, D.DimGoing{d, True{}}, _}", "3n+lim"))}
      cv.at({GOY("d", "True{}")}, {SE()}, 3n+lim, {ARGS}, cv.probe_eq2(ix, d, {ARGS}, nz), cv.settled(ix, {ARGS}, nz))
    case D.Dim{{+ix, D.DimGoing{{+d, False{{}}}}, +pv}}:
      %Equal.sym({MB}, pv, Some{{{R}}}, hp) : {FIX(RUN("D.Dim{ix, D.DimGoing{d, False{}}, _}", "3n+lim"))}
      %Equal.sym(D.Dim, {RUN(GOY("d", "False{}"), "3n+lim")}, {RUN(PK("0n"), "2n+lim")}, cv.going_eq(ix, d, {ARGS}, nz)) : {eqd(STEP("_"), "_")}
      cv.parked(lim, 0n, ix, {ARGS}, nz, nat.le_add(lim, 1n))
    case D.Dim{{+ix, D.DimParked{{+t}}, +pv}}:
      %Equal.sym({MB}, pv, Some{{{R}}}, hp) : {FIX(RUN("D.Dim{ix, D.DimParked{t}, _}", "3n+lim"))}
      cv.parked(1n+lim, t, ix, {ARGS}, nz, nat.le_succ(lim, Nat.add(lim, 1n+t), nat.le_add(lim, 1n+t)))
    case D.Dim{{+ix, D.DimSettled{{}}, +pv}}:
      %Equal.sym({MB}, pv, Some{{{R}}}, hp) : {FIX(RUN("D.Dim{ix, D.DimSettled{}, _}", "3n+lim"))}
      cv.fixed_run({SE()}, 3n+lim, {ARGS}, cv.settled(ix, {ARGS}, nz))

# one step with a sample of some time leaves the state holding its rates

def cv.primes.prev(pv: {MB}, +ix: Nat, +m: D.DimMode, {SIG}, {NZ}) -> {{{PRV(STEP("D.Dim{ix, m, pv}"))} == Some{{{R}}} : {MB}}}:
  match pv:
    case None{{}}:
      %Equal.sym(Bool, U32.is_zero(el), False{{}}, nz) : {{{PRV(ST(ON("_", P, "D.Dim{ix, m, None{}}", S)))} == Some{{{R}}} : {MB}}}
      {{==}}
    case Some{{+q}}:
      %Equal.sym(Bool, U32.is_zero(el), False{{}}, nz) : {{{PRV(ST(ON("_", P, "D.Dim{ix, m, Some{q}}", S)))} == Some{{{R}}} : {MB}}}
      C.decide(m, {CMPW("cs", "pct", R, "q")}, {N}, lim, ix, {R})

def cv.primes(st: D.Dim, {SIG}, {NZ}) -> {{{PRV(STEP("st"))} == Some{{{R}}} : {MB}}}:
  match st:
    case D.Dim{{+ix, +m, +pv}}:
      cv.primes.prev(pv, ix, m, {ARGS}, nz)

def cv.settle(z: Bool, +st: D.Dim, {SIG}, +ez: {eqb("U32.is_zero(el)", "z")}) -> {FIX(RUN("st", "4n+lim"))}:
  match z:
    case True{{}}:
      cv.skip({RUN("st", "4n+lim")}, {ARGS}, ez)
    case False{{}}:
      cv.primed({STEP("st")}, {ARGS}, ez, cv.primes(st, {ARGS}, ez))

# Runs keep the index in the table

def run.valid(ss: List<&2, D.DimSample>, +p: D.DimParams, +st: D.Dim, +v: {tt("D.Dim.valid(p, st)")}) -> {tt("D.Dim.valid(p, D.Dim.run.go(ss, p, st))")}:
  match ss:
    case Nil{{}}:
      v
    case Con{{+s, +rest}}:
      run.valid(rest, p, {ST("D.Dim.step(p, st, s)")}, A.on(U32.is_zero(D.DimSample.elapsed(s)), p, st, s, v))

def get.some(xs: List<&2, D.DimProfile>, i: Nat, +h: {tt(LTN("i", "List.length(&2, D.DimProfile, xs)"))}) -> {tt("Maybe.is_some(&2, D.DimProfile, List.get(&2, D.DimProfile, xs, i))")}:
  match xs i:
    case Nil{{}} i:
      Empty.absurd({tt("Maybe.is_some(&2, D.DimProfile, List.get(&2, D.DimProfile, Nil{}, i))")}, ab.ft(bo.lt_zero(i, h)))
    case Con{{x, t}} 0n:
      {{==}}
    case Con{{x, t}} 1n+k:
      get.some(t, k, h)

# The laws

def Laws.dim_new_valid(p, h):
  match p:
    case D.DimParams{{+ps, +sx, pct, lim, cs}}:
      new.valid(Nat.is_lt(sx, {N}), sx, ps, {{==}}, h)

def Laws.dim_step_valid(p, st, s, v):
  A.on(U32.is_zero(D.DimSample.elapsed(s)), p, st, s, v)

def Laws.dim_run_valid(p, st, ss, v):
  run.valid(ss, p, st, v)

def Laws.dim_profile_some(p, st, v):
  get.some(D.DimParams.profiles(p), D.Dim.index(st), v)

def Laws.dim_step_by_one(p, st, s):
  bo.and_l({AND(LE(IX(ST("D.Dim.step(p, st, s)")), "1n+" + IX("st")), LE(IX("st"), "1n+" + IX(ST("D.Dim.step(p, st, s)"))))}, {OR(CH("D.Dim.step(p, st, s)"), EQN(IX(ST("D.Dim.step(p, st, s)")), IX("st")))}, B.on(U32.is_zero(D.DimSample.elapsed(s)), p, st, s))

def Laws.dim_unchanged(p, st, s, u):
  nat.eq_of({IX(ST("D.Dim.step(p, st, s)"))}, {IX("st")}, bo.or_still({CH("D.Dim.step(p, st, s)")}, {EQN(IX(ST("D.Dim.step(p, st, s)")), IX("st"))}, bo.and_r({AND(LE(IX(ST("D.Dim.step(p, st, s)")), "1n+" + IX("st")), LE(IX("st"), "1n+" + IX(ST("D.Dim.step(p, st, s)"))))}, {OR(CH("D.Dim.step(p, st, s)"), EQN(IX(ST("D.Dim.step(p, st, s)")), IX("st")))}, B.on(U32.is_zero(D.DimSample.elapsed(s)), p, st, s)), u))

def Laws.dim_same_rates(p, s):
  match p:
    case D.DimParams{{ps, sx, +pct, lim, +cs}}:
      cmp.same(cs, pct, D.Dim.rates(s))

def Laws.dim_settles(p, st, s):
  match p s:
    case D.DimParams{{+ps, +sx, +pct, +lim, +cs}} D.DimSample{{+pk, +by, +ev, +co, +el}}:
      cv.settle(U32.is_zero(el), st, {ARGS}, {{==}})

def Laws.dim_rest(p, x, s, n, f):
  cv.rest(n, p, x, s, f)

def Laws.dim_wit():
  {{==}}

def Laws.dim_vec_climb_index():
  {{==}}

def Laws.dim_vec_climb_mode():
  {{==}}

def Laws.dim_vec_probe_index():
  {{==}}

def Laws.dim_vec_probe_mode():
  {{==}}
'''

# helpers used above, placed before their first use
helpers = f'''
def bo.lt_zero(i: Nat, +h: {tt(LTN("i", "0n"))}) -> {{False{{}} == True{{}} : Bool}}:
  match i:
    case 0n:
      h
    case 1n+k:
      h

def new.valid(inside: Bool, +sx: Nat, +ps: List<&2, D.DimProfile>, +e: {eqb(LTN("sx", LEN("ps")), "inside")}, +h: {tt(LTN("0n", LEN("ps")))}) -> {tt(LTN("D.Dim.new.at(inside, sx)", LEN("ps")))}:
  match inside:
    case True{{}}:
      e
    case False{{}}:
      h

'''
text = text.replace("# Runs keep the index in the table\n", helpers.lstrip("\n") + "# Runs keep the index in the table\n", 1)
text = text.replace("def run.valid(", "def run.valid(", 1)

if "--check" in sys.argv[1:]:
    with open(out, newline="") as f:
        same = f.read() == text
    print("PROOF.bend is up to date" if same else "PROOF.bend is out of date")
    sys.exit(0 if same else 1)
with open(out, "w", newline="\n") as f:
    f.write(text)
