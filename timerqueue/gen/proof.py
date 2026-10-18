#!/usr/bin/env python3
"""Generates timerqueue/PROOF.bend: the sorted-list lemmas (insertion,
removal, membership, ids, the expiry loop) and the laws, whose statements
repeat long terms (the expiry loop applied to the default store); the
shorthands below build them. The order lemmas they use are in
proof_order.bend, which is written by hand.

Run from anywhere: python3 gen/proof.py rewrites ../PROOF.bend; with
--check it only reports whether the file is up to date (exit 1 if not).
"""
import os, sys
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "PROOF.bend")

L = "List<&2, T.TqTimer>"
def tt(x): return "{%s == True{} : Bool}" % x
def ff(x): return "{%s == False{} : Bool}" % x
def eqb(a, b): return "{%s == %s : Bool}" % (a, b)
def SORT(xs): return "T.TqTimer.sorted(%s)" % xs
def LE(x, y): return "T.TqTimer.le(%s, %s)" % (x, y)
def LT(x, y): return "T.TqTimer.lt(%s, %s)" % (x, y)
def EQ(x, y): return "T.TqTimer.is_eq(%s, %s)" % (x, y)
def GE(y, xs): return "tq.all_ge(%s, %s)" % (y, xs)
def INS(xs, x): return "SL.TqSorted.insert(%s, %s)" % (xs, x)
def PUT(b, x, y, a, t): return "SL.TqSorted.insert.put(%s, %s, %s, %s, %s)" % (b, x, y, a, t)
def REM(xs, x): return "SL.TqSorted.remove(%s, %s)" % (xs, x)
def RPUT(b, y, r): return "SL.TqSorted.remove.put(%s, %s, %s)" % (b, y, r)
def IDS(n, xs): return "T.TqTimer.ids_below(%s, %s)" % (n, xs)
def ID(x): return "T.TqTimer.id(%s)" % x
def EXP(x): return "T.TqTimer.expiry(%s)" % x
def MEM(xs, y): return "T.TqTimer.member(%s, %s)" % (xs, y)
def OR(a, b): return "Bool.or(%s, %s)" % (a, b)
def APP(a, b): return "List.append(&2, T.TqTimer, %s, %s)" % (a, b)
def DUE(now, xs): return "T.TqTimer.all_due(%s, %s)" % (now, xs)
def LATER(now, xs): return "T.TqTimer.all_later(%s, %s)" % (now, xs)
def FROM(t, xs): return "T.TqTimer.all_from(%s, %s)" % (t, xs)
def NLT(a, b): return "Nat.is_lt(%s, %s)" % (a, b)
def K(e, i): return "T.TqTimer{%s, %s}" % (e, i)
def C(x, t): return "Con{%s, %s}" % (x, t)
def AL(a, b, e): return "O.bo.and_l(%s, %s, %s)" % (a, b, e)
def AR(a, b, e): return "O.bo.and_r(%s, %s, %s)" % (a, b, e)
def AI(a, b, e1, e2): return "O.bo.and_intro(%s, %s, %s, %s)" % (a, b, e1, e2)
ST0 = "~List<&2, T.TqTimer>, ~SL.TqSorted.store()"
def SP(l): return "Q.TimerQueue.expire.split(%s, %s, now)" % (ST0, l)
def GO(d, x, t): return "Q.TimerQueue.expire.go(%s, 1n+List.length(&2, T.TqTimer, %s), Some{%s}, %s, Con{%s, %s}, now)" % (ST0, t, x, d, x, t)
def FI(r): return "Q.TqSplit.fired(List<&2, T.TqTimer>, %s)" % r
def STO(r): return "Q.TqSplit.store(List<&2, T.TqTimer>, %s)" % r
def DUEX(x): return "T.TqTime.le(T.TqTimer.expiry(%s), now)" % x
TM = "T.TqTimer"
W = "W.W64"
VSPLIT = lambda q, n, v: (AL(SORT(q), IDS(n, q), v), AR(SORT(q), IDS(n, q), v))

text = f'''import Base
import ../word64/word64.bend as W
import ./timer.bend as T
import ./store.bend as S
import ./sorted.bend as SL
import ./timerqueue.bend as Q
import ./proof_order.bend as O
import ./LAWS.bend as Laws

# Every timer of a list at or after y

def tq.all_ge(+y: {TM}, xs: {L}) -> Bool:
  match xs:
    case Nil{{}}:
      True{{}}
    case Con{{z, r}}:
      Bool.and({LE("y", "z")}, {GE("y", "r")})

# Sorted lists

def ls.tail(+y: {TM}, t: {L}, +h: {tt(SORT(C("y", "t")))}) -> {tt(SORT("t"))}:
  match t:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      {AR(LE("y", "z"), SORT(C("z", "r")), "h")}

def ls.ge_trans(t: {L}, +y: {TM}, +z: {TM}, +h: {tt(LE("y", "z"))}, +g: {tt(GE("z", "t"))}) -> {tt(GE("y", "t"))}:
  match t:
    case Nil{{}}:
      {{==}}
    case Con{{+w, +r}}:
      {AI(LE("y", "w"), GE("y", "r"), "O.kt.le_trans(y, z, w, h, " + AL(LE("z", "w"), GE("z", "r"), "g") + ")", "ls.ge_trans(r, y, z, h, " + AR(LE("z", "w"), GE("z", "r"), "g") + ")")}

def ls.all(t: {L}, +y: {TM}, +h: {tt(SORT(C("y", "t")))}) -> {tt(GE("y", "t"))}:
  match t:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      {AI(LE("y", "z"), GE("y", "r"), AL(LE("y", "z"), SORT(C("z", "r")), "h"), "ls.ge_trans(r, y, z, " + AL(LE("y", "z"), SORT(C("z", "r")), "h") + ", ls.all(r, z, " + AR(LE("y", "z"), SORT(C("z", "r")), "h") + "))")}

def ls.cons(r: {L}, +y: {TM}, +g: {tt(GE("y", "r"))}, +s: {tt(SORT("r"))}) -> {tt(SORT(C("y", "r")))}:
  match r:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r2}}:
      {AI(LE("y", "z"), SORT(C("z", "r2")), AL(LE("y", "z"), GE("y", "r2"), "g"), "s")}

# Insertion keeps a list sorted

def ins.put(b: Bool, +x: {TM}, +y: {TM}, +z: {TM}, +r: {L}, +eb: {eqb(LT("x", "z"), "b")}, +hy: {tt(LE("y", "x"))}, +hs: {tt(SORT(C("y", C("z", "r"))))}, ih: {tt(LE("z", "x"))} -> {tt(SORT(C("z", INS("r", "x"))))}) -> {tt(SORT(C("y", PUT("b", "x", "z", INS("r", "x"), "r"))))}:
  match b:
    case True{{}}:
      {AI(LE("y", "x"), SORT(C("x", C("z", "r"))), "hy", AI(LE("x", "z"), SORT(C("z", "r")), "O.kt.lt_le(x, z, eb)", AR(LE("y", "z"), SORT(C("z", "r")), "hs")))}
    case False{{}}:
      {AI(LE("y", "z"), SORT(C("z", INS("r", "x"))), AL(LE("y", "z"), SORT(C("z", "r")), "hs"), "ih(O.kt.not_lt(x, z, eb))")}

def ins.head(t: {L}, +y: {TM}, +x: {TM}, +hy: {tt(LE("y", "x"))}, +hs: {tt(SORT(C("y", "t")))}) -> {tt(SORT(C("y", INS("t", "x"))))}:
  match t:
    case Nil{{}}:
      {AI(LE("y", "x"), "True{}", "hy", "{==}")}
    case Con{{+z, +r}}:
      ins.put({LT("x", "z")}, x, y, z, r, {{==}}, hy, hs, u => ins.head(r, z, x, u, {AR(LE("y", "z"), SORT(C("z", "r")), "hs")}))

def ins.top(b: Bool, +x: {TM}, +y: {TM}, +t: {L}, +eb: {eqb(LT("x", "y"), "b")}, +h: {tt(SORT(C("y", "t")))}) -> {tt(SORT(PUT("b", "x", "y", INS("t", "x"), "t")))}:
  match b:
    case True{{}}:
      {AI(LE("x", "y"), SORT(C("y", "t")), "O.kt.lt_le(x, y, eb)", "h")}
    case False{{}}:
      ins.head(t, y, x, O.kt.not_lt(x, y, eb), h)

def ins.sorted(xs: {L}, +x: {TM}, +h: {tt(SORT("xs"))}) -> {tt(SORT(INS("xs", "x")))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+y, +t}}:
      ins.top({LT("x", "y")}, x, y, t, {{==}}, h)

# Removal keeps a list sorted

def ge.rput(b: Bool, +y: {TM}, +z: {TM}, +rest: {L}, +g1: {tt(LE("y", "z"))}, +g2: {tt(GE("y", "rest"))}) -> {tt(GE("y", RPUT("b", "z", "rest")))}:
  match b:
    case True{{}}:
      g2
    case False{{}}:
      {AI(LE("y", "z"), GE("y", "rest"), "g1", "g2")}

def ls.ge_remove(t: {L}, +y: {TM}, +x: {TM}, +g: {tt(GE("y", "t"))}) -> {tt(GE("y", REM("t", "x")))}:
  match t:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      ge.rput({EQ("z", "x")}, y, z, {REM("r", "x")}, {AL(LE("y", "z"), GE("y", "r"), "g")}, ls.ge_remove(r, y, x, {AR(LE("y", "z"), GE("y", "r"), "g")}))

def rem.put(b: Bool, +y: {TM}, +rest: {L}, +g: {tt(GE("y", "rest"))}, +s: {tt(SORT("rest"))}) -> {tt(SORT(RPUT("b", "y", "rest")))}:
  match b:
    case True{{}}:
      s
    case False{{}}:
      ls.cons(rest, y, g, s)

def rem.sorted(xs: {L}, +x: {TM}, +h: {tt(SORT("xs"))}) -> {tt(SORT(REM("xs", "x")))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+y, +t}}:
      rem.put({EQ("y", "x")}, y, {REM("t", "x")}, ls.ge_remove(t, y, x, ls.all(t, y, h)), rem.sorted(t, x, ls.tail(y, t, h)))

# Ids stay below the next one

def ids.succ(xs: {L}, +n: Nat, +h: {tt(IDS("n", "xs"))}) -> {tt(IDS("1n+n", "xs"))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      {AI(NLT(ID("z"), "1n+n"), IDS("1n+n", "r"), "O.n.lt_succ(" + ID("z") + ", n, " + AL(NLT(ID("z"), "n"), IDS("n", "r"), "h") + ")", "ids.succ(r, n, " + AR(NLT(ID("z"), "n"), IDS("n", "r"), "h") + ")")}

def ids.put(b: Bool, +x: {TM}, +y: {TM}, +t: {L}, +n: Nat, +hx: {tt(NLT(ID("x"), "n"))}, +h: {tt(IDS("n", C("y", "t")))}, +ih: {tt(IDS("n", INS("t", "x")))}) -> {tt(IDS("n", PUT("b", "x", "y", INS("t", "x"), "t")))}:
  match b:
    case True{{}}:
      {AI(NLT(ID("x"), "n"), IDS("n", C("y", "t")), "hx", "h")}
    case False{{}}:
      {AI(NLT(ID("y"), "n"), IDS("n", INS("t", "x")), AL(NLT(ID("y"), "n"), IDS("n", "t"), "h"), "ih")}

def ids.ins(xs: {L}, +x: {TM}, +n: Nat, +hx: {tt(NLT(ID("x"), "n"))}, +h: {tt(IDS("n", "xs"))}) -> {tt(IDS("n", INS("xs", "x")))}:
  match xs:
    case Nil{{}}:
      {AI(NLT(ID("x"), "n"), "True{}", "hx", "{==}")}
    case Con{{+y, +t}}:
      ids.put({LT("x", "y")}, x, y, t, n, hx, h, ids.ins(t, x, n, hx, {AR(NLT(ID("y"), "n"), IDS("n", "t"), "h")}))

def ids.rput(b: Bool, +y: {TM}, +rest: {L}, +n: Nat, +hy: {tt(NLT(ID("y"), "n"))}, +ih: {tt(IDS("n", "rest"))}) -> {tt(IDS("n", RPUT("b", "y", "rest")))}:
  match b:
    case True{{}}:
      ih
    case False{{}}:
      {AI(NLT(ID("y"), "n"), IDS("n", "rest"), "hy", "ih")}

def ids.rem(xs: {L}, +x: {TM}, +n: Nat, +h: {tt(IDS("n", "xs"))}) -> {tt(IDS("n", REM("xs", "x")))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+y, +t}}:
      ids.rput({EQ("y", "x")}, y, {REM("t", "x")}, n, {AL(NLT(ID("y"), "n"), IDS("n", "t"), "h")}, ids.rem(t, x, n, {AR(NLT(ID("y"), "n"), IDS("n", "t"), "h")}))

# Membership

def mem.put(b: Bool, +x: {TM}, +z: {TM}, +t: {L}, +y: {TM}, +ih: {eqb(MEM(INS("t", "x"), "y"), OR(EQ("x", "y"), MEM("t", "y")))}) -> {eqb(MEM(PUT("b", "x", "z", INS("t", "x"), "t"), "y"), OR(EQ("x", "y"), MEM(C("z", "t"), "y")))}:
  match b:
    case True{{}}:
      {{==}}
    case False{{}}:
      %Equal.sym(Bool, {MEM(INS("t", "x"), "y")}, {OR(EQ("x", "y"), MEM("t", "y"))}, ih) : {eqb(OR(EQ("z", "y"), "_"), OR(EQ("x", "y"), OR(EQ("z", "y"), MEM("t", "y"))))}
      O.bo.or_swap({EQ("z", "y")}, {EQ("x", "y")}, {MEM("t", "y")})

def mem.ins(xs: {L}, +x: {TM}, +y: {TM}) -> {eqb(MEM(INS("xs", "x"), "y"), OR(EQ("x", "y"), MEM("xs", "y")))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +t}}:
      mem.put({LT("x", "z")}, x, z, t, y, mem.ins(t, x, y))

def mg.put(b: Bool, +y: {TM}, +rest: {L}, +x: {TM}, +eb: {eqb(EQ("y", "x"), "b")}, +ih: {ff(MEM("rest", "x"))}) -> {ff(MEM(RPUT("b", "y", "rest"), "x"))}:
  match b:
    case True{{}}:
      ih
    case False{{}}:
      %Equal.sym(Bool, {EQ("y", "x")}, False{{}}, eb) : {ff(OR("_", MEM("rest", "x")))}
      %Equal.sym(Bool, {MEM("rest", "x")}, False{{}}, ih) : {ff(OR("False{}", "_"))}
      {{==}}

def mem.gone(xs: {L}, +x: {TM}) -> {ff(MEM(REM("xs", "x"), "x"))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+y, +t}}:
      mg.put({EQ("y", "x")}, y, {REM("t", "x")}, x, {{==}}, mem.gone(t, x))

def mo.put(b: Bool, +z: {TM}, +x: {TM}, +y: {TM}, +t: {L}, +eb: {eqb(EQ("z", "x"), "b")}, +d: {ff(EQ("x", "y"))}, +ih: {eqb(MEM(REM("t", "x"), "y"), MEM("t", "y"))}) -> {eqb(MEM(RPUT("b", "z", REM("t", "x")), "y"), MEM(C("z", "t"), "y"))}:
  match b:
    case True{{}}:
      %Equal.sym({TM}, z, x, O.kt.eq(z, x, eb)) : {eqb(MEM(REM("t", "x"), "y"), OR(EQ("_", "y"), MEM("t", "y")))}
      %Equal.sym(Bool, {EQ("x", "y")}, False{{}}, d) : {eqb(MEM(REM("t", "x"), "y"), OR("_", MEM("t", "y")))}
      ih
    case False{{}}:
      %Equal.sym(Bool, {MEM(REM("t", "x"), "y")}, {MEM("t", "y")}, ih) : {eqb(OR(EQ("z", "y"), "_"), OR(EQ("z", "y"), MEM("t", "y")))}
      {{==}}

def mem.other(xs: {L}, +x: {TM}, +y: {TM}, +d: {ff(EQ("x", "y"))}) -> {eqb(MEM(REM("xs", "x"), "y"), MEM("xs", "y"))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +t}}:
      mo.put({EQ("z", "x")}, z, x, y, t, {{==}}, d, mem.other(t, x, y, d))

def mem.fresh(xs: {L}, +n: Nat, +e: {W}, +h: {tt(IDS("n", "xs"))}) -> {ff(MEM("xs", K("e", "n")))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{T.TqTimer{{+ez, +iz}}, +r}}:
      %Equal.sym(Bool, {EQ(K("ez", "iz"), K("e", "n"))}, False{{}}, O.kt.fresh(ez, iz, e, n, {AL(NLT("iz", "n"), IDS("n", "r"), "h")})) : {ff(OR("_", MEM("r", K("e", "n"))))}
      %Equal.sym(Bool, {MEM("r", K("e", "n"))}, False{{}}, mem.fresh(r, n, e, {AR(NLT("iz", "n"), IDS("n", "r"), "h")})) : {ff(OR("False{}", "_"))}
      {{==}}

def mem.app(a: {L}, +b: {L}, +x: {TM}) -> {eqb(MEM(APP("a", "b"), "x"), OR(MEM("a", "x"), MEM("b", "x")))}:
  match a:
    case Nil{{}}:
      {{==}}
    case Con{{+y, +r}}:
      %Equal.sym(Bool, {MEM(APP("r", "b"), "x")}, {OR(MEM("r", "x"), MEM("b", "x"))}, mem.app(r, b, x)) : {eqb(OR(EQ("y", "x"), "_"), OR(OR(EQ("y", "x"), MEM("r", "x")), MEM("b", "x")))}
      O.bo.or_assoc({EQ("y", "x")}, {MEM("r", "x")}, {MEM("b", "x")})

# The expiry loop on a sorted list: each lemma by whether the first timer
# is due

def ex.app.case(d: Bool, +x: {TM}, +t: {L}, +now: {W}, +ih: {{{APP(FI(SP("t")), STO(SP("t")))} == t : {L}}}) -> {{{APP(FI(GO("d", "x", "t")), STO(GO("d", "x", "t")))} == Con{{x, t}} : {L}}}:
  match d:
    case True{{}}:
      %Equal.sym({L}, {APP(FI(SP("t")), STO(SP("t")))}, t, ih) : {{Con{{x, _}} == Con{{x, t}} : {L}}}
      {{==}}
    case False{{}}:
      {{==}}

def ex.app(l: {L}, +now: {W}) -> {{{APP(FI(SP("l")), STO(SP("l")))} == l : {L}}}:
  match l:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      ex.app.case({DUEX("x")}, x, t, now, ex.app(t, now))

def ex.due.case(d: Bool, +x: {TM}, +t: {L}, +now: {W}, +ed: {eqb(DUEX("x"), "d")}, +ih: {tt(DUE("now", FI(SP("t"))))}) -> {tt(DUE("now", FI(GO("d", "x", "t"))))}:
  match d:
    case True{{}}:
      {AI(DUEX("x"), DUE("now", FI(SP("t"))), "ed", "ih")}
    case False{{}}:
      {{==}}

def ex.due(l: {L}, +now: {W}) -> {tt(DUE("now", FI(SP("l"))))}:
  match l:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      ex.due.case({DUEX("x")}, x, t, now, {{==}}, ex.due(t, now))

def ex.ge.case(d: Bool, +y: {TM}, +x: {TM}, +t: {L}, +now: {W}, +g1: {tt(LE("y", "x"))}, +ih: {tt(GE("y", FI(SP("t"))))}) -> {tt(GE("y", FI(GO("d", "x", "t"))))}:
  match d:
    case True{{}}:
      {AI(LE("y", "x"), GE("y", FI(SP("t"))), "g1", "ih")}
    case False{{}}:
      {{==}}

def ex.ge(t: {L}, +y: {TM}, +now: {W}, +g: {tt(GE("y", "t"))}) -> {tt(GE("y", FI(SP("t"))))}:
  match t:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      ex.ge.case({DUEX("x")}, y, x, r, now, {AL(LE("y", "x"), GE("y", "r"), "g")}, ex.ge(r, y, now, {AR(LE("y", "x"), GE("y", "r"), "g")}))

def ex.sorted.case(d: Bool, +x: {TM}, +t: {L}, +now: {W}, +h: {tt(SORT(C("x", "t")))}, +ih: {tt(SORT(FI(SP("t"))))}) -> {tt(SORT(FI(GO("d", "x", "t"))))}:
  match d:
    case True{{}}:
      ls.cons({FI(SP("t"))}, x, ex.ge(t, x, now, ls.all(t, x, h)), ih)
    case False{{}}:
      {{==}}

def ex.sorted(l: {L}, +now: {W}, +h: {tt(SORT("l"))}) -> {tt(SORT(FI(SP("l"))))}:
  match l:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      ex.sorted.case({DUEX("x")}, x, t, now, h, ex.sorted(t, now, ls.tail(x, t, h)))

def ex.later_ge(t: {L}, +x: {TM}, +now: {W}, +hx: {tt("T.TqTime.lt(now, " + EXP("x") + ")")}, +g: {tt(GE("x", "t"))}) -> {tt(LATER("now", "t"))}:
  match t:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      {AI("T.TqTime.lt(now, " + EXP("z") + ")", LATER("now", "r"), "O.tm.lt_le(now, " + EXP("x") + ", " + EXP("z") + ", hx, O.kt.le_time(x, z, " + AL(LE("x", "z"), GE("x", "r"), "g") + "))", "ex.later_ge(r, x, now, hx, " + AR(LE("x", "z"), GE("x", "r"), "g") + ")")}

def ex.later.case(d: Bool, +x: {TM}, +t: {L}, +now: {W}, +ed: {eqb(DUEX("x"), "d")}, +h: {tt(SORT(C("x", "t")))}, +ih: {tt(LATER("now", STO(SP("t"))))}) -> {tt(LATER("now", STO(GO("d", "x", "t"))))}:
  match d:
    case True{{}}:
      ih
    case False{{}}:
      {AI("T.TqTime.lt(now, " + EXP("x") + ")", LATER("now", "t"), "O.tm.not_le(" + EXP("x") + ", now, ed)", "ex.later_ge(t, x, now, O.tm.not_le(" + EXP("x") + ", now, ed), ls.all(t, x, h))")}

def ex.later(l: {L}, +now: {W}, +h: {tt(SORT("l"))}) -> {tt(LATER("now", STO(SP("l"))))}:
  match l:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      ex.later.case({DUEX("x")}, x, t, now, {{==}}, h, ex.later(t, now, ls.tail(x, t, h)))

def ex.st_sorted.case(d: Bool, +x: {TM}, +t: {L}, +now: {W}, +h: {tt(SORT(C("x", "t")))}, +ih: {tt(SORT(STO(SP("t"))))}) -> {tt(SORT(STO(GO("d", "x", "t"))))}:
  match d:
    case True{{}}:
      ih
    case False{{}}:
      h

def ex.st_sorted(l: {L}, +now: {W}, +h: {tt(SORT("l"))}) -> {tt(SORT(STO(SP("l"))))}:
  match l:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      ex.st_sorted.case({DUEX("x")}, x, t, now, h, ex.st_sorted(t, now, ls.tail(x, t, h)))

def ex.st_ids.case(d: Bool, +x: {TM}, +t: {L}, +now: {W}, +n: Nat, +h: {tt(IDS("n", C("x", "t")))}, +ih: {tt(IDS("n", STO(SP("t"))))}) -> {tt(IDS("n", STO(GO("d", "x", "t"))))}:
  match d:
    case True{{}}:
      ih
    case False{{}}:
      h

def ex.st_ids(l: {L}, +now: {W}, +n: Nat, +h: {tt(IDS("n", "l"))}) -> {tt(IDS("n", STO(SP("l"))))}:
  match l:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      ex.st_ids.case({DUEX("x")}, x, t, now, n, h, ex.st_ids(t, now, n, {AR(NLT(ID("x"), "n"), IDS("n", "t"), "h")}))

def never.mem(+q: {L}, +now: {W}, +x: {TM}, +c: {ff(MEM("q", "x"))}) -> {ff(MEM(APP(FI(SP("q")), STO(SP("q"))), "x"))}:
  %Equal.sym({L}, {APP(FI(SP("q")), STO(SP("q")))}, q, ex.app(q, now)) : {ff(MEM("_", "x"))}
  c

def next.from(r: {L}, +x: {TM}, +g: {tt(GE("x", "r"))}) -> {tt(FROM(EXP("x"), "r"))}:
  match r:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r2}}:
      {AI("T.TqTime.le(" + EXP("x") + ", " + EXP("z") + ")", FROM(EXP("x"), "r2"), "O.kt.le_time(x, z, " + AL(LE("x", "z"), GE("x", "r2"), "g") + ")", "next.from(r2, x, " + AR(LE("x", "z"), GE("x", "r2"), "g") + ")")}

# The laws

def Laws.tq_new_valid():
  {{==}}

def Laws.tq_add_valid(tq, e, v):
  match tq:
    case Q.TimerQueue{{+q, +n}}:
      {AI(SORT(INS("q", K("e", "n"))), IDS("1n+n", INS("q", K("e", "n"))), "ins.sorted(q, " + K("e", "n") + ", " + VSPLIT("q", "n", "v")[0] + ")", "ids.ins(q, " + K("e", "n") + ", 1n+n, O.n.lt_self_succ(n), ids.succ(q, n, " + VSPLIT("q", "n", "v")[1] + "))")}

def Laws.tq_delete_valid(tq, x, v):
  match tq:
    case Q.TimerQueue{{+q, +n}}:
      {AI(SORT(REM("q", "x")), IDS("n", REM("q", "x")), "rem.sorted(q, x, " + VSPLIT("q", "n", "v")[0] + ")", "ids.rem(q, x, n, " + VSPLIT("q", "n", "v")[1] + ")")}

def Laws.tq_expire_valid(tq, now, v):
  match tq:
    case Q.TimerQueue{{+q, +n}}:
      {AI(SORT(STO(SP("q"))), IDS("n", STO(SP("q"))), "ex.st_sorted(q, now, " + VSPLIT("q", "n", "v")[0] + ")", "ex.st_ids(q, now, n, " + VSPLIT("q", "n", "v")[1] + ")")}

def Laws.tq_sorted(tq, v):
  match tq:
    case Q.TimerQueue{{+q, +n}}:
      {VSPLIT("q", "n", "v")[0]}

def Laws.tq_new_empty():
  {{==}}

def Laws.tq_add_timer(tq, e):
  match tq:
    case Q.TimerQueue{{q, +n}}:
      {{==}}

def Laws.tq_add_contains(tq, e):
  match tq:
    case Q.TimerQueue{{+q, +n}}:
      %Equal.sym(Bool, {MEM(INS("q", K("e", "n")), K("e", "n"))}, {OR(EQ(K("e", "n"), K("e", "n")), MEM("q", K("e", "n")))}, mem.ins(q, {K("e", "n")}, {K("e", "n")})) : {tt("_")}
      %Equal.sym(Bool, {EQ(K("e", "n"), K("e", "n"))}, True{{}}, O.kt.refl({K("e", "n")})) : {tt(OR("_", MEM("q", K("e", "n"))))}
      {{==}}

def Laws.tq_add_fresh(tq, e, v):
  match tq:
    case Q.TimerQueue{{+q, +n}}:
      mem.fresh(q, n, e, {VSPLIT("q", "n", "v")[1]})

def Laws.tq_add_others(tq, e, x, i):
  match tq x:
    case Q.TimerQueue{{+q, +n}} T.TqTimer{{+ex, +ix}}:
      %Equal.sym(Bool, {MEM(INS("q", K("e", "n")), K("ex", "ix"))}, {OR(EQ(K("e", "n"), K("ex", "ix")), MEM("q", K("ex", "ix")))}, mem.ins(q, {K("e", "n")}, {K("ex", "ix")})) : {eqb("_", MEM("q", K("ex", "ix")))}
      %Equal.sym(Bool, {EQ(K("e", "n"), K("ex", "ix"))}, False{{}}, O.kt.fresh2(e, n, ex, ix, i)) : {eqb(OR("_", MEM("q", K("ex", "ix"))), MEM("q", K("ex", "ix")))}
      {{==}}

def Laws.tq_delete_gone(tq, x):
  match tq:
    case Q.TimerQueue{{+q, n}}:
      mem.gone(q, x)

def Laws.tq_delete_others(tq, x, y, d):
  match tq:
    case Q.TimerQueue{{+q, n}}:
      mem.other(q, x, y, d)

def Laws.tq_next_first(tq):
  match tq:
    case Q.TimerQueue{{Nil{{}}, n}}:
      {{==}}
    case Q.TimerQueue{{Con{{x, r}}, n}}:
      {{==}}

def Laws.tq_next_min(tq, t, v, h):
  match tq:
    case Q.TimerQueue{{Nil{{}}, n}}:
      Empty.absurd({tt(FROM("t", "Nil{}"))}, O.ab.none_some({W}, t, h))
    case Q.TimerQueue{{Con{{T.TqTimer{{+e, +i}}, +r}}, +n}}:
      %Equal.cong(Maybe<&2, {W}>, {W}, m => Maybe.default(&2, {W}, m, e), Some{{e}}, Some{{t}}, h) : {tt(FROM("_", C(K("e", "i"), "r")))}
      {AI("T.TqTime.le(e, e)", FROM("e", "r"), "O.tm.le_refl(e)", "next.from(r, " + K("e", "i") + ", ls.all(r, " + K("e", "i") + ", " + AL(SORT(C(K("e", "i"), "r")), IDS("n", C(K("e", "i"), "r")), "v") + "))")}

def Laws.tq_expire_split(tq, now):
  match tq:
    case Q.TimerQueue{{+q, n}}:
      ex.app(q, now)

def Laws.tq_expire_due(tq, now):
  match tq:
    case Q.TimerQueue{{+q, n}}:
      ex.due(q, now)

def Laws.tq_expire_sorted(tq, now, v):
  match tq:
    case Q.TimerQueue{{+q, +n}}:
      ex.sorted(q, now, {VSPLIT("q", "n", "v")[0]})

def Laws.tq_expire_later(tq, now, v):
  match tq:
    case Q.TimerQueue{{+q, +n}}:
      ex.later(q, now, {VSPLIT("q", "n", "v")[0]})

def Laws.tq_expire_never(tq, now, x, c):
  match tq:
    case Q.TimerQueue{{+q, n}}:
      O.bo.or_false_pair({MEM(FI(SP("q")), "x")}, {MEM(STO(SP("q")), "x")}, Equal.trans(Bool, {OR(MEM(FI(SP("q")), "x"), MEM(STO(SP("q")), "x"))}, {MEM(APP(FI(SP("q")), STO(SP("q"))), "x")}, False{{}}, Equal.sym(Bool, {MEM(APP(FI(SP("q")), STO(SP("q"))), "x")}, {OR(MEM(FI(SP("q")), "x"), MEM(STO(SP("q")), "x"))}, mem.app({FI(SP("q"))}, {STO(SP("q"))}, x)), never.mem(q, now, x, c)))

def or.false_l(a: Bool, -b: Bool, +e: {ff(OR("a", "b"))}) -> {ff("a")}:
  match a:
    case True{{}}:
      Empty.absurd({ff("True{}")}, O.ab.tf(e))
    case False{{}}:
      {{==}}

def Laws.tq_deleted_never_fires(tq, now, x):
  match tq:
    case Q.TimerQueue{{+q, n}}:
      or.false_l({MEM(FI(SP(REM("q", "x"))), "x")}, {MEM(STO(SP(REM("q", "x"))), "x")}, Equal.trans(Bool, {OR(MEM(FI(SP(REM("q", "x"))), "x"), MEM(STO(SP(REM("q", "x"))), "x"))}, {MEM(APP(FI(SP(REM("q", "x"))), STO(SP(REM("q", "x")))), "x")}, False{{}}, Equal.sym(Bool, {MEM(APP(FI(SP(REM("q", "x"))), STO(SP(REM("q", "x")))), "x")}, {OR(MEM(FI(SP(REM("q", "x"))), "x"), MEM(STO(SP(REM("q", "x"))), "x"))}, mem.app({FI(SP(REM("q", "x")))}, {STO(SP(REM("q", "x")))}, x)), never.mem({REM("q", "x")}, now, x, mem.gone(q, x))))

def Laws.tq_issued_add(tq, e, x, i):
  match tq:
    case Q.TimerQueue{{q, +n}}:
      %Equal.sym(Bool, Nat.is_lt({ID("x")}, 1n+n), True{{}}, O.n.lt_succ({ID("x")}, n, i)) : {{(_, Nat.is_lt(n, 1n+n)) == (True{{}}, True{{}}) : Bool & Bool}}
      %Equal.sym(Bool, Nat.is_lt(n, 1n+n), True{{}}, O.n.lt_self_succ(n)) : {{(True{{}}, _) == (True{{}}, True{{}}) : Bool & Bool}}
      {{==}}

def Laws.tq_issued_delete(tq, x):
  match tq:
    case Q.TimerQueue{{q, n}}:
      {{==}}

def Laws.tq_issued_expire(tq, now):
  match tq:
    case Q.TimerQueue{{q, n}}:
      {{==}}

def Laws.tq_vec():
  {{==}}

def Laws.tq_wit():
  {{==}}
'''

if "--check" in sys.argv[1:]:
    with open(out, newline="") as f:
        same = f.read() == text
    print("PROOF.bend is up to date" if same else "PROOF.bend is out of date")
    sys.exit(0 if same else 1)
with open(out, "w", newline="\n") as f:
    f.write(text)
