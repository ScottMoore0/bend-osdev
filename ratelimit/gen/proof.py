#!/usr/bin/env python3
"""Generates ratelimit/PROOF.bend, whose lemma statements repeat long terms
(a check on a state with its window matched, for each policy and each
outcome); the shorthands below build them.

Run from anywhere: python3 gen/proof.py rewrites ../PROOF.bend; with
--check it only reports whether the file is up to date (exit 1 if not).
"""
import os, sys
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "PROOF.bend")
S = lambda i,b,w,m: "R.RateLimit{%s, %s, %s, %s}" % (i,b,w,m)
def onx(off, s, now): return "R.RateLimit.check.on(%s, %s, %s)" % (off, s, now)
def st(x): return "R.RateLimitStep.state(%s)" % x
def al(x): return "R.RateLimitStep.allowed(%s)" % x
def held(x): return "R.RateLimit.held(%s)" % x
def burst(x): return "R.RateLimit.burst(%s)" % x
def sup(x): return "R.RateLimit.suppressed(%s)" % x
def rec(x, now): return "R.RateLimit.recent(%s, %s)" % (x, now)
def le(a,b): return "{Nat.is_le(%s, %s) == True{} : Bool}" % (a,b)
def length(x): return "List.length(&2, W.W64, %s)" % x
def keep(i, now, ts): return "R.RateLimit.keep(%s, %s, %s)" % (i, now, ts)
def log(room, i, b, k, m, now): return "R.RateLimit.check.log(%s, %s, %s, %s, %s, %s)" % (room, i, b, k, m, now)
def count(room, i, b, t, n, m): return "R.RateLimit.check.count(%s, %s, %s, %s, %s, %s)" % (room, i, b, t, n, m)
def frame(ins, i, b, t, n, m, now): return "R.RateLimit.check.frame(%s, %s, %s, %s, %s, %s, %s)" % (ins, i, b, t, n, m, now)
def check(s, now): return "R.RateLimit.check(%s, %s)" % (s, now)
L = "List<&2, W.W64>"
LOG = log("room", "i", "b", "kept", "m", "now")
CNT = count("room", "i", "b", "t", "n", "m")
FRM = frame("inside", "i", "b", "t", "n", "m", "now")
SW = S("i", "b", "w", "m")
ON = lambda off: onx(off, SW, "now")
K = keep("i", "now", "ts")
SL = S("i", "b", "R.RateLimitLog{ts}", "m")
SF = S("i", "b", "R.RateLimitFrame{t, n, o}", "m")
INS = "Bool.and(o, R.RateLimit.within(i, now, t))"
ROOMK = "Nat.is_lt(%s, b)" % length(K)
X = "R.RateLimit.run.go(rest, %s)" % st(check("s", "t"))
def runall(x): return "R.RateLimitRun.allowed(%s)" % x
def runst(x): return "R.RateLimitRun.state(%s)" % x
def refs(x): return "R.RateLimit.refusals(%s)" % x
A = al(check("s", "t"))
S1 = st(check("s", "t"))
S0 = S("i","b","w","0n")
RUN0 = 'R.RateLimit.run.go(ts, %s)' % S0
CONAX = "Con{" + A + ", " + runall(X) + "}"

text = f'''import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./ratelimit.bend as R
import ./LAWS.bend as Laws

# Contradictions

def ab.bool(b: Bool) -> Type:
  match b:
    case True{{}}:
      Unit
    case False{{}}:
      Empty

def ab.ft(e: {{False{{}} == True{{}} : Bool}}) -> Empty:
  %Equal.sym(Bool, False{{}}, True{{}}, e) : ab.bool(_)
  Unit{{}}

# Nat

def nat.le_refl(n: Nat) -> {le("n", "n")}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      nat.le_refl(p)

def nat.le_zero(n: Nat) -> {le("0n", "n")}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      {{==}}

def nat.le_succ(a: Nat, b: Nat, e: {le("a", "b")}) -> {le("a", "1n+b")}:
  match a b:
    case 0n _:
      {{==}}
    case 1n+ap 0n:
      Empty.absurd({le("1n+ap", "1n")}, ab.ft(e))
    case 1n+ap 1n+bp:
      nat.le_succ(ap, bp, e)

def nat.le_trans(a: Nat, b: Nat, c: Nat, e: {le("a", "b")}, f: {le("b", "c")}) -> {le("a", "c")}:
  match a b c:
    case 0n _ _:
      nat.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({le("1n+ap", "c")}, ab.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({le("1n+ap", "0n")}, ab.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nat.le_trans(ap, bp, cp, e, f)

# a < b: 1 + a <= b
def nat.lt_succ_le(a: Nat, b: Nat, e: {{Nat.is_lt(a, b) == True{{}} : Bool}}) -> {le("1n+a", "b")}:
  match a b:
    case 0n 0n:
      Empty.absurd({le("1n", "0n")}, ab.ft(e))
    case 0n 1n+bp:
      nat.le_zero(bp)
    case 1n+ap 0n:
      Empty.absurd({le("2n+ap", "0n")}, ab.ft(e))
    case 1n+ap 1n+bp:
      nat.lt_succ_le(ap, bp, e)

def nat.add_zero(a: Nat) -> {{Nat.add(a, 0n) == a : Nat}}:
  match a:
    case 0n:
      {{==}}
    case 1n+p:
      %nat.add_zero(p) : {{1n+Nat.add(p, 0n) == 1n+_ : Nat}}
      {{==}}

def nat.add_succ(a: Nat, -b: Nat) -> {{Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}}:
  match a:
    case 0n:
      {{==}}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), nat.add_succ(p, b)) : {{1n+_ == 2n+Nat.add(p, b) : Nat}}
      {{==}}

# What a step adds: one held event for an allowed one; one refusal for a
# refused one

def rl.plus(a: Bool, n: Nat) -> Nat:
  match a:
    case True{{}}:
      1n+n
    case False{{}}:
      n

def rl.plusr(a: Bool, m: Nat) -> Nat:
  match a:
    case True{{}}:
      m
    case False{{}}:
      1n+m

# The sliding policy, by whether there is room

def log.allowed(room: Bool, -i: W.W64, -b: Nat, -kept: {L}, -m: Nat, -now: W.W64) -> {{{al(LOG)} == room : Bool}}:
  match room:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def log.held(room: Bool, -i: W.W64, +b: Nat, +kept: {L}, -m: Nat, -now: W.W64, eroom: {{Nat.is_lt({length("kept")}, b) == room : Bool}}, hk: {le(length("kept"), "b")}) -> {le(held(st(LOG)), burst(st(LOG)))}:
  match room:
    case True{{}}:
      nat.lt_succ_le({length("kept")}, b, eroom)
    case False{{}}:
      hk

def log.eq(room: Bool, -i: W.W64, -b: Nat, -kept: {L}, -m: Nat, -now: W.W64) -> {{{held(st(LOG))} == rl.plus({al(LOG)}, {length("kept")}) : Nat}}:
  match room:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def log.supp(room: Bool, -i: W.W64, -b: Nat, -kept: {L}, -m: Nat, -now: W.W64) -> {{{sup(st(LOG))} == rl.plusr({al(LOG)}, m) : Nat}}:
  match room:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def log.kept(room: Bool, -i: W.W64, -b: Nat, -kept: {L}, -m: Nat, -now: W.W64) -> {{(R.RateLimit.interval({st(LOG)}), {burst(st(LOG))}) == (i, b) : W.W64 & Nat}}:
  match room:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

# The fixed policy, by whether there is room

def count.allowed(room: Bool, -i: W.W64, -b: Nat, -t: W.W64, -n: Nat, -m: Nat) -> {{{al(CNT)} == room : Bool}}:
  match room:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def count.held(room: Bool, -i: W.W64, +b: Nat, -t: W.W64, +n: Nat, -m: Nat, eroom: {{Nat.is_lt(n, b) == room : Bool}}, hn: {le("n", "b")}) -> {le(held(st(CNT)), burst(st(CNT)))}:
  match room:
    case True{{}}:
      nat.lt_succ_le(n, b, eroom)
    case False{{}}:
      hn

def count.eq(room: Bool, -i: W.W64, -b: Nat, -t: W.W64, -n: Nat, -m: Nat) -> {{{held(st(CNT))} == rl.plus({al(CNT)}, n) : Nat}}:
  match room:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def count.supp(room: Bool, -i: W.W64, -b: Nat, -t: W.W64, -n: Nat, -m: Nat) -> {{{sup(st(CNT))} == rl.plusr({al(CNT)}, m) : Nat}}:
  match room:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def count.kept(room: Bool, -i: W.W64, -b: Nat, -t: W.W64, -n: Nat, -m: Nat) -> {{(R.RateLimit.interval({st(CNT)}), {burst(st(CNT))}) == (i, b) : W.W64 & Nat}}:
  match room:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

# The fixed policy, by whether the window is open

def frame.allowed(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64) -> {{{al(FRM)} == Nat.is_lt(R.RateLimit.recent.frame(inside, n), b) : Bool}}:
  match inside:
    case True{{}}:
      count.allowed(Nat.is_lt(n, b), i, b, t, n, m)
    case False{{}}:
      count.allowed(Nat.is_lt(0n, b), i, b, now, 0n, m)

def frame.held(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64, h: {le("n", "b")}) -> {le(held(st(FRM)), burst(st(FRM)))}:
  match inside:
    case True{{}}:
      count.held(Nat.is_lt(n, b), i, b, t, n, m, {{==}}, h)
    case False{{}}:
      count.held(Nat.is_lt(0n, b), i, b, now, 0n, m, {{==}}, nat.le_zero(b))

def frame.eq(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64) -> {{{held(st(FRM))} == rl.plus({al(FRM)}, R.RateLimit.recent.frame(inside, n)) : Nat}}:
  match inside:
    case True{{}}:
      count.eq(Nat.is_lt(n, b), i, b, t, n, m)
    case False{{}}:
      count.eq(Nat.is_lt(0n, b), i, b, now, 0n, m)

def frame.supp(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64) -> {{{sup(st(FRM))} == rl.plusr({al(FRM)}, m) : Nat}}:
  match inside:
    case True{{}}:
      count.supp(Nat.is_lt(n, b), i, b, t, n, m)
    case False{{}}:
      count.supp(Nat.is_lt(0n, b), i, b, now, 0n, m)

def frame.kept(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64) -> {{(R.RateLimit.interval({st(FRM)}), {burst(st(FRM))}) == (i, b) : W.W64 & Nat}}:
  match inside:
    case True{{}}:
      count.kept(Nat.is_lt(n, b), i, b, t, n, m)
    case False{{}}:
      count.kept(Nat.is_lt(0n, b), i, b, now, 0n, m)

def frame.recent(inside: Bool, +n: Nat) -> {le("R.RateLimit.recent.frame(inside, n)", "n")}:
  match inside:
    case True{{}}:
      nat.le_refl(n)
    case False{{}}:
      nat.le_zero(n)

# The kept times are no more than the times

def put.len(k: Bool, -t: W.W64, +r: {L}, +n: Nat, ih: {le(length("r"), "n")}) -> {le(length("R.RateLimit.keep.put(t, r, k)"), "1n+n")}:
  match k:
    case True{{}}:
      ih
    case False{{}}:
      nat.le_succ({length("r")}, n, ih)

def keep.len_le(+i: W.W64, +now: W.W64, ts: {L}) -> {le(length(K), length("ts"))}:
  match ts:
    case Nil{{}}:
      {{==}}
    case Con{{+t, +rest}}:
      put.len(R.RateLimit.within(i, now, t), t, {keep("i", "now", "rest")}, {length("rest")}, keep.len_le(i, now, rest))

# A check with rate limiting on, for each policy

def gate.on(+i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {{{al(ON("False{}"))} == Nat.is_lt({rec(SW, "now")}, b) : Bool}}:
  match w:
    case R.RateLimitLog{{+ts}}:
      log.allowed({ROOMK}, i, b, {K}, m, now)
    case R.RateLimitFrame{{+t, +n, +o}}:
      frame.allowed({INS}, i, b, t, n, m, now)

def eq.on(+i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {{{held(st(ON("False{}")))} == rl.plus({al(ON("False{}"))}, {rec(SW, "now")}) : Nat}}:
  match w:
    case R.RateLimitLog{{+ts}}:
      log.eq({ROOMK}, i, b, {K}, m, now)
    case R.RateLimitFrame{{+t, +n, +o}}:
      frame.eq({INS}, i, b, t, n, m, now)

# A check either way

def held.on(off: Bool, +i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64, h: {le(held(SW), "b")}) -> {le(held(st(ON("off"))), burst(st(ON("off"))))}:
  match off:
    case True{{}}:
      h
    case False{{}}:
      match w:
        case R.RateLimitLog{{+ts}}:
          log.held({ROOMK}, i, b, {K}, m, now, {{==}}, nat.le_trans({length(K)}, {length("ts")}, b, keep.len_le(i, now, ts), h))
        case R.RateLimitFrame{{+t, +n, +o}}:
          frame.held({INS}, i, b, t, n, m, now, h)

def supp.on(off: Bool, +i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {{{sup(st(ON("off")))} == rl.plusr({al(ON("off"))}, m) : Nat}}:
  match off:
    case True{{}}:
      {{==}}
    case False{{}}:
      match w:
        case R.RateLimitLog{{+ts}}:
          log.supp({ROOMK}, i, b, {K}, m, now)
        case R.RateLimitFrame{{+t, +n, +o}}:
          frame.supp({INS}, i, b, t, n, m, now)

def kept.on(off: Bool, +i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {{(R.RateLimit.interval({st(ON("off"))}), {burst(st(ON("off")))}) == (i, b) : W.W64 & Nat}}:
  match off:
    case True{{}}:
      {{==}}
    case False{{}}:
      match w:
        case R.RateLimitLog{{+ts}}:
          log.kept({ROOMK}, i, b, {K}, m, now)
        case R.RateLimitFrame{{+t, +n, +o}}:
          frame.kept({INS}, i, b, t, n, m, now)

def quiet.on(off: Bool, +i: W.W64, +b: Nat, +w: R.RateLimitWindow, +m: Nat, +now: W.W64, q: {{{rec(SW, "now")} == 0n : Nat}}, hb: {{Nat.is_lt(0n, b) == True{{}} : Bool}}) -> {{{al(ON("off"))} == True{{}} : Bool}}:
  match off:
    case True{{}}:
      {{==}}
    case False{{}}:
      %Equal.sym(Bool, {al(ON("False{}"))}, Nat.is_lt({rec(SW, "now")}, b), gate.on(i, b, w, m, now)) : {{_ == True{{}} : Bool}}
      %Equal.sym(Nat, {rec(SW, "now")}, 0n, q) : {{Nat.is_lt(_, b) == True{{}} : Bool}}
      hb

def keeps.on(off: Bool, +i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {{{al(onx("off", S0, "now"))} == {al(ON("off"))} : Bool}}:
  match off:
    case True{{}}:
      {{==}}
    case False{{}}:
      match w:
        case R.RateLimitLog{{+ts}}:
          %Equal.sym(Bool, {al(log(ROOMK, "i", "b", K, "0n", "now"))}, {ROOMK}, log.allowed({ROOMK}, i, b, {K}, 0n, now)) : {{_ == {al(onx("False{}", SL, "now"))} : Bool}}
          %Equal.sym(Bool, {al(log(ROOMK, "i", "b", K, "m", "now"))}, {ROOMK}, log.allowed({ROOMK}, i, b, {K}, m, now)) : {{{ROOMK} == _ : Bool}}
          {{==}}
        case R.RateLimitFrame{{+t, +n, +o}}:
          %Equal.sym(Bool, {al(frame(INS, "i", "b", "t", "n", "0n", "now"))}, Nat.is_lt(R.RateLimit.recent.frame({INS}, n), b), frame.allowed({INS}, i, b, t, n, 0n, now)) : {{_ == {al(onx("False{}", SF, "now"))} : Bool}}
          %Equal.sym(Bool, {al(frame(INS, "i", "b", "t", "n", "m", "now"))}, Nat.is_lt(R.RateLimit.recent.frame({INS}, n), b), frame.allowed({INS}, i, b, t, n, m, now)) : {{Nat.is_lt(R.RateLimit.recent.frame({INS}, n), b) == _ : Bool}}
          {{==}}

# Steps and runs

def step.bound(+s: R.RateLimit, +now: W.W64, h: {le(held("s"), burst("s"))}) -> {le(held(st(check("s","now"))), burst(st(check("s","now"))))}:
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      held.on(W.W64.is_zero(i), i, b, w, m, now, h)

def step.supp(+s: R.RateLimit, +now: W.W64) -> {{{sup(st(check("s","now")))} == rl.plusr({al(check("s","now"))}, {sup("s")}) : Nat}}:
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      supp.on(W.W64.is_zero(i), i, b, w, m, now)

def run.bound(ts: {L}, +s: R.RateLimit, h: {le(held("s"), burst("s"))}) -> {le(held(runst('R.RateLimit.run.go(ts, s)')), burst(runst('R.RateLimit.run.go(ts, s)')))}:
  match ts:
    case Nil{{}}:
      h
    case Con{{+t, +rest}}:
      run.bound(rest, {S1}, step.bound(s, t, h))

def run.arith(a: Bool, +xs: List<&2, Bool>, +m: Nat) -> {{Nat.add({refs("xs")}, rl.plusr(a, m)) == Nat.add({refs("Con{a, xs}")}, m) : Nat}}:
  match a:
    case True{{}}:
      {{==}}
    case False{{}}:
      nat.add_succ({refs("xs")}, m)

def run.supp(ts: {L}, +s: R.RateLimit) -> {{{sup(runst('R.RateLimit.run.go(ts, s)'))} == Nat.add({refs(runall('R.RateLimit.run.go(ts, s)'))}, {sup("s")}) : Nat}}:
  match ts:
    case Nil{{}}:
      {{==}}
    case Con{{+t, +rest}}:
      %Equal.sym(Nat, {sup(runst(X))}, Nat.add({refs(runall(X))}, {sup(S1)}), run.supp(rest, {S1})) : {{_ == Nat.add({refs(CONAX)}, {sup("s")}) : Nat}}
      %Equal.sym(Nat, {sup(S1)}, rl.plusr({A}, {sup("s")}), step.supp(s, t)) : {{Nat.add({refs(runall(X))}, _) == Nat.add({refs(CONAX)}, {sup("s")}) : Nat}}
      run.arith({A}, {runall(X)}, {sup("s")})

# The laws

def Laws.ratelimit_new(p, i, b):
  match p:
    case R.RateLimitSliding{{}}:
      {{==}}
    case R.RateLimitFixed{{}}:
      {{==}}

def Laws.ratelimit_new_default(i, b):
  {{==}}

def Laws.ratelimit_gate(s, now, h):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      %Equal.sym(Bool, W.W64.is_zero(i), False{{}}, h) : {{{al(ON("_"))} == Nat.is_lt({rec(SW, "now")}, b) : Bool}}
      gate.on(i, b, w, m, now)

def Laws.ratelimit_off(s, now, h):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      %Equal.sym(Bool, W.W64.is_zero(i), True{{}}, h) : {{{ON("_")} == R.RateLimitStep{{{SW}, True{{}}}} : R.RateLimitStep}}
      {{==}}

def Laws.ratelimit_quiet(s, now, q, hb):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      quiet.on(W.W64.is_zero(i), i, b, w, m, now, q, hb)

def Laws.ratelimit_held_allowed(s, now, h, a):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      %a : {{{held(st(check(SW, "now")))} == rl.plus(_, {rec(SW, "now")}) : Nat}}
      %Equal.sym(Bool, W.W64.is_zero(i), False{{}}, h) : {{{held(st(ON("_")))} == rl.plus({al(ON("_"))}, {rec(SW, "now")}) : Nat}}
      eq.on(i, b, w, m, now)

def Laws.ratelimit_held_refused(s, now, h, a):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      %a : {{{held(st(check(SW, "now")))} == rl.plus(_, {rec(SW, "now")}) : Nat}}
      %Equal.sym(Bool, W.W64.is_zero(i), False{{}}, h) : {{{held(st(ON("_")))} == rl.plus({al(ON("_"))}, {rec(SW, "now")}) : Nat}}
      eq.on(i, b, w, m, now)

def Laws.ratelimit_recent_le_held(s, now):
  match s:
    case R.RateLimit{{+i, b, R.RateLimitLog{{+ts}}, m}}:
      keep.len_le(i, now, ts)
    case R.RateLimit{{+i, b, R.RateLimitFrame{{+t, +n, +o}}, m}}:
      frame.recent({INS}, n)

def Laws.ratelimit_held_bound(s, now, h):
  step.bound(s, now, h)

def Laws.ratelimit_run_bound(s, ts, h):
  run.bound(ts, s, h)

def Laws.ratelimit_kept(s, now):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      kept.on(W.W64.is_zero(i), i, b, w, m, now)

def Laws.ratelimit_suppressed_allowed(s, now, a):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      %a : {{{sup(st(check(SW, "now")))} == rl.plusr(_, m) : Nat}}
      supp.on(W.W64.is_zero(i), i, b, w, m, now)

def Laws.ratelimit_suppressed_refused(s, now, a):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      %a : {{{sup(st(check(SW, "now")))} == rl.plusr(_, m) : Nat}}
      supp.on(W.W64.is_zero(i), i, b, w, m, now)

def Laws.ratelimit_report(s):
  match s:
    case R.RateLimit{{i, b, w, m}}:
      {{==}}

def Laws.ratelimit_report_keeps(s, now):
  match s:
    case R.RateLimit{{+i, +b, +w, +m}}:
      keeps.on(W.W64.is_zero(i), i, b, w, m, now)

def Laws.ratelimit_run_suppressed(s, ts):
  match s:
    case R.RateLimit{{+i, +b, +w, m}}:
      %nat.add_zero({refs(runall(RUN0))}) : {{{sup(runst(RUN0))} == _ : Nat}}
      run.supp(ts, {S0})

def Laws.ratelimit_wit():
  {{==}}

def Laws.ratelimit_vec_sliding():
  {{==}}

def Laws.ratelimit_vec_policies():
  {{==}}

def Laws.ratelimit_vec_report():
  {{==}}

def Laws.ratelimit_vec_printk():
  {{==}}
'''
# The window law over a run (not an f-string: no long repeated terms)
text += r'''
# The window law over a run, for the sliding policy. At a fixed time now,
# with every time of the run at most the next and the last at most now:
# what the state's log holds against now (RateLimit.recent) grows by one at
# each allowed event within the window ending at now, and by nothing
# otherwise. Keeping only the times within the window at an earlier time t
# drops none that are within it at now (wd.mono: now - u < interval and
# u <= t <= now give t - u < interval), so the allowed events within the
# window at now are what the final state holds against now: at most burst.

def wd.sliding(s: R.RateLimit) -> Bool:
  match s:
    case R.RateLimit{i, b, R.RateLimitLog{ts}, m}:
      True{}
    case R.RateLimit{i, b, R.RateLimitFrame{t, n, o}, m}:
      False{}

def wd.log(s: R.RateLimit) -> List<&2, W.W64>:
  match s:
    case R.RateLimit{i, b, R.RateLimitLog{ts}, m}:
      ts
    case R.RateLimit{i, b, R.RateLimitFrame{t, n, o}, m}:
      Nil{}

def wd.all_le(xs: List<&2, W.W64>, +t: W.W64) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(W.W64.is_le(x, t), wd.all_le(rest, t))

def wd.bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def wd.fst(p: W.W64 & Nat) -> W.W64:
  (x, y) = p
  x

def wd.snd(p: W.W64 & Nat) -> Nat:
  (x, y) = p
  y

# Bool

def wd.and_l(x: Bool, -y: Bool, +e: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

def wd.and_r(x: Bool, -y: Bool, +e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == True{} : Bool}, ab.ft(e))

def wd.and_intro(-x: Bool, -y: Bool, +ex: {x == True{} : Bool}, +ey: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

# Nat

def wd.succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def wd.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      wd.succ_cong(Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), wd.add_assoc(p, b, c))

def wd.add_one(+n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  Equal.trans(Nat, Nat.add(n, 1n), 1n+Nat.add(n, 0n), 1n+n, nat.add_succ(n, 0n), wd.succ_cong(Nat.add(n, 0n), n, nat.add_zero(n)))

def wd.le_lt(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.ft(h2))
    case 0n 0n 1n+zp:
      {==}
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, ab.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, ab.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      wd.le_lt(xp, yp, zp, h1, h2)

def wd.le_rw2(-x: Nat, -y: Nat, -y2: Nat, e: {y == y2 : Nat}, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, y2) == True{} : Bool}:
  %e : {Nat.is_le(x, _) == True{} : Bool}
  h

# t <= n: t - u <= n - u
def wd.sub_mono(t: Nat, n: Nat, u: Nat, h: {Nat.is_le(t, n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(t, u), Nat.sub(n, u)) == True{} : Bool}:
  match t n:
    case 0n _:
      nat.le_zero(Nat.sub(n, u))
    case 1n+tp 0n:
      Empty.absurd({Nat.is_le(Nat.sub(1n+tp, u), Nat.sub(0n, u)) == True{} : Bool}, ab.ft(h))
    case 1n+ +tp 1n+ +np:
      match u:
        case 0n:
          h
        case 1n+up:
          wd.sub_mono(tp, np, up, h)

def wd.eq_zero(x: Nat, e: {Nat.is_eq(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, ab.ft(e))

def wd.not_lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Times, through word64's laws

def wd.le_nat(+a: W.W64, +b: W.W64, h: {W.W64.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(W.W64.to_nat(a), W.W64.to_nat(b)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(W.W64.to_nat(a), W.W64.to_nat(b)), W.W64.is_le(a, b), True{}, Equal.sym(Bool, W.W64.is_le(a, b), Nat.is_le(W.W64.to_nat(a), W.W64.to_nat(b)), WL.le_value(a, b)), h)

def wd.le_w(+a: W.W64, +b: W.W64, h: {Nat.is_le(W.W64.to_nat(a), W.W64.to_nat(b)) == True{} : Bool}) -> {W.W64.is_le(a, b) == True{} : Bool}:
  Equal.trans(Bool, W.W64.is_le(a, b), Nat.is_le(W.W64.to_nat(a), W.W64.to_nat(b)), True{}, WL.le_value(a, b), h)

def wd.le_trans_w(+a: W.W64, +b: W.W64, +c: W.W64, h1: {W.W64.is_le(a, b) == True{} : Bool}, h2: {W.W64.is_le(b, c) == True{} : Bool}) -> {W.W64.is_le(a, c) == True{} : Bool}:
  wd.le_w(a, c, nat.le_trans(W.W64.to_nat(a), W.W64.to_nat(b), W.W64.to_nat(c), wd.le_nat(a, b, h1), wd.le_nat(b, c, h2)))

def wd.le_refl_w(+a: W.W64) -> {W.W64.is_le(a, a) == True{} : Bool}:
  wd.le_w(a, a, nat.le_refl(W.W64.to_nat(a)))

# u <= now: u is within the window ending at now when now - u < interval
def wd.within_nat(+i: W.W64, +now: W.W64, +u: W.W64, h: {Nat.is_le(W.W64.to_nat(u), W.W64.to_nat(now)) == True{} : Bool}) -> {R.RateLimit.within(i, now, u) == Nat.is_lt(Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i)) : Bool}:
  Equal.trans(Bool, W.W64.is_lt(W.W64.sub(now, u), i), Nat.is_lt(W.W64.to_nat(W.W64.sub(now, u)), W.W64.to_nat(i)), Nat.is_lt(Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i)), WL.lt_value(W.W64.sub(now, u), i), Equal.cong(Nat, Bool, x => Nat.is_lt(x, W.W64.to_nat(i)), W.W64.to_nat(W.W64.sub(now, u)), Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), WL.sub_value(now, u, h)))

# u <= t <= now: within the window at now, within it at t
def wd.mono(+i: W.W64, +u: W.W64, +t: W.W64, +now: W.W64, hu: {W.W64.is_le(u, t) == True{} : Bool}, ht: {W.W64.is_le(t, now) == True{} : Bool}, e: {R.RateLimit.within(i, now, u) == True{} : Bool}) -> {R.RateLimit.within(i, t, u) == True{} : Bool}:
  +ut = wd.le_nat(u, t, hu)
  +tn = wd.le_nat(t, now, ht)
  +e2 = Equal.trans(Bool, Nat.is_lt(Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i)), R.RateLimit.within(i, now, u), True{}, Equal.sym(Bool, R.RateLimit.within(i, now, u), Nat.is_lt(Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i)), wd.within_nat(i, now, u, nat.le_trans(W.W64.to_nat(u), W.W64.to_nat(t), W.W64.to_nat(now), ut, tn))), e)
  Equal.trans(Bool, R.RateLimit.within(i, t, u), Nat.is_lt(Nat.sub(W.W64.to_nat(t), W.W64.to_nat(u)), W.W64.to_nat(i)), True{}, wd.within_nat(i, t, u, ut), wd.le_lt(Nat.sub(W.W64.to_nat(t), W.W64.to_nat(u)), Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i), wd.sub_mono(W.W64.to_nat(t), W.W64.to_nat(now), W.W64.to_nat(u), tn), e2))

# outside the window at t: outside it at now
def wd.out.go(w: Bool, +i: W.W64, +u: W.W64, +t: W.W64, +now: W.W64, hu: {W.W64.is_le(u, t) == True{} : Bool}, ht: {W.W64.is_le(t, now) == True{} : Bool}, ew: {R.RateLimit.within(i, now, u) == w : Bool}, e: {R.RateLimit.within(i, t, u) == False{} : Bool}) -> {R.RateLimit.within(i, now, u) == False{} : Bool}:
  match w:
    case True{}:
      Empty.absurd({R.RateLimit.within(i, now, u) == False{} : Bool}, ab.ft(Equal.trans(Bool, False{}, R.RateLimit.within(i, t, u), True{}, Equal.sym(Bool, R.RateLimit.within(i, t, u), False{}, e), wd.mono(i, u, t, now, hu, ht, ew))))
    case False{}:
      ew

def wd.out(+i: W.W64, +u: W.W64, +t: W.W64, +now: W.W64, hu: {W.W64.is_le(u, t) == True{} : Bool}, ht: {W.W64.is_le(t, now) == True{} : Bool}, e: {R.RateLimit.within(i, t, u) == False{} : Bool}) -> {R.RateLimit.within(i, now, u) == False{} : Bool}:
  wd.out.go(R.RateLimit.within(i, now, u), i, u, t, now, hu, ht, {==}, e)

# with a zero interval nothing is within the window
def wd.zero_within(+i: W.W64, +now: W.W64, +u: W.W64, e: {W.W64.is_zero(i) == True{} : Bool}) -> {R.RateLimit.within(i, now, u) == False{} : Bool}:
  +ez = wd.eq_zero(W.W64.to_nat(i), Equal.trans(Bool, Nat.is_eq(W.W64.to_nat(i), 0n), W.W64.is_eq(i, W.W64.zero()), True{}, Equal.sym(Bool, W.W64.is_eq(i, W.W64.zero()), Nat.is_eq(W.W64.to_nat(i), W.W64.to_nat(W.W64.zero())), WL.eq_value(i, W.W64.zero())), e))
  Equal.trans(Bool, R.RateLimit.within(i, now, u), Nat.is_lt(W.W64.to_nat(W.W64.sub(now, u)), W.W64.to_nat(i)), False{}, WL.lt_value(W.W64.sub(now, u), i), Equal.trans(Bool, Nat.is_lt(W.W64.to_nat(W.W64.sub(now, u)), W.W64.to_nat(i)), Nat.is_lt(W.W64.to_nat(W.W64.sub(now, u)), 0n), False{}, Equal.cong(Nat, Bool, x => Nat.is_lt(W.W64.to_nat(W.W64.sub(now, u)), x), W.W64.to_nat(i), 0n, ez), wd.not_lt_zero(W.W64.to_nat(W.W64.sub(now, u)))))

# Keeping the times within the window at t (all of them at most t, t at
# most now) changes nothing against now

def wd.kc.put(w: Bool, -u: W.W64, +x: List<&2, W.W64>, +y: List<&2, W.W64>, ih: {List.length(&2, W.W64, x) == List.length(&2, W.W64, y) : Nat}) -> {List.length(&2, W.W64, R.RateLimit.keep.put(u, x, w)) == List.length(&2, W.W64, R.RateLimit.keep.put(u, y, w)) : Nat}:
  match w:
    case True{}:
      wd.succ_cong(List.length(&2, W.W64, x), List.length(&2, W.W64, y), ih)
    case False{}:
      ih

def wd.kc.go(w1: Bool, +i: W.W64, +u: W.W64, +t: W.W64, +now: W.W64, +r: List<&2, W.W64>, hu: {W.W64.is_le(u, t) == True{} : Bool}, ht: {W.W64.is_le(t, now) == True{} : Bool}, e1: {R.RateLimit.within(i, t, u) == w1 : Bool}, ih: {List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, r))) == List.length(&2, W.W64, R.RateLimit.keep(i, now, r)) : Nat}) -> {List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep.put(u, R.RateLimit.keep(i, t, r), w1))) == List.length(&2, W.W64, R.RateLimit.keep.put(u, R.RateLimit.keep(i, now, r), R.RateLimit.within(i, now, u))) : Nat}:
  match w1:
    case True{}:
      wd.kc.put(R.RateLimit.within(i, now, u), u, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, r)), R.RateLimit.keep(i, now, r), ih)
    case False{}:
      %Equal.sym(Bool, R.RateLimit.within(i, now, u), False{}, wd.out(i, u, t, now, hu, ht, e1)) : {List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, r))) == List.length(&2, W.W64, R.RateLimit.keep.put(u, R.RateLimit.keep(i, now, r), _)) : Nat}
      ih

def wd.kc(ls: List<&2, W.W64>, +i: W.W64, +t: W.W64, +now: W.W64, +ha: {wd.all_le(ls, t) == True{} : Bool}, +ht: {W.W64.is_le(t, now) == True{} : Bool}) -> {List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls))) == List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{+u, +r}:
      wd.kc.go(R.RateLimit.within(i, t, u), i, u, t, now, r, wd.and_l(W.W64.is_le(u, t), wd.all_le(r, t), ha), ht, {==}, wd.kc(r, i, t, now, wd.and_r(W.W64.is_le(u, t), wd.all_le(r, t), ha), ht))

# keeping keeps every time at most t
def wd.ka.put(w: Bool, +u: W.W64, +x: List<&2, W.W64>, +t: W.W64, hu: {W.W64.is_le(u, t) == True{} : Bool}, hx: {wd.all_le(x, t) == True{} : Bool}) -> {wd.all_le(R.RateLimit.keep.put(u, x, w), t) == True{} : Bool}:
  match w:
    case True{}:
      wd.and_intro(W.W64.is_le(u, t), wd.all_le(x, t), hu, hx)
    case False{}:
      hx

def wd.ka(ls: List<&2, W.W64>, +i: W.W64, +q: W.W64, +t: W.W64, +ha: {wd.all_le(ls, t) == True{} : Bool}) -> {wd.all_le(R.RateLimit.keep(i, q, ls), t) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+u, +r}:
      wd.ka.put(R.RateLimit.within(i, q, u), u, R.RateLimit.keep(i, q, r), t, wd.and_l(W.W64.is_le(u, t), wd.all_le(r, t), ha), wd.ka(r, i, q, t, wd.and_r(W.W64.is_le(u, t), wd.all_le(r, t), ha)))

def wd.al_trans(xs: List<&2, W.W64>, +t: W.W64, +t2: W.W64, +h: {wd.all_le(xs, t) == True{} : Bool}, +ht: {W.W64.is_le(t, t2) == True{} : Bool}) -> {wd.all_le(xs, t2) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      wd.and_intro(W.W64.is_le(x, t2), wd.all_le(r, t2), wd.le_trans_w(x, t, t2, wd.and_l(W.W64.is_le(x, t), wd.all_le(r, t), h), ht), wd.al_trans(r, t, t2, wd.and_r(W.W64.is_le(x, t), wd.all_le(r, t), h), ht))

# One check of a sliding state: what it holds against now afterwards

def wd.st.w(w: Bool, -t: W.W64, +x: List<&2, W.W64>, +n: Nat, e: {List.length(&2, W.W64, x) == n : Nat}) -> {List.length(&2, W.W64, R.RateLimit.keep.put(t, x, w)) == Nat.add(n, wd.bit(w)) : Nat}:
  match w:
    case True{}:
      Equal.trans(Nat, 1n+List.length(&2, W.W64, x), 1n+n, Nat.add(n, 1n), wd.succ_cong(List.length(&2, W.W64, x), n, e), Equal.sym(Nat, Nat.add(n, 1n), 1n+n, wd.add_one(n)))
    case False{}:
      Equal.trans(Nat, List.length(&2, W.W64, x), n, Nat.add(n, 0n), e, Equal.sym(Nat, Nat.add(n, 0n), n, nat.add_zero(n)))

def wd.st.room(room: Bool, +i: W.W64, +b: Nat, +ls: List<&2, W.W64>, +m: Nat, +t: W.W64, +now: W.W64, kc: {List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls))) == List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)) : Nat}) -> {R.RateLimit.recent(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, R.RateLimit.keep(i, t, ls), m, t)), now) == Nat.add(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), wd.bit(Bool.and(R.RateLimitStep.allowed(R.RateLimit.check.log(room, i, b, R.RateLimit.keep(i, t, ls), m, t)), R.RateLimit.within(i, now, t)))) : Nat}:
  match room:
    case True{}:
      wd.st.w(R.RateLimit.within(i, now, t), t, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls)), List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), kc)
    case False{}:
      Equal.trans(Nat, List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls))), List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), Nat.add(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), 0n), kc, Equal.sym(Nat, Nat.add(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), 0n), List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), nat.add_zero(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)))))

def wd.st.off(off: Bool, +i: W.W64, +b: Nat, +ls: List<&2, W.W64>, +m: Nat, +t: W.W64, +now: W.W64, e: {W.W64.is_zero(i) == off : Bool}, kc: {List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls))) == List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)) : Nat}) -> {R.RateLimit.recent(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, R.RateLimitLog{ls}, m}, t)), now) == Nat.add(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), wd.bit(Bool.and(R.RateLimitStep.allowed(R.RateLimit.check.on(off, R.RateLimit{i, b, R.RateLimitLog{ls}, m}, t)), R.RateLimit.within(i, now, t)))) : Nat}:
  match off:
    case True{}:
      +c = List.length(&2, W.W64, R.RateLimit.keep(i, now, ls))
      Equal.trans(Nat, c, Nat.add(c, 0n), Nat.add(c, wd.bit(R.RateLimit.within(i, now, t))), Equal.sym(Nat, Nat.add(c, 0n), c, nat.add_zero(c)), Equal.cong(Bool, Nat, x => Nat.add(c, wd.bit(x)), False{}, R.RateLimit.within(i, now, t), Equal.sym(Bool, R.RateLimit.within(i, now, t), False{}, wd.zero_within(i, now, t, e))))
    case False{}:
      wd.st.room(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, t, ls)), b), i, b, ls, m, t, now, kc)

def wd.st(+s: R.RateLimit, +t: W.W64, +now: W.W64, hsl: {wd.sliding(s) == True{} : Bool}, ha: {wd.all_le(wd.log(s), t) == True{} : Bool}, ht: {W.W64.is_le(t, now) == True{} : Bool}) -> {R.RateLimit.recent(R.RateLimitStep.state(R.RateLimit.check(s, t)), now) == Nat.add(R.RateLimit.recent(s, now), wd.bit(Bool.and(R.RateLimitStep.allowed(R.RateLimit.check(s, t)), R.RateLimit.within(R.RateLimit.interval(s), now, t)))) : Nat}:
  match s:
    case R.RateLimit{+i, +b, R.RateLimitLog{+ls}, +m}:
      wd.st.off(W.W64.is_zero(i), i, b, ls, m, t, now, {==}, wd.kc(ls, i, t, now, ha, ht))
    case R.RateLimit{i, b, R.RateLimitFrame{t2, n, o}, m}:
      Empty.absurd({R.RateLimit.recent(R.RateLimitStep.state(R.RateLimit.check(R.RateLimit{i, b, R.RateLimitFrame{t2, n, o}, m}, t)), now) == Nat.add(R.RateLimit.recent(R.RateLimit{i, b, R.RateLimitFrame{t2, n, o}, m}, now), wd.bit(Bool.and(R.RateLimitStep.allowed(R.RateLimit.check(R.RateLimit{i, b, R.RateLimitFrame{t2, n, o}, m}, t)), R.RateLimit.within(i, now, t)))) : Nat}, ab.ft(hsl))

# One check keeps the state sliding, its log's times at most t

def wd.pr.room(room: Bool, +i: W.W64, +b: Nat, +ls: List<&2, W.W64>, +m: Nat, +t: W.W64, +ha: {wd.all_le(ls, t) == True{} : Bool}) -> {Bool.and(wd.sliding(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, R.RateLimit.keep(i, t, ls), m, t))), wd.all_le(wd.log(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, R.RateLimit.keep(i, t, ls), m, t))), t)) == True{} : Bool}:
  match room:
    case True{}:
      wd.and_intro(W.W64.is_le(t, t), wd.all_le(R.RateLimit.keep(i, t, ls), t), wd.le_refl_w(t), wd.ka(ls, i, t, t, ha))
    case False{}:
      wd.ka(ls, i, t, t, ha)

def wd.pr.off(off: Bool, +i: W.W64, +b: Nat, +ls: List<&2, W.W64>, +m: Nat, +t: W.W64, +ha: {wd.all_le(ls, t) == True{} : Bool}) -> {Bool.and(wd.sliding(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, R.RateLimitLog{ls}, m}, t))), wd.all_le(wd.log(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, R.RateLimitLog{ls}, m}, t))), t)) == True{} : Bool}:
  match off:
    case True{}:
      ha
    case False{}:
      wd.pr.room(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, t, ls)), b), i, b, ls, m, t, ha)

def wd.pr(+s: R.RateLimit, +t: W.W64, hsl: {wd.sliding(s) == True{} : Bool}, ha: {wd.all_le(wd.log(s), t) == True{} : Bool}) -> {Bool.and(wd.sliding(R.RateLimitStep.state(R.RateLimit.check(s, t))), wd.all_le(wd.log(R.RateLimitStep.state(R.RateLimit.check(s, t))), t)) == True{} : Bool}:
  match s:
    case R.RateLimit{+i, +b, R.RateLimitLog{+ls}, +m}:
      wd.pr.off(W.W64.is_zero(i), i, b, ls, m, t, ha)
    case R.RateLimit{i, b, R.RateLimitFrame{t2, n, o}, m}:
      Empty.absurd({Bool.and(wd.sliding(R.RateLimitStep.state(R.RateLimit.check(R.RateLimit{i, b, R.RateLimitFrame{t2, n, o}, m}, t))), wd.all_le(wd.log(R.RateLimitStep.state(R.RateLimit.check(R.RateLimit{i, b, R.RateLimitFrame{t2, n, o}, m}, t))), t)) == True{} : Bool}, ab.ft(hsl))

# An allowed time within the window at now adds one to the window's count

def wd.pw(w: Bool, -t: W.W64, +k: List<&2, W.W64>) -> {List.length(&2, W.W64, R.RateLimit.keep.put(t, k, w)) == Nat.add(wd.bit(w), List.length(&2, W.W64, k)) : Nat}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def wd.put_w(a: Bool, +i: W.W64, +now: W.W64, +t: W.W64, +x: List<&2, W.W64>) -> {R.RateLimit.in_window(i, now, R.RateLimit.allowed_times.put(a, t, x)) == Nat.add(wd.bit(Bool.and(a, R.RateLimit.within(i, now, t))), R.RateLimit.in_window(i, now, x)) : Nat}:
  match a:
    case True{}:
      wd.pw(R.RateLimit.within(i, now, t), t, R.RateLimit.keep(i, now, x))
    case False{}:
      {==}

# interval and burst are kept (ratelimit_kept), over a step and a run

def wd.int(+s: R.RateLimit, +t: W.W64) -> {R.RateLimit.interval(R.RateLimitStep.state(R.RateLimit.check(s, t))) == R.RateLimit.interval(s) : W.W64}:
  Equal.cong(W.W64 & Nat, W.W64, p => wd.fst(p), (R.RateLimit.interval(R.RateLimitStep.state(R.RateLimit.check(s, t))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check(s, t)))), (R.RateLimit.interval(s), R.RateLimit.burst(s)), Laws.ratelimit_kept(s, t))

def wd.bur(+s: R.RateLimit, +t: W.W64) -> {R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check(s, t))) == R.RateLimit.burst(s) : Nat}:
  Equal.cong(W.W64 & Nat, Nat, p => wd.snd(p), (R.RateLimit.interval(R.RateLimitStep.state(R.RateLimit.check(s, t))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check(s, t)))), (R.RateLimit.interval(s), R.RateLimit.burst(s)), Laws.ratelimit_kept(s, t))

def wd.run_burst(ts: List<&2, W.W64>, +s: R.RateLimit) -> {R.RateLimit.burst(R.RateLimitRun.state(R.RateLimit.run.go(ts, s))) == R.RateLimit.burst(s) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      Equal.trans(Nat, R.RateLimit.burst(R.RateLimitRun.state(R.RateLimit.run.go(rest, R.RateLimitStep.state(R.RateLimit.check(s, t))))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check(s, t))), R.RateLimit.burst(s), wd.run_burst(rest, R.RateLimitStep.state(R.RateLimit.check(s, t))), wd.bur(s, t))

# the next time after a sorted list's head is at most now
def wd.next_le(rest: List<&2, W.W64>, +now: W.W64, +hs: {R.RateLimit.sorted_upto(rest, now) == True{} : Bool}) -> {W.W64.is_le(R.RateLimit.sorted_upto.next(rest, now), now) == True{} : Bool}:
  match rest:
    case Nil{}:
      wd.le_refl_w(now)
    case Con{+t, +r}:
      wd.le_trans_w(t, R.RateLimit.sorted_upto.next(r, now), now, wd.and_l(W.W64.is_le(t, R.RateLimit.sorted_upto.next(r, now)), R.RateLimit.sorted_upto(r, now), hs), wd.next_le(r, now, wd.and_r(W.W64.is_le(t, R.RateLimit.sorted_upto.next(r, now)), R.RateLimit.sorted_upto(r, now), hs)))

# The run: what the state holds against now, plus the allowed times within
# the window at now, is what the final state holds against now
def wd.run(ts: List<&2, W.W64>, +s: R.RateLimit, +now: W.W64, +hsl: {wd.sliding(s) == True{} : Bool}, +hs: {R.RateLimit.sorted_upto(ts, now) == True{} : Bool}, +ha: {wd.all_le(wd.log(s), R.RateLimit.sorted_upto.next(ts, now)) == True{} : Bool}) -> {Nat.add(R.RateLimit.recent(s, now), R.RateLimit.in_window(R.RateLimit.interval(s), now, R.RateLimit.allowed_times(ts, R.RateLimitRun.allowed(R.RateLimit.run.go(ts, s))))) == R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(ts, s)), now) : Nat}:
  match ts:
    case Nil{}:
      nat.add_zero(R.RateLimit.recent(s, now))
    case Con{+t, +rest}:
      +s1 = R.RateLimitStep.state(R.RateLimit.check(s, t))
      +a = R.RateLimitStep.allowed(R.RateLimit.check(s, t))
      +x = R.RateLimit.allowed_times(rest, R.RateLimitRun.allowed(R.RateLimit.run.go(rest, s1)))
      +iv = R.RateLimit.interval(s)
      +nx = R.RateLimit.sorted_upto.next(rest, now)
      +htn = wd.and_l(W.W64.is_le(t, nx), R.RateLimit.sorted_upto(rest, now), hs)
      +hs1 = wd.and_r(W.W64.is_le(t, nx), R.RateLimit.sorted_upto(rest, now), hs)
      +ht = wd.le_trans_w(t, nx, now, htn, wd.next_le(rest, now, hs1))
      +pr = wd.pr(s, t, hsl, ha)
      +hsl1 = wd.and_l(wd.sliding(s1), wd.all_le(wd.log(s1), t), pr)
      +ha1 = wd.al_trans(wd.log(s1), t, nx, wd.and_r(wd.sliding(s1), wd.all_le(wd.log(s1), t), pr), htn)
      +bt = wd.bit(Bool.and(a, R.RateLimit.within(iv, now, t)))
      +rs = R.RateLimit.recent(s, now)
      +r1 = R.RateLimit.recent(s1, now)
      Equal.trans(Nat, Nat.add(rs, R.RateLimit.in_window(iv, now, R.RateLimit.allowed_times.put(a, t, x))), Nat.add(rs, Nat.add(bt, R.RateLimit.in_window(iv, now, x))), R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(rest, s1)), now), Equal.cong(Nat, Nat, v => Nat.add(rs, v), R.RateLimit.in_window(iv, now, R.RateLimit.allowed_times.put(a, t, x)), Nat.add(bt, R.RateLimit.in_window(iv, now, x)), wd.put_w(a, iv, now, t, x)), Equal.trans(Nat, Nat.add(rs, Nat.add(bt, R.RateLimit.in_window(iv, now, x))), Nat.add(Nat.add(rs, bt), R.RateLimit.in_window(iv, now, x)), R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(rest, s1)), now), Equal.sym(Nat, Nat.add(Nat.add(rs, bt), R.RateLimit.in_window(iv, now, x)), Nat.add(rs, Nat.add(bt, R.RateLimit.in_window(iv, now, x))), wd.add_assoc(rs, bt, R.RateLimit.in_window(iv, now, x))), Equal.trans(Nat, Nat.add(Nat.add(rs, bt), R.RateLimit.in_window(iv, now, x)), Nat.add(r1, R.RateLimit.in_window(iv, now, x)), R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(rest, s1)), now), Equal.cong(Nat, Nat, v => Nat.add(v, R.RateLimit.in_window(iv, now, x)), Nat.add(rs, bt), r1, Equal.sym(Nat, r1, Nat.add(rs, bt), wd.st(s, t, now, hsl, ha, ht))), Equal.trans(Nat, Nat.add(r1, R.RateLimit.in_window(iv, now, x)), Nat.add(r1, R.RateLimit.in_window(R.RateLimit.interval(s1), now, x)), R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(rest, s1)), now), Equal.cong(W.W64, Nat, v => Nat.add(r1, R.RateLimit.in_window(v, now, x)), iv, R.RateLimit.interval(s1), Equal.sym(W.W64, R.RateLimit.interval(s1), iv, wd.int(s, t))), wd.run(rest, s1, now, hsl1, hs1, ha1)))))

def Laws.ratelimit_run_window(i, b, ts, now, h):
  +s0 = R.RateLimit.new(i, b)
  +fin = R.RateLimitRun.state(R.RateLimit.run.go(ts, s0))
  +e = wd.run(ts, s0, now, {==}, h, {==})
  %Equal.sym(Nat, R.RateLimit.in_window(i, now, R.RateLimit.allowed_times(ts, R.RateLimitRun.allowed(R.RateLimit.run.go(ts, s0)))), R.RateLimit.recent(fin, now), e) : {Nat.is_le(_, U32.to_nat(b)) == True{} : Bool}
  nat.le_trans(R.RateLimit.recent(fin, now), R.RateLimit.held(fin), U32.to_nat(b), Laws.ratelimit_recent_le_held(fin, now), wd.le_rw2(R.RateLimit.held(fin), R.RateLimit.burst(fin), U32.to_nat(b), wd.run_burst(ts, s0), Laws.ratelimit_run_bound(s0, ts, nat.le_zero(U32.to_nat(b)))))

def Laws.ratelimit_window_wit():
  {==}

def Laws.ratelimit_vec_window():
  {==}
'''

if "--check" in sys.argv[1:]:
    with open(out, newline="") as f:
        same = f.read() == text
    print("PROOF.bend is up to date" if same else "PROOF.bend is out of date")
    sys.exit(0 if same else 1)
with open(out, "w", newline="\n") as f:
    f.write(text)
