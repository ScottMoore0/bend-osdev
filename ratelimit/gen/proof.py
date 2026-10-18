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
'''
if "--check" in sys.argv[1:]:
    with open(out, newline="") as f:
        same = f.read() == text
    print("PROOF.bend is up to date" if same else "PROOF.bend is out of date")
    sys.exit(0 if same else 1)
with open(out, "w", newline="\n") as f:
    f.write(text)
