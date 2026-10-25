import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./ratelimit.bend as R
import ./LAWS.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

# Contradictions

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

# Nat

def nat.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.le_succ(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, ab.ft(e))
    case 1n+ap 1n+bp:
      nat.le_succ(ap, bp, e)

# a < b: 1 + a <= b
def nat.lt_succ_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ab.ft(e))
    case 0n 1n+bp:
      nat.le_zero(bp)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(2n+ap, 0n) == True{} : Bool}, ab.ft(e))
    case 1n+ap 1n+bp:
      nat.lt_succ_le(ap, bp, e)

# What a step adds: one held event for an allowed one; one refusal for a
# refused one

def rl.plus(a: Bool, n: Nat) -> Nat:
  match a:
    case True{}:
      1n+n
    case False{}:
      n

def rl.plusr(a: Bool, m: Nat) -> Nat:
  match a:
    case True{}:
      m
    case False{}:
      1n+m

# The sliding policy, by whether there is room

def log.allowed(room: Bool, -i: W.W64, -b: Nat, -kept: List<&2, W.W64>, -m: Nat, -now: W.W64) -> {R.RateLimitStep.allowed(R.RateLimit.check.log(room, i, b, kept, m, now)) == room : Bool}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

def log.held(room: Bool, -i: W.W64, +b: Nat, +kept: List<&2, W.W64>, -m: Nat, -now: W.W64, eroom: {Nat.is_lt(List.length(&2, W.W64, kept), b) == room : Bool}, hk: {Nat.is_le(List.length(&2, W.W64, kept), b) == True{} : Bool}) -> {Nat.is_le(R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, kept, m, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, kept, m, now)))) == True{} : Bool}:
  match room:
    case True{}:
      nat.lt_succ_le(List.length(&2, W.W64, kept), b, eroom)
    case False{}:
      hk

def log.eq(room: Bool, -i: W.W64, -b: Nat, -kept: List<&2, W.W64>, -m: Nat, -now: W.W64) -> {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, kept, m, now))) == rl.plus(R.RateLimitStep.allowed(R.RateLimit.check.log(room, i, b, kept, m, now)), List.length(&2, W.W64, kept)) : Nat}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

def log.supp(room: Bool, -i: W.W64, -b: Nat, -kept: List<&2, W.W64>, -m: Nat, -now: W.W64) -> {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, kept, m, now))) == rl.plusr(R.RateLimitStep.allowed(R.RateLimit.check.log(room, i, b, kept, m, now)), m) : Nat}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

def log.kept(room: Bool, -i: W.W64, -b: Nat, -kept: List<&2, W.W64>, -m: Nat, -now: W.W64) -> {(R.RateLimit.interval(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, kept, m, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, kept, m, now)))) == (i, b) : W.W64 & Nat}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

# The fixed policy, by whether there is room

def count.allowed(room: Bool, -i: W.W64, -b: Nat, -t: W.W64, -n: Nat, -m: Nat) -> {R.RateLimitStep.allowed(R.RateLimit.check.count(room, i, b, t, n, m)) == room : Bool}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

def count.held(room: Bool, -i: W.W64, +b: Nat, -t: W.W64, +n: Nat, -m: Nat, eroom: {Nat.is_lt(n, b) == room : Bool}, hn: {Nat.is_le(n, b) == True{} : Bool}) -> {Nat.is_le(R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.count(room, i, b, t, n, m))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check.count(room, i, b, t, n, m)))) == True{} : Bool}:
  match room:
    case True{}:
      nat.lt_succ_le(n, b, eroom)
    case False{}:
      hn

def count.eq(room: Bool, -i: W.W64, -b: Nat, -t: W.W64, -n: Nat, -m: Nat) -> {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.count(room, i, b, t, n, m))) == rl.plus(R.RateLimitStep.allowed(R.RateLimit.check.count(room, i, b, t, n, m)), n) : Nat}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

def count.supp(room: Bool, -i: W.W64, -b: Nat, -t: W.W64, -n: Nat, -m: Nat) -> {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check.count(room, i, b, t, n, m))) == rl.plusr(R.RateLimitStep.allowed(R.RateLimit.check.count(room, i, b, t, n, m)), m) : Nat}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

def count.kept(room: Bool, -i: W.W64, -b: Nat, -t: W.W64, -n: Nat, -m: Nat) -> {(R.RateLimit.interval(R.RateLimitStep.state(R.RateLimit.check.count(room, i, b, t, n, m))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check.count(room, i, b, t, n, m)))) == (i, b) : W.W64 & Nat}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

# The fixed policy, by whether the window is open

def frame.allowed(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64) -> {R.RateLimitStep.allowed(R.RateLimit.check.frame(inside, i, b, t, n, m, now)) == Nat.is_lt(R.RateLimit.recent.frame(inside, n), b) : Bool}:
  match inside:
    case True{}:
      count.allowed(Nat.is_lt(n, b), i, b, t, n, m)
    case False{}:
      count.allowed(Nat.is_lt(0n, b), i, b, now, 0n, m)

def frame.held(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64, h: {Nat.is_le(n, b) == True{} : Bool}) -> {Nat.is_le(R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.frame(inside, i, b, t, n, m, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check.frame(inside, i, b, t, n, m, now)))) == True{} : Bool}:
  match inside:
    case True{}:
      count.held(Nat.is_lt(n, b), i, b, t, n, m, {==}, h)
    case False{}:
      count.held(Nat.is_lt(0n, b), i, b, now, 0n, m, {==}, nat.le_zero(b))

def frame.eq(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64) -> {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.frame(inside, i, b, t, n, m, now))) == rl.plus(R.RateLimitStep.allowed(R.RateLimit.check.frame(inside, i, b, t, n, m, now)), R.RateLimit.recent.frame(inside, n)) : Nat}:
  match inside:
    case True{}:
      count.eq(Nat.is_lt(n, b), i, b, t, n, m)
    case False{}:
      count.eq(Nat.is_lt(0n, b), i, b, now, 0n, m)

def frame.supp(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64) -> {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check.frame(inside, i, b, t, n, m, now))) == rl.plusr(R.RateLimitStep.allowed(R.RateLimit.check.frame(inside, i, b, t, n, m, now)), m) : Nat}:
  match inside:
    case True{}:
      count.supp(Nat.is_lt(n, b), i, b, t, n, m)
    case False{}:
      count.supp(Nat.is_lt(0n, b), i, b, now, 0n, m)

def frame.kept(inside: Bool, +i: W.W64, +b: Nat, +t: W.W64, +n: Nat, +m: Nat, +now: W.W64) -> {(R.RateLimit.interval(R.RateLimitStep.state(R.RateLimit.check.frame(inside, i, b, t, n, m, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check.frame(inside, i, b, t, n, m, now)))) == (i, b) : W.W64 & Nat}:
  match inside:
    case True{}:
      count.kept(Nat.is_lt(n, b), i, b, t, n, m)
    case False{}:
      count.kept(Nat.is_lt(0n, b), i, b, now, 0n, m)

def frame.recent(inside: Bool, +n: Nat) -> {Nat.is_le(R.RateLimit.recent.frame(inside, n), n) == True{} : Bool}:
  match inside:
    case True{}:
      UL.nat_le_refl(n)
    case False{}:
      nat.le_zero(n)

# The kept times are no more than the times

def put.len(k: Bool, -t: W.W64, +r: List<&2, W.W64>, +n: Nat, ih: {Nat.is_le(List.length(&2, W.W64, r), n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, W.W64, R.RateLimit.keep.put(t, r, k)), 1n+n) == True{} : Bool}:
  match k:
    case True{}:
      ih
    case False{}:
      nat.le_succ(List.length(&2, W.W64, r), n, ih)

def keep.len_le(+i: W.W64, +now: W.W64, ts: List<&2, W.W64>) -> {Nat.is_le(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), List.length(&2, W.W64, ts)) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      put.len(R.RateLimit.within(i, now, t), t, R.RateLimit.keep(i, now, rest), List.length(&2, W.W64, rest), keep.len_le(i, now, rest))

# A check with rate limiting on, for each policy

def gate.on(+i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {R.RateLimitStep.allowed(R.RateLimit.check.on(False{}, R.RateLimit{i, b, w, m}, now)) == Nat.is_lt(R.RateLimit.recent(R.RateLimit{i, b, w, m}, now), b) : Bool}:
  match w:
    case R.RateLimitLog{+ts}:
      log.allowed(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), m, now)
    case R.RateLimitFrame{+t, +n, +o}:
      frame.allowed(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, m, now)

def eq.on(+i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.on(False{}, R.RateLimit{i, b, w, m}, now))) == rl.plus(R.RateLimitStep.allowed(R.RateLimit.check.on(False{}, R.RateLimit{i, b, w, m}, now)), R.RateLimit.recent(R.RateLimit{i, b, w, m}, now)) : Nat}:
  match w:
    case R.RateLimitLog{+ts}:
      log.eq(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), m, now)
    case R.RateLimitFrame{+t, +n, +o}:
      frame.eq(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, m, now)

# A check either way

def held.on(off: Bool, +i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64, h: {Nat.is_le(R.RateLimit.held(R.RateLimit{i, b, w, m}), b) == True{} : Bool}) -> {Nat.is_le(R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, w, m}, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, w, m}, now)))) == True{} : Bool}:
  match off:
    case True{}:
      h
    case False{}:
      match w:
        case R.RateLimitLog{+ts}:
          log.held(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), m, now, {==}, UO.nat_le_trans(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), List.length(&2, W.W64, ts), b, keep.len_le(i, now, ts), h))
        case R.RateLimitFrame{+t, +n, +o}:
          frame.held(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, m, now, h)

def supp.on(off: Bool, +i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, w, m}, now))) == rl.plusr(R.RateLimitStep.allowed(R.RateLimit.check.on(off, R.RateLimit{i, b, w, m}, now)), m) : Nat}:
  match off:
    case True{}:
      {==}
    case False{}:
      match w:
        case R.RateLimitLog{+ts}:
          log.supp(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), m, now)
        case R.RateLimitFrame{+t, +n, +o}:
          frame.supp(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, m, now)

def kept.on(off: Bool, +i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {(R.RateLimit.interval(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, w, m}, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, w, m}, now)))) == (i, b) : W.W64 & Nat}:
  match off:
    case True{}:
      {==}
    case False{}:
      match w:
        case R.RateLimitLog{+ts}:
          log.kept(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), m, now)
        case R.RateLimitFrame{+t, +n, +o}:
          frame.kept(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, m, now)

def quiet.on(off: Bool, +i: W.W64, +b: Nat, +w: R.RateLimitWindow, +m: Nat, +now: W.W64, q: {R.RateLimit.recent(R.RateLimit{i, b, w, m}, now) == 0n : Nat}, hb: {Nat.is_lt(0n, b) == True{} : Bool}) -> {R.RateLimitStep.allowed(R.RateLimit.check.on(off, R.RateLimit{i, b, w, m}, now)) == True{} : Bool}:
  match off:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, R.RateLimitStep.allowed(R.RateLimit.check.on(False{}, R.RateLimit{i, b, w, m}, now)), Nat.is_lt(R.RateLimit.recent(R.RateLimit{i, b, w, m}, now), b), gate.on(i, b, w, m, now)) : {_ == True{} : Bool}
      %Equal.sym(Nat, R.RateLimit.recent(R.RateLimit{i, b, w, m}, now), 0n, q) : {Nat.is_lt(_, b) == True{} : Bool}
      hb

def keeps.on(off: Bool, +i: W.W64, +b: Nat, w: R.RateLimitWindow, +m: Nat, +now: W.W64) -> {R.RateLimitStep.allowed(R.RateLimit.check.on(off, R.RateLimit{i, b, w, 0n}, now)) == R.RateLimitStep.allowed(R.RateLimit.check.on(off, R.RateLimit{i, b, w, m}, now)) : Bool}:
  match off:
    case True{}:
      {==}
    case False{}:
      match w:
        case R.RateLimitLog{+ts}:
          %Equal.sym(Bool, R.RateLimitStep.allowed(R.RateLimit.check.log(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), 0n, now)), Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), log.allowed(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), 0n, now)) : {_ == R.RateLimitStep.allowed(R.RateLimit.check.on(False{}, R.RateLimit{i, b, R.RateLimitLog{ts}, m}, now)) : Bool}
          %Equal.sym(Bool, R.RateLimitStep.allowed(R.RateLimit.check.log(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), m, now)), Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), log.allowed(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), m, now)) : {Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b) == _ : Bool}
          {==}
        case R.RateLimitFrame{+t, +n, +o}:
          %Equal.sym(Bool, R.RateLimitStep.allowed(R.RateLimit.check.frame(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, 0n, now)), Nat.is_lt(R.RateLimit.recent.frame(Bool.and(o, R.RateLimit.within(i, now, t)), n), b), frame.allowed(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, 0n, now)) : {_ == R.RateLimitStep.allowed(R.RateLimit.check.on(False{}, R.RateLimit{i, b, R.RateLimitFrame{t, n, o}, m}, now)) : Bool}
          %Equal.sym(Bool, R.RateLimitStep.allowed(R.RateLimit.check.frame(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, m, now)), Nat.is_lt(R.RateLimit.recent.frame(Bool.and(o, R.RateLimit.within(i, now, t)), n), b), frame.allowed(Bool.and(o, R.RateLimit.within(i, now, t)), i, b, t, n, m, now)) : {Nat.is_lt(R.RateLimit.recent.frame(Bool.and(o, R.RateLimit.within(i, now, t)), n), b) == _ : Bool}
          {==}

# Steps and runs

def step.bound(+s: R.RateLimit, +now: W.W64, h: {Nat.is_le(R.RateLimit.held(s), R.RateLimit.burst(s)) == True{} : Bool}) -> {Nat.is_le(R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check(s, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check(s, now)))) == True{} : Bool}:
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      held.on(W.W64.is_zero(i), i, b, w, m, now, h)

def step.supp(+s: R.RateLimit, +now: W.W64) -> {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check(s, now))) == rl.plusr(R.RateLimitStep.allowed(R.RateLimit.check(s, now)), R.RateLimit.suppressed(s)) : Nat}:
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      supp.on(W.W64.is_zero(i), i, b, w, m, now)

def run.bound(ts: List<&2, W.W64>, +s: R.RateLimit, h: {Nat.is_le(R.RateLimit.held(s), R.RateLimit.burst(s)) == True{} : Bool}) -> {Nat.is_le(R.RateLimit.held(R.RateLimitRun.state(R.RateLimit.run.go(ts, s))), R.RateLimit.burst(R.RateLimitRun.state(R.RateLimit.run.go(ts, s)))) == True{} : Bool}:
  match ts:
    case Nil{}:
      h
    case Con{+t, +rest}:
      run.bound(rest, R.RateLimitStep.state(R.RateLimit.check(s, t)), step.bound(s, t, h))

def run.arith(a: Bool, +xs: List<&2, Bool>, +m: Nat) -> {Nat.add(R.RateLimit.refusals(xs), rl.plusr(a, m)) == Nat.add(R.RateLimit.refusals(Con{a, xs}), m) : Nat}:
  match a:
    case True{}:
      {==}
    case False{}:
      UL.nat_add_succ(R.RateLimit.refusals(xs), m)

def run.supp(ts: List<&2, W.W64>, +s: R.RateLimit) -> {R.RateLimit.suppressed(R.RateLimitRun.state(R.RateLimit.run.go(ts, s))) == Nat.add(R.RateLimit.refusals(R.RateLimitRun.allowed(R.RateLimit.run.go(ts, s))), R.RateLimit.suppressed(s)) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      %Equal.sym(Nat, R.RateLimit.suppressed(R.RateLimitRun.state(R.RateLimit.run.go(rest, R.RateLimitStep.state(R.RateLimit.check(s, t))))), Nat.add(R.RateLimit.refusals(R.RateLimitRun.allowed(R.RateLimit.run.go(rest, R.RateLimitStep.state(R.RateLimit.check(s, t))))), R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check(s, t)))), run.supp(rest, R.RateLimitStep.state(R.RateLimit.check(s, t)))) : {_ == Nat.add(R.RateLimit.refusals(Con{R.RateLimitStep.allowed(R.RateLimit.check(s, t)), R.RateLimitRun.allowed(R.RateLimit.run.go(rest, R.RateLimitStep.state(R.RateLimit.check(s, t))))}), R.RateLimit.suppressed(s)) : Nat}
      %Equal.sym(Nat, R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check(s, t))), rl.plusr(R.RateLimitStep.allowed(R.RateLimit.check(s, t)), R.RateLimit.suppressed(s)), step.supp(s, t)) : {Nat.add(R.RateLimit.refusals(R.RateLimitRun.allowed(R.RateLimit.run.go(rest, R.RateLimitStep.state(R.RateLimit.check(s, t))))), _) == Nat.add(R.RateLimit.refusals(Con{R.RateLimitStep.allowed(R.RateLimit.check(s, t)), R.RateLimitRun.allowed(R.RateLimit.run.go(rest, R.RateLimitStep.state(R.RateLimit.check(s, t))))}), R.RateLimit.suppressed(s)) : Nat}
      run.arith(R.RateLimitStep.allowed(R.RateLimit.check(s, t)), R.RateLimitRun.allowed(R.RateLimit.run.go(rest, R.RateLimitStep.state(R.RateLimit.check(s, t)))), R.RateLimit.suppressed(s))

# The laws

def Laws.ratelimit_new(p, i, b):
  match p:
    case R.RateLimitSliding{}:
      {==}
    case R.RateLimitFixed{}:
      {==}

def Laws.ratelimit_new_default(i, b):
  {==}

def Laws.ratelimit_gate(s, now, h):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      %Equal.sym(Bool, W.W64.is_zero(i), False{}, h) : {R.RateLimitStep.allowed(R.RateLimit.check.on(_, R.RateLimit{i, b, w, m}, now)) == Nat.is_lt(R.RateLimit.recent(R.RateLimit{i, b, w, m}, now), b) : Bool}
      gate.on(i, b, w, m, now)

def Laws.ratelimit_off(s, now, h):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      %Equal.sym(Bool, W.W64.is_zero(i), True{}, h) : {R.RateLimit.check.on(_, R.RateLimit{i, b, w, m}, now) == R.RateLimitStep{R.RateLimit{i, b, w, m}, True{}} : R.RateLimitStep}
      {==}

def Laws.ratelimit_quiet(s, now, q, hb):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      quiet.on(W.W64.is_zero(i), i, b, w, m, now, q, hb)

def Laws.ratelimit_held_allowed(s, now, h, a):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      %a : {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check(R.RateLimit{i, b, w, m}, now))) == rl.plus(_, R.RateLimit.recent(R.RateLimit{i, b, w, m}, now)) : Nat}
      %Equal.sym(Bool, W.W64.is_zero(i), False{}, h) : {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.on(_, R.RateLimit{i, b, w, m}, now))) == rl.plus(R.RateLimitStep.allowed(R.RateLimit.check.on(_, R.RateLimit{i, b, w, m}, now)), R.RateLimit.recent(R.RateLimit{i, b, w, m}, now)) : Nat}
      eq.on(i, b, w, m, now)

def Laws.ratelimit_held_refused(s, now, h, a):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      %a : {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check(R.RateLimit{i, b, w, m}, now))) == rl.plus(_, R.RateLimit.recent(R.RateLimit{i, b, w, m}, now)) : Nat}
      %Equal.sym(Bool, W.W64.is_zero(i), False{}, h) : {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check.on(_, R.RateLimit{i, b, w, m}, now))) == rl.plus(R.RateLimitStep.allowed(R.RateLimit.check.on(_, R.RateLimit{i, b, w, m}, now)), R.RateLimit.recent(R.RateLimit{i, b, w, m}, now)) : Nat}
      eq.on(i, b, w, m, now)

def Laws.ratelimit_recent_le_held(s, now):
  match s:
    case R.RateLimit{+i, b, R.RateLimitLog{+ts}, m}:
      keep.len_le(i, now, ts)
    case R.RateLimit{+i, b, R.RateLimitFrame{+t, +n, +o}, m}:
      frame.recent(Bool.and(o, R.RateLimit.within(i, now, t)), n)

def Laws.ratelimit_held_bound(s, now, h):
  step.bound(s, now, h)

def Laws.ratelimit_run_bound(s, ts, h):
  run.bound(ts, s, h)

def Laws.ratelimit_kept(s, now):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      kept.on(W.W64.is_zero(i), i, b, w, m, now)

def Laws.ratelimit_suppressed_allowed(s, now, a):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      %a : {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check(R.RateLimit{i, b, w, m}, now))) == rl.plusr(_, m) : Nat}
      supp.on(W.W64.is_zero(i), i, b, w, m, now)

def Laws.ratelimit_suppressed_refused(s, now, a):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      %a : {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check(R.RateLimit{i, b, w, m}, now))) == rl.plusr(_, m) : Nat}
      supp.on(W.W64.is_zero(i), i, b, w, m, now)

def Laws.ratelimit_report(s):
  match s:
    case R.RateLimit{i, b, w, m}:
      {==}

def Laws.ratelimit_report_keeps(s, now):
  match s:
    case R.RateLimit{+i, +b, +w, +m}:
      keeps.on(W.W64.is_zero(i), i, b, w, m, now)

def Laws.ratelimit_run_suppressed(s, ts):
  match s:
    case R.RateLimit{+i, +b, +w, m}:
      %UL.nat_add_zero(R.RateLimit.refusals(R.RateLimitRun.allowed(R.RateLimit.run.go(ts, R.RateLimit{i, b, w, 0n})))) : {R.RateLimit.suppressed(R.RateLimitRun.state(R.RateLimit.run.go(ts, R.RateLimit{i, b, w, 0n}))) == _ : Nat}
      run.supp(ts, R.RateLimit{i, b, w, 0n})

def Laws.ratelimit_wit():
  {==}

def Laws.ratelimit_vec_sliding():
  {==}

def Laws.ratelimit_vec_policies():
  {==}

def Laws.ratelimit_vec_report():
  {==}

def Laws.ratelimit_vec_printk():
  {==}

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

def wd.add_one(+n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  Equal.trans(Nat, Nat.add(n, 1n), 1n+Nat.add(n, 0n), 1n+n, UL.nat_add_succ(n, 0n), wd.succ_cong(Nat.add(n, 0n), n, UL.nat_add_zero(n)))

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
  wd.le_w(a, c, UO.nat_le_trans(W.W64.to_nat(a), W.W64.to_nat(b), W.W64.to_nat(c), wd.le_nat(a, b, h1), wd.le_nat(b, c, h2)))

def wd.le_refl_w(+a: W.W64) -> {W.W64.is_le(a, a) == True{} : Bool}:
  wd.le_w(a, a, UL.nat_le_refl(W.W64.to_nat(a)))

# u <= now: u is within the window ending at now when now - u < interval
def wd.within_nat(+i: W.W64, +now: W.W64, +u: W.W64, h: {Nat.is_le(W.W64.to_nat(u), W.W64.to_nat(now)) == True{} : Bool}) -> {R.RateLimit.within(i, now, u) == Nat.is_lt(Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i)) : Bool}:
  Equal.trans(Bool, W.W64.is_lt(W.W64.sub(now, u), i), Nat.is_lt(W.W64.to_nat(W.W64.sub(now, u)), W.W64.to_nat(i)), Nat.is_lt(Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i)), WL.lt_value(W.W64.sub(now, u), i), Equal.cong(Nat, Bool, x => Nat.is_lt(x, W.W64.to_nat(i)), W.W64.to_nat(W.W64.sub(now, u)), Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), WL.sub_value(now, u, h)))

# u <= t <= now: within the window at now, within it at t
def wd.mono(+i: W.W64, +u: W.W64, +t: W.W64, +now: W.W64, hu: {W.W64.is_le(u, t) == True{} : Bool}, ht: {W.W64.is_le(t, now) == True{} : Bool}, e: {R.RateLimit.within(i, now, u) == True{} : Bool}) -> {R.RateLimit.within(i, t, u) == True{} : Bool}:
  +ut = wd.le_nat(u, t, hu)
  +tn = wd.le_nat(t, now, ht)
  +e2 = Equal.trans(Bool, Nat.is_lt(Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i)), R.RateLimit.within(i, now, u), True{}, Equal.sym(Bool, R.RateLimit.within(i, now, u), Nat.is_lt(Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i)), wd.within_nat(i, now, u, UO.nat_le_trans(W.W64.to_nat(u), W.W64.to_nat(t), W.W64.to_nat(now), ut, tn))), e)
  Equal.trans(Bool, R.RateLimit.within(i, t, u), Nat.is_lt(Nat.sub(W.W64.to_nat(t), W.W64.to_nat(u)), W.W64.to_nat(i)), True{}, wd.within_nat(i, t, u, ut), UO.nat_le_lt_trans(Nat.sub(W.W64.to_nat(t), W.W64.to_nat(u)), Nat.sub(W.W64.to_nat(now), W.W64.to_nat(u)), W.W64.to_nat(i), wd.sub_mono(W.W64.to_nat(t), W.W64.to_nat(now), W.W64.to_nat(u), tn), e2))

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
      Equal.trans(Nat, List.length(&2, W.W64, x), n, Nat.add(n, 0n), e, Equal.sym(Nat, Nat.add(n, 0n), n, UL.nat_add_zero(n)))

def wd.st.room(room: Bool, +i: W.W64, +b: Nat, +ls: List<&2, W.W64>, +m: Nat, +t: W.W64, +now: W.W64, kc: {List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls))) == List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)) : Nat}) -> {R.RateLimit.recent(R.RateLimitStep.state(R.RateLimit.check.log(room, i, b, R.RateLimit.keep(i, t, ls), m, t)), now) == Nat.add(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), wd.bit(Bool.and(R.RateLimitStep.allowed(R.RateLimit.check.log(room, i, b, R.RateLimit.keep(i, t, ls), m, t)), R.RateLimit.within(i, now, t)))) : Nat}:
  match room:
    case True{}:
      wd.st.w(R.RateLimit.within(i, now, t), t, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls)), List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), kc)
    case False{}:
      Equal.trans(Nat, List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls))), List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), Nat.add(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), 0n), kc, Equal.sym(Nat, Nat.add(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), 0n), List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), UL.nat_add_zero(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)))))

def wd.st.off(off: Bool, +i: W.W64, +b: Nat, +ls: List<&2, W.W64>, +m: Nat, +t: W.W64, +now: W.W64, e: {W.W64.is_zero(i) == off : Bool}, kc: {List.length(&2, W.W64, R.RateLimit.keep(i, now, R.RateLimit.keep(i, t, ls))) == List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)) : Nat}) -> {R.RateLimit.recent(R.RateLimitStep.state(R.RateLimit.check.on(off, R.RateLimit{i, b, R.RateLimitLog{ls}, m}, t)), now) == Nat.add(List.length(&2, W.W64, R.RateLimit.keep(i, now, ls)), wd.bit(Bool.and(R.RateLimitStep.allowed(R.RateLimit.check.on(off, R.RateLimit{i, b, R.RateLimitLog{ls}, m}, t)), R.RateLimit.within(i, now, t)))) : Nat}:
  match off:
    case True{}:
      +c = List.length(&2, W.W64, R.RateLimit.keep(i, now, ls))
      Equal.trans(Nat, c, Nat.add(c, 0n), Nat.add(c, wd.bit(R.RateLimit.within(i, now, t))), Equal.sym(Nat, Nat.add(c, 0n), c, UL.nat_add_zero(c)), Equal.cong(Bool, Nat, x => Nat.add(c, wd.bit(x)), False{}, R.RateLimit.within(i, now, t), Equal.sym(Bool, R.RateLimit.within(i, now, t), False{}, wd.zero_within(i, now, t, e))))
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
      UL.nat_add_zero(R.RateLimit.recent(s, now))
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
      Equal.trans(Nat, Nat.add(rs, R.RateLimit.in_window(iv, now, R.RateLimit.allowed_times.put(a, t, x))), Nat.add(rs, Nat.add(bt, R.RateLimit.in_window(iv, now, x))), R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(rest, s1)), now), Equal.cong(Nat, Nat, v => Nat.add(rs, v), R.RateLimit.in_window(iv, now, R.RateLimit.allowed_times.put(a, t, x)), Nat.add(bt, R.RateLimit.in_window(iv, now, x)), wd.put_w(a, iv, now, t, x)), Equal.trans(Nat, Nat.add(rs, Nat.add(bt, R.RateLimit.in_window(iv, now, x))), Nat.add(Nat.add(rs, bt), R.RateLimit.in_window(iv, now, x)), R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(rest, s1)), now), Equal.sym(Nat, Nat.add(Nat.add(rs, bt), R.RateLimit.in_window(iv, now, x)), Nat.add(rs, Nat.add(bt, R.RateLimit.in_window(iv, now, x))), UL.nat_add_assoc(rs, bt, R.RateLimit.in_window(iv, now, x))), Equal.trans(Nat, Nat.add(Nat.add(rs, bt), R.RateLimit.in_window(iv, now, x)), Nat.add(r1, R.RateLimit.in_window(iv, now, x)), R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(rest, s1)), now), Equal.cong(Nat, Nat, v => Nat.add(v, R.RateLimit.in_window(iv, now, x)), Nat.add(rs, bt), r1, Equal.sym(Nat, r1, Nat.add(rs, bt), wd.st(s, t, now, hsl, ha, ht))), Equal.trans(Nat, Nat.add(r1, R.RateLimit.in_window(iv, now, x)), Nat.add(r1, R.RateLimit.in_window(R.RateLimit.interval(s1), now, x)), R.RateLimit.recent(R.RateLimitRun.state(R.RateLimit.run.go(rest, s1)), now), Equal.cong(W.W64, Nat, v => Nat.add(r1, R.RateLimit.in_window(v, now, x)), iv, R.RateLimit.interval(s1), Equal.sym(W.W64, R.RateLimit.interval(s1), iv, wd.int(s, t))), wd.run(rest, s1, now, hsl1, hs1, ha1)))))

def Laws.ratelimit_run_window(i, b, ts, now, h):
  +s0 = R.RateLimit.new(i, b)
  +fin = R.RateLimitRun.state(R.RateLimit.run.go(ts, s0))
  +e = wd.run(ts, s0, now, {==}, h, {==})
  %Equal.sym(Nat, R.RateLimit.in_window(i, now, R.RateLimit.allowed_times(ts, R.RateLimitRun.allowed(R.RateLimit.run.go(ts, s0)))), R.RateLimit.recent(fin, now), e) : {Nat.is_le(_, U32.to_nat(b)) == True{} : Bool}
  UO.nat_le_trans(R.RateLimit.recent(fin, now), R.RateLimit.held(fin), U32.to_nat(b), Laws.ratelimit_recent_le_held(fin, now), wd.le_rw2(R.RateLimit.held(fin), R.RateLimit.burst(fin), U32.to_nat(b), wd.run_burst(ts, s0), Laws.ratelimit_run_bound(s0, ts, nat.le_zero(U32.to_nat(b)))))

def Laws.ratelimit_window_wit():
  {==}

def Laws.ratelimit_vec_window():
  {==}
