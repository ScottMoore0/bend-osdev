import Base
import ../word64/word64.bend as W
import ./ratelimit.bend as R
import ./LAWS.bend as Laws

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

def nat.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat.le_refl(p)

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

def nat.le_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      nat.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, ab.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, ab.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nat.le_trans(ap, bp, cp, e, f)

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

def nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nat.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def nat.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), nat.add_succ(p, b)) : {1n+_ == 2n+Nat.add(p, b) : Nat}
      {==}

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
      nat.le_refl(n)
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
          log.held(Nat.is_lt(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), b), i, b, R.RateLimit.keep(i, now, ts), m, now, {==}, nat.le_trans(List.length(&2, W.W64, R.RateLimit.keep(i, now, ts)), List.length(&2, W.W64, ts), b, keep.len_le(i, now, ts), h))
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
      nat.add_succ(R.RateLimit.refusals(xs), m)

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
      %nat.add_zero(R.RateLimit.refusals(R.RateLimitRun.allowed(R.RateLimit.run.go(ts, R.RateLimit{i, b, w, 0n})))) : {R.RateLimit.suppressed(R.RateLimitRun.state(R.RateLimit.run.go(ts, R.RateLimit{i, b, w, 0n}))) == _ : Nat}
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
