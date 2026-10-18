# Properties, for every state (of either policy), time and list of times:
#
# * the gate: with rate limiting on (a nonzero interval), an event is
#   allowed exactly when fewer than burst allowed events are within the
#   window ending at it (RateLimit.recent); with an interval of 0 every
#   event is allowed and nothing changes;
# * after a quiet interval (no allowed event within the window), an event
#   is allowed (when burst is at least 1);
# * every allowed event is held against the window, and nothing outside it
#   is: after an allowed event the state holds the window's events and this
#   one, after a refused one just the window's;
# * at most burst: a state holding at most burst events still does after a
#   check and after any run of checks, and the window never counts more
#   than the state holds; so no check sees burst or more allowed events in
#   its window and lets another through;
# * suppressed counts: an allowed event leaves the count alone, a refused
#   one adds one; a report answers the count and clears it, and changes
#   nothing else; so after a report, the count is the number of refused
#   calls since;
# * interval and burst never change.
#
# The window's own arithmetic (that a time within the window at a later
# check was within it at every check between, for nondecreasing times) is
# not stated: it needs laws of W64 subtraction and order, which word64
# leaves to its tests. The differential test checks the trace property
# itself, for the sliding policy, on random times.
import Base
import ../word64/word64.bend as W
import ./ratelimit.bend as R

# A new state

law ratelimit_new:
  for p: R.RateLimitPolicy
  for i: W.W64
  for b: U32
  {(R.RateLimit.held(R.RateLimit.new_with(p, i, b)), R.RateLimit.suppressed(R.RateLimit.new_with(p, i, b)), R.RateLimit.burst(R.RateLimit.new_with(p, i, b))) == (0n, 0n, U32.to_nat(b)) : Nat & Nat & Nat}

law ratelimit_new_default:
  for i: W.W64
  for b: U32
  {R.RateLimit.new(i, b) == R.RateLimit.new_with(R.RateLimitSliding{}, i, b) : R.RateLimit}

# The gate

law ratelimit_gate:
  for +s: R.RateLimit
  for +now: W.W64
  for h: {W.W64.is_zero(R.RateLimit.interval(s)) == False{} : Bool}
  {R.RateLimitStep.allowed(R.RateLimit.check(s, now)) == Nat.is_lt(R.RateLimit.recent(s, now), R.RateLimit.burst(s)) : Bool}

law ratelimit_off:
  for +s: R.RateLimit
  for +now: W.W64
  for h: {W.W64.is_zero(R.RateLimit.interval(s)) == True{} : Bool}
  {R.RateLimit.check(s, now) == R.RateLimitStep{s, True{}} : R.RateLimitStep}

law ratelimit_quiet:
  for +s: R.RateLimit
  for +now: W.W64
  for q: {R.RateLimit.recent(s, now) == 0n : Nat}
  for b: {Nat.is_lt(0n, R.RateLimit.burst(s)) == True{} : Bool}
  {R.RateLimitStep.allowed(R.RateLimit.check(s, now)) == True{} : Bool}

# What the state holds

law ratelimit_held_allowed:
  for +s: R.RateLimit
  for +now: W.W64
  for h: {W.W64.is_zero(R.RateLimit.interval(s)) == False{} : Bool}
  for a: {R.RateLimitStep.allowed(R.RateLimit.check(s, now)) == True{} : Bool}
  {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check(s, now))) == 1n+R.RateLimit.recent(s, now) : Nat}

law ratelimit_held_refused:
  for +s: R.RateLimit
  for +now: W.W64
  for h: {W.W64.is_zero(R.RateLimit.interval(s)) == False{} : Bool}
  for a: {R.RateLimitStep.allowed(R.RateLimit.check(s, now)) == False{} : Bool}
  {R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check(s, now))) == R.RateLimit.recent(s, now) : Nat}

law ratelimit_recent_le_held:
  for +s: R.RateLimit
  for +now: W.W64
  {Nat.is_le(R.RateLimit.recent(s, now), R.RateLimit.held(s)) == True{} : Bool}

# At most burst

law ratelimit_held_bound:
  for +s: R.RateLimit
  for +now: W.W64
  for h: {Nat.is_le(R.RateLimit.held(s), R.RateLimit.burst(s)) == True{} : Bool}
  {Nat.is_le(R.RateLimit.held(R.RateLimitStep.state(R.RateLimit.check(s, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check(s, now)))) == True{} : Bool}

law ratelimit_run_bound:
  for +s: R.RateLimit
  for +ts: List<&2, W.W64>
  for h: {Nat.is_le(R.RateLimit.held(s), R.RateLimit.burst(s)) == True{} : Bool}
  {Nat.is_le(R.RateLimit.held(R.RateLimitRun.state(R.RateLimit.run(s, ts))), R.RateLimit.burst(R.RateLimitRun.state(R.RateLimit.run(s, ts)))) == True{} : Bool}

law ratelimit_kept:
  for +s: R.RateLimit
  for +now: W.W64
  {(R.RateLimit.interval(R.RateLimitStep.state(R.RateLimit.check(s, now))), R.RateLimit.burst(R.RateLimitStep.state(R.RateLimit.check(s, now)))) == (R.RateLimit.interval(s), R.RateLimit.burst(s)) : W.W64 & Nat}

# Suppressed counts

law ratelimit_suppressed_allowed:
  for +s: R.RateLimit
  for +now: W.W64
  for a: {R.RateLimitStep.allowed(R.RateLimit.check(s, now)) == True{} : Bool}
  {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check(s, now))) == R.RateLimit.suppressed(s) : Nat}

law ratelimit_suppressed_refused:
  for +s: R.RateLimit
  for +now: W.W64
  for a: {R.RateLimitStep.allowed(R.RateLimit.check(s, now)) == False{} : Bool}
  {R.RateLimit.suppressed(R.RateLimitStep.state(R.RateLimit.check(s, now))) == 1n+R.RateLimit.suppressed(s) : Nat}

law ratelimit_report:
  for +s: R.RateLimit
  {(R.RateLimitReport.suppressed(R.RateLimit.report(s)), R.RateLimit.suppressed(R.RateLimitReport.state(R.RateLimit.report(s)))) == (R.RateLimit.suppressed(s), 0n) : Nat & Nat}

law ratelimit_report_keeps:
  for +s: R.RateLimit
  for +now: W.W64
  {R.RateLimitStep.allowed(R.RateLimit.check(R.RateLimitReport.state(R.RateLimit.report(s)), now)) == R.RateLimitStep.allowed(R.RateLimit.check(s, now)) : Bool}

law ratelimit_run_suppressed:
  for +s: R.RateLimit
  for +ts: List<&2, W.W64>
  {R.RateLimit.suppressed(R.RateLimitRun.state(R.RateLimit.run(R.RateLimitReport.state(R.RateLimit.report(s)), ts))) == R.RateLimit.refusals(R.RateLimitRun.allowed(R.RateLimit.run(R.RateLimitReport.state(R.RateLimit.report(s)), ts))) : Nat}

# Witnesses: each hypothesis above can hold

law ratelimit_wit:
  {(W.W64.is_zero(R.RateLimit.interval(R.RateLimit.new(W.W64.from_u32(10), 3))), W.W64.is_zero(R.RateLimit.interval(R.RateLimit.new(W.W64.zero(), 3))), R.RateLimit.recent(R.RateLimit.new(W.W64.from_u32(10), 3), W.W64.zero()), Nat.is_lt(0n, R.RateLimit.burst(R.RateLimit.new(W.W64.from_u32(10), 3))), R.RateLimitStep.allowed(R.RateLimit.check(R.RateLimit.new(W.W64.from_u32(10), 0), W.W64.zero())), Nat.is_le(R.RateLimit.held(R.RateLimit.new(W.W64.from_u32(10), 3)), R.RateLimit.burst(R.RateLimit.new(W.W64.from_u32(10), 3)))) == (False{}, True{}, 0n, True{}, False{}, True{}) : Bool & Bool & Nat & Bool & Bool & Bool}

# Vectors: burst 3 per 10 units

# the sliding window: 0, 1, 2 allowed; 3 and 9 refused; 10 allowed (0 has
# left the window), 11 and 12 too; 13 refused; 25 allowed after a quiet
# interval
law ratelimit_vec_sliding:
  {R.RateLimitRun.allowed(R.RateLimit.run(R.RateLimit.new(W.W64.from_u32(10), 3), [W.W64.from_u32(0), W.W64.from_u32(1), W.W64.from_u32(2), W.W64.from_u32(3), W.W64.from_u32(9), W.W64.from_u32(10), W.W64.from_u32(11), W.W64.from_u32(12), W.W64.from_u32(13), W.W64.from_u32(25)])) == [True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}, False{}, True{}] : List<&2, Bool>}

# the two policies differ: after 0, 8 and 9, the sliding window lets 10
# through and refuses 11 and 12; the fixed window opens anew at 10 and lets
# all three through, five in the stretch from 8 to 12
law ratelimit_vec_policies:
  {(R.RateLimitRun.allowed(R.RateLimit.run(R.RateLimit.new(W.W64.from_u32(10), 3), [W.W64.from_u32(0), W.W64.from_u32(8), W.W64.from_u32(9), W.W64.from_u32(10), W.W64.from_u32(11), W.W64.from_u32(12)])), R.RateLimitRun.allowed(R.RateLimit.run(R.RateLimit.new_with(R.RateLimitFixed{}, W.W64.from_u32(10), 3), [W.W64.from_u32(0), W.W64.from_u32(8), W.W64.from_u32(9), W.W64.from_u32(10), W.W64.from_u32(11), W.W64.from_u32(12)]))) == ([True{}, True{}, True{}, True{}, False{}, False{}], [True{}, True{}, True{}, True{}, True{}, True{}]) : List<&2, Bool> & List<&2, Bool>}

# the suppressed count after the sliding run above, and after a report
law ratelimit_vec_report:
  {(R.RateLimit.suppressed(R.RateLimitRun.state(R.RateLimit.run(R.RateLimit.new(W.W64.from_u32(10), 3), [W.W64.from_u32(0), W.W64.from_u32(1), W.W64.from_u32(2), W.W64.from_u32(3), W.W64.from_u32(9)]))), R.RateLimit.suppressed(R.RateLimitReport.state(R.RateLimit.report(R.RateLimitRun.state(R.RateLimit.run(R.RateLimit.new(W.W64.from_u32(10), 3), [W.W64.from_u32(0), W.W64.from_u32(1), W.W64.from_u32(2), W.W64.from_u32(3), W.W64.from_u32(9)])))))) == (2n, 0n) : Nat & Nat}
