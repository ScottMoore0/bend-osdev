# bend-osdev-ratelimit: allow at most burst events per interval, and count
# the ones refused, as a pure state machine.
#
# RateLimit.check(state, now) says whether an event at time now is allowed,
# and answers the new state. The time is passed in, never read: a W64 in
# whatever unit the caller keeps (jiffies, nanoseconds, a test's own
# steps), the same unit as the interval. An event at time t is within the
# window at time now when now - t < interval (modulo 2^64, so a time ahead
# of now is outside it).
#
# Two window policies (RateLimitPolicy):
# * sliding (the default): an event is allowed when fewer than burst
#   allowed events lie within the window ending at now; the state keeps the
#   times of those events (at most burst of them), newest first. So no
#   window of length interval ever holds more than burst allowed events;
# * fixed: a window opens at the first event after the previous one closed
#   and lasts interval; at most burst events are allowed in it. This is the
#   behaviour the kernel documents for printk_ratelimit_burst (after the
#   interval has elapsed, another burst may be sent), and RateLimit.printk
#   uses it: cheaper (no list), but a stretch of
#   length interval that straddles two fixed windows can hold up to
#   2 * burst allowed events.
#
# An interval of 0 turns rate limiting off: every event is allowed (as the
# kernel documents for its printk_ratelimit sysctl). Refused events are
# counted until the caller takes the count with RateLimit.report, to print
# "N callbacks suppressed".
import Base
import ../word64/word64.bend as W

type RateLimitPolicy is Data:
  RateLimitSliding{}
  RateLimitFixed{}

def RateLimitPolicy.default() -> RateLimitPolicy:
  RateLimitSliding{}

# the window's state: the sliding policy's kept times, newest first; or the
# fixed policy's window start, the events allowed in it, and whether one
# has opened yet
type RateLimitWindow is Data:
  RateLimitLog{times: List<&2, W.W64>}
  RateLimitFrame{begin: W.W64, count: Nat, open: Bool}

type RateLimit is Data:
  RateLimit{interval: W.W64, burst: Nat, win: RateLimitWindow, missed: Nat}

# what a check answers: the new state, and whether the event is allowed
type RateLimitStep is Data:
  RateLimitStep{state: RateLimit, allowed: Bool}

# what a report answers: the state with its count cleared, and the count
type RateLimitReport is Data:
  RateLimitReport{state: RateLimit, suppressed: Nat}

def RateLimit.new_with(p: RateLimitPolicy, interval: W.W64, burst: U32) -> RateLimit:
  match p:
    case RateLimitSliding{}:
      RateLimit{interval, U32.to_nat(burst), RateLimitLog{Nil{}}, 0n}
    case RateLimitFixed{}:
      RateLimit{interval, U32.to_nat(burst), RateLimitFrame{W.W64.zero(), 0n, False{}}, 0n}

def RateLimit.new(interval: W.W64, burst: U32) -> RateLimit:
  RateLimit.new_with(RateLimitPolicy.default(), interval, burst)

# The printk defaults the kernel documents for its printk_ratelimit and
# printk_ratelimit_burst sysctls: an interval of 5 seconds and a burst of
# 10, with the window the sysctl text describes (after the interval has
# elapsed, another burst may be sent): the fixed policy. per_second is the
# caller's time units in a second.

def RateLimit.printk_interval_seconds() -> U32:
  5

def RateLimit.printk_burst() -> U32:
  10

def RateLimit.printk(per_second: W.W64) -> RateLimit:
  RateLimit.new_with(RateLimitFixed{}, W.W64.mul(W.W64.from_u32(RateLimit.printk_interval_seconds()), per_second), RateLimit.printk_burst())

# Observers

def RateLimit.interval(s: RateLimit) -> W.W64:
  match s:
    case RateLimit{i, b, w, m}:
      i

def RateLimit.burst(s: RateLimit) -> Nat:
  match s:
    case RateLimit{i, b, w, m}:
      b

# the refused calls since the last report
def RateLimit.suppressed(s: RateLimit) -> Nat:
  match s:
    case RateLimit{i, b, w, m}:
      m

def RateLimitStep.state(r: RateLimitStep) -> RateLimit:
  match r:
    case RateLimitStep{s, a}:
      s

def RateLimitStep.allowed(r: RateLimitStep) -> Bool:
  match r:
    case RateLimitStep{s, a}:
      a

def RateLimitReport.state(r: RateLimitReport) -> RateLimit:
  match r:
    case RateLimitReport{s, n}:
      s

def RateLimitReport.suppressed(r: RateLimitReport) -> Nat:
  match r:
    case RateLimitReport{s, n}:
      n

# whether an event at time t is within the window ending at now
def RateLimit.within(+interval: W.W64, +now: W.W64, +t: W.W64) -> Bool:
  W.W64.is_lt(W.W64.sub(now, t), interval)

# the sliding policy's kept times that are still within the window at now
def RateLimit.keep.put(t: W.W64, rest: List<&2, W.W64>, keep: Bool) -> List<&2, W.W64>:
  match keep:
    case True{}:
      Con{t, rest}
    case False{}:
      rest

def RateLimit.keep(+interval: W.W64, +now: W.W64, ts: List<&2, W.W64>) -> List<&2, W.W64>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      RateLimit.keep.put(t, RateLimit.keep(interval, now, rest), RateLimit.within(interval, now, t))

# the allowed events the window holds against now: those the next check
# counts towards burst
def RateLimit.recent.frame(inside: Bool, n: Nat) -> Nat:
  match inside:
    case True{}:
      n
    case False{}:
      0n

def RateLimit.recent(s: RateLimit, +now: W.W64) -> Nat:
  match s:
    case RateLimit{+i, b, RateLimitLog{ts}, m}:
      List.length(&2, W.W64, RateLimit.keep(i, now, ts))
    case RateLimit{+i, b, RateLimitFrame{+t, n, o}, m}:
      RateLimit.recent.frame(Bool.and(o, RateLimit.within(i, now, t)), n)

# the allowed events the state holds at all (at most burst; see LAWS.bend)
def RateLimit.held(s: RateLimit) -> Nat:
  match s:
    case RateLimit{i, b, RateLimitLog{ts}, m}:
      List.length(&2, W.W64, ts)
    case RateLimit{i, b, RateLimitFrame{t, n, o}, m}:
      n

# Checking an event

# the sliding policy, with the kept times: room for one more, or not
def RateLimit.check.log(room: Bool, +i: W.W64, +b: Nat, kept: List<&2, W.W64>, +m: Nat, +now: W.W64) -> RateLimitStep:
  match room:
    case True{}:
      RateLimitStep{RateLimit{i, b, RateLimitLog{Con{now, kept}}, m}, True{}}
    case False{}:
      RateLimitStep{RateLimit{i, b, RateLimitLog{kept}, 1n+m}, False{}}

def RateLimit.check.sliding(+i: W.W64, +b: Nat, +kept: List<&2, W.W64>, +m: Nat, +now: W.W64) -> RateLimitStep:
  RateLimit.check.log(Nat.is_lt(List.length(&2, W.W64, kept), b), i, b, kept, m, now)

# the fixed policy: inside the open window (room for one more, or not), or
# a new window opening at now
def RateLimit.check.count(room: Bool, +i: W.W64, +b: Nat, t: W.W64, +n: Nat, +m: Nat) -> RateLimitStep:
  match room:
    case True{}:
      RateLimitStep{RateLimit{i, b, RateLimitFrame{t, 1n+n, True{}}, m}, True{}}
    case False{}:
      RateLimitStep{RateLimit{i, b, RateLimitFrame{t, n, True{}}, 1n+m}, False{}}

def RateLimit.check.frame(inside: Bool, +i: W.W64, +b: Nat, t: W.W64, +n: Nat, +m: Nat, now: W.W64) -> RateLimitStep:
  match inside:
    case True{}:
      RateLimit.check.count(Nat.is_lt(n, b), i, b, t, n, m)
    case False{}:
      RateLimit.check.count(Nat.is_lt(0n, b), i, b, now, 0n, m)

def RateLimit.check.on(off: Bool, s: RateLimit, +now: W.W64) -> RateLimitStep:
  match off:
    case True{}:
      RateLimitStep{s, True{}}
    case False{}:
      match s:
        case RateLimit{+i, +b, RateLimitLog{ts}, +m}:
          RateLimit.check.sliding(i, b, RateLimit.keep(i, now, ts), m, now)
        case RateLimit{+i, +b, RateLimitFrame{+t, +n, o}, +m}:
          RateLimit.check.frame(Bool.and(o, RateLimit.within(i, now, t)), i, b, t, n, m, now)

# whether an event at time now is allowed, and the new state (the kernel's
# __ratelimit)
def RateLimit.check(+s: RateLimit, +now: W.W64) -> RateLimitStep:
  RateLimit.check.on(W.W64.is_zero(RateLimit.interval(s)), s, now)

# the refused count, taken and cleared (the "N callbacks suppressed" report)
def RateLimit.report(s: RateLimit) -> RateLimitReport:
  match s:
    case RateLimit{i, b, w, +m}:
      RateLimitReport{RateLimit{i, b, w, 0n}, m}

# Runs: checks at each of a list of times, in order, answering the final
# state and whether each event was allowed

type RateLimitRun is Data:
  RateLimitRun{state: RateLimit, allowed: List<&2, Bool>}

def RateLimitRun.state(r: RateLimitRun) -> RateLimit:
  match r:
    case RateLimitRun{s, a}:
      s

def RateLimitRun.allowed(r: RateLimitRun) -> List<&2, Bool>:
  match r:
    case RateLimitRun{s, a}:
      a

def RateLimit.run.cons(a: Bool, +r: RateLimitRun) -> RateLimitRun:
  RateLimitRun{RateLimitRun.state(r), Con{a, RateLimitRun.allowed(r)}}

def RateLimit.run.go(ts: List<&2, W.W64>, s: RateLimit) -> RateLimitRun:
  match ts:
    case Nil{}:
      RateLimitRun{s, Nil{}}
    case Con{+t, rest}:
      +r = RateLimit.check(s, t)
      RateLimit.run.cons(RateLimitStep.allowed(r), RateLimit.run.go(rest, RateLimitStep.state(r)))

def RateLimit.run(s: RateLimit, ts: List<&2, W.W64>) -> RateLimitRun:
  RateLimit.run.go(ts, s)

# the number of refusals in a run's answers
def RateLimit.refusals(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{True{}, t}:
      RateLimit.refusals(t)
    case Con{False{}, t}:
      1n+RateLimit.refusals(t)

# Windows over a run: the times allowed, how many lie in a window, and
# whether times never go back

# the times of ts whose answers (a run's allowed list, in the same order)
# are True
def RateLimit.allowed_times.put(a: Bool, t: W.W64, rest: List<&2, W.W64>) -> List<&2, W.W64>:
  match a:
    case True{}:
      Con{t, rest}
    case False{}:
      rest

def RateLimit.allowed_times(ts: List<&2, W.W64>, xs: List<&2, Bool>) -> List<&2, W.W64>:
  match ts xs:
    case Nil{} _:
      Nil{}
    case Con{t, rest} Nil{}:
      Nil{}
    case Con{t, rest} Con{a, more}:
      RateLimit.allowed_times.put(a, t, RateLimit.allowed_times(rest, more))

# the number of times of ts within the window of length interval ending at
# now
def RateLimit.in_window(+interval: W.W64, +now: W.W64, ts: List<&2, W.W64>) -> Nat:
  List.length(&2, W.W64, RateLimit.keep(interval, now, ts))

# whether the times of ts, and then now, never decrease
def RateLimit.sorted_upto.next(rest: List<&2, W.W64>, now: W.W64) -> W.W64:
  match rest:
    case Nil{}:
      now
    case Con{t, r}:
      t

def RateLimit.sorted_upto(ts: List<&2, W.W64>, +now: W.W64) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{+t, +rest}:
      Bool.and(W.W64.is_le(t, RateLimit.sorted_upto.next(rest, now)), RateLimit.sorted_upto(rest, now))
