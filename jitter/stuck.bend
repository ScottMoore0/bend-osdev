# The stuck test of the CPU Jitter RNG (Müller, "CPU Time Jitter Based
# Non-Physical True Random Number Generator", section 3.1.6): for each time
# delta t_n it takes the first and second derivatives
#
#   t2_n = t_n - t_{n-1}        t3_n = t2_n - t2_{n-1}
#
# and the delta is stuck when t_n, t2_n or t3_n is 0. A stuck delta is not
# counted towards the deltas a block needs. Differences are modulo 2^64, so
# t2_n is 0 exactly when t_n = t_{n-1}, and t3_n is 0 exactly when
# t2_n = t2_{n-1}: that is how they are tested here.
import Base
import ../word64/word64.bend as W
import ./sample.bend as Sm

# the previous delta and the previous first derivative
type JitStuckState is Data:
  JitStuckState{prev: W.W64, prev2: W.W64}

# before any delta: both 0
def JitStuck.new() -> JitStuckState:
  JitStuckState{W.W64.zero(), W.W64.zero()}

# whether the delta t is stuck after the deltas the state has seen
def JitStuck.is_stuck(s: JitStuckState, +t: W.W64) -> Bool:
  match s:
    case JitStuckState{+p, p2}:
      Bool.or(W.W64.is_zero(t), Bool.or(Sm.JitSample.eq(t, p), Sm.JitSample.eq(W.W64.sub(t, p), p2)))

# the state after the delta t
def JitStuck.next(s: JitStuckState, +t: W.W64) -> JitStuckState:
  match s:
    case JitStuckState{p, p2}:
      JitStuckState{t, W.W64.sub(t, p)}
