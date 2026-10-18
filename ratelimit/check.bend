import Base
import ../word64/word64.bend as W
import ./ratelimit.bend as R

def show(xs: List<&2, Bool>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{True{}, t}:
      "+" ++ show(t)
    case Con{False{}, t}:
      "-" ++ show(t)

def at(xs: List<&2, U32>) -> List<&2, W.W64>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{W.W64.from_u32(x), at(t)}

def report(r: R.RateLimitRun) -> String:
  match r:
    case R.RateLimitRun{s, a}:
      show(a) ++ " (" ++ Nat.show(R.RateLimitReport.suppressed(R.RateLimit.report(s))) ++ " callbacks suppressed)"

# burst 3 per 10 units of time
def main() -> IO(Unit):
  +ts = at([0, 1, 2, 3, 9, 10, 11, 12, 13, 25])
  +edge = at([0, 8, 9, 10, 11, 12])
  +i = W.W64.from_u32(10)
  do IO<Unit>:
    IO.print("sliding: " ++ report(R.RateLimit.run(R.RateLimit.new(i, 3), ts)))
    IO.print("fixed:   " ++ report(R.RateLimit.run(R.RateLimit.new_with(R.RateLimitFixed{}, i, 3), ts)))
    IO.print("sliding: " ++ report(R.RateLimit.run(R.RateLimit.new(i, 3), edge)))
    IO.print("fixed:   " ++ report(R.RateLimit.run(R.RateLimit.new_with(R.RateLimitFixed{}, i, 3), edge)))
    IO.print("off:     " ++ report(R.RateLimit.run(R.RateLimit.new(W.W64.zero(), 0), ts)))
    IO.print("burst 0: " ++ report(R.RateLimit.run(R.RateLimit.new(i, 0), edge)))
    IO.print("printk:  " ++ report(R.RateLimit.run(R.RateLimit.printk(W.W64.from_u32(1000)), at([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4999, 5000, 5001]))))
    IO.print("wrap:    " ++ report(R.RateLimit.run(R.RateLimit.new(i, 1), [W.W64.max(), W.W64.zero(), W.W64.from_u32(9), W.W64.from_u32(10)])))

#|sliding: +++--+++-+ (3 callbacks suppressed)
#|fixed:   +++--+++-+ (3 callbacks suppressed)
#|sliding: ++++-- (2 callbacks suppressed)
#|fixed:   ++++++ (0 callbacks suppressed)
#|off:     ++++++++++ (0 callbacks suppressed)
#|burst 0: ------ (6 callbacks suppressed)
#|printk:  ++++++++++---++ (3 callbacks suppressed)
#|wrap:    +-+- (2 callbacks suppressed)
