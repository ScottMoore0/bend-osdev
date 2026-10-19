# The reference test's program (run.sh): 200 stamps from the clock, each
# read after hashing the one before, then their deltas, one line each.
import Base
import ../../word64/word64.bend as W
import ../time.bend as T
import ../jitterclock.bend as C

def shows(xs: List<&2, W.W64>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      W.W64.show(x) ++ " " ++ shows(t)

def report(+ts: List<&2, W.W64>) -> IO(Unit):
  do IO<Unit>:
    IO.print(shows(ts))
    IO.print(shows(T.JClock.time.deltas(ts)))

def main() -> IO(Unit):
  do IO<Unit>:
    ts : List<&2, W.W64> <- C.JClock.stamps(200n)
    report(ts)
