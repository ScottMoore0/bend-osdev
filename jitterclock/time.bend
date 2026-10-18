# Time stamps, pure: a clock reading's two halves as a W64, the deltas
# between consecutive stamps (modulo 2^64), and how many deltas a read
# collects.
import Base
import ../word64/word64.bend as W
import ../jitter/jitter.bend as J

# the stamp with these halves (high, low)
def JClock.time.join(p: U32 & U32) -> W.W64:
  (h, l) = p
  W.W64.from_parts(h, l)

def JClock.time.deltas.from(ts: List<&2, W.W64>, +prev: W.W64) -> List<&2, W.W64>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      Con{W.W64.sub(t, prev), JClock.time.deltas.from(rest, t)}

# each stamp minus the one before it: one fewer than the stamps
def JClock.time.deltas(ts: List<&2, W.W64>) -> List<&2, W.W64>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      JClock.time.deltas.from(rest, t)

# the deltas a read of n bytes collects: twice what the blocks need (32
# bytes a block, and the blocks discarded first), and 64 more, so that
# stuck deltas (about 7% on the machine the tests were written on) leave
# enough
def JClock.time.budget(+p: J.JitParams, n: Nat) -> Nat:
  Nat.add(64n, Nat.mul(Nat.mul(2n, J.JitParams.need(p)), Nat.add(J.JitParams.prime(p), Nat.div(Nat.add(n, 31n), 32n))))
