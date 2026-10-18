# The pure parts of jitterclock (time.bend), for every input: a reading's
# halves joined give a stamp with those halves; the deltas are one fewer
# than the stamps, and each is a stamp minus the one before it. Vectors:
# the deltas of three stamps, and the deltas a 32-byte read collects under
# the default parameters.
#
# The clock effect itself (jitterclock.bend's JClock.eff.now, and the defs
# that read it) has no laws: it is tested on both lanes (check.bend, and
# ref/ against Python's reading of the same clock).
import Base
import ../word64/word64.bend as W
import ../jitter/jitter.bend as J
import ./time.bend as T

law time_join_hi:
  for +h: U32
  for +l: U32
  {W.W64.hi(T.JClock.time.join((h, l))) == h : U32}

law time_join_lo:
  for +h: U32
  for +l: U32
  {W.W64.lo(T.JClock.time.join((h, l))) == l : U32}

law deltas_length:
  for ts: List<&2, W.W64>
  {List.length(&2, W.W64, T.JClock.time.deltas(ts)) == Nat.sub(List.length(&2, W.W64, ts), 1n) : Nat}

law deltas_step:
  for +a: W.W64
  for +b: W.W64
  for t: List<&2, W.W64>
  {T.JClock.time.deltas(Con{a, Con{b, t}}) == Con{W.W64.sub(b, a), T.JClock.time.deltas(Con{b, t})} : List<&2, W.W64>}

law deltas_vec:
  {T.JClock.time.deltas([W.W64.from_u32(1), W.W64.from_u32(4), W.W64.from_u32(9)]) == [W.W64.from_u32(3), W.W64.from_u32(5)] : List<&2, W.W64>}

# 64 + 2 * 963 * (1 discarded + 1 block)
law budget_default:
  {T.JClock.time.budget(J.JitParams.default(), 32n) == 3916n : Nat}
