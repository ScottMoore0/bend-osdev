# The two approved continuous health tests of NIST SP 800-90B (January
# 2018), section 4.4, as pure state machines over samples (W64 time
# deltas, compared as sample.bend compares them). Each takes its cutoff C
# (and the APT its window W) as an argument, and a failure, once signalled,
# stays: the state answers failed from then on.
#
# Repetition Count Test (section 4.4.1): A is the first sample and B = 1;
# for each later sample X, if X = A then B = B + 1 and a failure is
# signalled if B >= C, else A = X and B = 1. With an entropy estimate of H
# bits per sample and a false-positive probability alpha, C = 1 +
# ceil(-log2(alpha) / H).
#
# Adaptive Proportion Test (section 4.4.2): A is the first sample of a
# window and B = 1; for each of the next W - 1 samples, if it equals A
# then B = B + 1, and a failure is signalled if B >= C; then a new window
# starts with the next sample. W is 512 for a source with more than two
# values.
import Base
import ../word64/word64.bend as W
import ./sample.bend as Sm

# ---------------------------------------------------------------- RCT

# a: the sample repeated, b: how many times in a row, started: whether a
# sample has been seen, failed: whether the test has failed
type JitRct is Data:
  JitRct{a: W.W64, b: Nat, started: Bool, failed: Bool}

def JitRct.new() -> JitRct:
  JitRct{W.W64.zero(), 0n, False{}, False{}}

def JitRct.failed(r: JitRct) -> Bool:
  match r:
    case JitRct{a, b, s, f}:
      f

# B: the length of the current run of identical samples
def JitRct.count(r: JitRct) -> Nat:
  match r:
    case JitRct{a, b, s, f}:
      b

def jit.rct.same(same: Bool, +c: Nat, a: W.W64, +b: Nat, f: Bool, x: W.W64) -> JitRct:
  match same:
    case True{}:
      JitRct{a, 1n+b, True{}, Bool.or(f, Nat.is_le(c, 1n+b))}
    case False{}:
      JitRct{x, 1n, True{}, f}

# the test after one more sample, with cutoff c
def JitRct.feed(+c: Nat, r: JitRct, +x: W.W64) -> JitRct:
  match r:
    case JitRct{+a, b, s, f}:
      match s:
        case False{}:
          JitRct{x, 1n, True{}, f}
        case True{}:
          jit.rct.same(Sm.JitSample.eq(x, a), c, a, b, f, x)

def jit.rct.run(xs: List<&2, W.W64>, +c: Nat, r: JitRct) -> JitRct:
  match xs:
    case Nil{}:
      r
    case Con{x, rest}:
      jit.rct.run(rest, c, JitRct.feed(c, r, x))

# the test after samples in order
def JitRct.run(+c: Nat, r: JitRct, xs: List<&2, W.W64>) -> JitRct:
  jit.rct.run(xs, c, r)

# ---------------------------------------------------------------- APT

# a: the window's first sample, b: how many of the window's samples equal
# it, i: how many samples the window has seen, open: whether the window
# takes more samples, failed: whether the test has failed
type JitApt is Data:
  JitApt{a: W.W64, b: Nat, i: Nat, open: Bool, failed: Bool}

def JitApt.new() -> JitApt:
  JitApt{W.W64.zero(), 0n, 0n, False{}, False{}}

def JitApt.failed(t: JitApt) -> Bool:
  match t:
    case JitApt{a, b, i, o, f}:
      f

# B: how many of the window's samples equal its first
def JitApt.count(t: JitApt) -> Nat:
  match t:
    case JitApt{a, b, i, o, f}:
      b

# A: the window's first sample
def JitApt.base(t: JitApt) -> W.W64:
  match t:
    case JitApt{a, b, i, o, f}:
      a

def jit.apt.same(same: Bool, +w: Nat, +c: Nat, a: W.W64, +b: Nat, +i2: Nat, f: Bool) -> JitApt:
  match same:
    case True{}:
      JitApt{a, 1n+b, i2, Nat.is_lt(i2, w), Bool.or(f, Nat.is_le(c, 1n+b))}
    case False{}:
      JitApt{a, b, i2, Nat.is_lt(i2, w), f}

# the test after one more sample, with window w and cutoff c
def JitApt.feed(+w: Nat, +c: Nat, t: JitApt, +x: W.W64) -> JitApt:
  match t:
    case JitApt{+a, b, i, o, f}:
      match o:
        case False{}:
          JitApt{x, 1n, 1n, Nat.is_lt(1n, w), f}
        case True{}:
          jit.apt.same(Sm.JitSample.eq(x, a), w, c, a, b, 1n+i, f)

def jit.apt.run(xs: List<&2, W.W64>, +w: Nat, +c: Nat, t: JitApt) -> JitApt:
  match xs:
    case Nil{}:
      t
    case Con{x, rest}:
      jit.apt.run(rest, w, c, JitApt.feed(w, c, t, x))

# the test after samples in order
def JitApt.run(+w: Nat, +c: Nat, t: JitApt, xs: List<&2, W.W64>) -> JitApt:
  jit.apt.run(xs, w, c, t)
