# bend-osdev-dim: dynamic interrupt moderation, as a pure state machine.
#
# A driver hands Dim.step one sample per interval: the packets, bytes,
# events (interrupts) and completions of the interval, and the time it took
# (Dim.interval makes one from two readings of raw counters). The state
# machine compares the interval's rates with the previous interval's and
# decides whether to step the moderation profile (an index into a table of
# usec/packet pairs) right (more moderation), left (less), or to stay,
# aiming at the best throughput. It reads no clock and touches no device:
# the caller applies the profile the state names (Dim.profile) when a step
# says the index changed.
#
# The states and step results are those of the kernel's net_dim
# documentation (the README says which details are this package's own):
# * comparison: down a chain of criteria (by default bytes per msec,
#   higher is better; packets per msec, higher is better; events per msec,
#   lower is better), stopping at the first whose difference is significant
#   (more than a percentage of the old value): better or worse; if none is,
#   the same;
# * going right or left (DIM_GOING_RIGHT, DIM_GOING_LEFT): a better
#   interval steps on the same way, a worse one turns and steps the other
#   way (dim_turn), the same one parks on top (dim_on_top,
#   DIM_PARKING_ON_TOP);
# * a step (DIM_STEPPED) that cannot be taken because the index is on the
#   leftmost or rightmost profile (DIM_ON_EDGE), or that makes too many
#   steps of one kind since the last parking (DIM_TOO_TIRED), parks tired
#   (DIM_PARKING_TIRED);
# * parked on top, a significant difference (better or worse) starts
#   moving again: right from the leftmost profile, left otherwise;
# * parked tired, the state does not leave for tired samples whatever they
#   show; then it verifies its parking by a step the other way;
# * parking clears the counts of steps (the movement history).
import Base
import ../word64/word64.bend as W

# A moderation profile: wait up to usec microseconds, or up to pkts
# packets, before raising an interrupt
type DimProfile is Data:
  DimProfile{usec: U32, pkts: U32}

# One interval's counts and its length in microseconds
type DimSample is Data:
  DimSample{pkts: U32, bytes: U32, events: U32, comps: U32, elapsed: U32}

# Raw counters read at one moment: a timestamp in microseconds, and
# counters that wrap modulo 2^32 (as struct dim_sample holds them)
type DimCounters is Data:
  DimCounters{time: W.W64, pkts: U32, bytes: U32, events: U32, comps: U32}

# An interval's rates, per millisecond (as struct dim_stats)
type DimRates is Data:
  DimRates{bytes: W.W64, pkts: W.W64, events: W.W64, comps: W.W64}

type DimMetric is Data:
  DimBytes{}
  DimPackets{}
  DimEvents{}
  DimCompletions{}

# one criterion of the comparison: a rate, and whether higher is better
type DimCriterion is Data:
  DimCriterion{metric: DimMetric, higher_better: Bool}

type DimVerdict is Data:
  DimBetter{}
  DimSame{}
  DimWorse{}

# profiles: the table, least moderation first; start: the index a new
# state starts at; significance: the percentage of the old rate a
# difference must exceed; tired: samples a tired parking lasts; max_steps:
# steps of one kind (right, or left) since the last parking that make the
# state too tired to go on; chain: the criteria, in order
type DimParams is Data:
  DimParams{profiles: List<&2, DimProfile>, start: Nat, significance: U32, tired: Nat, max_steps: Nat, chain: List<&2, DimCriterion>}

# going (right: towards more moderation), with the steps right and left
# taken since the last parking; parked on top; or parked tired (right: the
# direction of the step that tired it; spent: the samples spent parked)
type DimMode is Data:
  DimGoing{right: Bool, steps_right: Nat, steps_left: Nat}
  DimParkedTop{}
  DimParkedTired{right: Bool, spent: Nat}

type Dim is Data:
  Dim{ix: Nat, mode: DimMode, prev: Maybe<&2, DimRates>}

# what a step answers: the new state, and whether its profile index
# changed (the driver then applies Dim.profile)
type DimStep is Data:
  DimStep{state: Dim, changed: Bool}

# Defaults (the document gives no numbers for these; see the README)

def DimParams.profiles_default() -> List<&2, DimProfile>:
  [DimProfile{2, 256}, DimProfile{8, 128}, DimProfile{32, 64}, DimProfile{64, 32}, DimProfile{128, 16}]

def DimParams.chain_default() -> List<&2, DimCriterion>:
  [DimCriterion{DimBytes{}, True{}}, DimCriterion{DimPackets{}, True{}}, DimCriterion{DimEvents{}, False{}}]

# for completion queues (rdma_dim's completions): the completion rate
# first, then the event rate
def DimParams.chain_completions() -> List<&2, DimCriterion>:
  [DimCriterion{DimCompletions{}, True{}}, DimCriterion{DimEvents{}, False{}}]

def DimParams.default() -> DimParams:
  DimParams{DimParams.profiles_default(), 0n, 10, 10n, 10n, DimParams.chain_default()}

# Observers

def DimParams.profiles(p: DimParams) -> List<&2, DimProfile>:
  match p:
    case DimParams{ps, s, g, t, x, c}:
      ps

def DimParams.tired(p: DimParams) -> Nat:
  match p:
    case DimParams{ps, s, g, t, x, c}:
      t

def DimParams.max_steps(p: DimParams) -> Nat:
  match p:
    case DimParams{ps, s, g, t, x, c}:
      x

def DimSample.elapsed(s: DimSample) -> U32:
  match s:
    case DimSample{p, b, e, c, t}:
      t

def DimStep.state(r: DimStep) -> Dim:
  match r:
    case DimStep{s, c}:
      s

def DimStep.changed(r: DimStep) -> Bool:
  match r:
    case DimStep{s, c}:
      c

def Dim.index(s: Dim) -> Nat:
  match s:
    case Dim{i, m, p}:
      i

def Dim.mode(s: Dim) -> DimMode:
  match s:
    case Dim{i, m, p}:
      m

# the previous interval's rates, once there has been one
def Dim.prev(s: Dim) -> Maybe<&2, DimRates>:
  match s:
    case Dim{i, m, p}:
      p

# whether the state is parked (on top or tired): the document's state in
# which checks become less frequent, so a caller may lengthen its intervals
def Dim.parked(s: Dim) -> Bool:
  match s:
    case Dim{i, DimGoing{r, a, b}, p}:
      False{}
    case Dim{i, DimParkedTop{}, p}:
      True{}
    case Dim{i, DimParkedTired{r, k}, p}:
      True{}

# whether the state's index is within the table
def Dim.valid(p: DimParams, s: Dim) -> Bool:
  Nat.is_lt(Dim.index(s), List.length(&2, DimProfile, DimParams.profiles(p)))

# the profile the state names
def Dim.profile(p: DimParams, s: Dim) -> Maybe<&2, DimProfile>:
  List.get(&2, DimProfile, DimParams.profiles(p), Dim.index(s))

# A new state: at the start index (0 if that is past the table), going
# right, with no previous interval

def Dim.new.at(inside: Bool, +start: Nat) -> Nat:
  match inside:
    case True{}:
      start
    case False{}:
      0n

def Dim.new(p: DimParams) -> Dim:
  match p:
    case DimParams{+ps, +s, g, t, x, c}:
      Dim{Dim.new.at(Nat.is_lt(s, List.length(&2, DimProfile, ps)), s), DimGoing{True{}, 0n, 0n}, None{}}

# An interval from two readings of raw counters: the counts between them
# (modulo 2^32, so a counter that wrapped counts right) and the time
# between them (at most 2^32 - 1 microseconds)

def Dim.interval.usec(hi_zero: Bool, lo: U32) -> U32:
  match hi_zero:
    case True{}:
      lo
    case False{}:
      4294967295

def Dim.interval(a: DimCounters, b: DimCounters) -> DimSample:
  match a b:
    case DimCounters{ta, pa, ba, ea, ca} DimCounters{tb, pb, bb, eb, cb}:
      +d = W.W64.sub(tb, ta)
      DimSample{U32.sub(pb, pa), U32.sub(bb, ba), U32.sub(eb, ea), U32.sub(cb, ca), Dim.interval.usec(U32.is_zero(W.W64.hi(d)), W.W64.lo(d))}

# Rates and their comparison

def Dim.rate(+v: U32, +usec: U32) -> W.W64:
  W.W64.div(W.W64.mul(W.W64.from_u32(v), W.W64.from_u32(1000)), W.W64.from_u32(usec))

def Dim.rates(s: DimSample) -> DimRates:
  match s:
    case DimSample{p, b, e, c, +t}:
      DimRates{Dim.rate(b, t), Dim.rate(p, t), Dim.rate(e, t), Dim.rate(c, t)}

def Dim.metric(m: DimMetric, r: DimRates) -> W.W64:
  match m r:
    case DimBytes{} DimRates{b, p, e, c}:
      b
    case DimPackets{} DimRates{b, p, e, c}:
      p
    case DimEvents{} DimRates{b, p, e, c}:
      e
    case DimCompletions{} DimRates{b, p, e, c}:
      c

# equal rates, compared through the halves
def Dim.same_rate(+a: W.W64, +b: W.W64) -> Bool:
  Bool.and(U32.is_eq(W.W64.hi(a), W.W64.hi(b)), U32.is_eq(W.W64.lo(a), W.W64.lo(b)))

def Dim.compare.sig(significant: Bool, c: Cmp) -> Cmp:
  match significant:
    case True{}:
      c
    case False{}:
      EQ{}

# the new rate a against the old b: GT for a significant rise, LT for a
# significant fall, EQ otherwise; significant: 100 * |a - b| > pct * b
def Dim.compare.move(up: Bool, +pct: U32, +a: W.W64, +b: W.W64) -> Cmp:
  match up:
    case True{}:
      Dim.compare.sig(W.W64.is_lt(W.W64.mul(b, W.W64.from_u32(pct)), W.W64.mul(W.W64.sub(a, b), W.W64.from_u32(100))), GT{})
    case False{}:
      Dim.compare.sig(W.W64.is_lt(W.W64.mul(b, W.W64.from_u32(pct)), W.W64.mul(W.W64.sub(b, a), W.W64.from_u32(100))), LT{})

def Dim.compare.rate.go(same: Bool, +pct: U32, +a: W.W64, +b: W.W64) -> Cmp:
  match same:
    case True{}:
      EQ{}
    case False{}:
      Dim.compare.move(W.W64.is_lt(b, a), pct, a, b)

def Dim.compare.rate(+pct: U32, +a: W.W64, +b: W.W64) -> Cmp:
  Dim.compare.rate.go(Dim.same_rate(a, b), pct, a, b)

# each criterion's comparison, with whether higher is better
type DimCmp is Data:
  DimCmp{cmp: Cmp, higher_better: Bool}

def Dim.compare.all(cs: List<&2, DimCriterion>, +pct: U32, +a: DimRates, +b: DimRates) -> List<&2, DimCmp>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{DimCriterion{+m, hb}, rest}:
      Con{DimCmp{Dim.compare.rate(pct, Dim.metric(m, a), Dim.metric(m, b)), hb}, Dim.compare.all(rest, pct, a, b)}

def Dim.verdict.of(up: Bool, higher_better: Bool) -> DimVerdict:
  match up higher_better:
    case True{} True{}:
      DimBetter{}
    case True{} False{}:
      DimWorse{}
    case False{} True{}:
      DimWorse{}
    case False{} False{}:
      DimBetter{}

# the first significant comparison decides
def Dim.verdict(xs: List<&2, DimCmp>) -> DimVerdict:
  match xs:
    case Nil{}:
      DimSame{}
    case Con{DimCmp{EQ{}, hb}, rest}:
      Dim.verdict(rest)
    case Con{DimCmp{GT{}, hb}, rest}:
      Dim.verdict.of(True{}, hb)
    case Con{DimCmp{LT{}, hb}, rest}:
      Dim.verdict.of(False{}, hb)

def Dim.compare.with(cs: List<&2, DimCriterion>, +pct: U32, +a: DimRates, +b: DimRates) -> DimVerdict:
  Dim.verdict(Dim.compare.all(cs, pct, a, b))

# a new interval's rates against the previous interval's
def Dim.compare(p: DimParams, +a: DimRates, +b: DimRates) -> DimVerdict:
  match p:
    case DimParams{ps, s, pct, t, x, cs}:
      Dim.compare.with(cs, pct, a, b)

# Steps

def Dim.mk(+ix: Nat, m: DimMode, r: DimRates, changed: Bool) -> DimStep:
  DimStep{Dim{ix, m, Some{r}}, changed}

# whether a step that way stays within a table of len profiles (if not,
# the index is on that edge: DIM_ON_EDGE)
def Dim.can(+len: Nat, right: Bool, +ix: Nat) -> Bool:
  match right:
    case True{}:
      Nat.is_lt(1n+ix, len)
    case False{}:
      Nat.is_lt(0n, ix)

# after a step: too tired (DIM_TOO_TIRED), or going on (DIM_STEPPED)
def Dim.land(tired: Bool, right: Bool, +ix: Nat, +rs: Nat, +ls: Nat, r: DimRates) -> DimStep:
  match tired:
    case True{}:
      Dim.mk(ix, DimParkedTired{right, 0n}, r, True{})
    case False{}:
      Dim.mk(ix, DimGoing{right, rs, ls}, r, True{})

def Dim.walk.go(can: Bool, right: Bool, +rs: Nat, +ls: Nat, +maxs: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match can:
    case True{}:
      match right:
        case True{}:
          Dim.land(Nat.is_le(maxs, 1n+rs), True{}, 1n+ix, 1n+rs, ls, r)
        case False{}:
          Dim.land(Nat.is_le(maxs, 1n+ls), False{}, Nat.sub(ix, 1n), rs, 1n+ls, r)
    case False{}:
      Dim.mk(ix, DimParkedTired{right, 0n}, r, False{})

# a step that way, with the steps taken so far
def Dim.walk(+len: Nat, +maxs: Nat, +right: Bool, +rs: Nat, +ls: Nat, +ix: Nat, r: DimRates) -> DimStep:
  Dim.walk.go(Dim.can(len, right, ix), right, rs, ls, maxs, ix, r)

def Dim.decide.going(c: DimVerdict, +right: Bool, +rs: Nat, +ls: Nat, +len: Nat, +maxs: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match c:
    case DimSame{}:
      Dim.mk(ix, DimParkedTop{}, r, False{})
    case DimBetter{}:
      Dim.walk(len, maxs, right, rs, ls, ix, r)
    case DimWorse{}:
      Dim.walk(len, maxs, Bool.not(right), rs, ls, ix, r)

def Dim.decide.top(c: DimVerdict, +len: Nat, +maxs: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match c:
    case DimSame{}:
      Dim.mk(ix, DimParkedTop{}, r, False{})
    case DimBetter{}:
      Dim.walk(len, maxs, Nat.is_eq(ix, 0n), 0n, 0n, ix, r)
    case DimWorse{}:
      Dim.walk(len, maxs, Nat.is_eq(ix, 0n), 0n, 0n, ix, r)

# parked tired: whatever the interval shows, wait out the parking, then
# verify it by a step the other way
def Dim.decide.tired(out: Bool, +right: Bool, +k: Nat, +len: Nat, +maxs: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match out:
    case True{}:
      Dim.walk(len, maxs, Bool.not(right), 0n, 0n, ix, r)
    case False{}:
      Dim.mk(ix, DimParkedTired{right, 1n+k}, r, False{})

def Dim.decide(m: DimMode, c: DimVerdict, +len: Nat, +limit: Nat, +maxs: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match m:
    case DimGoing{right, rs, ls}:
      Dim.decide.going(c, right, rs, ls, len, maxs, ix, r)
    case DimParkedTop{}:
      Dim.decide.top(c, len, maxs, ix, r)
    case DimParkedTired{+right, +k}:
      Dim.decide.tired(Nat.is_le(limit, k), right, k, len, maxs, ix, r)

def Dim.step.prev(prev: Maybe<&2, DimRates>, p: DimParams, +ix: Nat, m: DimMode, +r: DimRates) -> DimStep:
  match prev:
    case None{}:
      DimStep{Dim{ix, m, Some{r}}, False{}}
    case Some{q}:
      match p:
        case DimParams{ps, s, pct, limit, maxs, cs}:
          Dim.decide(m, Dim.compare.with(cs, pct, r, q), List.length(&2, DimProfile, ps), limit, maxs, ix, r)

def Dim.step.on(skip: Bool, p: DimParams, st: Dim, s: DimSample) -> DimStep:
  match skip:
    case True{}:
      DimStep{st, False{}}
    case False{}:
      match st:
        case Dim{+ix, m, prev}:
          Dim.step.prev(prev, p, ix, m, Dim.rates(s))

# one interval's sample (net_dim): the new state, and whether the profile
# changed. A sample of no time (elapsed 0) gives no reliable rates and is
# ignored.
def Dim.step(p: DimParams, st: Dim, +s: DimSample) -> DimStep:
  Dim.step.on(U32.is_zero(DimSample.elapsed(s)), p, st, s)

# samples in order: the final state
def Dim.run.go(ss: List<&2, DimSample>, +p: DimParams, st: Dim) -> Dim:
  match ss:
    case Nil{}:
      st
    case Con{s, rest}:
      Dim.run.go(rest, p, DimStep.state(Dim.step(p, st, s)))

def Dim.run(+p: DimParams, st: Dim, ss: List<&2, DimSample>) -> Dim:
  Dim.run.go(ss, p, st)

# how many identical samples bring any state to rest, for a table of at
# least two profiles and max_steps of at least 2 (see LAWS.bend)
def Dim.settle_bound(p: DimParams) -> Nat:
  match p:
    case DimParams{ps, s, g, +t, x, c}:
      3n+Nat.add(t, 1n+t)
