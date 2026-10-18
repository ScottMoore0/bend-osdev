# bend-osdev-dim: dynamic interrupt moderation, as a pure state machine.
#
# A driver hands Dim.step one sample per interval: the packets, bytes,
# events (interrupts) and completions of the interval, and the time it took.
# The state machine compares the interval's rates with the previous
# interval's and decides whether to step the moderation profile (an index
# into a table of usec/packet pairs) up (more moderation), down (less), or
# to stay, aiming at the best throughput. It reads no clock and touches no
# device: the caller applies the profile the state names (Dim.profile) when
# a step says the index changed.
#
# The decision (written from the kernel's net_dim documentation, in this
# package's own words; see the README):
# * a comparison of two intervals goes down a chain of criteria (by default
#   the byte rate, higher is better; then the packet rate, higher is
#   better; then the event rate, lower is better) and stops at the first
#   whose difference is significant (more than a percentage of the old
#   value): better or worse; if none is, the two are the same;
# * going in a direction (right: more moderation; left: less), a better
#   interval takes another step that way, a worse one steps back the other
#   way, and the same one parks: the index stays;
# * parked, a change (better or worse) resumes moving: right from the
#   leftmost profile, left otherwise. Parked on an edge of the table (the
#   leftmost or the rightmost profile) for tired samples in a row, it
#   probes one step inward, to check that the edge is still the best place;
#   if the probe makes no difference it settles there, and moves again only
#   on a change.
import Base
import ../word64/word64.bend as W

# A moderation profile: wait up to usec microseconds, or up to pkts
# packets, before raising an interrupt
type DimProfile is Data:
  DimProfile{usec: U32, pkts: U32}

# One interval's counts and its length in microseconds
type DimSample is Data:
  DimSample{pkts: U32, bytes: U32, events: U32, comps: U32, elapsed: U32}

# An interval's rates, per second
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
# difference must exceed; tired: samples parked on an edge before a probe
# (0: never probe); chain: the criteria, in order
type DimParams is Data:
  DimParams{profiles: List<&2, DimProfile>, start: Nat, significance: U32, tired: Nat, chain: List<&2, DimCriterion>}

# going (right: towards more moderation; probe: this step was a probe from
# an edge), parked (with the samples parked on an edge so far), or settled
# after a probe that made no difference
type DimMode is Data:
  DimGoing{right: Bool, probe: Bool}
  DimParked{tired: Nat}
  DimSettled{}

type Dim is Data:
  Dim{ix: Nat, mode: DimMode, prev: Maybe<&2, DimRates>}

# what a step answers: the new state, and whether its profile index
# changed (the driver then applies Dim.profile)
type DimStep is Data:
  DimStep{state: Dim, changed: Bool}

# Defaults

def DimParams.profiles_default() -> List<&2, DimProfile>:
  [DimProfile{2, 256}, DimProfile{8, 128}, DimProfile{32, 64}, DimProfile{64, 32}, DimProfile{128, 16}]

def DimParams.chain_default() -> List<&2, DimCriterion>:
  [DimCriterion{DimBytes{}, True{}}, DimCriterion{DimPackets{}, True{}}, DimCriterion{DimEvents{}, False{}}]

# for completion queues (as RDMA's use of the same algorithm): the
# completion rate first, then the event rate
def DimParams.chain_completions() -> List<&2, DimCriterion>:
  [DimCriterion{DimCompletions{}, True{}}, DimCriterion{DimEvents{}, False{}}]

def DimParams.default() -> DimParams:
  DimParams{DimParams.profiles_default(), 0n, 10, 10n, DimParams.chain_default()}

# Observers

def DimParams.profiles(p: DimParams) -> List<&2, DimProfile>:
  match p:
    case DimParams{ps, s, g, t, c}:
      ps

def DimParams.tired(p: DimParams) -> Nat:
  match p:
    case DimParams{ps, s, g, t, c}:
      t

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
    case DimParams{+ps, +s, g, t, c}:
      Dim{Dim.new.at(Nat.is_lt(s, List.length(&2, DimProfile, ps)), s), DimGoing{True{}, False{}}, None{}}

# Rates and their comparison

def Dim.rate(+v: U32, +usec: U32) -> W.W64:
  W.W64.div(W.W64.mul(W.W64.from_u32(v), W.W64.from_u32(1000000)), W.W64.from_u32(usec))

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
    case DimParams{ps, s, pct, t, cs}:
      Dim.compare.with(cs, pct, a, b)

# Steps

def Dim.mk(+ix: Nat, m: DimMode, r: DimRates, changed: Bool) -> DimStep:
  DimStep{Dim{ix, m, Some{r}}, changed}

# whether a step that way stays within a table of len profiles
def Dim.can(+len: Nat, right: Bool, +ix: Nat) -> Bool:
  match right:
    case True{}:
      Nat.is_lt(1n+ix, len)
    case False{}:
      Nat.is_lt(0n, ix)

def Dim.move.go(can: Bool, right: Bool, +ix: Nat, r: DimRates) -> DimStep:
  match can:
    case True{}:
      match right:
        case True{}:
          Dim.mk(1n+ix, DimGoing{True{}, False{}}, r, True{})
        case False{}:
          Dim.mk(Nat.sub(ix, 1n), DimGoing{False{}, False{}}, r, True{})
    case False{}:
      Dim.mk(ix, DimParked{0n}, r, False{})

# a step that way if there is room; parked if not
def Dim.move(+len: Nat, +right: Bool, +ix: Nat, r: DimRates) -> DimStep:
  Dim.move.go(Dim.can(len, right, ix), right, ix, r)

# a probe from an edge, one step inward
def Dim.probe(right: Bool, +ix: Nat, r: DimRates) -> DimStep:
  match right:
    case True{}:
      Dim.mk(1n+ix, DimGoing{True{}, True{}}, r, True{})
    case False{}:
      Dim.mk(Nat.sub(ix, 1n), DimGoing{False{}, True{}}, r, True{})

# the inward direction from an edge: right from the leftmost profile, left
# from the rightmost; None in the middle, or in a table of one profile
def Dim.inward.go(multi: Bool, left: Bool, right: Bool) -> Maybe<&2, Bool>:
  match multi:
    case False{}:
      None{}
    case True{}:
      match left:
        case True{}:
          Some{True{}}
        case False{}:
          match right:
            case True{}:
              Some{False{}}
            case False{}:
              None{}

def Dim.inward(+len: Nat, +ix: Nat) -> Maybe<&2, Bool>:
  Dim.inward.go(Nat.is_lt(1n, len), Nat.is_eq(ix, 0n), Nat.is_eq(1n+ix, len))

def Dim.tire.go(off: Bool, tired: Bool, dir: Bool, +t: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match off:
    case True{}:
      Dim.mk(ix, DimParked{t}, r, False{})
    case False{}:
      match tired:
        case True{}:
          Dim.probe(dir, ix, r)
        case False{}:
          Dim.mk(ix, DimParked{1n+t}, r, False{})

# parked, and the interval the same: count the samples on an edge, and
# probe inward when there have been tired of them
def Dim.tire(edge: Maybe<&2, Bool>, +limit: Nat, +t: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match edge:
    case None{}:
      Dim.mk(ix, DimParked{t}, r, False{})
    case Some{dir}:
      Dim.tire.go(Nat.is_eq(limit, 0n), Nat.is_le(limit, 1n+t), dir, t, ix, r)

# parked or settled, and the interval changed: move again
def Dim.resume(+len: Nat, +ix: Nat, r: DimRates) -> DimStep:
  Dim.move(len, Nat.is_eq(ix, 0n), ix, r)

# going, and the interval the same: park (settle, after a probe)
def Dim.decide.park(probe: Bool, +ix: Nat, r: DimRates) -> DimStep:
  match probe:
    case True{}:
      Dim.mk(ix, DimSettled{}, r, False{})
    case False{}:
      Dim.mk(ix, DimParked{0n}, r, False{})

def Dim.decide.going(c: DimVerdict, +right: Bool, probe: Bool, +len: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match c:
    case DimSame{}:
      Dim.decide.park(probe, ix, r)
    case DimBetter{}:
      Dim.move(len, right, ix, r)
    case DimWorse{}:
      Dim.move(len, Bool.not(right), ix, r)

def Dim.decide.parked(c: DimVerdict, +t: Nat, +len: Nat, +limit: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match c:
    case DimSame{}:
      Dim.tire(Dim.inward(len, ix), limit, t, ix, r)
    case DimBetter{}:
      Dim.resume(len, ix, r)
    case DimWorse{}:
      Dim.resume(len, ix, r)

def Dim.decide.settled(c: DimVerdict, +len: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match c:
    case DimSame{}:
      Dim.mk(ix, DimSettled{}, r, False{})
    case DimBetter{}:
      Dim.resume(len, ix, r)
    case DimWorse{}:
      Dim.resume(len, ix, r)

def Dim.decide(m: DimMode, c: DimVerdict, +len: Nat, +limit: Nat, +ix: Nat, r: DimRates) -> DimStep:
  match m:
    case DimGoing{right, probe}:
      Dim.decide.going(c, right, probe, len, ix, r)
    case DimParked{t}:
      Dim.decide.parked(c, t, len, limit, ix, r)
    case DimSettled{}:
      Dim.decide.settled(c, len, ix, r)

def Dim.step.prev(prev: Maybe<&2, DimRates>, p: DimParams, +ix: Nat, m: DimMode, +r: DimRates) -> DimStep:
  match prev:
    case None{}:
      DimStep{Dim{ix, m, Some{r}}, False{}}
    case Some{q}:
      match p:
        case DimParams{ps, s, pct, limit, cs}:
          Dim.decide(m, Dim.compare.with(cs, pct, r, q), List.length(&2, DimProfile, ps), limit, ix, r)

def Dim.step.on(skip: Bool, p: DimParams, st: Dim, s: DimSample) -> DimStep:
  match skip:
    case True{}:
      DimStep{st, False{}}
    case False{}:
      match st:
        case Dim{+ix, m, prev}:
          Dim.step.prev(prev, p, ix, m, Dim.rates(s))

# one interval's sample (net_dim): the new state, and whether the profile
# changed. A sample of no time (elapsed 0) is ignored.
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

# how many identical samples bring any state to rest (see LAWS.bend)
def Dim.settle_bound(p: DimParams) -> Nat:
  4n+DimParams.tired(p)
