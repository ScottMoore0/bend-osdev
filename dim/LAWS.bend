# Properties, for every parameter record (profile table, thresholds and
# criteria), state and sample:
#
# * the profile index stays within the table: a new state's index is in
#   it (for a table that is not empty), and a step, or any run of steps,
#   keeps a state's index in it; so the state always names a profile;
# * a step changes the index by at most one, and a step that reports no
#   change leaves the index as it was;
# * identical samples converge, wherever the documented parking
#   behaviour guarantees it: in a table of at least two profiles, with
#   max_steps at least 2, an interval compares the same as itself, and
#   after Dim.settle_bound(p) identical samples (twice the tired count,
#   plus four) the state is at rest, a fixed point of a step with that
#   sample, so every further identical sample leaves it, and its profile,
#   as it is. Going, the same interval parks on top, where it stays;
#   parked tired, it waits out the parking, verifies by a step the other
#   way (or, on an edge, parks tired once more and steps inward), and then
#   parks on top. In a table of one profile a tired parking repeats (the
#   index stays), and with max_steps below 2 every verifying step is too
#   tired: those are the documented behaviour's own cycles.
#
# Vectors: a run that climbs while the throughput improves and parks on
# top when it stops improving; one that steps onto the edge, parks tired
# and verifies; an interval from wrapping counters.
import Base
import ../word64/word64.bend as W
import ./dim.bend as D

# The index stays within the table

law dim_new_valid:
  for p: D.DimParams
  for h: {Nat.is_lt(0n, List.length(&2, D.DimProfile, D.DimParams.profiles(p))) == True{} : Bool}
  {D.Dim.valid(p, D.Dim.new(p)) == True{} : Bool}

law dim_step_valid:
  for +p: D.DimParams
  for +st: D.Dim
  for +s: D.DimSample
  for +v: {D.Dim.valid(p, st) == True{} : Bool}
  {D.Dim.valid(p, D.DimStep.state(D.Dim.step(p, st, s))) == True{} : Bool}

law dim_run_valid:
  for +p: D.DimParams
  for +st: D.Dim
  for +ss: List<&2, D.DimSample>
  for +v: {D.Dim.valid(p, st) == True{} : Bool}
  {D.Dim.valid(p, D.Dim.run(p, st, ss)) == True{} : Bool}

law dim_profile_some:
  for +p: D.DimParams
  for +st: D.Dim
  for +v: {D.Dim.valid(p, st) == True{} : Bool}
  {Maybe.is_some(&2, D.DimProfile, D.Dim.profile(p, st)) == True{} : Bool}

# At most one step at a time

law dim_step_by_one:
  for +p: D.DimParams
  for +st: D.Dim
  for +s: D.DimSample
  {Bool.and(Nat.is_le(D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))), 1n+D.Dim.index(st)), Nat.is_le(D.Dim.index(st), 1n+D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))))) == True{} : Bool}

law dim_unchanged:
  for +p: D.DimParams
  for +st: D.Dim
  for +s: D.DimSample
  for +u: {D.DimStep.changed(D.Dim.step(p, st, s)) == False{} : Bool}
  {D.Dim.index(D.DimStep.state(D.Dim.step(p, st, s))) == D.Dim.index(st) : Nat}

# Identical samples converge

law dim_same_rates:
  for +p: D.DimParams
  for +s: D.DimSample
  {D.Dim.compare(p, D.Dim.rates(s), D.Dim.rates(s)) == D.DimSame{} : D.DimVerdict}

law dim_settles:
  for +p: D.DimParams
  for +st: D.Dim
  for +s: D.DimSample
  for +hl: {Nat.is_lt(1n, List.length(&2, D.DimProfile, D.DimParams.profiles(p))) == True{} : Bool}
  for +hm: {Nat.is_le(2n, D.DimParams.max_steps(p)) == True{} : Bool}
  {D.DimStep.state(D.Dim.step(p, D.Dim.run(p, st, List.replicate(D.DimSample, D.Dim.settle_bound(p), s)), s)) == D.Dim.run(p, st, List.replicate(D.DimSample, D.Dim.settle_bound(p), s)) : D.Dim}

law dim_rest:
  for +p: D.DimParams
  for +x: D.Dim
  for +s: D.DimSample
  for +n: Nat
  for +f: {D.DimStep.state(D.Dim.step(p, x, s)) == x : D.Dim}
  {D.Dim.run(p, x, List.replicate(D.DimSample, n, s)) == x : D.Dim}

# Witnesses and vectors (intervals of 1 ms with b bytes, b / 1000 packets
# and 100 events; each vector computes one run, which keeps it within
# --verdict's fuel)

law dim_wit:
  {(Nat.is_lt(0n, List.length(&2, D.DimProfile, D.DimParams.profiles(D.DimParams.default()))), Nat.is_lt(1n, List.length(&2, D.DimProfile, D.DimParams.profiles(D.DimParams.default()))), Nat.is_le(2n, D.DimParams.max_steps(D.DimParams.default())), D.Dim.valid(D.DimParams.default(), D.Dim.new(D.DimParams.default())), D.DimStep.changed(D.Dim.step(D.DimParams.default(), D.Dim.new(D.DimParams.default()), D.DimSample{1000, 1000000, 100, 0, 1000}))) == (True{}, True{}, True{}, True{}, False{}) : Bool & Bool & Bool & Bool & Bool}

# the byte rate rises 20% twice: two steps right; then within 10%: parked
# on top
law dim_vec_climb_index:
  {D.Dim.index(D.Dim.run(D.DimParams.default(), D.Dim.new(D.DimParams.default()), [D.DimSample{1000, 1000000, 100, 0, 1000}, D.DimSample{1200, 1200000, 100, 0, 1000}, D.DimSample{1440, 1440000, 100, 0, 1000}, D.DimSample{1400, 1400000, 100, 0, 1000}])) == 2n : Nat}

law dim_vec_climb_mode:
  {D.Dim.mode(D.Dim.run(D.DimParams.default(), D.Dim.new(D.DimParams.default()), [D.DimSample{1000, 1000000, 100, 0, 1000}, D.DimSample{1200, 1200000, 100, 0, 1000}, D.DimSample{1440, 1440000, 100, 0, 1000}, D.DimSample{1400, 1400000, 100, 0, 1000}])) == D.DimParkedTop{} : D.DimMode}

# two profiles, starting on the right one: a better interval cannot step
# right (on the edge), so it parks tired; with tired 0 the next sample
# verifies by a step left
law dim_vec_edge_index:
  {D.Dim.index(D.Dim.run(D.DimParams{[D.DimProfile{1, 1}, D.DimProfile{2, 2}], 1n, 10, 0n, 10n, D.DimParams.chain_default()}, D.Dim.new(D.DimParams{[D.DimProfile{1, 1}, D.DimProfile{2, 2}], 1n, 10, 0n, 10n, D.DimParams.chain_default()}), [D.DimSample{1000, 1000000, 100, 0, 1000}, D.DimSample{1200, 1200000, 100, 0, 1000}, D.DimSample{1200, 1200000, 100, 0, 1000}])) == 0n : Nat}

law dim_vec_edge_mode:
  {D.Dim.mode(D.Dim.run(D.DimParams{[D.DimProfile{1, 1}, D.DimProfile{2, 2}], 1n, 10, 0n, 10n, D.DimParams.chain_default()}, D.Dim.new(D.DimParams{[D.DimProfile{1, 1}, D.DimProfile{2, 2}], 1n, 10, 0n, 10n, D.DimParams.chain_default()}), [D.DimSample{1000, 1000000, 100, 0, 1000}, D.DimSample{1200, 1200000, 100, 0, 1000}, D.DimSample{1200, 1200000, 100, 0, 1000}])) == D.DimGoing{False{}, 0n, 1n} : D.DimMode}

# an interval from counters that wrapped
law dim_vec_interval:
  {D.Dim.interval(D.DimCounters{W.W64.from_u32(1000), 4294967290, 7, 3, 0}, D.DimCounters{W.W64.from_u32(2500), 10, 1007, 5, 9}) == D.DimSample{16, 1000, 2, 9, 1500} : D.DimSample}
