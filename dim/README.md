# bend-osdev-dim

Dynamic interrupt moderation (DIM), in the style of the Linux kernel's
`net_dim`, as a pure state machine. A driver hands `Dim.step` one sample per
interval (the packets, bytes, events and completions of the interval, and
the time it took); the state machine compares the interval's rates with the
previous interval's and decides whether to step the moderation profile (an
index into a table of usec/packet pairs) up, down, or to stay, aiming at the
best throughput. It reads no clock and touches no device: when a step says
the index changed, the driver applies `Dim.profile(p, state)`.

## Specification

The kernel's documentation, `Documentation/networking/net_dim.rst` ("Net
DIM - Generic Network Dynamic Interrupt Moderation", Tal Gilboa). This
package was written from that document only, restated in its own words;
**no kernel source was read** (in particular not `lib/dim`), and the
document was not re-read in this session (it had no network access): the
behaviour below is what this package commits to, and its laws and tests
hold it to that. What the document describes:

* each iteration takes a new sample, compares it with the previous one,
  decides on a moderation configuration from a table of predefined
  profiles, and leaves it to the driver to apply it;
* the comparison: bandwidth first (more is better), then, if that did not
  change, the packet rate (more is better), then the interrupt rate (fewer
  is better); a difference counts only if it exceeds a percentage of the
  old value;
* the algorithm's state is its direction: going left (less moderation),
  going right (more), or standing still (parked); after parking on the
  leftmost or rightmost profile it may check that decision by a step the
  other way, so as not to get stuck there;
* the tuning section: the profile table (usec and packet counts per
  profile) is a per-device setting.

Where the document leaves room, this package chooses (each a parameter
where it is a real choice):

* **The sample** is per interval (`DimSample{pkts, bytes, events, comps,
  elapsed}`, elapsed in microseconds), and rates are per second, in `W64`
  (bend-osdev-word64): `value * 10^6 / elapsed`. A sample with `elapsed`
  0 is ignored. Counting events up to an interval is the driver's.
* **The comparison** goes down a chain of criteria (`DimParams.chain`):
  `chain_default()` is bytes, packets (both higher is better), events
  (lower is better); `chain_completions()` puts the completion rate first,
  for completion queues. A rate rises or falls significantly when
  `100 * |new - old| > significance * old`.
* **Going** in a direction, a better interval takes another step that way,
  a worse one steps back the other way, the same one parks. Without room
  for the step (at an edge of the table) it parks.
* **Parked**, a change (better or worse) resumes moving: right from the
  leftmost profile, left otherwise. Parked on an edge (and with more than
  one profile), after `tired` samples in a row without change it probes one
  step inward; if the probe makes no difference it **settles** and moves
  again only on a change. `tired` 0 turns probing off. Settling after a
  probe is what makes identical samples converge, also in a table of two
  profiles, where both are edges.
* **The new state** starts at `start` (0 if that is past the table), going
  right, with no previous interval: the first sample only records its
  rates.

## Files

| File | Holds |
|---|---|
| `dim.bend` | the types, the parameters with their defaults, the comparison, the state machine |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/proof.py` | generates `PROOF.bend` (its lemmas follow every branch of a step and repeat long terms); `--check` tells whether the file is up to date |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `DimProfile{usec, pkts}` | a moderation profile |
| `DimSample{pkts, bytes, events, comps, elapsed}` | one interval |
| `DimRates{bytes, pkts, events, comps}`, `Dim.rates(s)` | an interval's rates per second |
| `DimMetric`: `DimBytes`, `DimPackets`, `DimEvents`, `DimCompletions`; `DimCriterion{metric, higher_better}` | one criterion of the comparison |
| `DimVerdict`: `DimBetter`, `DimSame`, `DimWorse`; `Dim.compare(p, new, old)` | the comparison of two intervals |
| `DimParams{profiles, start, significance, tired, chain}` | the parameters |
| `DimParams.default()`, `profiles_default()`, `chain_default()`, `chain_completions()` | the named defaults (below) |
| `DimMode`: `DimGoing{right, probe}`, `DimParked{tired}`, `DimSettled{}` | the direction |
| `Dim{ix, mode, prev}`, `Dim.new(p)` | the state (open: match on it, or use the observers) |
| `Dim.step(p, st, s)` | `DimStep{state, changed}`: the new state, and whether its profile index changed (`net_dim`) |
| `DimStep.state`, `DimStep.changed` | its fields |
| `Dim.run(p, st, samples)` | the state after the samples, in order |
| `Dim.index`, `Dim.mode`, `Dim.prev`, `Dim.profile(p, st)`, `Dim.valid(p, st)` | observers: the index, direction, previous rates, the profile named, whether the index is within the table |
| `Dim.settle_bound(p)` | `tired + 4`: identical samples after which any state is at rest |

Defaults (`DimParams.default()`): profiles (usec, packets) 2/256, 8/128,
32/64, 64/32, 128/16, least moderation first; start 0; significance 10
(percent); tired 10 samples; the bytes, packets, events chain. The document
gives no numbers for these (as recalled here), so they are this package's
choice, and every one is a parameter.

## Extension points

* **Every policy choice is a parameter** (`DimParams`): the profile table,
  the start index, the significance percentage, the tired count (0 turns
  probing off), and the comparison chain (any criteria, in any order, each
  higher or lower is better).
* **The state is open and a value**: a driver keeps one per queue, and may
  ignore a suggestion, as the document allows.
* **The decision is in one place** (`Dim.decide` and its helpers), apart
  from the comparison, so a different direction policy changes only it; the
  laws say what any such change must keep.
* Streaming is the shape: one sample per step.

## Laws

`LAWS.bend`, all proved in `PROOF.bend`, for every parameter record, state
and sample:

* **The index stays within the table**: a new state's index is in it, for
  a table that is not empty (`dim_new_valid`); a step and any run keep it
  there (`dim_step_valid`, `dim_run_valid`); so the state always names a
  profile (`dim_profile_some`).
* **At most one step at a time** (`dim_step_by_one`), and a step that says
  the profile did not change leaves the index as it was (`dim_unchanged`).
* **Identical samples converge**: an interval compares the same as itself
  (`dim_same_rates`), and after `Dim.settle_bound(p)` identical samples the
  state is a fixed point of a step with that sample (`dim_settles`), so
  every further identical sample leaves it, and its profile, as it is
  (`dim_rest`). This holds for every state and every parameter record:
  going, the same interval parks; parked off an edge, or with probing off,
  it stays; parked on an edge, the tired count runs out and one probe
  steps inward; the probe making no difference settles. So no state
  oscillates under identical samples.
* Vectors: a run that climbs two profiles while the byte rate rises and
  parks when it stops rising, and one that probes from the left edge and
  settles (`dim_vec_*`, each computing one run, which keeps them within
  `--verdict`'s fuel); a witness (`dim_wit`).

The proofs follow every branch of a step (`Dim.decide` and its helpers), on
Base's `Nat` and, for an interval's equality with itself, Base's `U32`
order (bit by bit) through word64's `W64.hi` and `W64.lo`; the rates'
arithmetic (`W64.mul`, `W64.div`) needs no law, since only the comparison's
outcomes matter, and an equal pair is recognised before any arithmetic.

## Tests

* `check.bend`: a climb, parking and a resumed move; a probe from the left
  edge and from the right; a table of one profile; ignored samples.
* `ref/run.sh`: 40 random sequences (1532 samples with the default seed),
  under random parameters (tables of 1 to 6 random profiles, start indices
  in and past the table, significance 0 to 50%, tired 0 to 5, both chains),
  of samples that repeat, rise and fall by up to half, with random interval
  lengths (and some of length 0), each ending with a run of identical
  samples longer than the settle bound, are run through `dim.bend` and
  through `ref/gen.py`'s Python model, and the index, mode and change flag
  after every step must match. **The model is written from the same
  document and shares an author with the package; there is no external
  oracle.** As it runs it also asserts the laws on every step (the index in
  the table, moving by at most one, and only when the step says so), and
  that every sequence is at rest after the settle bound.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (14 laws), `--verdict` ALL
PROOFS CHECK, `check.bend` passes, `ref/run.sh` 1532 samples in 40
sequences match, `scripts/deps.sh dim` ok.
