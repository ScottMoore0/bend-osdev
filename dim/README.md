# bend-osdev-dim

Dynamic interrupt moderation (DIM), in the style of the Linux kernel's
`net_dim`, as a pure state machine. A driver hands `Dim.step` one sample per
interval (the packets, bytes, events and completions of the interval, and
the time it took; `Dim.interval` makes one from two readings of raw
counters). The state machine compares the interval's rates with the
previous interval's and decides whether to step the moderation profile (an
index into a table of usec/packet pairs) right, left, or to stay, aiming at
the best throughput. It reads no clock and touches no device: when a step
says the index changed, the driver applies `Dim.profile(p, state)`.

## Specification

One document: **"Net DIM - Generic Network Dynamic Interrupt Moderation"**
(Tal Gilboa), <https://docs.kernel.org/networking/net_dim.html>
(`Documentation/networking/net_dim.rst`), including its rendered kernel-doc
section "Dynamic Interrupt Moderation (DIM) library API". It was read on
2026-10-18. **No kernel source was read**, in particular not `lib/dim` or
`include/linux/dim.h`, nor any mirror of them. The page documents no
separate RDMA DIM beyond `rdma_dim()` in that API section, and no other
docs.kernel.org page was found that does.

What comes from which section of the page:

| Fact | Section |
|---|---|
| each iteration samples, compares with the previous sample, decides, and leaves it to the driver to apply the profile | "Net DIM Algorithm" |
| bandwidth is compared first ("better" if it increases), then the packet rate (increase better), then the interrupt rate (increase worse); bandwidth matters more than reducing interrupts | "Net DIM Algorithm"; "Introduction" |
| a difference counts only if it is "greater than a certain percentage" | "Net DIM Algorithm" |
| going left reduces moderation, going right increases it, or the algorithm stands still | "Net DIM Algorithm" |
| when standing still, checks become less frequent; after parking on the leftmost or rightmost profile it may verify that by a step the other way | "Net DIM Algorithm" |
| the driver supplies raw counters (bytes, packets, interrupts) and a timestamp; DIM computes the rates, handling counter wrap-around, and tells whether they are reliable | "Registering a Network Device to DIM"; kernel-doc `struct dim_sample`, `dim_calc_stats()` |
| rates are per millisecond (`bpms`, `ppms`, `epms`, `cpms`) | kernel-doc `struct dim_stats` |
| the states `DIM_GOING_RIGHT`, `DIM_GOING_LEFT`, `DIM_PARKING_ON_TOP` (leaves on a significant difference), `DIM_PARKING_TIRED` (does not leave while `tired > 0`) | kernel-doc `enum dim_tune_state` |
| the verdicts `DIM_STATS_BETTER`, `DIM_STATS_SAME`, `DIM_STATS_WORSE` | kernel-doc `enum dim_stats_state` |
| the step results `DIM_STEPPED`, `DIM_TOO_TIRED` (the same kind of step repeated too many times: go to tired parking), `DIM_ON_EDGE` (the leftmost or rightmost profile) | kernel-doc `enum dim_step_result` |
| `steps_right`, `steps_left` and `tired` in the state; parking (on top, or tired) clears the movement history; `dim_turn` reverses the direction and does nothing while parked; `dim_on_top` decides that the current place is a top to park on | kernel-doc `struct dim`, `dim_park_on_top()`, `dim_park_tired()`, `dim_turn()`, `dim_on_top()` |
| a profile is per device and settable (usec and packet counts per profile) | "Tuning DIM"; kernel-doc `struct dim_cq_moder` |
| `rdma_dim` counts completions as events and decides once enough have accumulated; `struct dim_stats` carries `cpms` and `cpe_ratio` | kernel-doc `rdma_dim()`, `struct dim_stats` |

**The page gives no numbers** for the percentage, the tired parking's
length, the number of steps that tires, the number of events per sample,
or a default profile table. The only values it shows are an `ethtool`
example in "Tuning DIM" (RX profiles 1/1, 2/2, 3/64, 64/4, 64/64), which is
an example of setting a profile, not a default. So every number below is
this package's own choice, and every one is a parameter.

**This package's own design choices**, where the page leaves room:

* **The sample is per interval** (`DimSample{pkts, bytes, events, comps,
  elapsed}`, elapsed in microseconds), as the brief for this package asks.
  `Dim.interval(a, b)` derives one from two readings of raw counters
  (`DimCounters`, as `struct dim_sample` holds them), with counts modulo
  2^32 so that a wrapped counter counts right. A sample with `elapsed` 0
  gives no reliable rates and is ignored. Deciding when an interval has
  enough events, and lengthening intervals while parked (`Dim.parked`), are
  the caller's: the page gives no numbers for either.
* **Rates** are `value * 1000 / elapsed`, per millisecond, in `W64`.
* **The comparison** goes down a chain of criteria (`DimParams.chain`):
  `chain_default()` is the documented order (bytes and packets, higher is
  better; events, lower is better). `chain_completions()` puts the
  completion rate first, for completion queues; the page does not say how
  `rdma_dim` compares, or what `cpe_ratio` is used for, so neither is
  modelled. A rate rises or falls significantly when
  `100 * |new - old| > significance * old`.
* **`dim_on_top`**: going, an interval that compares the same is a top, and
  the state parks there.
* **Going**: a better interval steps on the same way, and a worse one turns
  (`dim_turn`) and steps the other way.
* **`DIM_ON_EDGE`** is read as a step that cannot be taken because the
  index is already on the leftmost or rightmost profile and the step points
  out of the table. The step is not taken, and the state parks tired.
  Reading it as "the step landed on an edge" would park after every arrival
  at an edge, and in a table of two profiles identical samples would then
  bounce between them for ever.
* **`DIM_TOO_TIRED`**: a step that makes `max_steps` steps of one kind
  (right, or left) since the last parking parks tired.
* **Parked on top**: a significant difference starts moving again, right
  from the leftmost profile and left otherwise. The page does not say which
  way.
* **Parked tired**: for `tired` samples the state does not leave, whatever
  they show. It counts the samples spent (`DimParkedTired{right, spent}`;
  the page's countdown `tired` is `tired - spent`), then verifies its
  parking by a step opposite to the step that tired it, with the movement
  history cleared.
* **A new state** starts at `start` (0 if that is past the table), going
  right. Its first sample only records rates.
* **A profile** is a usec/packet pair, as the brief asks. The page's
  `struct dim_cq_moder` also carries a completion counter and a CQ period
  mode, which are left to the driver.

## Files

| File | Holds |
|---|---|
| `dim.bend` | the types, the parameters with their defaults, intervals from counters, the comparison, the state machine |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/proof.py` | generates `PROOF.bend` (its lemmas follow every branch of a step and repeat long terms); `--check` tells whether the file is up to date |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `DimProfile{usec, pkts}` | a moderation profile |
| `DimSample{pkts, bytes, events, comps, elapsed}` | one interval |
| `DimCounters{time, pkts, bytes, events, comps}`, `Dim.interval(a, b)` | raw counters at one moment; the interval between two readings |
| `DimRates{bytes, pkts, events, comps}`, `Dim.rates(s)` | an interval's rates per millisecond |
| `DimMetric`: `DimBytes`, `DimPackets`, `DimEvents`, `DimCompletions`; `DimCriterion{metric, higher_better}` | one criterion of the comparison |
| `DimVerdict`: `DimBetter`, `DimSame`, `DimWorse`; `Dim.compare(p, new, old)` | the comparison of two intervals |
| `DimParams{profiles, start, significance, tired, max_steps, chain}` | the parameters |
| `DimParams.default()`, `profiles_default()`, `chain_default()`, `chain_completions()` | the named defaults (below) |
| `DimMode`: `DimGoing{right, steps_right, steps_left}`, `DimParkedTop{}`, `DimParkedTired{right, spent}` | the documented tuning states |
| `Dim{ix, mode, prev}`, `Dim.new(p)` | the state (open: match on it, or use the observers) |
| `Dim.step(p, st, s)` | `DimStep{state, changed}`: the new state, and whether its profile index changed (`net_dim`) |
| `DimStep.state`, `DimStep.changed` | its fields |
| `Dim.run(p, st, samples)` | the state after the samples, in order |
| `Dim.index`, `Dim.mode`, `Dim.prev`, `Dim.parked`, `Dim.profile(p, st)`, `Dim.valid(p, st)` | observers: the index, the state, the previous rates, whether parked, the profile named, whether the index is within the table |
| `Dim.settle_bound(p)` | `2 * tired + 4`: identical samples after which any state is at rest (see Laws) |

Defaults (`DimParams.default()`):
* profiles (usec, packets) 2/256, 8/128, 32/64, 64/32, 128/16, least
  moderation first;
* start 0, significance 10 (percent), tired 10 samples, max_steps 10;
* the documented bytes, packets, events chain.

None of these numbers comes from the page, which gives none (see above).

## Extension points

* **Every policy choice is a parameter** (`DimParams`): the profile table,
  the start index, the significance percentage, the tired parking's
  length, the steps that tire, and the comparison chain (any criteria, in
  any order, each higher or lower is better).
* **The state is open and a value**: a driver keeps one per queue, and may
  ignore a suggestion, as the page allows ("Net DIM Algorithm").
* **The decision is in one place** (`Dim.decide` and its helpers), apart
  from the comparison, so a different reading of the documented states
  changes only it; the laws say what any such change must keep.
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
* **Identical samples converge, wherever the documented parking behaviour
  guarantees it**: an interval compares the same as itself
  (`dim_same_rates`). In a table of at least two profiles, with
  `max_steps` at least 2, after `Dim.settle_bound(p)` identical samples the
  state is a fixed point of a step with that sample (`dim_settles`), so
  every further identical sample leaves it, and its profile, as it is
  (`dim_rest`). This holds for every state:
  * going, the same interval parks on top, where it stays;
  * parked tired, the state waits out the parking and verifies by a step
    the other way. If that step cannot be taken, it parks tired once more
    and then steps inward. The verifying step is not too tired, and the next
    identical interval parks on top.
* **Outside those hypotheses the documented behaviour itself cycles**: in a
  table of one profile a tired parking repeats (the index stays), and with
  `max_steps` below 2 every verifying step tires and parks again.
* Vectors (`dim_vec_*`): a run that climbs two profiles while the byte rate
  rises and parks on top when it stops rising; a run that hits the edge,
  parks tired and verifies; an interval from counters that wrapped. Each
  computes one run, which keeps it within `--verdict`'s fuel. A witness
  shows the hypotheses can hold (`dim_wit`).

The proofs follow every branch of a step (`Dim.decide` and its helpers) on
Base's `Nat` and, for an interval's equality with itself, Base's `U32`
order (bit by bit) through word64's `W64.hi` and `W64.lo`. The rates'
arithmetic (`W64.mul`, `W64.div`) needs no law: only the comparison's
outcomes matter, and an equal pair is recognised before any arithmetic.

## Tests

* `check.bend`:
  * a climb, parking on top, and a move resumed on a change;
  * identical samples parking on top;
  * a climb onto the right edge that parks tired and verifies;
  * a table of one profile;
  * ignored samples;
  * an interval from wrapping counters.
* `ref/run.sh`: 40 random sequences (1775 samples with the default seed)
  are run through `dim.bend` and through `ref/gen.py`'s Python model. The
  index, state and change flag after every step must match.
  * Parameters are random: tables of 1 to 6 random profiles, start indices
    in and past the table, significance 0 to 50%, tired 0 to 5, max_steps
    0 to 10, both chains.
  * Samples repeat, or rise and fall by up to half, with random interval
    lengths (some of length 0). Each sequence ends with a run of identical
    samples longer than the settle bound.
  * **The model is written from the same document and shares an author with
    the package; there is no external oracle.**
  * As it runs, the model asserts on every step that the index stays in the
    table and moves by at most one, and only when the step says so. Where
    the hypotheses hold, it asserts that the sequence is at rest after the
    settle bound.

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and the order of `Nat` and words (`LAWS_order.bend`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (15 laws), `--verdict` ALL
PROOFS CHECK, `check.bend` passes, `ref/run.sh` 1775 samples in 40
sequences match, `scripts/deps.sh dim` ok.
