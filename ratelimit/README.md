# bend-osdev-ratelimit

Rate limiting in the style of the Linux kernel's `ratelimit`, as a pure
state machine: allow at most `burst` events per `interval`, and count the
ones refused, so that the caller can report "N callbacks suppressed".

The time is passed in, never read: `RateLimit.check(state, now)` takes the
time of the event as a `W64` (bend-osdev-word64) in whatever unit the caller
keeps (jiffies, nanoseconds, a test's own steps), the same unit as the
interval. tcpip handles its timers the same way.

## Specification

The kernel's documented behaviour: the `printk_ratelimit` and
`printk_ratelimit_burst` sysctls in `Documentation/admin-guide/sysctl/kernel.rst`
(a burst of messages is let through, and then at most that many per
interval; an interval of 0 disables rate limiting), and the "N callbacks
suppressed" report of the refused calls. This package was written from that
documented behaviour, as an abstract data type; **no kernel source was
read**, and the documents were not re-read in this session (it had no
network access): the behaviour below is what this package commits to, and
its laws and tests hold it to that.

* An event at time `t` is **within the window** at time `now` when
  `now - t < interval`, the subtraction modulo 2^64 (so a time ahead of
  `now`, from a clock that went back, is outside it).
* **The sliding policy** (the default): an event is allowed when fewer than
  `burst` allowed events lie within the window ending at it. The state keeps
  the times of those events, newest first, and never more than `burst` of
  them. For nondecreasing times this is the strict reading of "at most
  `burst` per `interval`": no stretch of time of length `interval` ever
  holds more than `burst` allowed events.
* **The fixed policy** (`RateLimitFixed`): a window opens at the first event
  after the previous window closed and lasts `interval`; at most `burst`
  events are allowed in it. This is the shape of the kernel's own counter,
  cheaper (a start time and a count), but a stretch of length `interval`
  that straddles two windows can hold up to `2 * burst` allowed events (the
  vector `ratelimit_vec_policies` shows five where `burst` is 3).
* **An interval of 0 turns rate limiting off**: every event is allowed, and
  nothing is counted. A `burst` of 0 (with a nonzero interval) refuses every
  event.
* **Suppressed counts**: each refused event adds one; `RateLimit.report`
  answers the count and clears it. The kernel prints its report when a new
  window opens; here the caller decides when to report.

## Files

| File | Holds |
|---|---|
| `ratelimit.bend` | the policies, the state, `check`, `report`, runs |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/proof.py` | generates `PROOF.bend` (its lemmas repeat long terms); `--check` tells whether the file is up to date |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `RateLimit` | the state (opaque: use the defs below) |
| `RateLimitPolicy`: `RateLimitSliding{}`, `RateLimitFixed{}`; `RateLimitPolicy.default()` | the window policy; sliding by default |
| `RateLimit.new(interval, burst)`, `RateLimit.new_with(policy, interval, burst)` | a new state: `interval` a `W64`, `burst` a `U32` |
| `RateLimit.check(s, now)` | `RateLimitStep{state, allowed}`: whether an event at `now` is allowed, and the new state (the kernel's `__ratelimit`) |
| `RateLimitStep.state`, `RateLimitStep.allowed` | its fields |
| `RateLimit.suppressed(s)` | the refused calls since the last report |
| `RateLimit.report(s)` | `RateLimitReport{state, suppressed}`: the count, and the state with it cleared |
| `RateLimitReport.state`, `RateLimitReport.suppressed` | its fields |
| `RateLimit.run(s, ts)` | checks at each time of `ts` in order: `RateLimitRun{state, allowed}`, the final state and each answer |
| `RateLimitRun.state`, `RateLimitRun.allowed`, `RateLimit.refusals(xs)` | its fields; the number of `False` answers |
| `RateLimit.interval(s)`, `RateLimit.burst(s)` | the parameters (`burst` as a `Nat`) |
| `RateLimit.within(interval, now, t)` | whether `t` is within the window at `now` |
| `RateLimit.recent(s, now)` | the allowed events the next check at `now` counts against `burst` |
| `RateLimit.held(s)` | the allowed events the state holds at all (at most `burst`) |

## Extension points

* **The window policy is a parameter** (`RateLimit.new_with`), sliding by
  default; another policy (a token bucket, a decaying average) is another
  constructor of `RateLimitPolicy` and `RateLimitWindow`, and the laws are
  stated so that each policy has to meet them (`recent` and `held` are its
  view of the window).
* **`interval` and `burst`** are parameters, and the time unit is the
  caller's.
* **The representation is internal**: `RateLimit` is used only through the
  defs above.
* **Time is an argument**, so a test (or a simulation) drives the clock, and
  a kernel passes its own.
* Streaming is not applicable: a check is one step; `run` folds a list of
  them.

## Laws

`LAWS.bend`, all proved in `PROOF.bend`, for every state of either policy,
every time and every list of times:

* **The gate** (`ratelimit_gate`): with a nonzero interval, an event is
  allowed exactly when `recent(s, now) < burst`, fewer than `burst` allowed
  events within its window; `ratelimit_off`: with an interval of 0 the
  answer is `True` and the state is unchanged.
* **After a quiet interval an event is allowed** (`ratelimit_quiet`): when
  no allowed event lies within the window and `burst` is at least 1.
* **Every allowed event is held, nothing outside the window is**
  (`ratelimit_held_allowed`, `ratelimit_held_refused`): after an allowed
  event the state holds the window's events and this one; after a refused
  one, the window's; `ratelimit_recent_le_held`: the window counts no more
  than the state holds.
* **At most `burst`** (`ratelimit_held_bound`, and for whole runs
  `ratelimit_run_bound`): a state holding at most `burst` events (as a new
  one does, `ratelimit_new`) still does after any check; `ratelimit_kept`:
  `interval` and `burst` never change.
* **The suppressed count** (`ratelimit_suppressed_allowed`,
  `ratelimit_suppressed_refused`, `ratelimit_report`,
  `ratelimit_report_keeps`): an allowed event leaves the count alone and a
  refused one adds one; a report answers the count, clears it and changes no
  answer; and for runs, `ratelimit_run_suppressed`: after a report, the
  count is the number of refused calls since.
* Witnesses that the hypotheses can hold (`ratelimit_wit`), and vectors: a
  sliding run (`ratelimit_vec_sliding`), the two policies told apart
  (`ratelimit_vec_policies`), a count and its report
  (`ratelimit_vec_report`).

**Not proved: the window law over a whole run** ("in any stretch of length
`interval`, at most `burst` events are allowed", for nondecreasing times).
The laws above give it step by step: every check refuses when the window
already holds `burst` allowed events, and every allowed event is held. What
joins the steps is arithmetic on times: that an event within the window at a
later check was within it at every check between. That needs laws of `W64`
subtraction and order (monotonicity, for nondecreasing times), which
bend-osdev-word64 does not state (its arithmetic is tested against Python's
integers, not proved), and this package uses `W64` only through word64's
laws. The differential test checks the run form on every random sequence.

## Tests

* `check.bend`: the same times under both policies; the edge where they
  differ; rate limiting off; a burst of 0; times wrapping past 2^64.
* `ref/run.sh`: 40 random sequences (3566 events with the default seed) of
  checks and reports, half under each policy, with intervals of 0 to 99 and
  bursts of 0 to 7, times starting anywhere (some just below 2^64, so they
  wrap) and mostly nondecreasing (a quarter of the sequences move back as
  well as forward), are run through `ratelimit.bend` and through
  `ref/gen.py`'s Python model, and the answers must match. The model is
  written from the same description as this package and shares its author,
  so it is not an independent oracle; as it runs it also asserts, on every
  sequence, that for the sliding policy and nondecreasing times no stretch
  of length `interval` holds more than `burst` allowed events, that after a
  quiet interval an event is allowed, and that each report's count is the
  refusals since the last.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (20 laws), `--verdict` ALL
PROOFS CHECK, `check.bend` passes, `ref/run.sh` 3566 events in 40 sequences
match, `scripts/deps.sh ratelimit` ok.
