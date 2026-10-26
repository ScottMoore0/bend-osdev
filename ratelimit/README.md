# bend-osdev-ratelimit

Rate limiting in the style of the Linux kernel's `ratelimit`, as a pure
state machine: allow at most `burst` events per `interval`, and count the
ones refused, so that the caller can report "N callbacks suppressed".

The time is passed in, never read: `RateLimit.check(state, now)` takes the
time of the event as a `W64` (bend-osdev-word64) in whatever unit the caller
keeps (jiffies, nanoseconds, a test's own steps), the same unit as the
interval. tcpip handles its timers the same way.

## Specification

The kernel documents rate limiting in one place that was found:
**"Documentation for /proc/sys/kernel/"**,
<https://docs.kernel.org/admin-guide/sysctl/kernel.html>
(`Documentation/admin-guide/sysctl/kernel.rst`), in the entries
**`printk_ratelimit`** and **`printk_ratelimit_burst`**. It was read on
2026-10-18. From those entries:

* `printk_ratelimit` is the minimum length of time between rate-limited
  messages, in seconds, default **5**, and **a value of 0 disables rate
  limiting**;
* `printk_ratelimit_burst` is the number of messages let through before
  rate limiting starts, default **10**, and after `printk_ratelimit` seconds
  have elapsed another burst may be sent.

There is no rendered kernel-doc for `___ratelimit` or `struct
ratelimit_state` on docs.kernel.org. "The Linux Kernel API"
(<https://docs.kernel.org/core-api/kernel-api.html>, read in full) has none,
and "Message logging with printk"
(<https://docs.kernel.org/core-api/printk-basics.html>) only recommends the
`pr_*_ratelimited()` macros. So the interval/burst/suppressed-count
interface and the "N callbacks suppressed" report come from the brief for
this package, not from a document. **No kernel source was read**: search
results pointing at `lib/ratelimit.c` mirrors or mailing-list patches were
skipped.

How this package relates to the documented behaviour:

* **An interval of 0 turns rate limiting off**, as `printk_ratelimit`
  documents: every event is allowed, and nothing is counted. A `burst` of 0
  (with a nonzero interval) refuses every event; the page does not say what
  a burst of 0 means.
* **The documented defaults are a named constructor**:
  `RateLimit.printk(per_second)` is an interval of 5 seconds
  (`RateLimit.printk_interval_seconds()`) in the caller's units, a burst of
  10 (`RateLimit.printk_burst()`), and the fixed window below, which is the
  behaviour the sysctl text describes ("after printk_ratelimit seconds have
  elapsed, another burst of messages may be sent"). The vector
  `ratelimit_vec_printk` holds it to that.
* **The fixed policy** (`RateLimitFixed`, the documented behaviour): a
  window opens at the first event after the previous window closed and
  lasts `interval`; at most `burst` events are allowed in it. A stretch of
  length `interval` that straddles two windows can hold up to `2 * burst`
  allowed events (the vector `ratelimit_vec_policies` shows five where
  `burst` is 3).
* **The sliding policy** (the default, a deliberate choice): an event is
  allowed when fewer than `burst` allowed events lie within the window
  ending at it. The state keeps the times of those events, newest first,
  and never more than `burst` of them. For nondecreasing times this is the
  strict reading of "at most `burst` per `interval`" that the brief asks
  for: no stretch of time of length `interval` holds more than `burst`
  allowed events.
* **Within the window**: an event at time `t` is within the window at time
  `now` when `now - t < interval`, the subtraction modulo 2^64 (so a time
  ahead of `now`, from a clock that went back, is outside it). This
  package's choice; time is the caller's, in any unit.
* **Suppressed counts**: each refused event adds one; `RateLimit.report`
  answers the count and clears it, and the caller decides when to report
  (the brief's "N callbacks suppressed").

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
| `RateLimit.printk(per_second)`, `RateLimit.printk_interval_seconds()`, `RateLimit.printk_burst()` | the documented printk defaults: 5 seconds, a burst of 10, the fixed window |
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
| `RateLimit.allowed_times(ts, xs)` | the times of `ts` whose answers in `xs` (a run's `allowed`) are `True` |
| `RateLimit.in_window(interval, now, ts)` | how many times of `ts` are within the window ending at `now` |
| `RateLimit.sorted_upto(ts, now)` | whether the times of `ts`, then `now`, never decrease |

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
  (`ratelimit_vec_report`), and the documented printk defaults
  (`ratelimit_vec_printk`).

* **The window law over a whole run** (`ratelimit_run_window`), for the
  sliding policy: for times that never decrease, up to and including
  `now` (`sorted_upto(ts, now)`), the allowed events of a run from a new
  state that lie within the window of length `interval` ending at `now`
  are at most `burst`. Taking `now` to be the last allowed event in any
  stretch of length `interval`, every other allowed event of the stretch
  is within its window, so no stretch of length `interval` holds more than
  `burst` allowed events. With witnesses and a vector
  (`ratelimit_window_wit`, `ratelimit_vec_window`).

  How it is proved: at a fixed `now`, what the state holds against `now`
  (`recent`) grows by one at each allowed event within the window ending
  at `now`, and by nothing at any other check, because the times a check at
  `t` drops (outside the window at `t`) are outside the window at `now`
  too: for `u <= t <= now`, `now - u < interval` gives `t - u < interval`.
  That step is arithmetic on times, done through bend-osdev-word64's laws
  of `W64` subtraction and order (`sub_value`, `lt_value`, `le_value`,
  `eq_value`), never inside `W64`. So the count at `now` is what the final
  state holds against `now`, at most what it holds, at most `burst`
  (`ratelimit_recent_le_held`, `ratelimit_run_bound`).

The fixed policy has no such law: a stretch straddling two fixed windows
can hold `2 * burst` allowed events (`ratelimit_vec_policies`). Every
property stated is proved; the differential test also checks the run form
on every random sequence.

## Tests

* `check.bend`: the same times under both policies; the edge where they
  differ; rate limiting off; a burst of 0; the printk defaults in
  milliseconds; times wrapping past 2^64.
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

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and the order of `Nat` and words (`LAWS_order.bend`).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(2 s, 0.32 GB peak; `--verdict` 4 s, 0.35 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (24 laws), `--verdict` ALL
PROOFS CHECK, `check.bend` passes, `ref/run.sh` 3566 events in 40 sequences
match, `scripts/deps.sh ratelimit` ok.
