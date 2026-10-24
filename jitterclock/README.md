# bend-osdev-jitterclock

A clock for the jitter core: a library effect that reads a nanosecond
monotonic clock, a hash loop timed with it, and reads of random bytes that
feed the deltas to jitter (with SHA3-256 as the conditioner).

The clock read is a library effect, shaped as fileio's are (see fileio's
README, "Why a library"): a foreign def whose body imports its C side
(`jitterclock.c`) and its JavaScript side (`jitterclock.js`), so it runs
natively (`bend file.bend -o prog`) and on the JavaScript lane (`bend
file.bend`). Effects are tested, not proved; the pure parts (`time.bend`)
have laws, and the effect files are kept apart from them, so proofs never
import a foreign def.

## Sources

* **The clock:** POSIX `clock_gettime` with `CLOCK_MONOTONIC` (The Open
  Group Base Specifications Issue 7, IEEE Std 1003.1-2017) on the C side;
  Node's `process.hrtime.bigint()` (monotonic nanoseconds from an arbitrary
  origin), as Bun provides it, on the JavaScript side. The effect's shape
  (an argument per input, the answer built with the runtime's `io_tup`,
  registered with `io_eff`) follows Base's own effects (`bend2/effs/now.c`,
  `now.js`, Apache-2.0), which were read as the model; no Base source is
  copied.
* **What is timed:** Müller, *CPU Time Jitter Based Non-Physical True
  Random Number Generator* (4 May 2026), sections 3.1.4 (a delta is a time
  stamp minus the previous one) and 3.1.5 (the hash loop as a noise source:
  the time of SHA-3 computations); see jitter's README for the rest.

## Files and API

| File | Holds |
|---|---|
| `jitterclock.bend` | the effect (`JClock.eff.now`) and the reads on it |
| `jitterclock.c`, `jitterclock.js` | the effect's C side and JavaScript side |
| `time.bend` | `JClock.time.*`: stamps from halves, deltas, the read's budget (pure) |
| `LAWS.bend`, `PROOF.bend` | the laws about `time.bend` and their proofs |
| `LAWS_read.bend`, `PROOF_read.bend` | the law about the pure part of a read (a stopped clock), and its proof |
| `check.bend` | a runnable check of the effect and of reads |
| `ref/stamps.bend`, `ref/check.py`, `ref/run.sh` | the test against Python's reading of the same clock |

| Def | Meaning |
|---|---|
| `JClock.eff.now(dep: U32) -> IO(U32 & U32)` | the effect: CLOCK_MONOTONIC (natively) or `process.hrtime.bigint()` (JavaScript lane) in nanoseconds, as (high, low); `dep` is unused, and orders the read after the value it is computed from |
| `JClock.now(dep) -> IO(W64)` | the same as a `W64` |
| `JClock.work(t: W64) -> U32` | the hash loop's work: SHA3-256 of a stamp's eight bytes; its first byte |
| `JClock.stamps(n) -> IO(List<&2, W64>)` | n stamps, each read after hashing the one before |
| `JClock.deltas(n) -> IO(List<&2, W64>)` | n deltas: the times of n hashes |
| `JClock.read(p: JitParams, n) -> IO(Result<&2, &2, JitError, Octets>)` | n random bytes: `JClock.time.budget(p, n)` deltas, then jitter's `JitSha3.generate` |
| `JClock.time.join((hi, lo))`, `JClock.time.deltas(ts)`, `JClock.time.budget(p, n)` (`time.bend`) | a stamp from halves; consecutive differences; 64 + 2 * need * (blocks discarded + ceil(n / 32)) |

Each stamp's read takes the previous hash's first byte, and each hash takes
the previous stamp, so reads and hashes alternate in order, whatever order
the runtime evaluates pure code in. The deltas are collected first and then
given to the jitter core in one call: the effect and the logic stay apart.

A read that collects too many stuck deltas fails with `JitNeedMore`; a
caller may try again. A clock that looks stuck fails the health tests
(`JitRctFailure`, `JitAptFailure`); the jitter core never recovers from
that, and neither does a read.

## Extension points

* **Another clock** (a cycle counter, `CLOCK_MONOTONIC_RAW`, another
  platform's) is another effect of the same shape; `time.bend` and the
  jitter core take its stamps unchanged.
* **Other timed work:** `JClock.work` is the hash loop; a memory access
  loop would be another work function (and the domain separator 1 or 3 in
  `JitParams`).
* **The budget** is `JClock.time.budget`; a caller who wants another can
  call `JClock.deltas` and jitter's `read` directly.

## Laws

`LAWS.bend`, for `time.bend` only: `time_join_hi`, `time_join_lo` (from
word64's `hi_from_parts`, `lo_from_parts`), `deltas_length` (one fewer
delta than stamps), `deltas_step` (each delta is a stamp minus the one
before); vectors `deltas_vec`, `budget_default` (3916 deltas for 32 bytes
under the default parameters). The effects have no laws: they are tested.

`LAWS_read.bend`: `stopped_clock`: a clock that reads the same stamp every
time gives `JClock.read`'s pure part (the deltas of the budget's stamps,
given to `JitSha3.generate`) deltas that are all the same, so a read of 32
bytes under the default parameters fails with `JitRctFailure` rather than
running out of deltas: the budget (3916) is at least the RCT's cutoff (91),
and jitter's `constant_fails_default` does the rest.

## Tests

* `check.bend`, natively and on the JavaScript lane: 1000 stamps never go
  back; 1000 deltas are all above 0 and not all equal; a read of 32 bytes
  gives 32 bytes, and two reads differ; a read of 100 bytes gives 100.
* `ref/run.sh`, natively and on the JavaScript lane: 200 stamps, with
  Python's `time.clock_gettime_ns(CLOCK_MONOTONIC)` read just before and
  just after. On both lanes the stamps never go back, their deltas are
  exactly Python's differences of the stamps, and they span no more time
  than Python saw pass; natively, every stamp lies between Python's two
  readings (the same clock). Bun's `process.hrtime.bigint()` counts from
  its own origin, so on the JavaScript lane only the span is compared.
  Natively a hash and a clock read take about 17 µs here, about 0.5 ms on
  the JavaScript lane.

## Dependencies

`bytes`, `word64`, `crypto` (SHA3-256 for the hash loop's work), `jitter`
(the core, its parameters and errors).

## Status

Bend 2.0.37: `PROOF.bend` and `PROOF_read.bend` ALL PROOFS CHECK, `--verdict`
ALL PROOFS CHECK (`PROOF_read.bend`: 0.3 GB peak),
`check.bend` passes natively and on the JavaScript lane, `ref/run.sh`
passes on both lanes, `scripts/deps.sh` passes. Linux (WSL2) only so far;
the C side uses only POSIX calls, but macOS is untested.
