# bend-osdev-errseq

Error sequence counters, in the style of the Linux kernel's `errseq_t`, as a
pure state machine: a writer records errors in one place, and any number of
observers, each holding a cursor, learn of an error they have not seen
exactly once. A file's writeback errors are the usual use: every open file
description samples a cursor when it is opened and learns at its next
`fsync` of any error recorded since.

Nothing here reads shared memory or a clock: each operation takes the state
and answers the new one, so the caller decides where the state lives and how
it is shared between observers.

## Specification

The Linux kernel's documentation of `errseq_t`,
`Documentation/core-api/errseq.rst` (Jeff Layton): an error sequence counter
records the latest error and counts errors, observers sample it
(`errseq_sample`), test whether it changed since their sample
(`errseq_check`), and test and move their sample forward
(`errseq_check_and_advance`), and a "seen" flag records whether the latest
error has been reported to anyone. This package was written from that
documented behaviour, as an abstract data type; **no kernel source was
read**, and the document was not re-read in this session (it had no network
access): the behaviour below is what this package commits to, and its laws
and tests hold it to that.

Where the document leaves room, or describes the kernel's packing, this
package chooses:

* **The counter is a `Nat`**, not a field of a packed 32-bit word, so it
  never wraps, and every recorded error moves it on. The kernel packs the
  error, the seen flag and a counter into 32 bits and, to make the counter
  wrap more slowly, moves it on only when the previous error was seen; with
  an unbounded counter that economy is not needed, and an observer behind
  the counter learns of the latest error, once, however many were recorded.
* **Errors are `U32` error numbers**, with 0 meaning "no error": recording
  0 records nothing.
* **A fresh observer learns only of errors after it sampled** (by default).
  The kernel's sample is set one error back when nobody has been told of the
  latest error yet, so that the first observer to check learns of it; that
  is `ErrseqOptions.kernel()`.
* **Cursors are values**, `ErrseqCursor`; an observer keeps its own.

## Files

| File | Holds |
|---|---|
| `errseq.bend` | the state, cursors, options and the operations |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `Errseq` | the counter (opaque: use the defs below) |
| `ErrseqCursor` | an observer's cursor (opaque) |
| `ErrseqOptions{report_unseen}`, `ErrseqOptions.default()`, `ErrseqOptions.kernel()` | whether a sample taken while the latest error is unseen is set back so that it reports it: off by default, on in `kernel()` |
| `Errseq.new()` | no errors recorded |
| `Errseq.set(s, e)` | record error `e` (`errseq_set`); `e == 0` records nothing |
| `Errseq.sample(o, s)` | a new observer's cursor (`errseq_sample`) |
| `Errseq.check(s, c)` | `Some{e}`, the latest error, if one was recorded since the cursor; `None` if not (`errseq_check`) |
| `Errseq.check_and_advance(s, c)` | `ErrseqCheck{state, cursor, error}`: the same answer, the cursor moved up to date, and the latest error marked seen if it was reported (`errseq_check_and_advance`) |
| `ErrseqCheck.state`, `ErrseqCheck.cursor`, `ErrseqCheck.error` | its fields |
| `Errseq.seq(s)`, `Errseq.error(s)`, `Errseq.seen(s)`, `ErrseqCursor.seq(c)` | observers: the count, the latest error (0 before any), whether it was seen, a cursor's count |
| `Errseq.cursor_valid(s, c)` | whether `c` belongs to `s` (is at most its count); every cursor these defs give does |

## Extension points

* **The one behavioural choice is an option**, `ErrseqOptions`, with
  `default()` and `kernel()` named.
* **The representation is internal.** `Errseq` and `ErrseqCursor` are used
  only through the defs above, so a packed 32-bit form (the kernel's, with a
  counter that wraps) can replace the `Nat` counter; its laws would then need
  a hypothesis bounding the errors recorded between an observer's checks.
* **No storage or locking.** The state is a value; sharing it between
  writers and observers (a lock, an atomic word, a channel) is the caller's.
* Streaming is not applicable: every operation is one step.

## Laws

`LAWS.bend`, all proved in `PROOF.bend`, for every state, cursor and error:

* **A fresh observer learns only of errors after it sampled**:
  `errseq_fresh_quiet` (its first check reports nothing) and
  `errseq_fresh_sees_next` (it learns of the next error recorded).
* **Every observer learns of a new error**: `errseq_new_error_seen`, for
  every cursor that belongs to the state; `errseq_advance_reports_check`
  (check-and-advance reports what check would).
* **Exactly once**: after a check-and-advance there is nothing more to learn
  (`errseq_advance_then_quiet`), and advancing again reports nothing and
  changes nothing (`errseq_advance_twice`).
* **No new error, no report**: a check that reports nothing makes
  check-and-advance a no-op (`errseq_quiet_unchanged`); error 0 records
  nothing (`errseq_set_zero`); a new counter reports nothing
  (`errseq_new_quiet`).
* **Cursors stay valid, and observers are independent**: sampling and
  advancing give valid cursors (`errseq_sample_valid`,
  `errseq_advance_valid`); recording keeps a cursor valid
  (`errseq_set_keeps_valid`); one observer's advance changes neither the
  validity nor the answer of any other cursor
  (`errseq_advance_keeps_other_valid`, `errseq_advance_other_check`).
* **The kernel option**: a sample taken while the latest error is unseen
  reports it (`errseq_kernel_unseen`), but not once an observer has been told
  of it (`errseq_kernel_seen_quiet`); once it is seen, the two options
  sample alike (`errseq_kernel_quiet_when_seen`).
* A witness that the hypotheses can hold (`errseq_wit`) and a vector with
  two observers (`errseq_vec_two_observers`).

Together, for any interleaving: an observer's cursor is valid after every
step, so each error recorded after its last check is reported at its next
check, once.

## Tests

* `check.bend`: two observers of one file's writeback errors, a repeated
  check, error 0, and the two sampling options.
* `ref/run.sh`: 40 random sequences (3000 events with the default seed) of
  errors recorded (0, repeated and random numbers), and up to four observers
  sampling, checking and checking-and-advancing, half under each option, are
  run through `errseq.bend` and through `ref/gen.py`'s Python model, and the
  traces must match. The model is written from the same behaviour as this
  package (the README above) and shares its author, so it is not an
  independent oracle; as it runs it also asserts the properties on every
  step: each observer is told of an error exactly when one was recorded
  since it last learned of one (or since it sampled, under the kernel option
  if one was unseen then), and is told the latest. There is no external
  implementation to compare with outside the kernel.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (19 laws), `--verdict` ALL
PROOFS CHECK, `check.bend` passes, `ref/run.sh` 3000 events in 40 sequences
match, `scripts/deps.sh errseq` ok.
