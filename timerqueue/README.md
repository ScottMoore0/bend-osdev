# bend-osdev-timerqueue

Timers keyed by expiry, after the Linux kernel's time-ordered timer queues
(the queue under its high-resolution timers), as a pure state
machine: add a timer, delete one, ask for the next expiry, and expire every
timer due by a time. Time is passed in, never read: an expiry is a `W64`
(bend-osdev-word64) in whatever unit the caller keeps, and
`TimerQueue.expire(q, now)` takes `now` as an argument. tcpip handles its
timers the same way.

The queue keeps its timers in a store taken as a template argument: any
priority queue or ordered map with the six calls of `TqStore`. The default,
`TimerQueueList`, is a sorted list.

## Specification

**The kernel's timerqueue has no published documentation.** No
docs.kernel.org page documents it, and no rendered kernel-doc for its
functions was found. "The Linux Kernel API"
(<https://docs.kernel.org/core-api/kernel-api.html>) was read in full and
has none, and a search of docs.kernel.org finds the name only in passing.
The one document that describes the behaviour it serves is **"hrtimers -
subsystem for high-resolution kernel timers"**,
<https://docs.kernel.org/timers/hrtimers.html>
(`Documentation/timers/hrtimers.rst`), section **"hrtimer subsystem
implementation details"**, read on 2026-10-18. It says that timers are
enqueued at activation time into a red-black tree used solely for
time-sorted ordering, and that a separate list gives the expiry code fast
access to the queued timers. **No kernel source was read**: search results
pointing at mailing-list patches or source mirrors were skipped.

So this package's interface and behaviour are **its own design**, built on
that one documented fact (timers held in time order) and on the brief for
this package. In particular, the page does not say any of the following;
each is a choice made here:

* **A timer** (`TqTimer{expiry, id}`) is its expiry and an id the queue
  hands out in the order timers are added (0, 1, 2, ...). It is also the
  handle `delete` takes. A timer carries no payload: the caller keeps what a
  timer is for under its id (in an IDR from bend-osdev-idalloc, say).
* **The order** (`TqTimer.cmp`): by expiry, and timers with the same expiry
  by id, so by insertion order (the brief asks for this; hrtimers.rst says
  nothing about ties). Expiries compare as unsigned 64-bit values
  (`TqTime.cmp`: the high halves, then the low halves, through word64's
  `W64.hi` and `W64.lo`); there is no wrap-around.
* **The next expiry** is the least expiry held, or `None`.
* **Expiring** (`TimerQueue.expire(q, now)`) answers every timer with an
  expiry at or before `now`, earliest first, and the queue without them.
  hrtimers.rst does not describe how the expiry code runs due timers.
* **Deleting** a timer the queue does not hold changes nothing.
* **The store is any ordered structure**: the page's red-black tree is one
  possible `TqStore`; the default is a sorted list (see Extension points).

## Files

| File | Holds |
|---|---|
| `timer.bend` | `TqTimer`, the order on times and timers (`TqTime.*`, `TqTimer.*`), and list predicates the laws use |
| `store.bend` | the store interface `TqStore<Q>` and the calls through it |
| `sorted.bend` | the default store: a sorted list (`TqSorted.*`) |
| `timerqueue.bend` | the entry file: the queue over any store (`TimerQueue.*`) and the named default (`TimerQueueList.*`) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `proof_order.bend` | the order lemmas `PROOF.bend` uses: Base's Bool and Cmp lemmas, the U32 order through bend-osdev-u32's `LAWS_order.bend`, and the order of times and timers built on them |
| `gen/proof.py` | generates `PROOF.bend` (its lemmas repeat long terms); `--check` tells whether the file is up to date |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `TqTimer{expiry, id}`, `TqTimer.expiry`, `TqTimer.id` | a timer (open: match on it, or use the defs) |
| `TqTime.cmp`, `TqTime.le`, `TqTime.lt` | the order on times |
| `TqTimer.cmp`, `TqTimer.le`, `TqTimer.lt`, `TqTimer.is_eq` | the order on timers; `is_eq`: the same timer |
| `TqTimer.sorted`, `TqTimer.member`, `TqTimer.all_from`, `TqTimer.all_due`, `TqTimer.all_later`, `TqTimer.ids_below` | predicates on lists of timers |
| `TqStore<Q>{empty, insert, remove, first, drop_first, timers}` | the store interface (see Extension points) |
| `TqSorted.store()` | the default store, on `List<&2, TqTimer>` |
| `TimerQueue<Q>` | a queue over store type `Q` (opaque) |
| `TimerQueue.new(~Q, ~st)` | the empty queue |
| `TimerQueue.add(~Q, ~st, q, expiry)` | `TqAdded{queue, timer}`: the queue with a timer expiring at `expiry`, and that timer |
| `TimerQueue.delete(~Q, ~st, q, x)` | the queue without `x` |
| `TimerQueue.next_expiry(~Q, ~st, q)` | `Some` earliest expiry, or `None` |
| `TimerQueue.expire(~Q, ~st, q, now)` | `TqExpired{queue, fired}`: the timers due by `now`, in order, and the queue without them |
| `TimerQueue.pending(~Q, ~st, q)`, `TimerQueue.contains(~Q, ~st, q, x)` | the timers held, in order; whether `x` is held |
| `TimerQueue.next_id(Q, q)`, `TimerQueue.issued(Q, q, x)` | the id the next timer gets; whether `x`'s id was handed out |
| `TqAdded.queue`, `TqAdded.timer`, `TqExpired.queue`, `TqExpired.fired` | the fields (each takes `Q` first) |
| `TimerQueue.first_expiry(m)` | the expiry of `Some` timer |
| `TimerQueueList.new`, `.add`, `.delete`, `.next_expiry`, `.expire`, `.pending`, `.contains` | the same on the default store |
| `TimerQueueList.valid(q)` | the timers in order and every id below the next (true of every queue these defs build) |

## Extension points

* **The store is a template argument** (`~Q, ~st`): a `TqStore<Q>` of six
  functions over any store type `Q` (`Data`). Its contract: `timers(q)` are
  the timers held, in `TqTimer` order; `first(q)` is the first of them;
  `drop_first(q)` removes it; `insert(q, x)` adds `x`; `remove(q, x)`
  removes every timer equal to `x`; `empty` holds none. A binary heap, a
  pairing heap, a balanced tree or an ordered map keyed by `TqTimer` is
  another `TqStore` value, specialised at compile time; `ref/gen.py` shows
  the behaviour a store must reproduce (its model is a heap with lazy
  deletion), and the laws, stated for the default, are the ones to prove of
  another.
* **Why the default is a sorted list written here.** bend-osdev-maple maps
  ranges of `U32` indices to values, not `W64` keys with ties, and its laws
  are stated for its `U32` default; bend-collections' `Heap` (on the hub)
  has laws for its size and a vector, not for its order, and would bring a
  hub library's type into a core package, which CONVENTIONS.md sends to
  adapter packages. A sorted list is simple enough to prove everything about
  (insertion and removal take time in the number of timers; the first timer
  and its removal, constant time), and a faster store can be held to it.
* **The time unit and the order are the caller's**: any unit in a `W64`;
  times compare as unsigned values.
* **No payload**: a timer's id indexes the caller's own table, so the queue
  never constrains what a timer carries.
* Streaming is not applicable: each operation is one step.

## Laws

`LAWS.bend`, all proved in `PROOF.bend`, for the default store, for every
queue, time and timer ("valid": `TimerQueueList.valid`):

* **The invariant**: `tq_new_valid`, and add, delete and expire keep a
  queue valid (`tq_add_valid`, `tq_delete_valid`, `tq_expire_valid`); a
  valid queue's timers are in order (`tq_sorted`); a new queue is empty
  (`tq_new_empty`).
* **Add** (`tq_add_timer`): the new timer has the next id, which then moves
  on by one, so ids, and ties between equal expiries, follow insertion
  order; it is held afterwards (`tq_add_contains`), was not held before
  (`tq_add_fresh`), and every other timer the queue handed out is held
  afterwards exactly when it was before (`tq_add_others`).
* **Delete**: the timer is not held afterwards (`tq_delete_gone`), and every
  other timer is held exactly when it was before (`tq_delete_others`).
* **The next expiry is the minimum**: it is the first timer's expiry
  (`tq_next_first`), and every timer held expires at or after it
  (`tq_next_min`).
* **Expire**: the timers fired, then the timers left, are the timers held
  (`tq_expire_split`); the fired ones are all due (`tq_expire_due`) and in
  nondecreasing expiry order, ties by id (`tq_expire_sorted`); every timer
  left expires after `now` (`tq_expire_later`).
* **A deleted timer never fires**: the next expiry after a delete does not
  fire it (`tq_deleted_never_fires`), and a timer not held is neither fired
  nor held after an expiry (`tq_expire_never`). With `tq_delete_gone`, and
  `tq_add_others`, `tq_delete_others` and `tq_expire_never` for every later
  step (a timer handed out stays issued: `tq_issued_add`,
  `tq_issued_delete`, `tq_issued_expire`), a timer once deleted is never
  held, and so never fired, again.
* A vector (four timers, one deleted, an expiry) and witnesses that the
  hypotheses can hold (`tq_vec`, `tq_wit`).

* **The order on times is word64's** (`tq_time_cmp`): `TqTime.cmp`, built
  from `W64.hi` and `W64.lo`, agrees with `W64.cmp` for every pair of
  times, and so (by word64's `cmp_value`) with the order of the values.

The order lemmas are proved from Base's `U32` order (bit by bit, as
bend-osdev-maple does) and, for the equality of two times with equal
halves, word64's interface law `parts_of`; `tq_time_cmp` follows from
word64's laws `cmp_hi_lt`, `cmp_hi_eq` and `cmp_hi_gt`. Nothing looks
inside `W64`.

Every property this package states is proved; the differential test
also compares the fired order with Python's integers.

## Tests

* `check.bend`: four timers (two with the same expiry), one deleted, the
  next expiry, expiries at two times, and expiries on either side of 2^32
  (where the high half changes).
* `ref/run.sh`: 40 random sequences (2583 events with the default seed) of
  adds (expiries near 0, around 2^32, or anywhere), deletes (of live,
  fired, deleted and never-issued timers), next-expiry queries and
  expiries are run through `TimerQueueList` and through `ref/gen.py`'s
  Python model, a binary heap (`heapq`) with deleted timers dropped lazily,
  and the answers must match. The model is written from the same
  description and shares an author with the package (the heap is a
  different structure from the sorted list, but there is no external timer
  queue to compare with); as it runs it also asserts that every expiry is in
  order, all due and none deleted, that the timers left expire later, and
  that the next expiry is the minimum.

## Dependencies

bend-osdev-u32, in the proofs only: its laws of the order of `Nat` and words
(`LAWS_order.bend`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (26 laws), `--verdict` ALL
PROOFS CHECK, `check.bend` passes, `ref/run.sh` 2583 events in 40 sequences
match, `scripts/deps.sh timerqueue` ok.
