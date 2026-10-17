# bend-osdev-ringbuf

A fixed-capacity FIFO ring buffer of `U32`, in the style of the Linux
kernel's `kfifo`: a power-of-two number of slots in an `Array<U32>` updated
in place, with an in counter and an out counter.

## What it implements

The behaviour follows the kernel's public documentation of `kfifo` (the
"FIFO Buffer" section of its core API documentation), restated here in this
package's own words; no kernel source was read.

* A ring of order `k` has `2^k` slots (`ring.size(k)`). Two counters count
  the elements pushed (`in`) and popped (`out`); the element pushed when `in`
  was `n` sits in slot `n mod 2^k`, and the length is `in - out`.
* `ring.push(r, x)` writes `x` at `in` and moves `in` on; when the ring is
  full it answers `RingFull` and changes nothing.
* `ring.pop(r)` reads the slot at `out` and moves `out` on; when the ring is
  empty it answers `RingEmpty` and changes nothing. `ring.peek(r)` reads the
  same element without removing it.
* `ring.push_list(r, xs)` pushes the elements of `xs` in order while there is
  room and answers how many it pushed (the smaller of the list's length and
  the free space), as `kfifo_in` does. `ring.pop_list(r, n)` pops up to `n`
  elements, oldest first, as `kfifo_out` does.
* `ring.len`, `ring.avail`, `ring.capacity`, `ring.is_empty`, `ring.is_full`
  observe a ring. Every observer hands the ring back beside its answer,
  because the ring holds an `Array` and is linear.

The counters are `Nat`, not machine words that wrap: once `out` reaches the
capacity, both counters drop by the capacity. That keeps `out` below the
capacity and `in` below twice it, so they stay small however long the ring
runs, while the slot index (`in mod 2^k`, computed by the `Array`'s own index
masking) is unchanged.

## Files

| File | Holds |
|---|---|
| `ringbuf.bend` | the ring buffer: the fast implementation, on an `Array<U32>` |
| `model.bend` | the reference: the same interface on the list of the elements |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |
| `gen/proof_model.py` | generates the part of `PROOF.bend` from "# Lists and Nat, for the model" on (the model and relation proofs); `--check` tells whether the file is up to date |

## API

| Def or type | Meaning |
|---|---|
| `RingBuf` | a ring (opaque, linear) |
| `RingError`: `RingFull`, `RingEmpty` | why a push or a pop was refused |
| `ring.new(order)`, `ring.new_default()` | an empty ring of `2^order` slots; the default order is `ring.order_default()` = 8 (256 slots) |
| `ring.size(order)` | `2^order` |
| `ring.push(r, x)` | `RingBuf & Result<&2, &2, RingError, Unit>` |
| `ring.pop(r)`, `ring.peek(r)` | `RingBuf & Result<&2, &2, RingError, U32>` |
| `ring.push_list(r, xs)` | `RingBuf & Nat`: how many were pushed |
| `ring.pop_list(r, n)` | `RingBuf & List<&2, U32>`: the elements popped, oldest first |
| `ring.len(r)`, `ring.avail(r)`, `ring.capacity(r)` | `RingBuf & Nat` |
| `ring.is_empty(r)`, `ring.is_full(r)` | `RingBuf & Bool` |
| `ring.valid(r)` | `RingBuf & Bool`: the counters keep the invariant (always `True` for a ring built by these defs) |
| `RingModel{cap, items}`, `model.new(order)` | the reference model: the capacity and the elements, oldest first |
| `model.push`, `model.pop`, `model.peek`, `model.push_list`, `model.pop_list` | as for the ring, with the same errors |
| `model.len`, `model.avail`, `model.capacity`, `model.is_empty`, `model.is_full`, `model.valid`, `model.items` | observers (the model is `Data`, so they answer the value alone) |

## Extension points

* **The capacity is a parameter:** `ring.new(order)` takes it;
  `ring.new_default()` uses `ring.order_default()`. Orders up to 31 keep
  every slot index within a `U32`.
* **The representation is internal.** `RingBuf` keeps its counters and its
  `Array<U32>` private; another store (a ring of `Octets` bytes, or of
  another element type) can be built the same way, and the counter laws
  carry over unchanged because they do not depend on the elements.
* **Reference and fast implementations:** `model.bend` is the reference,
  written to be obviously correct; `ringbuf.bend` is the fast one. Another
  implementation can be held to the model the same way: the relation laws
  and the differential test.
* **The invariant is checkable:** `ring.valid` lets a caller (or a law about
  code built on this package) state that a ring came from these defs.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer).

**The model, for every model, element, list and count** (proved by
induction): the queue laws, so that interleaved pushes and pops behave as a
queue. A push on a model that is not full appends the element at the end and
answers `Done`; a push on a full one changes nothing; a pop on a model whose
elements are `y` then `t` answers `y` and leaves `t`; a pop on an empty one
changes nothing; peek answers what pop would and changes nothing.
`push_list` appends the elements that fit (all of them when the list fits)
and answers how many; `pop_list(m, n)` answers the first `n` elements and
leaves the rest. **FIFO:** pushing a list that fits and then popping
everything answers the old elements and then the list, in order. Every
operation keeps a model valid (its length at most its capacity).

**The Array ring, for every ring, element, list and count:**

* **the invariant:** `new` makes a valid ring, and `push`, `pop`, `peek`,
  `push_list` and `pop_list` keep a ring valid, so every ring these defs
  build is valid. For a valid ring the length is at most the capacity; the
  length and the free space add up to the capacity; the ring is empty
  exactly when its length is 0, and full exactly when its free space is 0;
* **refusals change nothing:** `push` on a full ring is
  `(r, Fail{RingFull})`, and `pop` or `peek` on an empty ring is
  `(r, Fail{RingEmpty})`, with `r` itself;
* **lengths:** a push on a ring that is not full succeeds and adds one to the
  length; a pop on a ring that is not empty succeeds and takes one from it;
  `peek` answers what `pop` would and leaves the length;
* **batches:** `push_list` pushes the smaller of the list's length and the
  free space; `pop_list` pops the smaller of `n` and the length.

**The Array ring against the model, for every valid ring and model with the
same capacity and length** (a relation on counters only): they agree on
`is_full`, `is_empty` and `avail`; `push` answers the same result on both
and leaves both with the same length and capacity; `pop` succeeds on one
exactly when it succeeds on the other, and leaves the same length and
capacity; `push_list` answers the same count, and `pop_list` the same number
of elements.

**For every value of the elements, on fixed shapes of the Array ring**
(vectors with variables, proved by computation): pushing four arbitrary
elements into an empty four-slot ring and popping four gives them back in
order; the same with the counters at 3, so the elements wrap past the last
slot; three elements across the end of an eight-slot ring; five pushed into
four slots, where the fifth is refused; pushes and pops interleaved.

**Witnesses:** a valid ring that is full; one that is not full and is empty;
one that is not empty; a ring and a model in the relation; and models that
are full, not full, empty, with a first element, and with room for a list.

**What is proved where.** Element order (FIFO) is proved for the model, for
every model and list. For the Array ring it is proved on the fixed shapes
above, and checked by the differential test against both the model and
`collections.deque`. The laws tie the two on everything that depends only on
the counters. To prove that the Array ring holds the model's elements
(`items(model) == contents(ring)` after every operation), Base needs two
lemmas about its `Array`:

* `Array.get` after `Array.set` at the **same** index answers the value set:
  for every array `a` of `2^k` slots and `U32` `i`, `v`,
  `Pair.snd(Array.get(U32, Array.set(U32, a, i, v), i)) == v`;
* `Array.get` after `Array.set` at a **different** index answers what was
  there: for `i` and `j` whose indices differ modulo the size,
  `Pair.snd(Array.get(U32, Array.set(U32, a, i, v), j)) == Pair.snd(Array.get(U32, a, j))`;

together with the facts they rest on: `Array.set` keeps the size,
`Array.get` hands back the same array, and arrays built by `Array.new` and
`Array.set` are perfect trees. Proving these here ran into three walls:

* the index arithmetic (a mask, and comparisons against the size, on a
  symbolic `U32`) needs a theory of `U32` masking, halving and subtraction;
* the checker has no eta rule for pairs, and `Array.set` destructures the
  pairs that `Array.size` and `Array.swap` answer;
* an `Array` is linear while proofs are live code, so two lemmas cannot both
  be applied to one array.

## Tests

`ref/run.sh` runs 24 random sequences (1491 operations: pushes, pops, peeks,
batch pushes and pops) on rings of 1 to 16 slots. Each sequence runs on both
the Array ring and the model, and every result, and the length and free space
after each operation, is compared with Python's `collections.deque` under the
same capacity. The sequences pass the end of the slots many times, so the
index wrap and the counter drop are exercised throughout.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 1491 operations in 24 sequences, on the
Array ring and on the model, match,
`scripts/deps.sh ringbuf` ok.
