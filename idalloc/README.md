# bend-osdev-idalloc

Integer ID allocation in the style of the Linux kernel's IDR and IDA: hand
out the lowest free ID within a range, optionally mapping it to a value, and
free it again.

## What it implements

The behaviour follows the kernel's public API documentation for IDR and IDA
(the "ID Allocation" page of its core API documentation), restated here in
this package's own words; no kernel source was read.

* An **IDR** (`Idr<V>`) maps allocated IDs (natural numbers) to values of
  type `V`.
  * `idr.alloc_range(V, r, IdRange{min, max}, v)` takes the **lowest** ID `i`
    with `min <= i <= max` that is not in use, maps it to `v` and answers the
    new state and `i`. If every ID of the range is in use it fails with
    `IdExhausted`; if `max < min`, with `IdBadRange`. `idr.alloc` uses the
    default range, `idr.alloc_min` the default maximum.
  * `idr.find(V, r, i)` is the value of `i`, or `None` if it is free.
  * `idr.remove(V, r, i)` frees `i` and answers its old value (`None` if it
    was free); `idr.free` frees it without the value.
  * `idr.replace(V, r, i, v)` maps an ID in use to a new value and answers the
    old one; it fails with `IdNotFound` if `i` is free.
* An **IDA** allocates IDs without values. Here an IDA is an `Idr<Unit>`, and
  `ida.alloc_range`, `ida.alloc`, `ida.alloc_min`, `ida.free` and
  `ida.in_use` are the IDR operations without a value. Freeing a free ID
  changes nothing.
* The **default range** is 0 to 2^31 − 1 (`id.range_default()`), the
  kernel's non-negative `int`; `id.range_min(min)` is `min` to that maximum.

## Files

| File | Holds |
|---|---|
| `idalloc.bend` | the types and operations, IDR and IDA |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `Idr<V>` | an IDR whose values have type `V` (opaque: use the defs below) |
| `IdRange{min, max}` | the IDs an allocation may answer, both ends included |
| `IdError`: `IdExhausted`, `IdBadRange`, `IdNotFound` | why an operation failed |
| `IdrAlloc<V>{map, id}` | what an allocation answers: the new state and the ID |
| `IdrOld<V>{map, old}` | what a replace answers: the new state and the old value |
| `id.range_default()`, `id.range_min(min)`, `id.max_default()` | the default range, 0 to 2^31 − 1 |
| `idr.new(V)` | the empty IDR |
| `idr.alloc_range(V, r, rg, v)`, `idr.alloc(V, r, v)`, `idr.alloc_min(V, r, min, v)` | allocate: `Result<&2, &2, IdError, IdrAlloc<V>>` |
| `idr.find(V, r, i)`, `idr.in_use(V, r, i)` | look up |
| `idr.remove(V, r, i)`, `idr.free(V, r, i)` | free, with or without the old value |
| `idr.replace(V, r, i, v)` | change a value: `Result<&2, &2, IdError, IdrOld<V>>` |
| `idr.ids(V, r)` | the IDs in use, in increasing order |
| `idr.state(V, res, r)`, `idr.id(V, res)` | the state after an allocation (`r` if it failed), and its ID |
| `ida.new`, `ida.alloc_range`, `ida.alloc`, `ida.alloc_min`, `ida.free`, `ida.in_use`, `ida.ids`, `ida.state`, `ida.id` | the same on an `Idr<Unit>` |

## Extension points

* **The range is a parameter.** Every allocation takes an `IdRange`; the
  kernel's defaults are `id.range_default()` and `id.range_min(min)`.
* **The value type is a parameter.** `Idr<V>` takes any `Data` type; the IDA
  is the instance `V = Unit`, so every IDR law holds for it too.
* **The representation is internal.** `Idr<V>` is a list of slots, one per
  ID up to the highest allocated (`None` when free). A faster representation
  (a radix tree of bitmaps, as the kernel uses) can replace it behind the
  same defs; the laws, which use only the public defs, then state what it
  must keep.

## Laws

`LAWS.bend`. For **every**
state, range, ID and value:

* **allocation (IDA and IDR):** the ID answered was free before and is in use
  after (for an IDR, mapped to the value); it lies in the range; every ID of
  the range below it was in use, so it is the lowest free one; no other ID
  changes; `IdExhausted` only when every ID of the range is in use;
  `IdBadRange` only when `max < min`;
* **free and remove:** the ID is free after; no other ID changes; `remove`
  answers the value the ID had; `free` is `remove` without the value;
* **replace:** the ID maps to the new value after, and mapped to the answered
  old value before; no other ID changes; on a free ID it fails with
  `IdNotFound`;
* **allocation after free:** freeing the ID just allocated and allocating
  again answers the same ID and the same state; and (IDA) freeing any ID of
  the range below the one an allocation would answer makes the next
  allocation answer it, and gives back the state from before the free;
* **vectors:** short allocation sequences, an exhausted and a bad range.

**Witnesses:** an allocation answering `Done` with an ID `j` in use in
`[min, id)` (with 0 and 1 in use, the next ID is 2 and `j` = 1); an
exhausted and a bad range (the vectors above); a `replace` answering
`Done`; and a `find` answering `None`.

The vectors use a range of 0 to 9: the Lean kernel behind `--verdict` does
not yet evaluate a vector through the default range, whose maximum is the
large `Nat` literal 2147483647n (it reports a mismatch with the TypeScript
checker). The properties cover every range, the default one included.

## Tests

`ref/run.sh` runs 40 random sequences of operations (1174 operations:
allocations with random and bad ranges, frees, finds, removes, replaces) on
an `Idr<U32>` and compares every result, and the IDs in use at the end, with
a model on a Python dict. There is no ID allocator outside this repository to
compare with (the kernel's lives inside the kernel), so the model is written
in `ref/gen.py` from the behaviour above.

## Limitations

* Allocation scans the slots from `min`, so it is linear in the ID it
  answers, and the state is as long as the highest ID allocated; the
  kernel's radix tree is logarithmic. The representation can be replaced
  (see Extension points).
* There is no cyclic allocation (`idr_alloc_cyclic`) and no iteration other
  than `idr.ids`.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 1174 operations in 40 sequences match,
`scripts/deps.sh idalloc` ok.
