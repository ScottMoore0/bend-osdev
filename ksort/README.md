# bend-osdev-ksort

Sorting, the counterparts of the Linux kernel's two sorts: a stable merge
sort on lists (`list_sort`) and an in-place heapsort on the first `n` slots
of an `Array` (`sort`). The comparison is a template argument.

## What it implements

Written from the textbook descriptions of the two algorithms (merge sort:
split, sort the halves, merge; heapsort: build a max-heap, then swap its
largest element to the end of the shrinking heap and sift down) and from
the kernel's public API documentation of `list_sort` and `sort` for what
they promise: `list_sort` is stable, `sort` is an O(n log n) heapsort that
needs no extra memory and is not stable. No kernel source was read.

* **The comparison** is `~le: A -> A -> Bool`, read as "a may come before
  b", as in Base's `List.sort`: `~U32.is_le` sorts ascending, `~U32.is_ge`
  descending. The kernel's `cmp` returns an `int`; a `Cmp`-returning
  comparison `c` becomes `~(a => b => Cmp.is_le(c(a, b)))`.
* **`ksort.list_sort(~A, ~le, xs)`** is stable: of two elements that compare
  equal (each `le` the other), the one first in the input stays first. It is
  top-down: the list is cut at its middle (`List.take` / `List.drop`), each
  half sorted, and the halves merged; the merge takes from the front half
  while `le(front, back)` holds. (The kernel's `list_sort` is bottom-up, which
  changes the order of the comparisons, not the result.)
* **`ksort.heap_sort(~A, ~le, a, n)`** sorts slots `0` to `n - 1` of `a` in
  place and answers the array. The slots from `n` on are never written: every
  write is a swap of two slots below `n` (`ksort.heap.swap` checks both
  indices). Indices are `U32`s, as Base's `Array` takes them.
* **`list_sort_by` and `heap_sort_by`** take a key `~key: A -> Nat` instead
  of a comparison, and sort by `key(a) <= key(b)`: the form the sortedness
  and stability laws are proved for (see Laws).

## Files

| File | Holds |
|---|---|
| `ksort.bend` | the list merge sort: `ksort.merge`, `ksort.list_sort`, `ksort.list_sort_by` |
| `heapsort.bend` | the Array heapsort: `ksort.heap_sort`, `ksort.heap_sort_by`, and its swap and sift steps |
| `spec.bend` | what sorted, permutation and stable mean, as functions that run: `ksort.count`, `ksort.sorted`, `ksort.sorted_by`, `ksort.keep` |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `proof_heap.bend` | the heapsort's list model and the lemmas tying the Array code to it |
| `check.bend` | examples, and the exhaustive heapsort test below |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's `sorted` (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `ksort.list_sort(~A, ~le, xs)` | `xs` sorted by `le`, stably |
| `ksort.list_sort_by(~A, ~key, xs)` | `xs` sorted by a `Nat` key, stably |
| `ksort.merge(~A, ~le, xs, ys)` | two sorted lists merged, `xs`'s element first on ties |
| `ksort.heap_sort(~A, ~le, a, n)` | the first `n` slots of `a` sorted in place; the others unchanged |
| `ksort.heap_sort_by(~A, ~key, a, n)` | the same by a `Nat` key |
| `ksort.count(~A, ~f, xs)` | how many elements satisfy `f` |
| `ksort.sorted(~A, ~le, xs)`, `ksort.sorted_by(~A, ~key, xs)` | each element `le` the next; each key at most the next |
| `ksort.keep(~A, ~key, k, xs)` | the elements whose key is `k`, in order |

`ksort.merge.go`, `ksort.half`, `ksort.msort`, the `ksort.heap.*` steps and
`KsortHeap` (the state of one sift) are internal.

## Extension points

* **The comparison and the key are templates.** Any `~le` works; nothing is
  assumed of it for the permutation laws. `~key` maps an element to a `Nat`;
  a `U32` field is `U32.to_nat(field)`.
* **The element type is a template** (`~A: Data`), for lists and arrays
  alike (an `Array` element type must be known at compile time, so the
  heapsort's helpers take it as `~A`).
* **Another sort** can be added beside these (an introsort, a bottom-up
  merge sort like the kernel's); its laws would be stated with the same
  vocabulary in `spec.bend`.
* **No streaming interface:** a sort needs all of its input.

## Laws

`LAWS.bend`, proved for **every** element type, comparison, key, predicate,
list and array:

* `list_sort_count`: `list_sort` answers a permutation of its input: every
  predicate `f` counts the same number of elements in both (for every `le`,
  lawful or not); `list_sort_length`: the same length; `list_sort_by_count`:
  the same for the sort by key;
* `list_sort_by_sorted`: `list_sort_by` answers a list sorted by key;
* `list_sort_by_stable`: for every key value `k`, the elements of key `k`
  come out in their input order (`keep(k, sort(xs)) == keep(k, xs)`);
* for every array of depth `d < 32` (built by `Arrays.of_list(d, xs, fl)`
  from a list of its `2^d` slots, as bend-osdev-array's `reflect` law shows
  every perfect array is) and every `n`:
  * `heap_sort_count`: the array's slots after the sort are a permutation of
    its slots before (every predicate counts the same);
  * `heap_sort_rest`: every slot from `n` on is unchanged;
  * `heap_sort_perfect`: the array keeps its shape;
* **vectors:** sorts of small lists, ascending, descending, empty, ties by
  key kept in order, and a heapsort of 7 of 8 slots.

**What is not proved, and why.** The sortedness and stability laws are
stated for sorts by a `Nat` key, not for every lawful comparison: they need
the comparison to be total and transitive, and in Bend 2.0.37 that
hypothesis can only be a function from elements to proofs, which a proof
cannot use more than once (it is not `Data`) and which, passed as a
template, `--verdict` cannot model. For a key the facts are `Nat`'s, proved
once. That the heapsort's output is **sorted** is not proved: it needs the
heap invariant through every sift, a much larger proof. It is tested
exhaustively instead (below), and by the differential test.

## Tests

* `check.bend`: examples, and an exhaustive test: every list of 0 to 7
  elements drawn from 0 to 3 (21845 lists) is written into an 8-slot array
  and heapsorted; the first slots must equal `list_sort`'s output (which the
  laws prove sorted and a permutation) and the rest must still hold their
  fill value.
* `ref/run.sh` compares 80 sorts with Python's `sorted`, which the Python
  language reference guarantees stable: `list_sort` ascending and descending
  on random lists of up to 400 elements; `list_sort_by` on lists with many
  equal keys, which must equal `sorted(xs, key=...)` exactly (stability);
  `heap_sort` on arrays of 1 to 512 slots with random `n`, the rest of the
  array checked unchanged; and `heap_sort_by`, its keys sorted and its values
  the same multiset.

## Other sorts in Bend

* Base's `List.sort(~A, ~le, xs)` is a bottom-up merge sort (stable by its
  construction); it has no laws.
* bend-kit-collections' `Heap.sort(~A, ~le, xs)` (0.1.3.0) is a heapsort on
  lists through a leftist heap; its only law is a vector. bend-collections'
  `binary_heap.to_sorted_list` (1.0.0.0) drains an array heap; its laws do
  not cover sorting. Neither proves that its output is sorted or a
  permutation, so neither meets REVIEW.md as a sort; both were read, not run.
  This package depends on neither.

## Dependencies

`bend-osdev-array` (the heapsort laws state the array as
`Arrays.of_list(d, xs, fl)` and read it with `Arrays.leaves` and
`Arrays.nth`, and are proved through array's `of_list_get`, `of_list_set`,
`of_list_leaves`, `index_below`, `index_of_u32` and the `nth_set_*` laws).
The code itself uses Base only.

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and the order of `Nat` and words (`LAWS_order.bend`).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(1 s, 0.29 GB peak; `--verdict` 2 s, 0.31 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes (0 of 21845 lists differ), `ref/run.sh` 80 sorts match,
`scripts/deps.sh ksort` ok.
