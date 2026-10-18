# bend-osdev-xarray

A sparse array from 32-bit indices to values, in the style of the Linux
kernel's XArray: load, store, insert and erase an entry, test for emptiness,
find the nearest entry at or after (or at or before) an index, list the
entries in a range, and keep three independent marks per entry. It is a
persistent (pure) radix tree, generic over the value type (`-V: Data`), and
every operation is proved correct for every array, index and value.

## What it implements

The behaviour is that of the kernel's XArray as an abstract data type, as its
public API documentation describes it (docs.kernel.org, "XArray", in
core-api). It is restated here in this package's own words, and the code is
written from these statements alone; no kernel source was read.

* An array maps each index to at most one value. The **empty** array holds
  nothing.
* **load** answers the value at an index, or nothing. **store** puts a value
  at an index, replacing any value there. **insert** does the same only when
  the index holds no value, and otherwise fails with `XArrayBusy` and changes
  nothing (the kernel's `xa_insert`). **erase** removes the value at an index.
* **is_empty** tells whether no index holds a value.
* **find** answers the smallest index at or after a start that holds a value;
  **find_last** the largest at or before it; each answers nothing when there
  is none.
* **range** lists, in ascending order of index, every index between two
  bounds (both included) that holds a value, with its value; nothing when the
  first bound is past the second.
* **Marks.** Each index has three independent flags, `XMark0`, `XMark1` and
  `XMark2` (the kernel's `XA_MARK_0..2`). **set_mark** sets one on an index
  that holds a value, and does nothing on an index that holds none;
  **clear_mark** clears one; **get_mark** tests one; **find_marked** answers
  the smallest index at or after a start that carries a mark. Erasing an index
  clears its marks; storing a new value at an index keeps them.

Where this differs from the kernel's XArray:

* indices are `U32` (the kernel's are `unsigned long`);
* the array is a value: an update answers a new array and leaves the old one
  as it was, so there is no locking, RCU, or allocation failure;
* there are no multi-index entries, value entries, reservations,
  `xa_cmpxchg`, or ID allocation (`xa_alloc`); erasing is its own def rather
  than storing `NULL`;
* `find` takes no upper bound: compare its answer with yours, or use `range`.

## Files

| File | Holds |
|---|---|
| `xarray.bend` | the radix tree and the XArray (the whole package; one concern) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`gen.py` writes `ref/cases.bend` and `ref/expected.txt`, which `ref/.gitignore` leaves out) |

## API

| Def / type | Meaning |
|---|---|
| `XArray<V>` | a sparse array of `V: Data` (opaque) |
| `XArray.empty(V)` | the empty array |
| `XArray.load(V, t, i)` | the value at `i`: `Maybe<&2, V>` |
| `XArray.store(V, t, i, v)` | `t` with `v` at `i` (marks at `i` kept) |
| `XArray.insert(V, t, i, v)` | `Done{store(V, t, i, v)}` if `i` holds nothing, else `Fail{XArrayBusy{}}`: `Result<&2, &2, XArrayError, XArray<V>>` |
| `XArray.erase(V, t, i)` | `t` with nothing at `i`, and no marks there |
| `XArray.is_empty(V, t)` | whether no index holds a value |
| `XArray.find(V, t, s)`, `XArray.find_last(V, t, s)` | the smallest index `>= s` / largest `<= s` holding a value: `Maybe<&2, U32>` |
| `XArray.range(V, t, a, b)` | the entries with `a <= index <= b`, ascending: `List<&2, XEntry<V>>` |
| `XEntry<V>` | `XEntry{index: U32, value: V}` (open: match on it) |
| `XMark` | `XMark0{}`, `XMark1{}`, `XMark2{}` (open); `XMark.is_eq(m, n)` |
| `XArray.set_mark(V, t, i, m)`, `XArray.clear_mark(V, t, i, m)` | set (only if `i` holds a value) / clear mark `m` at `i` |
| `XArray.get_mark(V, t, i, m)` | whether `i` carries `m` |
| `XArray.find_marked(V, t, s, m)` | the smallest index `>= s` carrying `m` |
| `XArrayError` | `XArrayBusy{}` (open) |

Everything else in `xarray.bend` (`XTree`, `XPath`, `XAt`, and the `XArray.*`
helpers not listed above) is internal.

## How it works

An index is read as its 32 bits, most significant first (its *path*), so the
tree's left-to-right order is the indices' numeric order. A node (`XBin`)
splits on one bit; a leaf (`XLeaf`) holds a value at depth 32; a subtree with
no values is `XNil`, and erase folds a node whose halves are both empty back
into `XNil`, so the tree stays sparse. A search walks down the start's path
and, where the start leans to the nearer half, falls back to the farther
half's extreme path only if the nearer half has nothing; on the arrays the
defs build every non-empty subtree holds a value, so a search visits at most
about two paths. Each mark is a second tree of the same shape over `Unit`,
holding the marked indices, so a marked search is the same search.

Costs: load, store, insert, erase and the mark operations each walk (and an
update copies) one path of 32 nodes; erase walks four (the value tree and the
three mark trees); find, find_last and find_marked walk about two paths;
range walks the bounds' paths and the paths of the entries it lists, a few
dozen steps per entry listed.

## Extension points

* **The value type** is a parameter: `XArray<V>` for any `V: Data`.
* **Fan-out: a documented constant, 2** (one index bit per level, height 32).
  Bend's `Data` values cannot hold an `Array`, so a node of 64 slots, as the
  kernel's, would be a 64-cell list (slow to index) or a binary tree inside the
  node, which is this tree again; and in a persistent tree a wider node makes
  every update copy more. A different node layout can replace `XTree` behind
  the same defs: the laws mention only the public interface, so they and the
  differential test carry over, and only the internal lemmas in `PROOF.bend`
  need redoing.
* **The index type is `U32`.** The tree works on paths of any length
  (`Word(n)`), so a 64-bit array is a front end mapping a `W64` (bend-osdev-word64)
  to a 64-bit path. It is not provided: its laws would need word64 to prove
  that `W64`'s order is its halves' order, which word64's laws do not yet
  state.
* **The number of marks is a constant, 3**, as the kernel's. Another mark is a
  constructor of `XMark` and a tree field of `XArray`.
* **The representation is internal** (`XArray`'s fields, `XTree`, the paths),
  so it can change without touching any user.
* **No streaming interface:** an XArray is a data structure updated one entry
  at a time, not data arriving in pieces.

## Laws

`LAWS.bend` has 47 laws, all
over the public interface.

**41 hold for every array, every index and every value** (and every value
type `V`), proved by induction over the tree:

* entries: `load_empty`, `load_store` (a load after a store at the same index
  gives the value), `load_store_other` (a store leaves every other index's load
  unchanged), `load_erase`, `load_erase_other`, `insert_absent`,
  `insert_present`;
* emptiness: `is_empty_empty`, `is_empty_load`, `is_empty_store`,
  `is_empty_false` (a non-empty array has an index holding a value);
* search: for `find`, the answer holds a value (`find_present`), is at or
  after the start (`find_at_or_after`), and no index between the start and it
  holds one (`find_first`); `None` means no index at or after the start holds
  one (`find_none`); the same four for `find_last`;
* range: every entry listed is in the array with that value (`range_present`)
  and within the bounds (`range_from`, `range_to`); consecutive entries have
  strictly ascending indices (`range_ascending`); every entry of the array
  within the bounds is listed (`range_complete`);
* marks: `mark_empty`, `mark_set` (a mark set on an index holding a value is
  seen), `mark_set_absent` (setting a mark on an empty index changes nothing),
  `mark_clear`, setting or clearing a mark changes no other index and no other
  mark (`mark_set_other_index`, `mark_set_other_mark`,
  `mark_clear_other_index`, `mark_clear_other_mark`) and no value
  (`load_set_mark`, `load_clear_mark`), an erase clears the index's marks and
  no other index's (`mark_erase`, `mark_erase_other`), a store keeps every
  mark (`mark_store`), and the four search laws for `find_marked`.

Inequality of indices is stated as `U32.is_eq(i, j) == False`, and order with
Base's `U32.is_le` / `U32.is_lt`. The proofs relate `U32.cmp` to the order of
paths once, for every pair of indices, by induction over Base's `Word`.

**6 are vectors** on a small array: a find, a find_last, a failing find, a
range over everything, erasing every entry back to empty, and a marked find.

On arrays the defs build, a marked index always holds a value: `set_mark`
marks only indices holding one, `erase` clears marks, and `store` keeps them.
The laws state each of these steps, but there is no single law "a mark implies
a value", since a law quantifies over every value of the type, including ones
the defs never build; the differential test checks it on every sequence.

## Tests

* `check.bend`: examples covering every def, at both ends of the index range.
* `ref/run.sh` compares the package with an independent model written in
  `ref/gen.py` (a Python dict from index to value, and a Python set per mark)
  on 60 random sequences of 300 operations each (18000 operations, 10170 of
  them queries whose answers are compared). Indices are drawn from small
  values, clusters, the extremes (0, 2^31 - 1, 2^31, 2^32 - 1) and uniform
  32-bit values, mostly reusing indices already seen, so stores replace,
  erases hit, and marks are set on present and absent indices. Seeds 1 to 5
  with 20 sequences of 600 operations each were also run and matched.

## Dependencies

None: Base only (`DEPS` is empty). Indices are Base's `U32`, not `W64`, for
the reason under Extension points.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 10170 queries over 18000 operations match.
