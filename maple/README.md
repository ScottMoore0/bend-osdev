# bend-osdev-maple

A range-indexed B-tree in the style of the Linux kernel's maple tree: a map
from non-overlapping ranges `[first, last]` of indices to values, with the
operations an operating system asks of one (address-space areas, ID ranges,
block extents): store a range over whatever was there, erase, load the value
at an index, find the entry at, after or before an index, iterate in order,
and search for a free run of indices of a given size.

This first version is a plain B-tree of fixed order with the maple tree's
interface; the maple tree's own node layouts are not reproduced (see
Specification).

## What it implements

The behaviour, in this package's own words:

* **A tree holds entries `[first, last] -> value`**, in index order, no two
  sharing an index, each with `first <= last`. Ranges are closed: `[a, b]`
  holds every index `i` with `a <= i <= b`, so a single index is `[i, i]`.
* **Storing `[a, b] -> v` overwrites.** Every entry it overlaps keeps only
  its part outside `[a, b]`: an entry straddling `a` is cut to end at `a - 1`,
  one straddling `b` to start at `b + 1`, and one spanning `[a, b]` is split
  in two, keeping its value on both sides. After the store, every index of
  `[a, b]` loads `v` and every other index loads what it loaded before.
  `set_range` ignores an inverted range (`a > b`); `store_range` refuses it
  with `MapleInverted{a, b}`. `store(t, i, v)` is `set_range(t, i, i, v)`.
* **Erasing.** `clear_range(t, a, b)` stores nothing over `[a, b]` (cutting
  and splitting as a store does); `erase(t, i)` clears the whole range of the
  entry holding `i` (nothing, if no entry holds it).
* **Lookups.** `load(t, i)` is the value at `i`; `lookup(t, i)` the entry
  holding `i`, with its range; `find(t, i)` the first entry ending at or
  after `i` (the one holding `i`, or the next); `next(t, i)` the first entry
  starting after `i`; `prev(t, i)` the last entry ending before `i`.
  Iteration is `find(t, 0)`, then `next(t, last)` of each answer, which
  visits `entries(t)` in order.
* **The gap search.** `empty_area(t, min, max, size)` (gap.bend) answers the
  lowest `s` such that the `size` indices `s .. s + size - 1` all lie within
  `[min, max]` and none is stored. It fails with `MapleBadSize` for size 0,
  `MapleBadRange{min, max}` if `max < min`, and `MapleBusy` when there is no
  such run. The run's end is `s + (size - 1)`, and a run that would wrap past
  the top index is never answered.

## Specification

* The Linux kernel's maple tree, as its interface is documented in
  `Documentation/core-api/maple_tree.rst` (Liam R. Howlett) and described in
  LWN's "Introducing maple trees" (2021): a B-tree for non-overlapping
  ranges, including ranges of one index; `mtree_store_range` and
  `mtree_store` overwrite what a range covers; `mtree_load`; `mtree_erase`
  erases the entry at an index; `mt_find`, `mt_next` and `mt_prev` walk the
  entries; `mas_empty_area` finds the lowest gap of a given size within a
  range, failing with `-EINVAL` for a bad size or range and `-EBUSY` when
  there is none. This package was written from that documented behaviour,
  as an abstract data type, and from the B-tree literature below. **No
  kernel source, and no other maple tree or B-tree implementation, was read**;
  the documents were not re-read in this session either (it had no network
  access): the behaviour above is what this package commits to, and its
  laws and tests hold it to that.
* B-trees: Bayer and McCreight, "Organization and Maintenance of Large
  Ordered Indexes", Acta Informatica 1 (1972); Knuth, *The Art of Computer
  Programming*, volume 3, section 6.2.4; Cormen, Leiserson, Rivest and
  Stein, *Introduction to Algorithms*, chapter 18. Here the entries live in
  the leaves, as in a B+-tree, and each slot of a branch records its child's
  last index (a pivot), as the maple tree's nodes do.

Where the documented interface leaves room, this package chooses:

* **Indices.** `U32` by default (the kernel uses `unsigned long`); any key
  type with an order, successor, predecessor, addition and zero can be used
  (see Extension points).
* **Values** are any `Data`. The kernel stores pointers, with `NULL` meaning
  empty and some values reserved; here there is no empty value: an index
  either holds an entry or not, and erasing is its own operation.
* **`next` and `prev` take no bound.** `mt_next(mt, index, max)` and
  `mt_prev(mt, index, min)` stop at a bound; here a caller compares the
  answer with its own bound.
* **Errors** are `MapleError<K>` constructors (`MapleInverted`,
  `MapleBadSize`, `MapleBadRange`, `MapleBusy`) rather than errno values.
* **The node layout is internal.** There are no separate range and
  allocation node types, no RCU, and no per-node gap tracking: a node holds
  up to `order` items (entries in a leaf, slots in a branch), 16 by default.
  An overfull node splits into two halves, so a tree built by appending in
  order has nodes about half full.

## Files

| File | Holds |
|---|---|
| `model.bend` | `MapleEntry`, `MapleError`; the list model, each operation as a plain scan of the entries (`MapleModel.*`, `MapleModel32.*`); the `U32` key operations (`MapleKey32.*`) |
| `node.bend` | the B-tree node and tree types, `MapleOptions`; restructuring nodes (appending chains, taking and dropping slots, splitting an overfull node); searching a node; the invariants (`pivots_ok`, `level`, the fill check `shape`) |
| `tree.bend` | joining two trees, and cutting a tree below or above an index (`MapleTree.join`, `lo`, `hi`) |
| `maple.bend` | the entry file: the public operations, generic (`Maple.*`) and on `U32` (`Maple32.*`) |
| `gap.bend` | the gap search (`Maple.empty_area`, `Maple32.empty_area`) |
| `LAWS.bend`, `PROOF.bend` | the laws of contents, lookups, the invariant and the depth of the leaves, and their proofs |
| `proof_order.bend`, `proof_lists.bend`, `proof_trees.bend`, `proof_level.bend` | the lemmas `PROOF.bend` uses: U32's successor and arithmetic (its order through bend-osdev-u32's `LAWS_order.bend`); the list model; the tree against the model; every leaf at one depth |
| `LAWS_fill.bend`, `PROOF_fill.bend` | the laws of the fill bounds (`balanced`), the order and the height bound, and their proofs |
| `proof_counts.bend` | the lemmas `PROOF_fill.bend` uses: `Nat` arithmetic on counts and halves; the counts that appending, taking, dropping, merging, splitting and joining nodes produce |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test |

## Public interface

Types:

| Type | Meaning |
|---|---|
| `MapleTree<K, V>` (node.bend) | a tree. **Opaque**: use it only through the defs below |
| `MapleEntry<K, V>`: `MapleEntry{first, last, value}` (model.bend) | an entry. Open: match on it, or use `MapleEntry.first`, `.last`, `.value` |
| `MapleOptions`: `MapleOptions{order}` (node.bend) | the choices a tree is built with; `MapleOptions.default()` is order 16 (an order below 3 is taken as 3) |
| `MapleError<K>` (model.bend) | `MapleInverted{first, last}`, `MapleBadSize{}`, `MapleBadRange{min, max}`, `MapleBusy{}` |

Defs. Each `Maple.x` takes the key type and its operations as template
arguments: `~K, ~cmp` (an order `K -> K -> Cmp`) for lookups, and also
`~inc, ~dec` (successor and predecessor) for updates, and `~add, ~zero` for
the gap search; `Maple32.x(V, ...)` is the named default on `U32`
(`U32.cmp`, `U32.inc`, `U32.sub(i, 1)`, `U32.add`, `0`). The structural ones
(`empty`, `entries`, `size`, `height`, `order`, `balanced`, `leveled`) take
`K, V` as erased arguments.

| Def | Meaning |
|---|---|
| `Maple.empty(K, V, opts)`, `Maple32.empty(V)`, `Maple32.empty_with(V, opts)` | the empty tree |
| `Maple.set_range(t, a, b, v)` | `t` with `[a, b]` holding `v`, overwriting; `t` if `a > b` |
| `Maple.store_range(t, a, b, v)` | the same, answering `Result<&2, &2, MapleError<K>, MapleTree<K, V>>`: `Fail{MapleInverted{a, b}}` if `a > b` |
| `Maple.store(t, i, v)` | `set_range(t, i, i, v)` |
| `Maple.clear_range(t, a, b)` | `t` with nothing stored in `[a, b]`; `t` if `a > b` |
| `Maple.erase(t, i)` | `t` without the entry holding `i` |
| `Maple.load(t, i)` | the value at `i`: `Maybe<&2, V>` |
| `Maple.lookup(t, i)` | the entry holding `i`: `Maybe<&2, MapleEntry<K, V>>` |
| `Maple.find(t, i)`, `Maple.next(t, i)`, `Maple.prev(t, i)` | the first entry ending at or after `i`; the first starting after `i`; the last ending before `i` |
| `Maple.entries(K, V, t)` | every entry, in index order |
| `Maple.size`, `Maple.height`, `Maple.order` | the number of entries; the height (`Nat`); the order |
| `Maple.empty_area(t, min, max, size)` (gap.bend) | the lowest free run: `Result<&2, &2, MapleError<K>, K>` |
| `Maple.valid(t)` | the invariant every operation keeps: the entries are in order, disjoint, each `first <= last`, and every pivot is its child's last index (a specification-level check, quadratic in the size) |
| `Maple.leveled(K, V, t)` | every leaf at depth `height` |
| `Maple.balanced(K, V, t)` | `leveled`, and every node but the root holds between half of `order + 1` and `order` items (a root at most `order`, and at least 2 if a branch) |

`Maple32.*` has each of these. The list model (`model.bend`):
`MapleModel.set_range`, `clear_range`, `load`, `lookup`, `find`, `next`,
`prev`, `empty_area` (the same meanings, on a `List<&2, MapleEntry<K, V>>`),
`below`/`above` (every entry cut to its part below or above an index) and
`wf` (in order and disjoint); `MapleModel32.*` for `U32`;
`MapleEntry32.holds(V, e, i)`. Everything else (the node constructors,
`MapleTree.join`, `lo`, `hi`, `MapleNode.*`, `MapleGap`) is internal.

## Extension points

* **Any index type.** The key type and its operations are template
  arguments, specialised at compile time. `check.bend` builds a tree keyed
  by 64-bit addresses with `Maple.set_range(~W.W64, ~W.W64.cmp, ~w_inc,
  ~w_dec, ...)`, the only reason `DEPS` lists `word64` (the library imports
  nothing). The laws are proved for `U32`; the proofs use only facts about
  `U32` that any such key type has (a total order, a successor that is the
  least index above, a predecessor undone by it, addition that is monotone
  where it does not wrap).
* **Any value type**: `V` is any `Data`.
* **The order** is `MapleOptions{order}` (default 16); a tree keeps it.
* **The node layout is internal.** Every law of `LAWS.bend` is stated over
  the entries and the list model, so the node format can change (different
  leaf and branch sizes, a split that leaves the left node full for
  in-order appends, the maple tree's dense and range node types) without
  changing one of them; the proofs about contents never look at counts.
  `LAWS_fill.bend` states this layout's fill bounds (`balanced`), so another
  layout would come with its own fill laws in place of those.
* **Gap tracking.** The gap search skips any subtree that ends before its
  cursor, and otherwise walks entries in order: it takes O(log n + k) steps
  for k entries between `min` and the answer. The kernel's allocation trees
  record the largest gap below each slot; that augmentation can be added to
  the slots and held to the same laws.
* **Reference and fast implementations.** `model.bend` is the reference; the
  tree is held to it by the laws for every tree and query.
* **Streaming** does not apply: the inputs are single operations, and a
  caller iterates with `find`/`next` (or `entries`) when it wants the
  entries one at a time.

## Laws

`LAWS.bend` states 67 laws:
42 **for every input** (every tree, range, index, size and value type, for
the `U32` default), and 25 vectors.

* **The invariant:** the empty tree is `valid`; `set_range`, `clear_range`
  and `erase` keep a tree `valid`; a valid tree's entries are in index order
  and disjoint (`wf`), so ranges never overlap.
* **Balance:** the empty tree is `leveled`, and `set_range`, `clear_range`
  and `erase` keep a tree `leveled`: every leaf stays at the same depth, the
  tree's height.
* **Contents:** on a valid tree, `entries(set_range(t, a, b, v))` and
  `entries(clear_range(t, a, b))` are what the list model gives; an inverted
  range changes nothing, `store_range` refuses it with `MapleInverted` and
  otherwise is `Done{set_range(...)}`; `store` is `set_range` of `[i, i]`.
* **Lookups:** on a valid tree, `load`, `lookup`, `find`, `next`, `prev` and
  `empty_area` answer exactly what the model's scan of `entries(t)` answers.
* **After an update:** after `set_range(t, a, b, v)` every index of `[a, b]`
  loads `v` and every other index loads what it did before; after
  `clear_range(t, a, b)` every index of `[a, b]` loads nothing and every
  other is unchanged; `erase(t, i)` clears exactly the range of the entry
  `lookup(t, i)` names (and changes nothing if there is none), and that
  entry holds `i`.
* **Iteration:** `find(t, 0)` is the first entry; `next(t, last of an
  entry)` is the entry after it, and `None` after the last; `prev(t, first
  of an entry)` is the entry before it.
* **The gap search:** an answer `s` has `min <= s <= s + size - 1 <= max`
  with no wrap, and every index of its run loads nothing; whenever some run
  of `size` free indices lies within `[min, max]`, the search answers (it
  does not fail), and its answer is at or below that run's start (the lowest
  one); size 0 answers `MapleBadSize`, and `max < min` (with a nonzero size)
  `MapleBadRange`.
* **Vectors:** a small tree overwritten across two entries, a range split in
  two, a clear, an erase, lookups, the gap search found and busy, an inverted
  store, a tree of order 3 and height 2 that is `leveled` and `balanced`,
  and an instance of every hypothesis the properties carry (a valid and a
  leveled tree, indices in and out of a range, an inverted range, an entry
  holding an index and one not, entries split around an entry and ending in
  one, lookups that find and miss, a nonzero size, a found gap and a free
  run), so that none is vacuous.

The proofs (`PROOF.bend` and the `proof_*.bend` files) build on facts about
`U32` proved from Base's bit-level definitions: its order, its successor
and predecessor, and that `x <= y` and no wrap in `y + d` give `x + d <=
y + d` without wrap (through the value of a word as a `Nat`). On the list
model: cutting below `a` keeps every index under `a` and clears the rest,
and cutting above `b` likewise, for every list; on an ordered list the cuts
and `set_range` keep it ordered. On the tree: every restructuring keeps the
entries in order, and every node built keeps right pivots, so cutting and
every lookup follow the model; `MapleNode.cons` leaves out empty children,
so every chain holds nodes of one height.

**The fill bounds** are proved in `LAWS_fill.bend` (14 laws, with
`PROOF_fill.bend`, checked in a process of its own): 10 **for every
input** (every tree, range, index and value type, for the `U32` default),
and 4 vectors.

* **Balance:** the empty trees are `balanced` (`balanced_empty`,
  `balanced_empty_with`), and `set_range`, `clear_range` and `erase` keep a
  tree `balanced` (`balanced_set_range`, `balanced_clear_range`,
  `balanced_erase`): every leaf at depth `height`, every node but the root
  holding from half of `order + 1` to `order` items, the root at most
  `order` (and at least 2 if a branch). These carry the hypothesis that the
  tree's order (`Maple.order`) is at least 3, which every tree the interface
  builds has: the empty trees' order is at least 3 (`order_empty_with`; an
  order below 3 is taken as 3), and `set_range`, `clear_range` and `erase`
  keep the order of every tree (`order_set_range`, `order_clear_range`,
  `order_erase`). Below 3 the bounds cannot be kept: a leaf of order 1
  holding one entry is balanced, and storing a second range splits it into
  two leaves under a root of two slots, more than its order.
* **The height bound:** a balanced tree of height `g + 1` holds at least
  `2 m^(g+1)` entries for every `m` with `2m <= order + 1`
  (`size_bound`), so, with `m = half(order + 1)`, its height is at most
  `log` base `half(order + 1)` of half its size.
* **Vectors:** the order of the empty trees (16, and 3 for an order of 1
  asked for), the bounds after ten stores at order 3 (leaves split, height
  2) and a clear across five of them (nodes merge), and the height bound on
  the result (height 2, 9 entries, `m = 2`).

The proofs (`proof_counts.bend`) follow the counts. A full node (any but the
root) of height `h` holds `L = half(order + 1)` to `order` items, and its
children are full nodes of height `h - 1`. `fit` turns a node of `L` to
`2 order` items into one or two full nodes (two halves, of `half(k)` and
`half(k + 1)` items, when it holds `k > order`), and a node of at most
`2 order` items, normalised as a root, into a root. Joining two trees
merges the shorter's root (at most `order` items) into a full node of the
taller's edge, so the merged node holds `L` to `2 order` items, and each
level on the way back up gains at most one slot; the root ends with 2 to
`order` slots. Cutting below or above an index joins trees made of the
original tree's nodes: the slots before the path, a chain of at most
`order` full nodes normalised as a root, and leaves of no more entries
than before. Storing and erasing are such cuts and joins.

## Tests

`ref/run.sh` runs 48 random sequences of operations (`set_range`,
`store_range`, `store`, `clear_range`, `erase`, `load`, `lookup`, `find`,
`next`, `prev`, iteration by `find`/`next` against `entries`, and
`empty_area`), up to 500 operations long, over indices from 0 to 16 up to
the full `U32` range (including 0, 1 and 2^32 - 1, inverted ranges, ranges
that overlap and split existing entries, and gap searches whose run would
wrap), with orders 3, 4, 5, 7 and 16, and compares every result, 2443 in
all, with an independent Python model: a sorted list of `(first, last,
value)` over Python integers (so nothing wraps), with gaps found by listing
the free runs of `[min, max]` (and, for narrow ranges, rechecked by trying
every start). No outside tool implements a maple tree, so the model was
written here, from the description above, by the same author as the
package. After every sequence, and at random points, it also checks the
size, that `valid`, `balanced` and `leveled` hold, and that the height is at
most the largest a B-tree of that order and size can have. `SEED`,
`MAPLE_SEQS` and `MAPLE_GROW` (the length of the long sequences) vary it; 5
seeds of 96 sequences, and 2 seeds of 24 sequences with 2500-operation long
ones, also matched.

`check.bend` runs the examples above, builds a tree of 1000 ranges (height
2) and clears half of them, builds the same tree with order 3 (height 6),
and queries a tree keyed by `W64`.

## Speed and sizes

Measured natively (Bend 2.0.37, `bend file.bend -o prog`, WSL2), each run
including building its tree, with the default order 16:

| Run | Time | Peak RAM |
|---|---|---|
| 100,000 ranges stored in index order | 0.43 s | 12 MB |
| 1,000,000 ranges stored in index order (height 6) | 5.1 s | 103 MB |
| the 100,000, then 100,000 random stores of up to 64 indices over them | 2.0 s | 17 MB |
| the 100,000, then 1,000,000 random loads | 1.3 s | 12 MB |
| the 100,000, then 50,000 range clears | 0.9 s | 16 MB |

So a store into a tree of 100,000 entries takes about 4 to 16 microseconds,
a load under 1. Every operation is pure: an update returns a new tree
sharing the untouched subtrees. A store or clear cuts the tree below and
above the range and joins the parts (O(log² n) node visits, plus the
entries removed); a load or find follows one path (O(log n)); `next` and
`prev` follow one path and fetch at most one neighbour's first or last entry
per level. Every loop over a list of entries is bounded by the order, and
the recursion depth by the height, so there is no length limit beyond
memory. `valid` scans all pairs of entries, so it is a check for tests, not
for large trees; `leveled` and `balanced` are linear.

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and the order of `Nat` and words (`LAWS_order.bend`).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(1 s, 0.35 GB peak; `--verdict` 4 s, 0.36 GB peak) and `PROOF_fill.bend`
(1 s, 0.30 GB peak; `--verdict` 2 s, 0.30 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes (native), `ref/run.sh` 2443 cases match,
`scripts/deps.sh maple` ok. Balance: every leaf at the same depth is proved
for every operation, and so are the fill bounds and the height bound
(`PROOF_fill.bend`, 14 laws, ALL PROOFS CHECK, `--verdict` ALL PROOFS
CHECK). Peaks under `--verdict`: `PROOF.bend` 0.24 GB, `PROOF_fill.bend`
0.21 GB.
