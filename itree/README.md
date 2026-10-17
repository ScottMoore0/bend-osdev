# bend-osdev-itree

An interval tree: a set of closed intervals `[start, last]` over an ordered
key, each holding a value, with insertion, removal, lookup, and the queries an
operating system asks of ranges (address ranges, block ranges, locked file
ranges): every interval overlapping a point or a range, the first of them,
and the next one after a given interval, which is how a caller iterates.

## What it implements

The behaviour, in this package's own words:

* **Intervals are closed.** `[s, l]` holds every key `k` with `s <= k <= l`.
  `[s, l]` and `[a, b]` **overlap** when they share a key: `s <= b` and
  `a <= l`. An interval with `s > l` is *inverted*: `ITree.insert` refuses it
  with `ITreeInverted{s, l}`, and `ITree.set` leaves the tree unchanged. (A
  half-open range `[s, e)` with `e > s` is the closed interval `[s, e - 1]`.)
* **The key of an interval is the pair `(start, last)`**, ordered by start,
  then by last. A tree holds each key at most once, with one value: setting an
  interval that is already there replaces its value. Two different intervals
  may share a start, or overlap; they are separate entries.
* **Results come in key order.** `overlapping(t, a, b)` is every stored entry
  overlapping `[a, b]`; `stab(t, p)` is `overlapping(t, p, p)`, the entries
  containing `p`. `first(t, a, b)` is the first entry, in key order, that
  overlaps `[a, b]`; `next(t, a, b, s, l)` is the first one whose key comes
  after `(s, l)`. Starting from `first` and passing each answer's key to
  `next` visits every overlapping entry in order, as `overlapping` lists
  them.
* **`remove(t, s, l)`** takes out the entry with key `(s, l)`, and nothing
  else; the tree is unchanged if there is none. `lookup(t, s, l)` is that
  entry's value.

## Specification

* Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, section
  14.3, "Interval trees": a balanced binary search tree on the intervals,
  each node augmented with the largest endpoint in its subtree, kept up to
  date through every rotation, and a search that skips any subtree whose
  largest endpoint is below the query's start, and any right subtree whose
  node starts after the query's end.
* Adelson-Velsky and Landis's balanced trees (AVL trees), as described in
  Knuth, *The Art of Computer Programming*, volume 3, section 6.2.3: the
  heights of every node's two subtrees differ by at most one, restored after
  each insertion or removal by a single or a double rotation. Such a tree of
  `n` nodes has height below `1.4405 log2(n + 2)`.

No other code was consulted; in particular no GPL interval-tree or
red-black-tree implementation was read.

## Files

| File | Holds |
|---|---|
| `itree.bend` | the tree: types, the generic operations (`ITree.*`, over a key type and order passed as template arguments) and the named default on `U32` (`ITree32.*`) |
| `model.bend` | the list model: each operation as a plain scan of the sorted list of entries, the reference the laws hold the tree to (`ITreeModel.*`, `ITreeModel32.*`) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test |

## Public interface

Types (in `itree.bend`):

| Type | Meaning |
|---|---|
| `ITree<K, V>` | a tree with keys `K` and values `V` (both `Data`). **Opaque**: use it only through the defs below |
| `ITreeEntry<K, V>`: `ITreeEntry{start, last, value}` | a stored interval and its value. Open: match on it, or use `ITreeEntry.start`, `.last`, `.value` |
| `ITreeError<K>`: `ITreeInverted{start, last}` | why `ITree.insert` refused an interval: its start is after its last |

Defs. Each `ITree.x` takes the key type and its order as template arguments,
`ITree.x(~K, ~cmp, V, ...)`, where `cmp: K -> K -> Cmp` is a total order;
`ITree32.x(V, ...)` is `ITree.x(~U32, ~U32.cmp, V, ...)`, the named default.
The structural ones (`to_list`, `size`, `height`, `max_last`, `balanced`,
`empty`) take `K, V` as erased arguments instead, and `ITree.overlaps(~K,
~cmp, s, l, a, b)` takes no `V`.

| Def | Meaning |
|---|---|
| `ITree.empty(K, V)` | the empty tree |
| `ITree.set(t, s, l, v)` | `t` with `[s, l]` holding `v` (replacing its value if present); `t` unchanged if `s > l` |
| `ITree.insert(t, s, l, v)` | the same, answering `Result<&2, &2, ITreeError<K>, ITree<K, V>>`: `Fail{ITreeInverted{s, l}}` if `s > l` |
| `ITree.remove(t, s, l)` | `t` without the entry `[s, l]` (unchanged if absent) |
| `ITree.lookup(t, s, l)` | the value of `[s, l]`: `Maybe<&2, V>` |
| `ITree.overlapping(t, a, b)` | every entry overlapping `[a, b]`, in key order: `List<&2, ITreeEntry<K, V>>` |
| `ITree.stab(t, p)` | every entry containing `p`, in key order |
| `ITree.first(t, a, b)` | the first entry overlapping `[a, b]`: `Maybe<&2, ITreeEntry<K, V>>` |
| `ITree.next(t, a, b, s, l)` | the first entry overlapping `[a, b]` whose key comes after `(s, l)` |
| `ITree.to_list(K, V, t)` | every entry, in key order |
| `ITree.size(K, V, t)`, `ITree.height(K, V, t)` | the number of entries; the height (`Nat`) |
| `ITree.max_last(K, V, t)` | the largest `last` in the tree (`None` when empty): the augmentation at the root |
| `ITree.overlaps(s, l, a, b)` | whether `[s, l]` and `[a, b]` overlap |
| `ITree.valid(t)` | the invariant every operation keeps: the keys of `to_list(t)` strictly increase, and every node stores the largest `last` of its subtree |
| `ITree.balanced(K, V, t)` | the AVL condition: every node stores its height, and its subtrees' heights differ by at most one |

`ITree32.*` has each of these (`ITree32.empty(V)`, `ITree32.set(V, t, s, l,
v)`, …, `ITree32.overlaps(s, l, a, b)`).

The list model (`model.bend`), on a `List<&2, ITreeEntry<K, V>>` in key
order: `ITreeModel.set`, `remove`, `lookup`, `overlapping`, `first`, `next`
(the same meanings as above), and `lasts_le(xs, m)` (every entry ends at or
before `m`) and `has_last(xs, m)` (some entry ends at `m`); `ITreeModel32.*`
for `U32`. Everything else in either file (the tree's constructors, the
`ITree.ins`, `rem`, `bal`, `ov`, `seek` helpers, `ITreeBound`) is internal.

## Extension points

* **Any key type and order.** The key type and its comparison are template
  arguments (`~K`, `~cmp`), specialised at compile time, so they cost nothing
  at run time; `ITree32` is the `U32` default. `check.bend` builds a tree
  keyed by 64-bit addresses with `ITree.set(~W.W64, ~W.W64.cmp, ...)`, the
  only reason this package lists `word64` in `DEPS` (the library itself
  imports nothing). Another order (a reversed one, a key with a tag) needs
  only a `K -> K -> Cmp`.
* **Any value type**: `V` is any `Data` (a mapping's permissions, a lock's
  owner, a device).
* **The balancing scheme is internal.** Every law is stated over the public
  interface and the list model, so the AVL rebalancing (`ITree.bal`) can be
  replaced, by a red-black or weight-balanced scheme, without changing a law;
  the proofs about contents and queries never look at heights.
* **Reference and fast implementations.** `model.bend` is the reference: a
  plain scan of the contents. The tree is held to it by the laws below, for
  every tree and every query.
* **Iteration** is `first` then `next`; a caller that wants the entries one
  at a time (to stop early, or to update as it goes) uses those instead of
  `overlapping`. The results are data, so there is no streaming input to
  offer: a tree is built by repeated `set`.

### Building on bend-collections or not

bend-collections@1.0.0.0 has a proved red-black map
(`src/containers/balanced_search_tree.bend`). This package does not build on
it, for three reasons:

1. An interval tree needs, at every node, the largest endpoint of its subtree,
   updated inside every rotation. The map's public interface offers no way to
   attach such a value to its nodes or to walk its subtrees, so an interval
   tree on top of it could answer a stabbing query only by scanning the
   entries in start order: O(n) instead of O(log n) plus the answers.
2. The map is an imperative store in `Array`s (node links are slot indices).
   Base has no lemmas about `Array.get` and `Array.set` yet, so for-all laws
   about query results through it are out of reach; a persistent tree of
   ordinary constructors lets every law below be proved by induction.
3. bend-osdev keeps interoperation with other libraries in adapter packages,
   not in core packages.

So the tree here is self-contained, written from the descriptions cited above.
AVL rather than red-black, because one rebalancing function serves both
insertion and removal, and removal stays simple.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer). The properties
are proved **for every tree, interval, query and value type**, for the named
default `ITree32`; "valid" is `ITree32.valid`:

* **the invariant:** the empty tree is valid; `set` and `remove` keep a tree
  valid (the keys stay in increasing order, and the augmented maximum at
  every node stays the largest `last` of its subtree);
* **contents:** for a valid tree, `to_list(set(t, s, l, v))` is
  `ITreeModel32.set(to_list(t), s, l, v)` (the entry put in its place,
  replacing an equal key's), and `to_list(remove(t, s, l))` is
  `ITreeModel32.remove(to_list(t), s, l)` (exactly the entries with that key
  taken out); for every tree, `set` of an inverted interval is the tree
  itself, `insert` of one is `Fail{ITreeInverted{s, l}}`, and `insert` of
  any other is `Done{set(...)}`;
* **queries:** for a valid tree, `overlapping`, `stab`, `first`, `next` and
  `lookup` equal the model's scan of `to_list(t)`: a query returns exactly
  the stored intervals that overlap it, in order;
* **after an update:** `lookup(set(t, s, l, v), s, l)` is `Some{v}`, any
  query overlapping `[s, l]` after `set` returns the entry with value `v`,
  and `lookup(remove(t, s, l), s, l)` is `None`;
* **the augmented maximum:** for a valid tree, `max_last(t)` is at least the
  `last` of every entry, and is the `last` of one of them; it is `None` only
  for the empty tree;
* **vectors:** the contents, queries, lookup, removal and maximum of a
  five-interval tree, which is valid and balanced; `insert` of an inverted
  interval; and an instance of each hypothesis the properties carry (a
  valid tree with a maximum, an empty tree's maximum, an interval in order,
  an inverted one, an overlap), so that none is vacuous.

The proofs use four facts about `U32.cmp`, proved from Base's definition by
induction on the bits: it is reflexive, `EQ` only on equal keys, antisymmetric
(`cmp(b, a)` is `cmp(a, b)` reversed), and transitive. The laws hold for any
`~cmp` with these four properties, but they are proved only for `U32`.

**Balance is tested, not proved.** The laws above do not depend on the
heights at all. That `set` and `remove` keep the AVL condition
(`ITree.balanced`), and so the height bound, is checked by the differential
test after every step and by `check.bend`; a proof would need lemmas about
`Nat` arithmetic over heights that this package does not have yet.

## Tests

`ref/run.sh` runs 48 random sequences of operations (`set`, `insert`,
`remove`, `overlapping`, `stab`, `first`, `next`, iteration by `first` and
`next`, `lookup`), up to 600 operations long, over keys from 0 to 16 up to
the full `U32` range (including 0 and 2^32 − 1, and inverted intervals), and
compares every result, 2399 in all, with an independent Python model: a
plain list of `(start, last, value)` scanned in full for every query, written
from the description above. After each sequence, and at random points, it
also checks the size, the maximum, that `valid` and `balanced` hold, and
that the height is at most the largest an AVL tree of that size can have.

`check.bend` runs the examples above, builds a tree of 1000 intervals
(height 10, the least possible) and removes half of them (height 9), and
queries a tree keyed by `W64`.

## Speed

Every operation is pure: an update returns a new tree sharing the untouched
subtrees with the old one. `set`, `insert`, `remove` and `lookup` take
O(log n) steps on a balanced tree. `overlapping` and `stab` visit O((k + 1)
log n) nodes for k answers. `first` and `next` follow O(log n) nodes, by the
usual argument for interval trees: a subtree is searched only if its largest
`last` reaches the query, and a search that fails in such a subtree shows
that every later entry starts after the query. The laws prove the answers,
not these costs.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 2399 cases match, `scripts/deps.sh itree`
ok. Balance (the AVL condition and height bound) is tested, not proved.
