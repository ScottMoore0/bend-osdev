# bend-osdev-array

Laws about Base's `Array`, proved for every input: what `Array.get`,
`Array.set`, `Array.size` and `Array.new` (Bend 2.0.37's `bend2/base.bend`)
do, stated against a list model. Base defines `Array<T>` in Bend itself, as a
tree of `ALeaf` / `ANode` indexed by `U32`, and has no lemmas about it; this
package supplies them, written so that they could be offered to Base later.
It has no run-time code of its own beyond two small index helpers.

## What it specifies

An array built by `Array.new(T, d, v)` is a **perfect tree of depth d**:
`2^d` slots, every leaf at depth `d`. Base reads and writes slot `i` of such
an array by masking `i` to its low `d` bits (`i & (2^d - 1)`) and walking the
tree from the most significant of those bits; "indexes wrap around". The
vocabulary the laws use (`array.bend`):

| Def | Meaning |
|---|---|
| `Arrays.slots(d)` | `2^d`, the slot count of a depth-`d` array |
| `Arrays.index(d, i)` | the slot Base uses for index `i`: `U32.to_nat(U32.and(i, U32.sub(U32.shln(1, d), 1)))` |
| `Arrays.is_perfect(T, d, a)` | whether `a` is a perfect tree of depth `d` |
| `Arrays.leaves(T, a)` | the list model: the slots in index order, as a `List<&2, T>` |
| `Arrays.of_list(T, d, xs, fill)` | the perfect array of depth `d` whose slots are `xs` (cut to `2^d`, or padded with `fill`) |
| `Arrays.nth(T, xs, k, fill)` | the model's element `k`, or `fill` past its end |

`index` and `slots` run. `is_perfect`, `leaves` and `of_list` are
specifications: they match on `ALeaf` / `ANode` for any element type, which
the compiled runtime (holding an array natively, 4 bytes per `U32` slot) does
not run ("an open Array element type"), so they appear only in laws and
proofs. At run time Base's `Array.to_list(~T, a)` lists the same slots.

## Files

| File | Holds |
|---|---|
| `array.bend` | the vocabulary above |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs (`PROOF.bend` holds every lemma, prefixed `AP.`) |
| `check.bend` | Base's arrays at run time: wrapped reads and writes, `to_list`, `index` |
| `ref/gen.py`, `ref/run.sh` | the differential test (`gen.py` writes `ref/cases.bend` and `ref/expected.txt`, which `ref/.gitignore` lists) |

## Laws

`LAWS.bend`, 38 laws: 27 for every input, 5 witnesses, 6 vectors
(`index_wrap`, `index_of_u32`, their witness and a vector are drafts, not yet
reviewed by the maintainer). `T` is any `Data` element type.

**For every array, of any shape** (no hypothesis):

* `get_same_array`: `Pair.fst(Array.get(T, a, i)) == a` (a read hands back
  the same array);
* `get_set_same`: `Pair.snd(Array.get(T, Array.set(T, a, i, v), i)) == v`;
* `set_keeps_size`: `Array.set` keeps `Array.size`'s count;
* `get_new`: every read of `Array.new(T, d, v)` answers `v`, for every `d`
  and `i`.

**Perfect trees:**

* `new_perfect`: `Array.new(T, d, v)` is perfect of depth `d`;
* `set_perfect`: `Array.set` keeps an array perfect of depth `d`;
* `size_perfect`: a perfect array's `Array.size` is `(a, U32.shln(1, d))`;
* `new_leaves`: `Arrays.leaves(T, Array.new(T, d, v))` is `List.replicate(T,
  slots(d), v)`.

**The list model, for perfect arrays of depth `d < 32`:**

* `model_length`: the model has `2^d` elements (any depth);
* `model_get`: `List.get(leaves(a), index(d, i)) == Some{Pair.snd(Array.get(T, a, i))}`;
* `model_set`: `leaves(Array.set(T, a, i, v)) == List.set(leaves(a), index(d, i), v)`;
* `get_set_other`: when the masked indices differ
  (`U32.is_eq(U32.and(i, m), U32.and(j, m)) == False`, `m = 2^d - 1`), a write
  at `i` leaves the read at `j` unchanged.

**Indices:** `index_below`: `index(d, i) < 2^d` (any depth); `index_of_nat`:
`index(d, U32.from_nat(k)) == k` for `k < 2^d`, `d < 32`; `index_wrap`
(draft): `index(d, U32.from_nat(2^d + k)) == k` for `k < 2^d`, `d < 32`, so a
counter between `2^d` and `2^(d+1)` wraps to its distance from `2^d`;
`index_of_u32` (draft): `index(d, i) == U32.to_nat(i)` for a `U32` `i` below
`2^d` (any depth), so an index computed by `U32` arithmetic reads the slot of
its value.

**Arrays built from a Data list** (the composable form):

* `reflect`: every perfect array of depth `d` is `of_list(T, d, xs, f)` for a
  list `xs` of `2^d` elements (an existential: the proof answers `xs`);
* `of_list_get`: `Array.get(T, of_list(T, d, xs, f), i) == (of_list(T, d, xs,
  f), nth(T, xs, index(d, i), f))` (`d < 32`, `xs` of `2^d` elements): the
  read answers a literal pair, with the same array;
* `of_list_set`: `Array.set(T, of_list(T, d, xs, f), i, v) == of_list(T, d,
  List.set(xs, index(d, i), v), f)`;
* `of_list_new`, `of_list_size`, `of_list_perfect`, `of_list_leaves`;
* the model's own facts: `set_length`, `nth_set_same`, `nth_set_other`,
  `nth_replicate`.

**Witnesses:** depth 2 with `Array.new` (perfect, below 32); the indices 1 and
2 (masks differ); slot 3 below `2^2`; a four-element list (the length
hypothesis); the `U32` 5 below `2^3` and slot 3 below `2^2` (the hypotheses
of `index_of_u32` and `index_wrap`). **Vectors:** a wrapped write and read,
the leaves of a written array, `index(3, 13) == 5`, `index(2, 4 + 3) == 3`, a
read of a written `of_list` array, and a tree that is not perfect.

### Ownership, pairs and what exactly is proved

* **Ownership.** An `Array` is a single-owner `Type`. A law's statement is
  checked dead, so it may name one array several times (`set_keeps_size`
  mentions `a` on both sides), and the laws above are stated directly over
  an array variable. The proofs consume each array once: `AP.reflect` turns
  it into a Data mirror tree (`AP.Tree`) and an equation, and every lemma
  then talks about the tree, which can be named freely.
* A **consumer's** proof meets the same limit: two laws applied to one array
  variable use it twice. The `of_list` family is for that case: apply
  `reflect` once (one use of the array), then state everything about
  `of_list(T, d, xs, f)` for the Data list `xs`; `of_list_get` and
  `of_list_set` keep that form, so a sequence of reads and writes is followed
  on `xs` alone, consuming each array once as the program does.
  `bend-osdev-blockdev`'s array image device is proved this way.
* **Pairs.** The checker has no eta rule for pairs, and Base destructures the
  pairs `Array.size` and `Array.swap` answer. The laws therefore say what the
  pair *is*: `size_perfect` and `of_list_get` answer literal pairs, so a
  consumer's helper that matches on the pair (`(a, x) = r`) reduces.
* **Depth.** The model laws need `d < 32`: at depth 32 `Array.size`'s count
  `2^32` wraps to 0 and every index reaches the last leaf, so
  `get_set_other` would be false there (such an array could not be held
  anyway). `get_set_same`, `get_same_array`, `set_keeps_size` and `get_new`
  hold at every depth and shape.
* **Base's `Array.to_list`** is not tied to `Arrays.leaves` by a law (it is
  a template answering `List<&1, T>`, and a law cannot pass a template a
  type variable); the differential test compares it with the model.

### How the proofs go

The mirror functions on `AP.Tree` (`AP.size`, `AP.swap_t`, `AP.swap_v`,
`AP.get_v`) copy Base's `Array.size`, `Array.swap.go` and `Array.get.go` with
the same index arithmetic, so "Base's code on a built tree is the mirror" is
a plain induction. The laws for every shape follow by induction on the tree.
For the list model the index arithmetic is tied to the indices' values, by
induction over Base's `Word(n)`: `U32.cmp` is the order of the values;
`Word.sub` (an add-with-carry of the complement) subtracts; halving
`shln(1, d + 1)` gives `shln(1, d)` below 2^32; `shln(1, d) - 1` is the mask of
the low `d` bits, and a word masked by it is below `2^d` (and unchanged when
it already is, and wraps a word of value `2^d + k` to `k`); `U32.from_nat`
and `U32.to_nat` are inverse below `2^32`. The
walk down a perfect tree then picks the left half exactly when the index is
below `2^(d-1)`, and subtracts `2^(d-1)` on the right, which is where the
model's element sits in `leaves(xs) ++ leaves(ys)`.

## What this allows elsewhere

**ringbuf** proves with these laws that the Array ring holds the model's
elements after every operation, for every sound ring (`ringbuf/README.md`,
the element laws): the ring's slots are reflected once into
`of_list(k, L, 0)`, every push is `of_list_set` and every read
`of_list_get`, and a counter's slot is `Arrays.index(k, counter)`, which
`index_of_nat` and `index_wrap` make the counter modulo `2^k` for the
counters of a valid ring.

**algo** proves with them that the `Array<U32>` binary search agrees with the
list reference for every perfect array whose searched prefix is sorted
(`algo/README.md`): each `Array.get` of the search is, by `of_list_get`, a
literal pair of the same array and `nth(L, index(d, mid))`, and
`index_of_u32` makes that `nth(L, mid)` for the in-range indices the search
computes by `U32` arithmetic.

## Extension points

* **The element type** is a parameter of every law (`-T: Data`).
* **More operations:** a law about another Base array def (`Array.map`,
  `Array.clone`) is proved the same way: add its mirror on `AP.Tree` and the
  equation tying it to Base's code.
* **Upstream:** the laws mention only Base's defs and this file's
  vocabulary; offered to Base, the vocabulary would move with them.
* **No streaming interface:** these are laws about a data structure, not data
  arriving in pieces.

## Tests

* `check.bend`: wrapped reads and writes on a depth-3 array at run time.
* `ref/run.sh` runs 40 random sequences (2905 operations: writes and reads
  at in-range indices, at the edges `0`, `2^d - 1`, `2^d`, `2^(d+1) - 1`,
  `2^32 - 1`, and at random `U32` indices, so the mask wraps) on arrays of
  depth 0 to 10, compiled natively, and compares every read and the final
  `Array.to_list` with a Python list model (an index masked to its low `d`
  bits). The model is written here from Base's documentation and shares an
  author with the package; what it checks is that the compiled runtime,
  which holds arrays natively, agrees with what the laws prove of Base's
  definitions.

## Dependencies

None: Base only (`DEPS` is empty).

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and the order of `Nat` and words (`LAWS_order.bend`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 2905 operations in 40 sequences match,
`scripts/deps.sh array` ok. Not yet offered upstream. `index_wrap`,
`index_of_u32`, `witness_index_wrap` and `vector_index_wrap` are drafts, not
yet reviewed by the maintainer.
