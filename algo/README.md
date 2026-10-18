# bend-osdev-algo

Small algorithms an operating system kernel uses everywhere: bit search in a
32- or 64-bit word, the next set or clear bit of a bitmap, and binary search
in a sorted sequence.

## What it implements

The behaviour is the usual one of these operations, as documented for C
compilers' bit builtins, for POSIX `ffs`, and in the kernel's public API
documentation for its bitmap and bitops helpers; it is restated here in this
package's own words, and the code is written from these statements alone.

* **Population count** (`popcount`, the kernel's "Hamming weight"): the
  number of set bits.
* **Find first set** (`ffs`): 1 plus the index of the lowest set bit, or 0
  for the zero word. `first_set` is the same as a 0-based index, `None` for
  zero.
* **Find last set** (`fls`): 1 plus the index of the highest set bit, or 0
  for zero. `last_set` is the 0-based index, `None` for zero.
* **Count trailing zeros** (`ctz`): the number of clear bits below the lowest
  set bit; the width (32 or 64) for zero, so that it is total.
* **Count leading zeros** (`clz`): the number of clear bits above the highest
  set bit; the width for zero.
* **Next set bit / next clear bit** of a bitmap (`next_set`, `next_clear`):
  the lowest index at or after `start`, and below `size`, whose bit is set
  (clear); `size` if there is none, including when `start >= size`. A bitmap
  is a list of 32-bit words, bit `i` in word `i / 32` at position `i mod 32`;
  bits past the last word count as clear.
* **Lower bound** of a key in a sorted sequence: the index of the first
  element that is not below the key, or the length if every element is.
  **Find**: that index if the element there equals the key, else none.

Bits are numbered from the least significant, 0 to 31 (63).

## Files

| File | Holds |
|---|---|
| `algo.bend` | bit search in a word: `bitw.*` for Base's `Word(n)` of any width, `bits32.*` for `U32`, `bits64.*` for `W64` |
| `bitmap.bend` | bitmaps: `bitmap.*`, on the bit sequences of `bitseq.*` |
| `bsearch.bend` | binary search: the list reference and the `Array<U32>` implementation |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def | Meaning |
|---|---|
| `bits32.popcount(x)`, `bits64.popcount(a)` | number of set bits (`Nat`) |
| `bits32.ffs(x)`, `bits32.fls(x)` (and `bits64.`) | 1-based lowest / highest set bit, 0 for zero |
| `bits32.first_set(x)`, `bits32.last_set(x)` (and `bits64.`) | 0-based lowest / highest set bit, `Maybe<&2, Nat>` |
| `bits32.ctz(x)`, `bits32.clz(x)` (and `bits64.`) | trailing / leading zeros; the width for zero |
| `bits32.test(x, k)`, `bits64.test(a, k)` | bit `k` (`False` past the width) |
| `bitw.popcount(n, w)`, `bitw.ffs`, `bitw.fls`, `bitw.ctz`, `bitw.clz`, `bitw.test`, `bitw.index` | the same on a `Word(n)` of any width |
| `bitmap.test(words, i)` | bit `i` of a bitmap |
| `bitmap.next_set(words, size, start)`, `bitmap.next_clear(...)` | next set / clear bit in `[start, size)`, else `size` |
| `bitmap.first_set(words, size)`, `bitmap.first_clear(words, size)` | the same from 0 |
| `bsearch.sorted(xs)` | each element of the list is at most the next |
| `bsearch.lower_bound(xs, key)`, `bsearch.find(xs, key)` | the reference, on a `List<&2, U32>`: `Nat`, `Maybe<&2, Nat>` |
| `bsearch.array_lower_bound(a, n, key)`, `bsearch.array_find(a, n, key)` | the fast search on the first `n` slots of an `Array<U32>`; hand the array back |

`BsearchState` is the internal state of the array search.

## Extension points

* **Other widths.** `bitw.*` work on Base's `Word(n)` for every `n`, and every
  law is proved at that generality: a new width (a 16-bit field, or a native
  `U64` when Base has one) needs only a wrapper like `bits32.*`.
* **`W64` is opaque.** `bits64.*` reach a `W64` only through
  bend-osdev-word64's `lo`, `hi` and `bits.cat`, and the proofs use its law
  `parts_of`; a change of `W64`'s representation does not touch this package.
* **Reference and fast binary search.** `bsearch.lower_bound` and
  `bsearch.find` are the reference (a scan, proved for every input);
  `bsearch.array_lower_bound` and `bsearch.array_find` are the fast
  implementation (O(log n) array reads), held to the reference by the vectors
  and by the differential test. Another fast implementation can be added
  beside them the same way.
* **Bitmaps of other word sizes.** `bitseq.next` works on any `List<&2,
  Bool>`; `bitmap.bits` is the one place that unpacks 32-bit words.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every `U32` and every `W64`:** `popcount` is at most the width, and a
  word's popcount plus its complement's is 32; the bit `first_set` names is
  set and no bit below it is; the bit `last_set` names is set and no bit
  above it is; `first_set` (32-bit and 64-bit) and `last_set` (32-bit) are
  `None` only for zero; `ctz` is the index of the lowest set bit; `clz` plus
  the index of the highest set bit is the width less one; the lowest set bit
  is at most the highest; and for a nonzero word `ctz + clz` is at most the
  width less one;
* **for every bitmap, size and start:** `next_set` and `next_clear` answer at
  most `size`; an answer below `size` is at or after `start` and has the bit
  wanted; no bit from `start` up to the answer has it;
* **for every list and key:** `lower_bound` is at most the length, and every
  element before it is below the key; for every **sorted** list, every
  element from it on is not below the key; `find` answers only an index that
  holds the key, and, on a sorted list, `None` only when no element is the
  key;
* **vectors:** edge cases of each function (zero, all ones, the top bit, the
  halves of a `W64`, a bitmap search past its size), and the `Array` search
  on a small sorted array.

**Witnesses:** `first_set` and `last_set` answering `Some` (on 40: bits 3
and 5) with a `j` below and above, and `None` (on 0), for `U32` and
`W64`; `next_set` and `next_clear` answering below the size, with a `j`
between the start and the answer; a sorted list with elements before and
from its lower bound, and `find` answering `Some` and `None`.

The proofs work on the bits of a `Word(n)` by induction on the width, so one
proof covers both widths. The binary search laws go through a proof that
`U32`'s order is the order of its value as a `Nat`.

**Not proved:** that the `Array<U32>` binary search agrees with the
reference for every input. Its reads go through Base's `Array.get`, whose
index arithmetic (a mask, and comparisons against the size, on a symbolic
`U32`) does not compute on a symbolic index, and Base has no lemmas about
`Array.get` and `Array.set` yet. It is checked by vectors and by the
differential test instead.

## Tests

`ref/run.sh` compares every function on random inputs and edge cases (728
cases) with Python: `int.bit_count`, `int.bit_length` and bit arithmetic for
the bit search, a direct scan of the bits for the bitmaps, and the standard
library's `bisect.bisect_left` for both binary searches.

## Overlap with Base and bend-collections

* Base's `U32.log2(x)` is the index of the highest set bit for a nonzero `x`
  (and 0 for 0, like 1), so it agrees with `last_set` on nonzero words;
  `last_set` and `fls` are kept because they tell zero apart and carry laws.
* bend-collections' `bitset.bend` has an internal helper `word_count(m, w)`,
  the popcount of the low `m` bits of a `U32`, used by its bitset; its
  `w64.bend` has a `clz` on its own two-limb `U64`, and its `natural.bend` a
  search for integer roots. None of these is a general binary search or a
  next-bit search; `popcount` here is kept as the proved, width-generic
  version.

## Speed

**Lanes.** The figures in this section were measured on bend's JavaScript lane
(`bend file.bend`, which runs `main` inside the bend process). That lane's
stack overflows at some tens of thousands of nested non-tail calls, and it
uses several times the memory of a native build (`bend file.bend -o prog`),
which has a 2 GB stack; see AGENTS.md, "Runtime and checker limits". They
will be re-measured natively once W64-heavy code builds natively
(bendlang/bend#1069).

The bit search walks the 32 (64) bits of a word one at a time, so that it can
be proved for every word; it does not use hardware instructions. The bitmap
search unpacks the words it reads into bits. The list reference is a linear
scan; the `Array` search makes 33 halving steps.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 728 cases match, `scripts/deps.sh algo`
ok.
