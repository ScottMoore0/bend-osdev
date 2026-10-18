# bend-osdev-word64

Unsigned 64-bit words (`W64`) for bend-osdev: arithmetic modulo 2^64, bit
operations, comparisons, the two 32-bit halves, and decimal and hex text.

Every bend-osdev package that needs 64 bits uses `W64`, and only through this
package. A `W64` is its two 32-bit halves, each a native `U32`: two machine
words, where a `Word(64n)` of bits (bend-kit-int's `U64`, used before) cost
sixty-four, and made records of several `W64`s more than Bend's C backend can
compile (bendlang/bend#1069). When Base gains a native `U64`
(bendlang/bend#1027), only this package changes. The type is deliberately not named `U64`, so it cannot clash with
Base's when that arrives.

## API

| Def | Meaning |
|---|---|
| `W64.zero`, `W64.one`, `W64.max` | 0, 1, 2^64 − 1 |
| `W64.from_u32(a)`, `W64.from_parts(hi, lo)`, `W64.from_nat(k)` | build a word (`from_nat` takes k mod 2^64) |
| `W64.lo(a)`, `W64.hi(a)`, `W64.to_nat(a)` | the low and high 32 bits; the value as a `Nat` |
| `add sub mul div mod` | arithmetic modulo 2^64 |
| `and or xor not shl shr` | bits; shifts by a `Nat` |
| `cmp is_eq is_lt is_le is_gt is_ge is_zero` | comparisons |
| `W64.show(a)`, `W64.show_hex(a)` | decimal; 16 lower-case hex digits |
| `W64.bits.lo`, `W64.bits.hi`, `W64.bits.cat` | split a `Word(m + n)` and join it back (used by bend-osdev-bytes) |
| `W64.divmod(a, b)` | the quotient and the remainder together |

## Extension points

* **The representation of `W64` is internal.** It is two `U32` halves today;
  swapping in Base's native `U64` changes only `word64.bend`. Other
  packages use only the defs above, and their proofs use only this package's
  laws (in particular `parts_of`), never the inside of `W64`.
* **Interface laws for dependents' proofs:** `parts_of` (a word is its halves
  joined), `hi_from_parts`, `lo_from_parts`, `lo_from_u32`.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer) has:

* **vectors** for the edge cases: wrapping at 2^64, shifts across the halves, a
  multiply that overflows, and the text forms;
* **properties for every input**: `lo(from_u32(a)) == a`;
  `hi(from_parts(h, l)) == h` and `lo(from_parts(h, l)) == l` for all `h`, `l`;
  and `from_parts(hi(v), lo(v)) == v` for every word `v`.

The arithmetic is this package's own, on the halves: carries and borrows
between them, a 64-bit product from 16-bit partial products, division by
shift-and-subtract (by zero: quotient 0, remainder `a`), shifts across the
halves (by 64 or more: 0), and decimal text by division through 16-bit
pieces. It is not proved for every input; `ref/run.sh` checks every operation
against Python's exact integers.

## Tests

`ref/run.sh` (850 cases with the default seed) compares every operation with
Python's integers on random words and on the edge values 0, 1, 2^32 - 1,
2^32, 2^63 and 2^64 - 1, with shifts of 0 to 70 bits and divisors of 0.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes and `ref/run.sh` 850 cases match, both as native binaries.
