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

## Files

| File | Holds |
|---|---|
| `word64.bend` | `W64` and its operations |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `proof_value.bend` | the lemmas the value laws rest on, for two halves of any width |
| `proof_shift.bend` | the lemmas the shift laws rest on, for two halves of any width |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's integers |

The code imports nothing but Base. The proofs (and `LAWS.bend`, for
`U32Nat.dbl` and `U32Nat.bit`) use bend-osdev-u32 (`DEPS`), whose laws give
the arithmetic of each 32-bit half.

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
  joined), `hi_from_parts`, `lo_from_parts`, `lo_from_u32`; and the value
  laws below (`cmp_value`, `lt_value`, `le_value`, `add_value`, `sub_value`
  and the rest), so that a dependent reasons about `W64` arithmetic as
  `Nat` arithmetic without looking inside `W64`.

## Laws

`LAWS.bend` has:

* **vectors** for the edge cases: wrapping at 2^64, shifts across the halves, a
  multiply that overflows, and the text forms;
* **properties for every input**: `lo(from_u32(a)) == a`;
  `hi(from_parts(h, l)) == h` and `lo(from_parts(h, l)) == l` for all `h`, `l`;
  and `from_parts(hi(v), lo(v)) == v` for every word `v`;
* **the value of a word** (`to_nat_parts`): `lo + hi * 2^32`, the weight
  2^32 written as 32 doublings (`U32Nat.dbl(32n, ...)`, from
  bend-osdev-u32); two words with the same value are the same word
  (`value_eq`);
* **comparison is the value order**, for every pair of words: `cmp_value`,
  and `lt_value`, `le_value`, `eq_value` for `is_lt`, `is_le`, `is_eq`;
  and it compares the high halves, then the low halves (`cmp_hi_lt`,
  `cmp_hi_gt`, `cmp_hi_eq`);
* **addition and subtraction as `Nat` arithmetic**, for every pair of
  words, with the carry and borrow between the halves: the sum of the
  values, less 2^64 when it wraps, which is exactly when the result is
  below the first operand (`add_wrap`); no wrap when the sum is no more
  than a word's value (`add_value`); the difference plus the subtrahend is
  the minuend, plus 2^64 when the subtrahend is the larger (`sub_wrap`),
  and the `Nat` difference when it is not (`sub_value`);
* **the shifts as `Nat` arithmetic**, for every word and every shift
  amount, across the halves: a shift left by k < 64 multiplies the value
  by 2^k when the result is no more than a word's value (`shl_value`); a
  shift right by k < 64 is the floor of the value divided by 2^k: 2^k times
  it is at most the value, and 2^k times one more is above it
  (`shr_value_le`, `shr_value_lt`); by 64 or more, both give 0
  (`shl_big`, `shr_big`).

How the value laws are proved (`proof_value.bend`): a word is two halves
of a width n, and every lemma is stated for n a variable: the value
`lo + 2^n * hi`, the order of two halves, and the carry or borrow between
them, from bend-osdev-u32's laws for each half (`word_add_wrap`,
`word_sub_wrap`, `word_cmp_value`, `word_value_lt`). The W64 laws
instantiate them at n = 32. This is so because a closed 2^32 (or 2^64) is
a unary `Nat` in the checkers: a type that holds one cannot be compared by
computation, so `W64.to_nat` weighs the high half by 32 doublings of its
value (symbolic when the half is unknown) rather than by a product with
the number 2^32, and no law or lemma instance names a closed power of two.

The shifts (`proof_shift.bend`) rest on the value of k one-bit shifts of a
half: a shift left multiplies by 2^k less the bits it carries out, a shift
right divides by 2^k rounding down, the bits a shift left by k carries out
are the shift right by n - k (a value below 2^n has one quotient and
remainder by 2^n), and an `or` of two halves whose bits do not meet is
their sum.

**Not proved for every input**, and tested instead: the product from
16-bit partial products (`mul`), division by shift-and-subtract (by zero:
quotient 0, remainder `a`), the bit operations (`and`, `or`, `xor`, `not`)
as values, and decimal and hex text by division through 16-bit pieces.
These need multiplication and division facts that bend-osdev-u32 does not
state yet. `ref/run.sh` checks every operation against Python's exact
integers.

## Tests

`ref/run.sh` (850 cases with the default seed) compares every operation with
Python's integers on random words and on the edge values 0, 1, 2^32 - 1,
2^32, 2^63 and 2^64 - 1, with shifts of 0 to 70 bits and divisors of 0.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (32 laws), `--verdict` ALL
PROOFS CHECK, `check.bend` passes and `ref/run.sh` 850 cases match, both
as native binaries.
