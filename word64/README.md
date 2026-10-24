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
| `LAWS.bend`, `PROOF.bend` | the laws of the halves, the value, comparison, addition, subtraction and the shifts, and their proofs |
| `LAWS_mul.bend`, `PROOF_mul.bend` | multiplication (`mulhi_value`, `mul_wrap`, `mul_low`, `mul_value`) |
| `LAWS_div.bend`, `PROOF_div.bend` | division (`divmod_value`, `mod_lt`, `div_zero`, `mod_zero`) |
| `LAWS_bits.bend`, `PROOF_bits.bend` | the bitwise operations and the one-bit shift (`and_comm` ... `not_sub`, `shl_one_wrap`) |
| `LAWS_text.bend`, `PROOF_text.bend` | decimal text (`show_reads`) |
| `gen/proof.py` | writes the four `PROOF_<part>.bend` (ring identities by `scripts/natproof.py`) |
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
  joined), `hi_from_parts`, `lo_from_parts`, `lo_from_u32`,
  `from_parts_zero_hi` (halves 0 and a are `from_u32(a)`) and
  `from_parts_zero` (halves 0 and 0 are `zero()`); and the value
  laws below (`cmp_value`, `lt_value`, `le_value`, `add_value`, `sub_value`
  and the rest), so that a dependent reasons about `W64` arithmetic as
  `Nat` arithmetic without looking inside `W64`.

## Laws

`LAWS.bend` has:

* **vectors** for the edge cases: wrapping at 2^64, shifts across the halves, a
  multiply that overflows, and the text forms;
* **properties for every input**: `lo(from_u32(a)) == a`;
  `hi(from_parts(h, l)) == h` and `lo(from_parts(h, l)) == l` for all `h`, `l`;
  `from_parts(0, a) == from_u32(a)` and `from_parts(0, 0) == zero()`;
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

The further pairs (each proof file checked in a process of its own; a
dependent imports the pair that holds the law it uses):

* **multiplication** (`LAWS_mul.bend`), for every input: `W64.mulhi(a, b)`
  is the high 32 bits of the product of two 32-bit words, with `U32.mul`
  the whole product (`mulhi_value`); `W64.mul` is the product modulo 2^64:
  its value is the low 64 bits of the product of the values
  (`U32Nat.low`), what wraps is 2^64 times the rest, and with the product
  no more than a word's value nothing wraps (`mul_wrap`, `mul_low`,
  `mul_value`). The proof puts the 16-bit partial products of `mulhi`
  together at a width n of two halves h (a lemma for any h and n = 2h,
  used at 16 and 32), from bend-osdev-u32's `u32_mul_*` laws.
* **division** (`LAWS_div.bend`), for every input: for b not 0, `W64.div`
  and `W64.mod` are the `Nat` quotient and remainder, a = q b + r with r <
  b (`divmod_value`, `mod_lt`); by 0 the quotient is 0 and the remainder a
  (`div_zero`, `mod_zero`). `W64.div.go` reads the bits of a's two halves,
  most significant first (`W64.div.bits`, one `W64.div.step` a bit):
  reading the m bits of w onto (q, r) with r < b gives (q', r') with q' b +
  r' = (q b + r) 2^m + w and r' < b, by induction on w, each step being
  bend-osdev-u32's `divstep_value` and `divstep_lt` at n = 64.
* **the bits** (`LAWS_bits.bend`), for every input: and, or and xor commute
  (`and_comm`, `or_comm`, `xor_comm`); and + or is the sum of the values,
  and so is xor + 2 and (`and_or`, `xor_and`); with no bit in common, or
  is the sum (`or_disjoint`); not is the subtraction from 2^64 - 1
  (`not_sub`); a shift left by one bit is twice the value, less 2^64 for
  the top bit going out (`shl_one_wrap`).
* **decimal text** (`LAWS_text.bend`), for every input: the digits of
  `W64.show(a)`, read back one by one with Base's `Nat.read.go` (the reader
  without `Nat.read`'s 2^48 gate), are the value (`show_reads`). Each
  division by 10 through the four 16-bit pieces is one lemma for a width n
  of two halves h; 20 digits are enough, since 10^20 > 2^64 (10^4 >= 2^13,
  five times).

**Not proved for every input**, and tested instead: hex text
(`W64.show_hex`, a vector here), and `W64.from_nat` (a vector).
`ref/run.sh` checks every operation against Python's exact integers.

**The division loop and the kernel.** `W64.div.go` recurses on the bits
of the dividend's halves, as Base's `U32.divmod.go` does on a word, rather
than on a count of 64: on an unknown dividend it is stuck at once. BendTT
(`--verdict`) normalizes both sides of any conversion that is not
syntactically equal, and a loop over a literal count unrolls all 64 steps
on unknown words, using the shifted remainder twice per step, so its
normal form doubles at every step; the kernel ran out of memory on it.
Recursing on the bits computes the same quotient and remainder for every
input (the same steps in the same order; `check.bend`'s division vectors
and `ref/run.sh` hold it), and the kernel checks `PROOF_div.bend` in a few
seconds.

## Tests

`ref/run.sh` (850 cases with the default seed) compares every operation with
Python's integers on random words and on the edge values 0, 1, 2^32 - 1,
2^32, 2^63 and 2^64 - 1, with shifts of 0 to 70 bits and divisors of 0.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (34 laws), `PROOF_mul.bend`
(4), `PROOF_div.bend` (4), `PROOF_bits.bend` (8) and `PROOF_text.bend` (1)
ALL PROOFS CHECK, and `--verdict` ALL PROOFS CHECK on each (about 4 s
each, peak 0.36 to 0.40 GB); `check.bend` passes and `ref/run.sh` 850 cases match, both as native
binaries.
