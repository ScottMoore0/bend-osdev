# bend-osdev-u32

The arithmetic of Base's machine words as `Nat` arithmetic: laws that say
what `U32` (and `Word(n)` of any width) comparison, addition, subtraction,
increment, shifts, multiplication, division and the bitwise operations
compute, in terms of the words' values (`U32.to_nat`, `Word.to_nat`), and
the `Nat` arithmetic (semiring laws, order, quotient and remainder, the low
and high bits) they are stated with. Other bend-osdev packages' proofs use these
laws instead of each proving them again.

The package has no word type of its own. Its public interface is its laws,
which are about Base's interface, and the small `Nat` functions (and one
word, the mask of the low k bits) the laws are stated with.

## Specification

There is no external specification: the operations are Base's (Bend
2.0.37's `base.bend`: `Word.adc`, `Word.cmp`, `Word.inc`, `Word.shl`,
`Word.shr`, `Word.not`, `Word.to_nat`, and the `U32` operations on them),
and the laws state the usual meaning of unsigned binary arithmetic: a word
of n bits, least significant first, has the value sum of bit_i * 2^i, and
the operations are the `Nat` ones modulo 2^n.

The proofs generalise the private lemmas that bend-osdev-algo
(`proof_u32.bend`: subtraction, addition, increment and halving when
nothing wraps) and bend-osdev-array (`PROOF.bend`: comparison as the value
order) proved for their own use; the order laws are those bend-osdev-maple,
-timerqueue and -itree proved, and the division laws those of
bend-osdev-ext2, -iodev and -blockdev.

## Files

| File | Holds |
|---|---|
| `u32.bend` | `U32Nat.dbl`, `U32Nat.bit`, `U32Nat.half`, `U32Nat.odd`, `U32Nat.low`, `U32Nat.high`, `U32Word.mask` |
| `LAWS.bend`, `PROOF.bend` | the laws of the words' values and of the `Nat` arithmetic, and their proofs |
| `LAWS_order.bend`, `PROOF_order.bend` | the order of `Nat`, `Word(n)` and `U32` (transitivity, reflexivity, antisymmetry), and its proofs |
| `LAWS_div.bend`, `PROOF_div.bend` | Base's `Nat` division by a divisor `1 + bp`, and its proofs |
| `gen/proof.py` | writes the part of `PROOF.bend` after its marker line (the proofs of the `Nat` library, multiplication, division, the bits and the shifts by k) |
| `check.bend` | the laws' two sides computed at run time, with the expected output |

## API

| Def | Meaning |
|---|---|
| `U32Nat.dbl(n, x)` | x * 2^n (x doubled n times); 2^n is `U32Nat.dbl(n, 1n)` |
| `U32Nat.bit(b)` | 1 for `True`, 0 for `False` |
| `U32Nat.half(x)` | x / 2, rounded down (by recursion: for proofs and small values) |
| `U32Nat.odd(x)` | x mod 2 |
| `U32Nat.low(k, x)` | x mod 2^k (the low k bits of x) |
| `U32Nat.high(k, x)` | x / 2^k, rounded down (the bits of x from k up) |
| `U32Word.mask(n, k)` | the word of width n whose low k bits are set (2^k - 1, for k <= n) |

## Laws

`LAWS.bend`, all proved in `PROOF.bend`, for every width n and all words:

* **Values:** `word_zero_value`; every word is below 2^n (`word_value_lt`);
  two words with the same value are the same word (`word_value_eq`,
  `u32_value_eq`); the complement of w is 2^n - 1 - w (`word_not_value`).
* **Comparison is the value order:** `word_cmp_value`, `u32_cmp_value`, and
  for `U32.is_lt`, `is_le`, `is_eq`: `u32_lt_value`, `u32_le_value`,
  `u32_eq_value`.
* **Addition:** the sum of the values, less 2^n when it wraps, and it wraps
  exactly when the result is below the first operand (`word_add_wrap`,
  `u32_add_wrap`); with the sum no more than a word's value it does not
  wrap (`word_add_value`, `u32_add_value`).
* **Subtraction:** the difference plus the subtrahend is the minuend, plus
  2^n when the subtrahend is the larger (`word_sub_wrap`, `u32_sub_wrap`);
  when it is not, the difference is the `Nat` difference (`word_sub_value`,
  `u32_sub_value`).
* **Increment and shifts:** increment is the successor, and a shift left
  by one bit the doubling, when the result is no more than a word's value
  (`word_inc_value`, `u32_inc_value`, `word_shl_value`, `u32_shl_value`); a
  shift left by k bits multiplies by 2^k under the same bound
  (`u32_shln_value`); a shift right by one bit halves, rounding down
  (`word_shr_value`, `u32_shr_value`).
* **The `Nat` functions:** `dbl_zero`, `dbl_add` (x * 2^n is additive),
  `dbl_dbl` (2^m * 2^k = 2^(m + k)), `dbl_lt`, `dbl_le` (it keeps the order),
  `half_double`, `half_double_one`.
* Witnesses that the bounds can hold and the wrapping cases happen
  (`u32_wit`), and a vector of the `Nat` functions (`dbl_vec`).
* **`Nat` arithmetic**, the library other packages' proofs use (and
  `scripts/natproof.py` writes ring identities from): the semiring laws
  (`nat_add_zero`, `nat_add_succ`, `nat_add_comm`, `nat_add_assoc`,
  `nat_add_left_comm`, `nat_add_cancel`, `nat_mul_zero`, `nat_mul_one`,
  `nat_one_mul`, `nat_mul_succ`, `nat_mul_comm`, `nat_mul_assoc`,
  `nat_mul_left_comm`, `nat_mul_add`, `nat_add_mul`, `nat_double`), and
  those of 2^n (`dbl_comm`, `dbl_mul_l`, `dbl_mul_r`, `dbl_le_exp`,
  `nat_le_dbl`); the order as witnesses: x <= y exactly when (y - x) + x =
  y (`nat_le_refl`, `nat_le_add`, `nat_lt_add`, `nat_le_witness`,
  `nat_lt_witness`, `nat_succ_add_absurd`, `nat_mul_lt`); a quotient and
  remainder are unique (`nat_div_unique`, `nat_mod_unique`); a sum below
  2^n does not wrap (`dbl_nowrap`).
* **The low and high bits:** x = low(k, x) + 2^k high(k, x) with low(k, x)
  < 2^k, and these are the only such pair (`low_high`, `low_lt`,
  `low_unique`, `high_unique`, `nat_odd_half`, `nat_odd_le`,
  `low_add_dbl`, `low_small`, `low_double`, `high_double`, `high_lt`).
* **Multiplication**, for every width and all words: the product's value
  is the low n bits of the product of the values, what wraps is 2^n times
  the rest, and with the product no more than a word's value nothing wraps
  (`word_mul_wrap`, `word_mul_low`, `word_mul_value`, `u32_mul_wrap`,
  `u32_mul_low`, `u32_mul_value`).
* **Division:** for b not 0, `U32.div` and `U32.mod` are the `Nat`
  quotient and remainder, a = q b + r with r < b (`u32_divmod`,
  `u32_mod_lt`); by 0 the quotient is 0 and the remainder a
  (`u32_div_zero`, `u32_mod_zero`); and one step of restoring division on
  n-bit registers, as Base's `U32.divmod` and bend-osdev-word64's
  `W64.div` take it (`divstep_value`, `divstep_lt`).
* **The bits:** and, or and xor commute; and + or is the sum of the
  values, and so is xor + 2 and; an or of a value with one below the low
  zero bits of the other is their sum; and with a mask of the low k bits
  is the low k bits; not is the subtraction from all ones
  (`word_and_comm`, `word_or_comm`, `word_xor_comm`, `word_and_or`,
  `word_xor_and`, `word_or_split`, `word_mask_value`, `word_and_mask`,
  `word_not_sub`, and the `u32_` ones; `u32_and_65535`: and with 65535 is
  the low 16 bits).
* **Shifts by k bits:** right, the bits from k up (`u32_shrn_value`);
  left, the low 32 bits of the value times 2^k (`u32_shln_low`).

`LAWS_order.bend`, all proved in `PROOF_order.bend`:

* **`Nat` order:** `nat_le_trans`, `nat_lt_trans`, `nat_lt_le_trans`,
  `nat_le_lt_trans`, and x <= x + w (`nat_le_add_r`).
* **`Word(n)`, every width:** `Word.cmp` is reflexive (`word_cmp_refl`),
  equal words are the only ones that compare `EQ` (`word_cmp_eq`), and `LT`
  is transitive (`word_cmp_lt_trans`).
* **`U32`:** the same for `U32.cmp` (`u32_cmp_refl`, `u32_cmp_eq`,
  `u32_cmp_lt_trans`); and for `U32.is_lt` and `U32.is_le`: `u32_le_refl`,
  `u32_lt_irrefl`, `u32_lt_le` (less is at most), the four transitivities
  (`u32_lt_trans`, `u32_le_trans`, `u32_lt_le_trans`, `u32_le_lt_trans`),
  `u32_le_antisym`, and the negations (`u32_not_lt`: not a < b gives
  b <= a; `u32_not_le`: not a <= b gives b < a; `u32_lt_not_le`,
  `u32_le_not_lt`).

`LAWS_div.bend`, all proved in `PROOF_div.bend`, for every divisor
`1n+bp`: the quotient and remainder recompose the dividend
(`nat_div_mod`), the remainder is below the divisor (`nat_mod_lt`), a
dividend g (1 + bp) + i with i below the divisor has quotient g and
remainder i (`nat_divmod_exact`), and rounding a up to a multiple of the
divisor adds (1 + bp - 1) - (a + bp) mod (1 + bp) (`nat_round_up`). These
are the facts about Base's `Nat.div` and `Nat.mod` themselves; `u32_divmod`
and `nat_div_unique` above are about `U32.div` and about any quotient.

A proof elsewhere imports the pair that holds the law it uses (`LAWS.bend`
with `PROOF.bend`, `LAWS_order.bend` with `PROOF_order.bend`, `LAWS_div.bend`
with `PROOF_div.bend`).

### Stating the bounds

A bound such as "no wrap" is stated as "no more than a word's value"
(`Nat.is_le(..., U32.to_nat(c))`), as algo does, and never as "below 2^32".
The checkers count a `Nat` in unary: a closed 2^32 in a type is expanded
whenever the checker compares that type by computation, and does not fit in
the checker's stack. So no law here mentions a closed power of two; 2^n
appears as `U32Nat.dbl(n, 1n)` with n a variable, or multiplying a value
that is not known (`U32Nat.dbl(32n, U32Nat.bit(c))` with `c` a comparison),
which stays symbolic. A proof that uses these laws at n = 32 keeps the same
discipline: bend-osdev-word64's `proof_value.bend` states its lemmas for a
width n that is a variable and instantiates them at 32 only where every
term is symbolic.

## Extension points

* The laws are about Base's words, so they hold for any code built on
  `Word(n)` and `U32`: a package with its own word type of n bits (as
  bend-osdev-word64's two halves) states its laws through these.
* More operations (rotations, signed comparison) are laws to add here, in
  the same style; ring identities between `Nat` terms are written by
  `scripts/natproof.py` (shared by the generators of word64, kmath, kstr
  and bignum) from the `Nat` laws.
* Streaming is not applicable.

## Tests

`check.bend` computes both sides of the wrapping laws at run time on the
edge values (2^32 - 1 + 2, 0 - 1 and the like), a shift left by 30 bits,
and the `Nat` functions. There is no independent reference beyond that:
the operations are Base's own, and their values are what the laws prove.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (108 laws), `PROOF_order.bend`
(23 laws) and `PROOF_div.bend` (4 laws) ALL PROOFS CHECK, `--verdict` ALL
PROOFS CHECK on each (the three together about 4 s, peak 0.28 GB),
`check.bend` passes, `scripts/deps.sh u32` ok. `PROOF.bend` is about 300 KB, of which
`gen/proof.py` writes all but the first 34 laws' proofs.
