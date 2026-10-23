# bend-osdev-u32

The arithmetic of Base's machine words as `Nat` arithmetic: laws that say
what `U32` (and `Word(n)` of any width) comparison, addition, subtraction,
increment and shifts compute, in terms of the words' values
(`U32.to_nat`, `Word.to_nat`). Other bend-osdev packages' proofs use these
laws instead of each proving them again.

The package has no word type of its own. Its public interface is its laws,
which are about Base's interface, and three small `Nat` functions the laws
are stated with.

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
order) proved for their own use.

## Files

| File | Holds |
|---|---|
| `u32.bend` | `U32Nat.dbl`, `U32Nat.bit`, `U32Nat.half` |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | the laws' two sides computed at run time, with the expected output |

## API

| Def | Meaning |
|---|---|
| `U32Nat.dbl(n, x)` | x * 2^n (x doubled n times); 2^n is `U32Nat.dbl(n, 1n)` |
| `U32Nat.bit(b)` | 1 for `True`, 0 for `False` |
| `U32Nat.half(x)` | x / 2, rounded down (by recursion: for proofs and small values) |

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
* More operations (multiplication, division, the bitwise operations) are
  laws to add here, in the same style.
* Streaming is not applicable.

## Tests

`check.bend` computes both sides of the wrapping laws at run time on the
edge values (2^32 - 1 + 2, 0 - 1 and the like), a shift left by 30 bits,
and the `Nat` functions. There is no independent reference beyond that:
the operations are Base's own, and their values are what the laws prove.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (34 laws), `--verdict` ALL
PROOFS CHECK, `check.bend` passes, `scripts/deps.sh u32` ok.
