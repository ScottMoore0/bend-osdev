# bend-osdev-bignum

Natural numbers of any size for public-key cryptography: conversion to and
from big-endian bytes and hex, comparison, the four operations and shifts;
modular arithmetic with Montgomery multiplication, modular inverse and gcd;
the Miller-Rabin primality test; and the Jacobi symbol. It is the integer
layer of the `rsa`, `dh`, `ecc`, `sm2` and `ecrdsa` packages.

The directory is `bignum` and the entry file `bignum/bignum.bend`; the hub
name is `bend-osdev-bignum`.

## Why not bend-kit-bignum

bend-kit-bignum@0.1.0.0 was allowed and looked at first. It is not used,
not even through an adapter, because:

* it is slow for this work: a 2048-bit modular exponentiation with a
  2048-bit exponent took 7.09 s natively against this package's 0.97 s
  (both Bend 2.0.37, WSL2, the same machine);
* its numbers are in base 10^4, so converting to and from bytes (what every
  public-key format needs) is quadratic, and reading a bit (what scalar
  multiplication and exponentiation do at every step) needs a division;
* it has no laws, no modular inverse, no Montgomery multiplication, no
  Jacobi symbol and no byte conversion.

This package is base 2^16, so bytes and bits are free, and the product of
two limbs plus two more limbs fits in a `U32`.

## Specifications

* **Octet strings and integers:** RFC 8017 (K. Moriarty, B. Kaliski, J.
  Jonsson, A. Rusch, *PKCS #1: RSA Cryptography Specifications Version
  2.2*, November 2016), section 4: I2OSP and OS2IP (`BnNat.to_octets`,
  `BnNat.of_octets`).
* **Miller-Rabin:** FIPS 186-5 (*Digital Signature Standard*, NIST,
  February 2023), Appendix B.3.1 (the test) and Appendix C.1 (the number of
  rounds a size needs, which the caller chooses through the bases it gives).
* **The Jacobi symbol:** FIPS 186-5, Appendix B.5.
* **Montgomery multiplication and the extended Euclidean algorithm** are
  written from their defining identities (a b R^-1 mod n; a x = 1 mod m),
  not from a text: P. L. Montgomery's 1985 paper, after which the method is
  named, and Knuth's description of the extended algorithm were **not
  read** for this package. The laws and the differential test below are
  what stand behind them.

## Files

| File | Holds |
|---|---|
| `bignum.bend` | the numbers (`BnNat`) and their arithmetic: bytes, hex, compare, add, subtract, multiply, shift, divide |
| `modular.bend` | arithmetic modulo m: add, sub, mul, exp (Montgomery for odd m, square and multiply otherwise), gcd, lcm, inverse |
| `mont.bend` | Montgomery contexts and arithmetic on Montgomery forms |
| `prime.bend` | the remainder by a small number, trailing zero bits, Miller-Rabin, probable primes, the next probable prime |
| `jacobi.bend` | the Jacobi symbol |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `LAWS_limbs.bend`, `PROOF_limbs.bend` | the limb laws (the value of a number, add, sub, cmp), and their proofs |
| `gen/proof_limbs.py` | writes `PROOF_limbs.bend` (ring identities by `scripts/natproof.py`) |
| `LAWS_mul.bend`, `PROOF_mul.bend` | the multiplication laws (`mul` is the product of the values), and their proofs |
| `LAWS_div.bend`, `PROOF_div.bend` | the division laws (`divmod`, `div` and `mod` are long division of the values), and their proofs |
| `gen/proof_mul.py`, `gen/proof_div.py` | write `PROOF_mul.bend` and `PROOF_div.bend` (ring identities by `scripts/natproof.py`) |
| `check.bend` | vectors with expected output |
| `gen/exhaustive.py` | writes the small-parameter exhaustive laws and their proofs (`--check` checks them) |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's integers |

Bend imports do not re-export: import the files you use.

## Public interface

| File | Defs and types |
|---|---|
| `bignum.bend` | `BnNat` (opaque); `BnDivMod` (opaque), `BnDivMod.q`, `.r`; `BnNat.zero`, `.one`, `.of_u32`, `.to_u32` (the low 32 bits), `.of_limbs`, `.to_limbs` (16-bit limbs, least significant first), `.of_octets` (OS2IP), `.to_octets(x, n)` (I2OSP: `None` when x needs more than n bytes), `.to_octets_min` (the shortest form; empty for 0), `.is_zero`, `.is_odd`, `.bit_len`, `.byte_len`, `.bit(x, i)`, `.cmp`, `.is_eq`, `.is_lt`, `.is_le`, `.add`, `.sub` (0 when b > a), `.mul`, `.shl`, `.shr`, `.divmod` (`None` for a zero divisor), `.mod` (a for m = 0), `.div`, `.hex` (lower case, no leading zeros, "0" for zero), `.of_hex` (`None` for a non-hex character) |
| `modular.bend` | `BnMod.add`, `.sub`, `.mul` (modulo m > 0), `.exp_plain` (square and multiply with division: the reference), `.exp` (Montgomery for odd m > 1), `.gcd`, `.lcm`, `.inv(a, m)` (`None` when gcd(a, m) is not 1 or m < 2) |
| `mont.bend` | `BnMont` (opaque); `BnMont.ctx(n)` (`None` unless n is odd and above 1), `.of_odd` (unchecked), `.modulus`, `.limbs`, `.to` (x R mod n), `.of` (back), `.one`, `.mul`, `.sqr`, `.add`, `.sub`, `.neg`, `.exp` (on forms), `.modexp(c, x, e)` (x^e mod n, plain in and out) |
| `prime.bend` | `BnNat.mod_u16(x, d)` (0 < d < 2^16), `BnNat.trailing_zeros`, `BnPrime.miller_rabin(n, bases)`, `BnPrime.is_probable(n, bases)` (trial division by the odd primes below 256, then Miller-Rabin), `BnPrime.next(start, bases, f)` (the first probable prime among the odd numbers from start, at most f + 1 tried) |
| `jacobi.bend` | `BnJacobi` (open: `BnJacZero`, `BnJacPlus`, `BnJacMinus`), `BnNat.jacobi(a, n)` (`None` unless n is odd and positive) |

A `BnNat` may carry zero limbs on top (a value reduced modulo n keeps n's
length): every def accepts them and compares by value (`BnNat.is_eq`).
Everything named `bn.*` is internal.

## Extension points

* **The bases of Miller-Rabin** are the caller's: random ones for keys
  (FIPS 186-5 draws them from [2, n - 2], Appendix C.1 gives how many),
  fixed ones for a deterministic test of small numbers; `rsa`'s key
  generation takes them as a parameter too.
* **The search bound** of `BnPrime.next` (f) is a parameter.
* **Montgomery contexts** are values: build one per modulus
  (`BnMont.ctx`) and reuse it; the `ecc` package keeps one per curve.
* **The reference exponentiation** (`BnMod.exp_plain`) stays public, so a
  faster method can be tied to it the way `BnMod.exp` is (a law and the
  differential test).
* The limb size is internal (`BnNat` is opaque): a wider limb could replace
  it without changing any other package.

## Laws

`LAWS.bend` has 12 laws, all proved (`PROOF.bend`) and all accepted by
`--verdict`.

* **For every input:** `octets_round_trip` (OS2IP then I2OSP to the bytes'
  own length gives the bytes back, for every byte string).
* **Small-parameter exhaustive** (`gen/exhaustive.py`; every value below the
  bound, each case by computation): `exp_mont_small` (Montgomery's
  exponentiation equals the reference square and multiply for every base
  and exponent below 7, modulo 7); `inv_small` (for every a below 12, the
  inverse modulo 12 is one, a x = 1, and exists exactly when gcd(a, 12) =
  1); `jacobi_small` (modulo the prime 11, the Jacobi symbol is Euler's
  criterion a^5 mod 11, for every a below 11).
* **Vectors** (by computation, values from Python's integers):
  `mul_vector`, `divmod_vector`, `modexp_vector`, `gcd_vector`,
  `inv_vector`, `miller_rabin_561` (the Carmichael number 561 fails base 2),
  `prime_65537`, `jacobi_vector`.

`LAWS_limbs.bend`, **for every input** (the first arithmetic laws, the
interface bignum's further laws build on): `bnlaw.value(x)` is the number
x's limbs stand for, sum x_i 2^(16 i), and `bnlaw.valid(x)` that every
limb is below 2^16 (its bits from 16 up are 0). `BnNat.of_limbs` makes a
valid number (`of_limbs_valid`); for valid a and b, `add` is the sum of the
values and valid (`add_value`, `add_valid`), `cmp` is the order of the
values (`cmp_value`), and `sub` is the difference, 0 when b > a
(`sub_value`); `sub` is always valid (`sub_valid`). One step of `bn.add`
takes t = x + y + c, below 2^32 since the three are 16-bit, and puts down
t & 65535 = low16(t) with the carry t >> 16 = high16(t), so by induction
on the limbs the values add up (bend-osdev-u32's `u32_and_65535`,
`u32_shrn_value`, `low_high`); `bn.cmp` compares the high limbs last, and
the high parts decide unless they are equal; one step of `bn.sub` takes t =
x + 2^16 - y - w, borrows 1 - high16(t) (0 or 1), and the borrow is the
one the rest needs. The `Nat` reasoning about 2^16 is done for a width that
is a variable and used at 16 (u32's README, "Stating the bounds").

### Multiplication and division

`LAWS_mul.bend`, **for every input**: for valid a and b, the value of
`BnNat.mul(a, b)` is the product of the values (`mul_value`), and the
product is valid for every a and b (`mul_valid`). A row of the schoolbook
product (`bn.mac`) adds x times the number b and a carry to an
accumulator; one step takes t = z + x y + c, at most (2^16 - 1)^2 +
2 (2^16 - 1) = 2^32 - 1, so it does not wrap, and puts down low16(t) with
the carry high16(t). By induction a row is acc + x b + c, and the rows add
up to a b.

`LAWS_div.bend`, **for every input**: `BnNat.divmod(a, b)` is `None`
exactly when the value of b is 0 (`divmod_none`), and otherwise its
quotient and remainder are `BnNat.div(a, b)` and `BnNat.mod(a, b)`
(`divmod_q`, `divmod_r`, through `BnDivMod.q` and `.r`). For valid a and
b with b above 0, a = q b + r with r < b (`divmod_value`, `mod_lt`); so,
for valid a and b, `mod` and `div` are Base's `Nat.mod` and `Nat.div` of
the values (`mod_value`, `div_value`; by 0 too, where both give a and 0).
The quotient is valid for every input (`div_valid`), the remainder for a
valid a (`mod_valid`: a remainder of a smaller a is a itself). The
division is shift and subtract: with la and lb the bit lengths, la < lb
gives a < b (2^lb <= 2 b, from `bn.wbits` on the top limb of the
normalised number), and otherwise the loop runs from d = la - lb down to
0 with s = b 2^i, keeping q b 2^(i+1) + r = a and r < b 2^(i+1); at the
start a < 2^la <= b 2^(d+1). On the way the proofs show that `bn.shl(x,
n)` is x 2^n (n = 16 (n / 16) + n mod 16, by Base's `Nat.divmod`), that
`bn.shr1` halves and `bn.shl1` doubles and adds a bit, and the bounds of
the bit length; these are lemmas in `PROOF_div.bend`, not laws.

**Not proved, and tested:** that the public shifts (`shl`, `shr`),
Montgomery multiplication and its contexts, the modular operations and
exponentiation, the inverse, gcd and lcm, the Jacobi symbol and
Miller-Rabin compute what they stand for on the numbers, for every input
(the next stages, on the laws above). The exhaustive laws cover small
values; `ref/run.sh` compares every def with Python's integers on numbers
of up to 2048 bits.

## Tests

* `check.bend`: OS2IP and I2OSP (with an I2OSP refused), the square of a
  600-bit number, a reduction modulo 2^127 - 1, x^65537 mod 2^521 - 1, the
  inverse of 3 modulo 2^127 - 1, the top bits of 7^(n-1) mod n for a
  2048-bit n, 2^4096 divided by 2^2048 + small, primality of
  2^127 - 1 and 2^521 - 1 (Mersenne primes) and of 2^128 + 1 (composite),
  two Jacobi symbols and an even modulus refused, a gcd; values from
  Python's integers.
* `ref/run.sh` (398 cases with the default seed, about 21 s): add, sub,
  mul, cmp, divmod, shifts, bit length and bits, OS2IP and I2OSP, modular
  exponentiation both ways and through a Montgomery context (with the
  contexts of 1 and of an even modulus refused), inverses and gcds, prime
  and composite numbers (primes from cryptography's RSA key generation,
  composites with small and large factors, Carmichael numbers),
  `BnPrime.next`, `mod_u16`, Jacobi symbols, hex in and out; random numbers
  of 0 to 2048 bits (and products and quotients of them) against Python's
  integers.

## Sizes and speed

Every loop is a tail call or bounded by the number's length. Native builds
(Bend 2.0.37, WSL2): a 2048-bit modular exponentiation with a 2048-bit
exponent, 0.97 s; RSA-2048 verification (e = 65537) about 24 ms and
signing with the CRT about 0.30 s (`rsa`). Division is shift and subtract
(quadratic in the bits), which only key generation and reductions of
unreduced inputs use; the exponentiations reduce by Montgomery's method.

## Notes on use

None of this is constant-time: the running time depends on the values
(exponent bits, the length of numbers, early exits in comparison). It is
no defence against timing side channels.

## Dependencies

`DEPS`: `bytes` (`Octets` for OS2IP and I2OSP, and its laws in the proof of
`octets_round_trip`), `u32` (`U32Nat.dbl` in the limb laws, and its laws in
their proofs).

## Status

Bend 2.0.37: `PROOF.bend` (12 laws), `PROOF_limbs.bend` (6),
`PROOF_mul.bend` (2) and `PROOF_div.bend` (9) ALL PROOFS CHECK, `--verdict`
ALL PROOFS CHECK on all four (`PROOF.bend` about 48 s, peak 0.50 GB;
`PROOF_limbs.bend` about 7 s, peak 0.34 GB; `PROOF_mul.bend` about 7 s,
peak 0.36 GB; `PROOF_div.bend` about 8 s, peak 0.45 GB), `check.bend`
passes, `ref/run.sh` 398 cases match, `scripts/deps.sh` passes.
