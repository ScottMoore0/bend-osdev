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

**Not proved, and tested:** that `add`, `mul`, `divmod` and the rest compute
the sum, product and quotient of the numbers their limbs stand for, for
every input. Those statements need the arithmetic of 16-bit limbs with
carries, which the checker cannot do symbolically on `U32` (it can only
evaluate closed terms), and a proof by hand over limb lists was beyond this
version. The exhaustive laws cover small values; `ref/run.sh` compares
every def with Python's integers on numbers of up to 2048 bits.

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
`octets_round_trip`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK
(about 46 s), `check.bend` passes, `ref/run.sh` 398 cases match,
`scripts/deps.sh` passes.
