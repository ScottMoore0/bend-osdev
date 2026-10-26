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
| `LAWS_mod.bend`, `PROOF_mod.bend` | the modular laws (`BnMod.add`, `sub`, `mul`, and `exp_plain` is x^e mod m), and their proofs |
| `LAWS_mont.bend`, `PROOF_mont.bend` | the Montgomery laws (REDC, the conversions, `modexp`), `BnMod.exp` is x^e mod m, and the two orders of a double exponentiation agree; and their proofs |
| `gen/proof_mod.py`, `gen/proof_mont.py` | write `PROOF_mod.bend` and `PROOF_mont.bend` (ring identities by `scripts/natproof.py`) |
| `LAWS_gcd.bend`, `PROOF_gcd.bend` | the gcd and lcm laws (`BnMod.gcd` and `BnMod.lcm` are kmath's gcd and lcm of the values), and their proofs |
| `LAWS_inv.bend`, `PROOF_inv.bend` | the modular inverse laws (`BnMod.inv` gives an inverse exactly when m > 1 and gcd(a, m) = 1), and their proofs |
| `LAWS_fermat.bend`, `PROOF_fermat.bend` | Fermat's little theorem on `Nat` (a^p = a mod p for a prime p), and its proof |
| `gen/proof_gcd.py`, `gen/proof_inv.py`, `gen/proof_fermat.py` | write `PROOF_gcd.bend`, `PROOF_inv.bend` and `PROOF_fermat.bend` (ring identities by `scripts/natproof.py`) |
| `LAWS_rsa.bend`, `PROOF_rsa.bend` | RSA on `Nat`: Fermat's theorem generalised, the Chinese remainder theorem's uniqueness, (m^e)^d = m mod p q, the CRT exponentiation (Garner's recombination), congruences modulo an lcm; Nat facts on mod and pow, and `is_odd` as the value's parity; and their proofs |
| `gen/proof_rsa.py` | writes `PROOF_rsa.bend` (ring identities by `scripts/natproof.py`) |
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

### Modular arithmetic, Montgomery multiplication and exponentiation

`LAWS_mod.bend`, **for every input** (valid a, b and m): `BnMod.add` is
(a + b) mod m and `BnMod.mul` is (a b) mod m (`mod_add_value`,
`mod_mul_value`); `BnMod.sub` is ((a mod m) + m - (b mod m)) mod m, as the
code computes it (`mod_sub_value`), which for m > 0 is a - b modulo m:
(sub(a, b) + b) mod m = a mod m (`mod_sub_add`); the three are valid
(`mod_add_valid`, `mod_sub_valid`, `mod_mul_valid`). `BnMod.exp_plain(x, e,
m)` is x^value(e) mod m (Base's `Nat.pow`) for valid x, e and m with m > 0
(`exp_plain_value`), and valid for every input (`exp_plain_valid`): before
bit p the accumulator is x^(e >> (p + 1)) mod m, `BnNat.bit(e, p)` is bit p
of the value (limb p / 16, bit p mod 16), and e >> bit_len(e) = 0.

`LAWS_mont.bend`, **for every input**, with R = 2^(16 k) for the k limbs of
an odd valid m > 1 (`BnMont.limbs`): `BnMont.ctx(m)` is the context of
`BnMont.of_odd(m)` (`ctx_of_odd`); for valid a, b below m, Montgomery
multiplication satisfies (mul(a, b) R) mod m = (a b) mod m and is below m
(`mont_mul_value`, `mont_mul_lt`; R^-1 is not named), and is valid for
every input (`mont_mul_valid`); `to(x)` is x R mod m for every valid x
(`mont_to_value`), the form of 1 is R mod m (`mont_one_value`), (of(y) R)
mod m = y mod m for a valid y below m (`mont_of_value`) and of(to(x)) = x
mod m (`mont_of_to`); `BnMont.modexp(c, x, e)` is x^e mod m
(`modexp_value`). `BnMod.exp` is x^e mod m for valid x, e and m with m > 0
(`exp_value`), so it has exp_plain's value (`exp_eq_plain`; for every odd
m > 1 by Montgomery's method, for any other m by exp_plain itself), and is
valid for every input (`exp_valid`); (x^a mod m)^b mod m = x^(a b) mod m
(`exp_exp_value`), and for an odd valid m > 1 the two orders give the same
number, exp(exp(x, a, m), b, m) = exp(exp(x, b, m), a, m) (`exp_exp_comm`:
the Montgomery result is normalised, and valid limbs without zeros on top
are determined by their value). This is dh's agreement (dh's
`LAWS_agree.bend`).

On the way (lemmas in `PROOF_mont.bend`, not laws): `bn.np(n0)` gives
n0 np + 1 = 0 mod 2^16 for every odd n0 (n0 n0 = 1 mod 8, and each Newton
step i (2 - x i) turns x i = 1 + 2^J h into x i (2 - x i) + 2^(2J) h^2 = 1
mod 2^16, the 32-bit wrap vanishing modulo 2^16: 3, 6, 12, 16 bits); one
REDC step puts t1 + m n with a zero low limb (t1_0 (1 + np n0) = 0 mod
2^16), so 2^16 t' = t + a_i b + m n, t stays below 2 n, after k steps
2^(16 k) t = a b mod n, and the conditional subtraction and the trim to k
limbs give the result below n; R is cancelled modulo the odd n (n = 1 + 2 H,
a = 2 a (1 + H) mod n); R^2 mod n is 1 doubled 32 k times, each step
reduced. Montgomery exponentiation squares and multiplies over each limb's
16 bits and the limbs most significant first. The Nat lemmas on `Nat.mod`
and `Nat.pow` are in `PROOF_mod.bend`.

### Greatest common divisor, inverse and Fermat's little theorem

`LAWS_gcd.bend`, **for every input** (valid a and b): `BnMod.gcd(a, b)`
is bend-osdev-kmath's `KMath.gcd` of the values and valid (`gcd_value`,
`gcd_valid`), so it divides a and b and every common divisor divides it
(`gcd_divides_l`, `gcd_divides_r`, `gcd_greatest`, with witnesses k gcd =
a), and gcd(a, 0) = a, gcd(0, b) = b (`gcd_zero_r`, `gcd_zero_l`; so
gcd(0, 0) = 0, as the code defines it); `BnMod.lcm(a, b)` = (a / gcd) b is
`KMath.lcm` of the values (`lcm_value`), valid for every input
(`lcm_valid`), a multiple of a and of b that divides every common multiple
(`lcm_multiple_l`, `lcm_multiple_r`, `lcm_least`), and 0 when a or b is
(`lcm_zero_r`, `lcm_zero_l`). Euclid's step (a, b) to (b, a mod b) keeps
kmath's gcd: a common divisor of a and b divides a mod b (d | x + y and
d | y give d | x), one of b and a mod b divides a = q b + r, and numbers
dividing each other are equal (kmath's `gcd_divides_l`, `gcd_divides_r`,
`gcd_greatest`). The fuel, 2 (bits(a) + bits(b)) + 4, suffices: the
measure bits(a) + bits(b) + [a < b] falls with every step, since for b <= a
the remainder r has 2 r < a < 2^bits(a), and for a < b, r = a (the bit
length bounds of `PROOF_div.bend`). The lcm laws are then kmath's.

`LAWS_inv.bend`, **for every input** (valid a and m): `BnMod.inv(a, m)` is
`Some` exactly when m > 1 and gcd(a, m) = 1 (`inv_some`, through
`bnlaw.is_some`; so `None` for m = 0 and m = 1, and for a = 0), and the t
it gives has a t mod m = 1, t < m and t valid (`inv_value`, `inv_lt`,
`inv_valid`). The extended Euclidean loop on (m, a mod m) keeps the Bezout
invariant r_i = t_i a (mod m), t_i < m: with q = r0 / r1, r = r0 mod r1 and
t = t0 - q t1 mod m (`BnMod.sub`, `BnMod.mul`), r + q t1 a = r0 = t0 a =
(t + q t1) a (mod m), and q t1 a cancels modulo m; it also keeps kmath's
gcd of (r0, r1), which is r0 when r1 = 0. Its fuel is the gcd's measure.

`LAWS_fermat.bend`, **for every input**, on `Nat`: for a prime p and every
a, a^p mod p = a mod p (`fermat`), with primality stated plainly:
`bnlaw.prime(p)` is p >= 2 and no d with 2 <= d < p divides p
(`bnlaw.nodiv`; `prime_vector` checks it on 0, 1, 2, 7 and 9). The proof is
the binomial one: Euclid's lemma (a prime dividing x y with 0 < x < p
divides y, by kmath's `gcd_mul`: gcd(y p, y x) = y gcd(p, x) = y), so p
divides C(p, k) for 0 < k < p (k C(p, k) = p C(p - 1, k - 1), Pascal's rule
by induction); the binomial theorem gives (1 + a)^p = 1 + a^p (mod p), and
induction on a gives a^p = a.

### RSA on the integers

`LAWS_rsa.bend`, **for every input**, on `Nat` (the number theory behind
`rsa`, usable by `dh` and `ecc` too), with primality as `bnlaw.prime`
above: for a prime p, a^(1 + k (p - 1)) mod p = a mod p for every a and k
(`fermat_gen`: a^(1 + (k + 1)(p - 1)) = a^(p - 1) a^(1 + k (p - 1)), which
is a^(p - 1) a = a^p = a by induction and `fermat`); for distinct primes p
and q, x = y mod p and x = y mod q give x = y mod p q (`crt_unique`: for x
<= y, (y - x) + x = x mod p gives p | y - x, likewise q, and for p < q,
Euclid's lemma takes q | k p to q | k, so p q | y - x); for distinct primes
p and q and d e = 1 modulo p - 1 and modulo q - 1, (m^e)^d mod p q = m mod p
q and (m^d)^e mod p q = m mod p q for every m (`rsa_nat`, `rsa_nat_rev`:
d e = 1 + k (p - 1), for p = 2 because d e > 0, as p and q are not both 2;
the hypothesis is the one `rsa`'s `Rsa.private_of` checks); the private
exponentiation by the Chinese remainder theorem (RFC 8017, 5.1.2 step
2.b), with m1 = c^(d mod (p - 1)) mod p, m2 = c^(d mod (q - 1)) mod q, h =
((m1 mod p + p - m2 mod p) mod p) t mod p and q t = 1 mod p, is m2 + q h =
c^d mod p q, for distinct primes p and q with p q odd and the same d e
(`crt_exp_nat`: p, q > 2, so d mod (p - 1) > 0 and m1 = c^d mod p; m2 + q h
= m2 mod q and = m1 mod p, and is below p q, so the uniqueness applies; with
p = 2, d mod 1 = 0 and m1 = 1, which is why `rsa`'s keys have an odd n); a
congruence modulo lcm(a, b) is one modulo a and modulo b (`mod_lcm_l`,
`mod_lcm_r`: x mod c = (x mod k c) mod c), so a d = e^-1 mod lcm(p - 1, q -
1) (FIPS 186-5's, `rsa`'s key generation) meets the hypotheses. With them,
the Nat facts the RSA laws of other packages are stated through, which
otherwise are lemmas: (x^a)^b = x^(a b), (x mod m)^e mod m = x^e mod m, a
mod m = a for a < m, and a mod m < m (`nat_pow_pow`, `nat_pow_mod`,
`nat_mod_small`, `nat_mod_lt`); and `BnNat.is_odd(x)` is whether value(x)
mod 2 = 1, for a valid x (`is_odd_value`: bit 0 of the low limb, the parity
of the value, u32's `nat_odd_half`).

**Not proved, and tested:** that the public shifts (`shl`, `shr`), the
Montgomery operations on forms other than `mul` (`sqr`, `add`, `sub`,
`neg`, `BnMont.exp` on its own), `BnNat.mod_u16`, `BnNat.trailing_zeros`,
the Jacobi symbol and Miller-Rabin compute what they stand for on the
numbers, for every input; and `exp_exp_comm` for an even m or m = 1, where
`exp_plain`'s result may keep zero limbs on top (the values agree there,
`exp_exp_value`). Miller-Rabin's "composite" answer being right (that a
prime passes every round) rests on Fermat's theorem, which is proved, and
still needs: a^(p - 1) = 1 for p not dividing a and x^2 = 1 giving x = 1
or p - 1 modulo a prime (Nat lemmas within reach of Euclid's lemma above);
the value laws of `BnNat.shr` and `BnNat.trailing_zeros` (so that n - 1 =
2^s d); `BnMont.sqr` and `BnMont.exp` on forms (y = x R mod n), with form
equality as equality modulo n; and the round's logic. Trial division's
rejection needs the value law of `mod_u16` (U32 Horner steps over the
reversed limbs). Euler's criterion (dh's footnote 22) needs, beyond Fermat,
that a non-residue y has y^((p - 1) / 2) = -1 (Lagrange's bound on the
roots of a polynomial modulo p, or Wilson's theorem), and the Jacobi
symbol's value for a prime n needs quadratic reciprocity, since the
algorithm's moduli after the first step are composite: both are out of
this stage's scope. The exhaustive laws cover small values; `ref/run.sh`
compares every def with Python's integers on numbers of up to 2048 bits.

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
`octets_round_trip`), `kmath` (`KMath.gcd` and `KMath.lcm` in the gcd and
inverse laws and `KMath.lcm` in `mod_lcm_l` and `mod_lcm_r`, and its gcd
and lcm laws in their proofs and in Fermat's), `u32`
(`U32Nat.dbl` in the limb laws, and its laws in their proofs). The library
code imports only `bytes`; `kmath` and `u32` are for the laws.

## Status

Bend 2.0.37: `PROOF.bend` (12 laws), `PROOF_limbs.bend` (6),
`PROOF_mul.bend` (2), `PROOF_div.bend` (9), `PROOF_mod.bend` (9),
`PROOF_mont.bend` (14), `PROOF_gcd.bend` (14), `PROOF_inv.bend` (4) and
`PROOF_fermat.bend` (2) ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK on
all nine (`PROOF.bend` about 44 s, peak 0.44 GB; `PROOF_limbs.bend` about
6 s, peak 0.34 GB; `PROOF_mul.bend` about 9 s, peak 0.36 GB;
`PROOF_div.bend` about 7 s, peak 0.42 GB; `PROOF_mod.bend` about 7 s, peak
0.50 GB; `PROOF_mont.bend` about 9 s, peak 0.56 GB; `PROOF_gcd.bend` about
20 s, peak 0.55 GB; `PROOF_inv.bend` about 22 s, peak 0.54 GB;
`PROOF_fermat.bend` about 20 s, peak 0.58 GB); Bend 2.0.39:
`PROOF_rsa.bend` (12) ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK (about
25 s, peak 0.56 GB); `check.bend` passes,
`ref/run.sh` 398 cases match, `scripts/deps.sh` passes.
