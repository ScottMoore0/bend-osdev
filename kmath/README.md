# bend-osdev-kmath

Integer helpers, the counterparts of pieces of the kernel's `lib/math`:
gcd, lcm and powers; integer square roots; 64-bit division with remainder;
division by an invariant through a multiply and shifts; best rational
approximation; CORDIC sine and cosine in fixed point; and small primality.

Written from the mathematics and public papers: Euclid's algorithm; the
digit-by-digit square root; Granlund and Montgomery, "Division by Invariant
Integers using Multiplication" (PLDI 1994), Figure 4.1 and Theorem 4.2;
continued fractions and semiconvergents (Khinchin, *Continued Fractions*,
section 6); Volder (1959) and Walther (1971) for CORDIC; trial division. No
GPL source was read.

## Files

| File | Holds |
|---|---|
| `kmath.bend` | `KMath.gcd`, `KMath.lcm`, `KMath.pow` on `Nat`; `KMath.gcd32`, `KMath.lcm32`, `KMath.pow32` on `U32` |
| `isqrt.bend` | `KMath.isqrt_nat`, `KMath.isqrt` (U32), `KMath.isqrt64` (W64), `KMath.pow2` |
| `div64.bend` | `KDiv64`, 64-bit division: unsigned, signed, rounded up |
| `reciprocal.bend` | `KRecip`: `KRecip.of(d)`, `KRecip.divide(a, r)`, and `KMath.fls` |
| `rational.bend` | `KRational`, `KMath.rational_best` |
| `cordic.bend`, `cordic_table.bend` | `KCordic`, `KMath.cordic`, `KMath.angle_of_degrees`; the generated constants |
| `prime.bend` | `KMath.is_prime`, `KMath.next_prime` |
| `LAWS.bend`, `PROOF.bend` | the square root, gcd and lcm laws and the vectors, and their proofs |
| `LAWS_div.bend`, `PROOF_div.bend` | 64-bit division for every input |
| `LAWS_fls.bend`, `PROOF_fls.bend` | the number of bits (`KMath.fls`) for every input |
| `LAWS_recip.bend`, `PROOF_recip.bend` | reciprocal division's exactness for every input |
| `LAWS_prime.bend`, `PROOF_prime.bend` | primality (`KMath.is_prime`) for every input |
| `gen/proof.py` | writes the five proof files (`gen/proof_gcd.py`, `gen/proof_div64.py`, `gen/proof_recip.py`, `gen/proof_krecip.py`, `gen/proof_prime.py`; ring identities by `scripts/natproof.py`) |

## API

| Def | Meaning |
|---|---|
| `KMath.gcd(a, b)`, `KMath.lcm(a, b)` | on `Nat`; gcd(0, 0) = 0, lcm(a, 0) = 0 |
| `KMath.pow(a, e)` | a^e on `Nat`, e a `U32`, by squaring from the top bit (no step exceeds the result, so it stays within a native `Nat`) |
| `KMath.gcd32`, `KMath.lcm32`, `KMath.pow32` | the same on `U32` (lcm and pow modulo 2^32) |
| `KMath.isqrt_nat(bits, n)` | the largest r with r² ≤ n, for n < 4^bits |
| `KMath.isqrt(n)`, `KMath.isqrt64(n)` | the same for a `U32`, and for a `W64` (on W64 arithmetic) |
| `KMath.div_u64_rem(n, d)`, `KMath.div_u64(n, d)` | a `W64` by a `U32`: `KDiv64{q, r}`, or the quotient |
| `KMath.div64_u64_rem`, `KMath.div64_u64`, `KMath.div64_u64_round_up` | a `W64` by a `W64` |
| `KMath.div64_s64_rem`, `KMath.div64_s64`, `KMath.div_s64_rem` | signed (two's complement): quotient toward zero, remainder with the dividend's sign; −2^63 / −1 wraps to −2^63 |
| `KRecip.of(d)`, `KRecip.divide(a, r)` | the precomputation for d ≥ 1, and a / d through it |
| `KMath.rational_best(n, d, max_num, max_den)` | the p/q closest to n/d with p ≤ max_num and q ≤ max_den (`KRational{num, den}`); on a tie the convergent |
| `KMath.cordic(angle)` | `KCordic{cos, sin}` of a binary angle (2^32 to the turn), in signed Q1.30 |
| `KMath.angle_of_degrees(d)` | the binary angle of a signed number of degrees |
| `KMath.is_prime(n)`, `KMath.next_prime(n)` | primality of a `U32`; the least prime above n (0 if none below 2^32) |

Division by zero follows word64 (quotient 0, remainder the dividend).
Natively a `Nat` holds values below 2^48, which bounds the `Nat` functions.

## Extension points

* **Word sizes:** `isqrt_nat` takes its number of bits, so other widths are
  one call; the 64-bit forms are on word64's `W64` and change with it.
* **Fixed-point formats:** CORDIC's step count and constants come from
  `gen/cordic.py`; a different step count or output format is a regenerated
  `cordic_table.bend`.
* **Faster paths:** each function is a single reference implementation; a
  faster one (a table of small primes, binary gcd, a Newton square root)
  can be added beside it and tied to it by a law or a differential test.

## Laws

`LAWS.bend`:

* **for every input:** for every n < 4^bits, r = `isqrt_nat(bits, n)` has
  r² ≤ n < (r + 1)², and so for every `U32` (every `U32` is below 4^16);
  `gcd(a, b)` divides a and b for every a and b, with witnesses
  (k · gcd(a, b) = a) (`gcd_divides_l`, `gcd_divides_r`), and every common
  divisor d of a and b (u d = a, v d = b) divides `gcd(a, b)`, so it is the
  greatest (`gcd_greatest`); `gcd(m a, m b) = m gcd(a, b)` (`gcd_mul`);
  `gcd(0, b) = b`, `gcd(a, 0) = a` (`gcd_zero_l`, `gcd_zero_r`).
  `lcm(a, b)` is a multiple of a and of b (`lcm_multiple_l`,
  `lcm_multiple_r`) and divides every common multiple m (u a = v b = m;
  `lcm_least`), with `lcm(0, b) = lcm(a, 0) = 0` (`lcm_zero_l`,
  `lcm_zero_r`), the zero cases as the code defines them (lcm(0, 0) = 0
  divides only 0, the only common multiple of 0 and 0). The proofs
  (`gen/proof.py`, `gen/proof_gcd.py`) build a small Nat library:
  addition and multiplication's identities, inequalities as witnesses,
  and the specification of Base's `Nat.divmod` (q·b + r = a with r < b),
  by induction on its loop. Euclid's invariant: a common divisor of a and
  1 + q divides a mod (1 + q) (r + (a / (1 + q)) v d = u d gives r = (u −
  (a / (1 + q)) v) d), so by induction on Euclid's fuel it divides the
  gcd. Homogeneity: (m a) mod (m b) = m (a mod b) by the uniqueness of a
  remainder (u32's `nat_mod_unique`), and the two runs of the loop step
  together. For lcm, with g = gcd(a, b) not 0 (b not 0), a / g = k1 where
  a = k1 g (`nat_div_unique`), so lcm = k1 b = k2 a; a common multiple m
  not 0 has a b dividing m a and m b, so a b divides gcd(m a, m b) = m g,
  and a b = lcm · g; cancelling g gives lcm dividing m.
* **vectors:** gcd, lcm, powers, small square roots, 64-bit division signed
  and unsigned, reciprocal division at the edges (d = 1, 3, 7, 2^31,
  2^32 − 1 with a = 0, d − 1, d, 2^32 − 1), the best approximation of π
  within 1000/1000 (355/113), CORDIC at 0 and 90 degrees, primes. The vector
  values are small, because a `Nat` is unary inside the checkers.

The further pairs, each proof file checked in a process of its own:

* **64-bit division** (`LAWS_div.bend`), for every input: for d not 0,
  `div_u64_rem` and `div64_u64_rem` give the `Nat` quotient and remainder,
  n = q d + r with r < d (`div_u64_rem_value`, `div_u64_rem_lt`,
  `div64_u64_rem_value`, `div64_u64_rem_lt`); `div_u64` and `div64_u64`
  are the quotient of the pair (`div_u64_q`, `div64_u64_q`); by 0 the
  quotient is 0 and the remainder n (`div_u64_rem_zero`,
  `div64_u64_rem_zero`); `div64_u64_round_up` gives the least multiple
  count, n <= q' d < n + d (`div64_round_up_le`, `div64_round_up_lt`).
  From word64's division laws (`LAWS_div.bend` there) and `add_value`.
* **the number of bits** (`LAWS_fls.bend`), for every `U32` x: x < 2^fls(x)
  (`fls_lt`), 2^fls(x) <= 2 x for x not 0 (`fls_le`), fls(x) <= 32
  (`fls_bound`); by induction on `krecip.bits.go`'s 32 steps.
* **primality** (`LAWS_prime.bend`), for every `U32` n with value N:
  `is_prime(n)` is True exactly when N ≥ 2 and no d with 2 ≤ d < N divides
  N, as three laws: a prime has N ≥ 2 (`prime_ge2`); for a prime there is
  no d with 2 ≤ d < N and k d = N (`prime_no_divisor`); and an N ≥ 2 that
  is not prime has such a d, with its cofactor (`composite_divisor`). The
  proofs (`gen/proof_prime.py`) follow the trial division: 2 for an even
  n, then the odd d = 3, 5, … while d ≤ n / d. "Past" (d > n / d, through
  u32's `U32.cmp` law) means N < d², and not past d² ≤ N. The loop runs on
  d = 3 + 2i with 2f + d = c for its fuel f, c = 2 · 32768 + 3 = 65539, so
  d + 2 never wraps (d + 2 ≤ c < 2^17) and the fuel runs out only at d = c
  > 2^16. A composite N = k e (2 ≤ e < N) gives k ≥ 2, so N ≥ 4; N is odd,
  so m = min(e, k) is odd, at least 3, divides N and has m² ≤ N; the loop,
  at an odd d ≤ m, stops at d = m (m divides N), or passes it by 2 (both
  odd), never stops past (d² ≤ m² ≤ N) and never runs out of fuel (c² >
  2^32 > N), so it answers False. It answers False only at a d that
  divides N with d² ≤ N, and then 3 ≤ d < N. The constant c stays the
  expression `2 · 32768 + to_nat(3)`, a parameter of the loop lemmas: an
  equation between closed Nat values of that size overflows the checkers'
  stack (an order test such as c < 2^17 does not).
* **reciprocal division is exact** (`LAWS_recip.bend`, Granlund and
  Montgomery's Theorem 4.2): `KRecip.divide(a, KRecip.of(d)) == U32.div(a,
  d)` for every a and every d not 0 (`recip_exact`). With l = fls(d - 1),
  d <= 2^l < 2d, c = 2^l - d (the wrapping `U32.sub(U32.shln(1, l), d)`),
  the precomputation's Q = floor(c 2^32 / d) and m = Q + 1 (which does not
  wrap: Q + 1 < 2^32 since c < d), and the divide step's t = floor(a m /
  2^32) <= a; the core (`km.k_core`, for 2^32 and 2^l as variables) is the
  theorem: with a = q d + r, r < d, the quotient of a + t by 2^l is q. The
  shifts compute that quotient ((t + ((a - t) >> 1)) >> (l - 1) = (a + t)
  >> l for l >= 1, and a itself for l = 0, d = 1).

Not proved for every input, and why:

* **Signed 64-bit division** (`div64_s64_rem`, `div_s64_rem`): the sign
  handling around the unsigned laws above is not stated yet; vectors and
  `ref/run.sh`.
* **The best rational approximation's optimality**, **CORDIC's error
  bound** and **`next_prime`** (that it is the least prime above n):
  vectors and `ref/run.sh`. CORDIC's bound is documented in `cordic.bend`:
  at most 64 units of 2^-30 (2^-24); an exact model of its steps gives at
  most 18.3 over 200,000 angles.
* **The `U32` forms** `gcd32`, `lcm32` (lcm modulo 2^32) and `pow32`, and
  `pow`: vectors and `ref/run.sh`.

## Tests

`ref/run.sh` (653 cases with the default seed) compares with Python:
`math.gcd`, `math.lcm`, `pow`, `math.isqrt`, exact integer division
(signed and unsigned, 32- and 64-bit divisors), floor division for
reciprocal division, `fractions.Fraction.limit_denominator` and an
exhaustive search over denominators for the best approximation, `math.cos`
and `math.sin` for CORDIC (4,007 angles, each within the bound), and trial
division for primes, on random and edge inputs.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(7 s, 0.34 GB peak; `--verdict` 15 s, 0.40 GB peak), `PROOF_div.bend` (2 s,
0.37 GB peak; `--verdict` 5 s, 0.41 GB peak), `PROOF_fls.bend` (2 s, 0.25 GB
peak; `--verdict` 1 s, 0.26 GB peak), `PROOF_prime.bend` (1 s, 0.38 GB peak;
`--verdict` 3 s, 0.40 GB peak) and `PROOF_recip.bend` (3 s, 0.46 GB peak;
`--verdict` 6 s, 0.62 GB peak) ALL PROOFS CHECK, with and without
`--verdict`.

Bend 2.0.37: `PROOF.bend` (37 laws), `PROOF_div.bend` (10), `PROOF_fls.bend`
(3), `PROOF_prime.bend` (3) and `PROOF_recip.bend` (1) ALL PROOFS CHECK;
`--verdict` ALL PROOFS CHECK on each (`PROOF.bend` about 14 s, peak 0.40
GB; `PROOF_div.bend` about 4 s, 0.41 GB; `PROOF_fls.bend` about 1 s, 0.26
GB; `PROOF_prime.bend` about 3 s, 0.36 GB; `PROOF_recip.bend` about 6 s,
0.59 GB); `check.bend` passes,
`ref/run.sh` 653 cases match, `scripts/deps.sh` passes.
