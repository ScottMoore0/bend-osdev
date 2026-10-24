# Properties, for every input:
#  * the integer square root (isqrt.bend): for every n below 4^bits,
#    r = isqrt_nat(bits, n) has r^2 <= n < (r + 1)^2, and so for every U32;
#  * the greatest common divisor (kmath.bend): gcd(a, b) divides a and b,
#    for every a and b (with witnesses: k * gcd(a, b) = a), and every common
#    divisor divides it; gcd(m a, m b) = m gcd(a, b);
#  * the least common multiple: lcm(a, b) is a multiple of a and of b, and
#    divides every common multiple; lcm(a, 0) = lcm(0, b) = 0.
#
# Vectors for the rest: 64-bit division (unsigned and signed), reciprocal
# division (Granlund and Montgomery's exactness, at the edges: d = 1, 3, 7,
# 2^31 and 2^32 - 1, with a = 0, d - 1, d and 2^32 - 1), the best rational
# approximation (355/113 for pi), CORDIC at 0 and 90 degrees, primality,
# powers and lcm values. The vectors keep Nat values small: a Nat is unary
# inside the checkers. ref/run.sh and check.bend test them on large values.
# Primality for every input is in LAWS_prime.bend.
import Base
import ../word64/word64.bend as W
import ./kmath.bend as K
import ./isqrt.bend as S
import ./div64.bend as D
import ./reciprocal.bend as R
import ./rational.bend as Q
import ./cordic.bend as C
import ./prime.bend as P

law isqrt_nat_le:
  for +bits: Nat
  for +n: Nat
  for h: {Nat.is_lt(n, Nat.mul(S.KMath.pow2(bits), S.KMath.pow2(bits))) == True{} : Bool}
  {Nat.is_le(Nat.mul(S.KMath.isqrt_nat(bits, n), S.KMath.isqrt_nat(bits, n)), n) == True{} : Bool}

law isqrt_nat_lt:
  for +bits: Nat
  for +n: Nat
  for h: {Nat.is_lt(n, Nat.mul(S.KMath.pow2(bits), S.KMath.pow2(bits))) == True{} : Bool}
  {Nat.is_lt(n, Nat.mul(Nat.add(S.KMath.isqrt_nat(bits, n), 1n), Nat.add(S.KMath.isqrt_nat(bits, n), 1n))) == True{} : Bool}

# the U32 instance: every U32 is below 4^16, so for every U32 n the root
# KMath.isqrt computes (isqrt_nat(16, n), then made a U32) is exact
law isqrt_u32_le:
  for +n: U32
  {Nat.is_le(Nat.mul(S.KMath.isqrt_nat(16n, U32.to_nat(n)), S.KMath.isqrt_nat(16n, U32.to_nat(n))), U32.to_nat(n)) == True{} : Bool}

law isqrt_u32_lt:
  for +n: U32
  {Nat.is_lt(U32.to_nat(n), Nat.mul(Nat.add(S.KMath.isqrt_nat(16n, U32.to_nat(n)), 1n), Nat.add(S.KMath.isqrt_nat(16n, U32.to_nat(n)), 1n))) == True{} : Bool}

law gcd_divides_l:
  for +a: Nat
  for +b: Nat
  exs k: Nat
  {Nat.mul(k, K.KMath.gcd(a, b)) == a : Nat}

law gcd_divides_r:
  for +a: Nat
  for +b: Nat
  exs k: Nat
  {Nat.mul(k, K.KMath.gcd(a, b)) == b : Nat}

# every common divisor d of a and b divides gcd(a, b), so it is the
# greatest (in the order of divisibility, and so of size when it is not 0)
law gcd_greatest:
  for +a: Nat
  for +b: Nat
  for +d: Nat
  for +u: Nat
  for +v: Nat
  for eu: {Nat.mul(u, d) == a : Nat}
  for ev: {Nat.mul(v, d) == b : Nat}
  exs k: Nat
  {Nat.mul(k, d) == K.KMath.gcd(a, b) : Nat}

law gcd_mul:
  for +m: Nat
  for +a: Nat
  for +b: Nat
  {K.KMath.gcd(Nat.mul(m, a), Nat.mul(m, b)) == Nat.mul(m, K.KMath.gcd(a, b)) : Nat}

law gcd_zero_l:
  for +b: Nat
  {K.KMath.gcd(0n, b) == b : Nat}

law gcd_zero_r:
  for +a: Nat
  {K.KMath.gcd(a, 0n) == a : Nat}

# lcm(a, b) is a common multiple of a and b and divides every common
# multiple, so it is the least; lcm(a, 0) = lcm(0, b) = 0
law lcm_multiple_l:
  for +a: Nat
  for +b: Nat
  exs k: Nat
  {Nat.mul(k, a) == K.KMath.lcm(a, b) : Nat}

law lcm_multiple_r:
  for +a: Nat
  for +b: Nat
  exs k: Nat
  {Nat.mul(k, b) == K.KMath.lcm(a, b) : Nat}

law lcm_least:
  for +a: Nat
  for +b: Nat
  for +m: Nat
  for +u: Nat
  for +v: Nat
  for eu: {Nat.mul(u, a) == m : Nat}
  for ev: {Nat.mul(v, b) == m : Nat}
  exs k: Nat
  {Nat.mul(k, K.KMath.lcm(a, b)) == m : Nat}

law lcm_zero_l:
  for +b: Nat
  {K.KMath.lcm(0n, b) == 0n : Nat}

law lcm_zero_r:
  for +a: Nat
  {K.KMath.lcm(a, 0n) == 0n : Nat}

# gcd, lcm, powers

law v_gcd:
  {K.KMath.gcd(1071n, 462n) == 21n : Nat}

law v_gcd_zero:
  {[K.KMath.gcd(0n, 0n), K.KMath.gcd(0n, 12n), K.KMath.gcd(12n, 0n)] == [0n, 12n, 12n] : List<&2, Nat>}

law v_lcm:
  {K.KMath.lcm(4n, 6n) == 12n : Nat}

law v_pow:
  {[K.KMath.pow(2n, 10), K.KMath.pow(3n, 5), K.KMath.pow(7n, 0)] == [1024n, 243n, 1n] : List<&2, Nat>}

law v_pow32:
  {K.KMath.pow32(3, 100) == 3476558801 : U32}

law v_isqrt_nat:
  {[S.KMath.isqrt_nat(4n, 200n), S.KMath.isqrt_nat(4n, 0n), S.KMath.isqrt_nat(4n, 255n), S.KMath.isqrt_nat(4n, 144n)] == [14n, 0n, 15n, 12n] : List<&2, Nat>}

# 64-bit division: (2^64 - 1) / 10 = 1844674407370955161 rem 5, and
# -7 / 2 = -3 rem -1 (truncated toward zero)

law v_div_u64_rem:
  {D.KMath.div_u64_rem(W.W64.max(), 10) == D.KDiv64{W.W64.from_parts(429496729, 2576980377), 5} : D.KDiv64}

law v_div64_u64_rem:
  {D.KMath.div64_u64_rem(W.W64.max(), W.W64.from_parts(1, 7)) == (W.W64.from_parts(0, 4294967289), W.W64.from_u32(48)) : W.W64 & W.W64}

law v_div_s64_rem:
  {D.KMath.div_s64_rem(W.W64.sub(W.W64.zero(), W.W64.from_u32(7)), 2) == D.KDiv64{W.W64.sub(W.W64.zero(), W.W64.from_u32(3)), 4294967295} : D.KDiv64}

law v_div_round_up:
  {D.KMath.div64_u64_round_up(W.W64.from_u32(7), W.W64.from_u32(2)) == W.W64.from_u32(4) : W.W64}

# reciprocal division at the edges

law v_recip_1:
  {[R.KRecip.divide(0, R.KRecip.of(1)), R.KRecip.divide(4294967295, R.KRecip.of(1))] == [0, 4294967295] : List<&2, U32>}

law v_recip_3:
  {[R.KRecip.divide(2, R.KRecip.of(3)), R.KRecip.divide(3, R.KRecip.of(3)), R.KRecip.divide(4294967295, R.KRecip.of(3))] == [0, 1, 1431655765] : List<&2, U32>}

law v_recip_7:
  {[R.KRecip.divide(6, R.KRecip.of(7)), R.KRecip.divide(7, R.KRecip.of(7)), R.KRecip.divide(4294967295, R.KRecip.of(7))] == [0, 1, 613566756] : List<&2, U32>}

law v_recip_pow2:
  {[R.KRecip.divide(2147483647, R.KRecip.of(2147483648)), R.KRecip.divide(2147483648, R.KRecip.of(2147483648)), R.KRecip.divide(4294967295, R.KRecip.of(2147483648))] == [0, 1, 1] : List<&2, U32>}

law v_recip_max:
  {[R.KRecip.divide(4294967294, R.KRecip.of(4294967295)), R.KRecip.divide(4294967295, R.KRecip.of(4294967295))] == [0, 1] : List<&2, U32>}

# rational approximation: pi to 355/113 within 1000/1000; 1000 within 10/10
# is 10/1; an exact fraction is itself

law v_rational_pi:
  {Q.KMath.rational_best(314159265, 100000000, 1000, 1000) == Q.KRational{355, 113} : Q.KRational}

law v_rational_bound:
  {Q.KMath.rational_best(1000, 1, 10, 10) == Q.KRational{10, 1} : Q.KRational}

law v_rational_exact:
  {Q.KMath.rational_best(1, 3, 10, 10) == Q.KRational{1, 3} : Q.KRational}

# CORDIC: cos and sin of 0 and of 90 degrees (2^30), in Q1.30

law v_cordic_0:
  {C.KMath.cordic(0) == C.KCordic{1073741828, 6} : C.KCordic}

law v_cordic_90:
  {C.KMath.cordic(1073741824) == C.KCordic{4294967293, 1073741828} : C.KCordic}

# primes

law v_is_prime:
  {[P.KMath.is_prime(0), P.KMath.is_prime(1), P.KMath.is_prime(2), P.KMath.is_prime(97), P.KMath.is_prime(91), P.KMath.is_prime(65537)] == [False{}, False{}, True{}, True{}, False{}, True{}] : List<&2, Bool>}

law v_next_prime:
  {[P.KMath.next_prime(0), P.KMath.next_prime(2), P.KMath.next_prime(13), P.KMath.next_prime(100)] == [2, 3, 17, 101] : List<&2, U32>}
