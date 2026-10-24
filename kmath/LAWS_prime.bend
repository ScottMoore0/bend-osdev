# Primality (prime.bend), for every U32 n, on its value N = U32.to_nat(n):
# KMath.is_prime(n) is True exactly when N >= 2 and no d with 2 <= d < N
# divides N. Stated as three laws: a prime is at least 2 (prime_ge2); no d
# with 2 <= d < N and some k with k d = N exists for a prime
# (prime_no_divisor); and a value of at least 2 that is not prime has such a
# divisor, with its cofactor (composite_divisor).
import Base
import ./prime.bend as P

law prime_ge2:
  for +n: U32
  for h: {P.KMath.is_prime(n) == True{} : Bool}
  {Nat.is_le(2n, U32.to_nat(n)) == True{} : Bool}

law prime_no_divisor:
  for +n: U32
  for +d: Nat
  for +k: Nat
  for h: {P.KMath.is_prime(n) == True{} : Bool}
  for h1: {Nat.is_le(2n, d) == True{} : Bool}
  for h2: {Nat.is_lt(d, U32.to_nat(n)) == True{} : Bool}
  for e: {Nat.mul(k, d) == U32.to_nat(n) : Nat}
  Empty

law composite_divisor:
  for +n: U32
  for h: {P.KMath.is_prime(n) == False{} : Bool}
  for h2: {Nat.is_le(2n, U32.to_nat(n)) == True{} : Bool}
  exs d: Nat
  {Nat.is_le(2n, d) == True{} : Bool} & {Nat.is_lt(d, U32.to_nat(n)) == True{} : Bool} & Sigma<&1, &1, Nat, k => {Nat.mul(k, d) == U32.to_nat(n) : Nat}>
