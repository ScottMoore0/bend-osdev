# bend-osdev-kmath, small primality and the next prime, by trial division:
# n is prime when n >= 2 and no d with 2 <= d and d * d <= n divides it
# (tested as d <= n / d, which cannot overflow). For U32 that is at most
# 32,768 odd divisors.
import Base

# odd divisors from d: past is "d > n / d", hit is "d divides n"
def kprime.go(fuel: Nat, past: Bool, hit: Bool, +n: U32, +d: U32) -> Bool:
  match fuel past hit:
    case _ True{} _:
      True{}
    case _ False{} True{}:
      False{}
    case 0n False{} False{}:
      True{}
    case 1n+k False{} False{}:
      +d2 = U32.add(d, 2)
      kprime.go(k, U32.is_gt(d2, U32.div(n, d2)), U32.is_eq(U32.mod(n, d2), 0), n, d2)

def kprime.odd(+n: U32) -> Bool:
  kprime.go(32768n, U32.is_gt(3, U32.div(n, 3)), U32.is_eq(U32.mod(n, 3), 0), n, 3)

def kprime.pick(small: Bool, even: Bool, +n: U32) -> Bool:
  match small even:
    case True{} _:
      Bool.or(U32.is_eq(n, 2), U32.is_eq(n, 3))
    case False{} True{}:
      False{}
    case False{} False{}:
      kprime.odd(n)

def KMath.is_prime(+n: U32) -> Bool:
  kprime.pick(U32.is_lt(n, 4), U32.is_eq(U32.and(n, 1), 0), n)

# the candidates from c: found is "c is prime", wrapped is "c passed 2^32 - 1"
def knext.go(fuel: Nat, found: Bool, wrapped: Bool, +c: U32) -> U32:
  match fuel found wrapped:
    case _ _ True{}:
      0
    case _ True{} False{}:
      c
    case 0n False{} False{}:
      0
    case 1n+k False{} False{}:
      +c2 = U32.add(c, 1)
      knext.go(k, KMath.is_prime(c2), U32.is_eq(c2, 0), c2)

# the least prime above n, or 0 when there is none below 2^32 (n >=
# 4294967291); the gaps between primes below 2^32 are under 400
def KMath.next_prime(+n: U32) -> U32:
  +c = U32.add(n, 1)
  knext.go(1000n, KMath.is_prime(c), U32.is_eq(c, 0), c)
