# bend-osdev-kmath: integer helpers. This file: the greatest common divisor,
# the least common multiple and integer powers, on Nat (natively a Nat holds
# values below 2^48), with U32 forms.
#
# The other concerns are in their own files: isqrt.bend (integer square
# roots), div64.bend (64-bit division with remainder), reciprocal.bend
# (division by an invariant through a multiply and shifts), rational.bend
# (best rational approximation), cordic.bend (fixed-point sine and cosine)
# and prime.bend (primality and the next prime).
import Base

# Euclid's algorithm: gcd(a, 0) = a and gcd(a, b) = gcd(b, a mod b). The
# remainder falls at every step, so b steps are enough: fuel starts at b.
def kmath.gcd.go(fuel: Nat, +a: Nat, +b: Nat) -> Nat:
  match fuel b:
    case 0n _:
      a
    case 1n+k 0n:
      a
    case 1n+k 1n+q:
      kmath.gcd.go(k, 1n+q, Nat.mod(a, 1n+q))

# gcd(a, b), with gcd(0, 0) = 0
def KMath.gcd(+a: Nat, +b: Nat) -> Nat:
  kmath.gcd.go(b, a, b)

# lcm(a, b) = a / gcd(a, b) * b, with lcm(a, 0) = lcm(0, b) = 0
def KMath.lcm(+a: Nat, +b: Nat) -> Nat:
  Nat.mul(Nat.div(a, KMath.gcd(a, b)), b)

# a^e by squaring, over the 32 bits of e from the top: r = r^2 * a^bit. Every
# r is a^(a prefix of e), so no step exceeds the result (natively a Nat
# stops at 2^48)
def kmath.pow.pick(top: Bool, +a: Nat, s: Nat) -> Nat:
  match top:
    case True{}:
      Nat.mul(a, s)
    case False{}:
      s

def kmath.pow.go(n: Nat, +a: Nat, +e: U32, +r: Nat) -> Nat:
  match n:
    case 0n:
      r
    case 1n+k:
      kmath.pow.go(k, a, U32.shl(e), kmath.pow.pick(U32.is_eq(U32.shrn(e, 31n), 1), a, Nat.mul(r, r)))

# a^e (a^0 = 1)
def KMath.pow(+a: Nat, e: U32) -> Nat:
  kmath.pow.go(32n, a, e, 1n)

# The same on U32 (gcd and lcm of U32 values; pow modulo 2^32)

def KMath.gcd32(a: U32, b: U32) -> U32:
  U32.from_nat(KMath.gcd(U32.to_nat(a), U32.to_nat(b)))

# lcm modulo 2^32
def KMath.lcm32(+a: U32, +b: U32) -> U32:
  U32.mul(U32.div(a, KMath.gcd32(a, b)), b)

def kmath.pow32.go(n: Nat, +a: U32, +e: U32, +r: U32) -> U32:
  match n:
    case 0n:
      r
    case 1n+k:
      +m = U32.sub(0, U32.shrn(e, 31n))
      kmath.pow32.go(k, a, U32.shl(e), U32.mul(U32.mul(r, r), U32.or(U32.and(a, m), U32.and(1, U32.not(m)))))

# a^e modulo 2^32
def KMath.pow32(+a: U32, e: U32) -> U32:
  kmath.pow32.go(32n, a, e, 1)
