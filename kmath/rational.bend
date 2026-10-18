# bend-osdev-kmath, best rational approximation: the fraction p/q closest to
# n/d with p <= max_num and q <= max_den (the kernel's
# rational_best_approximation).
#
# By continued fractions (any number theory text; Khinchin, "Continued
# Fractions", section 6): the convergents h_j/k_j of n/d are followed while
# they stay within the bounds. The best approximation is then the last
# convergent h1/k1 or the semiconvergent (t h1 + h0)/(t k1 + k0) with the
# largest t the bounds allow, whichever is closer to n/d, the convergent on a
# tie. With x and y the Euclidean remainders at that point, the errors are
# y / (d k1) and (x - t y) / (d (t k1 + k0)) (since n k_j - d h_j is a
# remainder up to sign), so the comparison is exact in 64-bit arithmetic.
#
# max_num and max_den should be at least 1; for d = 0 the answer is 1/0.
import Base
import ../word64/word64.bend as W

type KRational is Data:
  KRational{num: U32, den: U32}

# the state between steps, or the answer
type KRatStep is Data:
  KRatGo{x: U32, y: U32, h0: U32, k0: U32, h1: U32, k1: U32}
  KRatDone{num: U32, den: U32}

def krat.mul(a: U32, b: U32) -> W.W64:
  W.W64.mul(W.W64.from_u32(a), W.W64.from_u32(b))

# (max - c0) / c1, or "no limit" (2^32 - 1) when c1 = 0
def krat.room.pick(z: Bool, +max: U32, +c0: U32, +c1: U32) -> U32:
  match z:
    case True{}:
      4294967295
    case False{}:
      U32.div(U32.sub(max, c0), c1)

def krat.room(+max: U32, +c0: U32, +c1: U32) -> U32:
  krat.room.pick(U32.is_eq(c1, 0), max, c0, c1)

def krat.semi.pick(better: Bool, +t: U32, +h0: U32, +k0: U32, +h1: U32, +k1: U32) -> KRatStep:
  match better:
    case True{}:
      KRatDone{U32.add(U32.mul(t, h1), h0), U32.add(U32.mul(t, k1), k0)}
    case False{}:
      KRatDone{h1, k1}

# the bounds are crossed: the semiconvergent with the largest t, if it is
# strictly closer than h1/k1
def krat.semi(+x: U32, +y: U32, +h0: U32, +k0: U32, +h1: U32, +k1: U32, +t: U32) -> KRatStep:
  +better = Bool.and(Bool.not(U32.is_eq(t, 0)), W.W64.is_lt(krat.mul(U32.sub(x, U32.mul(t, y)), k1), krat.mul(y, U32.add(U32.mul(t, k1), k0))))
  krat.semi.pick(better, t, h0, k0, h1, k1)

def krat.fits.pick(fits: Bool, +x: U32, +y: U32, +a: U32, +h0: U32, +k0: U32, +h1: U32, +k1: U32, +maxn: U32, +maxd: U32) -> KRatStep:
  match fits:
    case True{}:
      KRatGo{y, U32.sub(x, U32.mul(a, y)), h1, k1, U32.add(U32.mul(a, h1), h0), U32.add(U32.mul(a, k1), k0)}
    case False{}:
      krat.semi(x, y, h0, k0, h1, k1, U32.min(krat.room(maxn, h0, h1), krat.room(maxd, k0, k1)))

# one step: the next convergent, if it fits
def krat.next.pick(z: Bool, +x: U32, +y: U32, +h0: U32, +k0: U32, +h1: U32, +k1: U32, +maxn: U32, +maxd: U32) -> KRatStep:
  match z:
    case True{}:
      KRatDone{h1, k1}
    case False{}:
      +a = U32.div(x, y)
      +h2 = W.W64.add(krat.mul(a, h1), W.W64.from_u32(h0))
      +k2 = W.W64.add(krat.mul(a, k1), W.W64.from_u32(k0))
      krat.fits.pick(Bool.and(W.W64.is_le(h2, W.W64.from_u32(maxn)), W.W64.is_le(k2, W.W64.from_u32(maxd))), x, y, a, h0, k0, h1, k1, maxn, maxd)

def krat.go(fuel: Nat, s: KRatStep, +maxn: U32, +maxd: U32) -> KRational:
  match fuel:
    case 0n:
      match s:
        case KRatGo{x, y, h0, k0, h1, k1}:
          KRational{h1, k1}
        case KRatDone{p, q}:
          KRational{p, q}
    case 1n+f:
      match s:
        case KRatGo{+x, +y, +h0, +k0, +h1, +k1}:
          krat.go(f, krat.next.pick(U32.is_eq(y, 0), x, y, h0, k0, h1, k1, maxn, maxd), maxn, maxd)
        case KRatDone{p, q}:
          KRational{p, q}

# the best approximation p/q of n/d with p <= max_num and q <= max_den
def KMath.rational_best(n: U32, d: U32, +max_num: U32, +max_den: U32) -> KRational:
  krat.go(64n, KRatGo{n, d, 0, 1, 1, 0}, max_num, max_den)
