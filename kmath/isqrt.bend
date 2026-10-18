# bend-osdev-kmath, integer square roots: the largest r with r^2 <= n.
#
# Digit by digit: r is built from its top bit down, and bit b is kept when
# (r + 2^b)^2 <= n. Before bit b, n < (r + 2^(b+1))^2; after it,
# n < (r + 2^b)^2; after bit 0, n < (r + 1)^2. So the result is exact
# whenever n < 4^bits at the start (LAWS.bend proves it for every such n).
import Base
import ../word64/word64.bend as W

# 2^k
def KMath.pow2(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.double(KMath.pow2(p))

def isqrt.pick(ok: Bool, +r: Nat, +c: Nat) -> Nat:
  match ok:
    case True{}:
      c
    case False{}:
      r

def isqrt.go(+b: Nat, +n: Nat, +r: Nat) -> Nat:
  match b:
    case 0n:
      r
    case 1n+k:
      +c = Nat.add(r, KMath.pow2(k))
      isqrt.go(k, n, isqrt.pick(Nat.is_le(Nat.mul(c, c), n), r, c))

# the integer square root of n, for n < 4^bits
def KMath.isqrt_nat(bits: Nat, +n: Nat) -> Nat:
  isqrt.go(bits, n, 0n)

# the integer square root of a U32 (every U32 is below 4^16)
def KMath.isqrt(n: U32) -> U32:
  U32.from_nat(KMath.isqrt_nat(16n, U32.to_nat(n)))

# The same for W64, on W64 arithmetic (n can exceed a native Nat): bit b of
# the root is kept when (r + 2^b)^2 = r^2 + 2^(b+1) r + 4^b <= n

def isqrt64.pick(ok: Bool, +r: W.W64, +c: W.W64) -> W.W64:
  match ok:
    case True{}:
      c
    case False{}:
      r

def isqrt64.go(+b: Nat, +n: W.W64, +r: W.W64) -> W.W64:
  match b:
    case 0n:
      r
    case 1n+k:
      +c = W.W64.or(r, W.W64.shl(W.W64.one(), k))
      isqrt64.go(k, n, isqrt64.pick(W.W64.is_le(W.W64.mul(c, c), n), r, c))

# the integer square root of a W64 (below 2^32, so a U32)
def KMath.isqrt64(n: W.W64) -> U32:
  W.W64.lo(isqrt64.go(32n, n, W.W64.zero()))
