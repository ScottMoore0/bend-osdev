# bend-osdev-kmath, division by an invariant: a / d as a multiply and two
# shifts, after a one-time precomputation for d (the kernel's
# reciprocal_value / reciprocal_divide).
#
# Granlund and Montgomery, "Division by Invariant Integers using
# Multiplication" (PLDI 1994), Figure 4.1, for 32-bit words: with
# l = ceil(log2 d) and m = floor(2^32 (2^l - d) / d) + 1 (which fits in 32
# bits), for every 32-bit a,
#   t = floor(m a / 2^32),  a / d = (t + ((a - t) >> min(l, 1))) >> max(l - 1, 0)
# exactly (their Theorem 4.2). d must be at least 1.
import Base
import ../word64/word64.bend as W

type KRecip is Data:
  KRecip{m: U32, sh1: Nat, sh2: Nat}

def krecip.bits.step(z: Bool, acc: Nat) -> Nat:
  match z:
    case True{}:
      acc
    case False{}:
      1n+acc

# the number of bits of x: 0 for 0, else floor(log2 x) + 1
def krecip.bits.go(n: Nat, +x: U32, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+k:
      krecip.bits.go(k, U32.shr(x), krecip.bits.step(U32.is_eq(x, 0), acc))

def KMath.fls(x: U32) -> Nat:
  krecip.bits.go(32n, x, 0n)

# (2^l - d) * 2^32; 2^l - d wraps to 2^32 - d when l = 32, as it should
def krecip.of(+d: U32, +l: Nat) -> KRecip:
  +num = W.W64.from_parts(U32.sub(U32.shln(1, l), d), 0)
  KRecip{U32.add(W.W64.lo(W.W64.div(num, W.W64.from_u32(d))), 1), Nat.min(l, 1n), Nat.sub(l, 1n)}

# the precomputation for d (d >= 1)
def KRecip.of(+d: U32) -> KRecip:
  krecip.of(d, KMath.fls(U32.sub(d, 1)))

def krecip.divide(+a: U32, m: U32, sh1: Nat, sh2: Nat) -> U32:
  +t = W.W64.hi(W.W64.mul(W.W64.from_u32(a), W.W64.from_u32(m)))
  U32.shrn(U32.add(t, U32.shrn(U32.sub(a, t), sh1)), sh2)

# a / d, for the precomputation r of d
def KRecip.divide(a: U32, r: KRecip) -> U32:
  match r:
    case KRecip{m, sh1, sh2}:
      krecip.divide(a, m, sh1, sh2)
