# bend-osdev-u32: the arithmetic of Base's words as Nat arithmetic.
#
# This package has no word type of its own: its laws (LAWS.bend) are about
# Base's Word(n) and U32 operations, stated through their values
# (Word.to_nat, U32.to_nat): comparison is the order of the values, and
# addition, subtraction, increment and the shifts are the Nat operations on
# the values when nothing wraps, and the wrapping ones otherwise. Other
# packages' proofs use these laws instead of each proving them again.
#
# The defs below are the Nat functions the laws are stated with. None of
# them names a power of two as a closed number: 2^n is U32Nat.dbl(n, 1n),
# and 2^32 itself is never written out (see README.md, "Stating the
# bounds").
import Base

# x times 2^n: x doubled n times
def U32Nat.dbl(n: Nat, x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+p:
      Nat.double(U32Nat.dbl(p, x))

# 1 for True, 0 for False
def U32Nat.bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# n / 2, rounded down
def U32Nat.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+U32Nat.half(q)

# x mod 2: 1 for an odd x, 0 for an even one
def U32Nat.odd(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          1n
        case 1n+q:
          U32Nat.odd(q)

# the low k bits of x (x mod 2^k), and the rest (x / 2^k, rounded down):
# x = low(k, x) + 2^k high(k, x)
def U32Nat.low(k: Nat, +x: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+j:
      Nat.add(U32Nat.odd(x), Nat.double(U32Nat.low(j, U32Nat.half(x))))

def U32Nat.high(k: Nat, x: Nat) -> Nat:
  match k:
    case 0n:
      x
    case 1n+j:
      U32Nat.high(j, U32Nat.half(x))

# the word of width n whose low k bits are set (2^k - 1, for k <= n): the
# mask that U32.and(x, m) takes x's low k bits with
def U32Word.mask(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          Word.zero(1n+p)
        case 1n+j:
          WCon{True{}, U32Word.mask(p, j)}
