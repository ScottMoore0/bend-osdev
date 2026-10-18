# bend-osdev-kmath, 64-bit division with remainder, on word64's W64: the
# kernel's div_u64_rem, div64_u64 and friends, unsigned and signed (two's
# complement, quotient truncated toward zero, the remainder taking the
# dividend's sign, as in C). Division by zero follows word64: quotient 0,
# remainder the dividend.
import Base
import ../word64/word64.bend as W

# a quotient and a 32-bit remainder
type KDiv64 is Data:
  KDiv64{q: W.W64, r: U32}

def kdiv64.of(p: W.W64 & W.W64) -> KDiv64:
  (q, r) = p
  KDiv64{q, W.W64.lo(r)}

# n / d and n mod d, for a 32-bit d
def KMath.div_u64_rem(+n: W.W64, +d: U32) -> KDiv64:
  kdiv64.of(W.W64.divmod(n, W.W64.from_u32(d)))

def KMath.div_u64(+n: W.W64, +d: U32) -> W.W64:
  W.W64.div(n, W.W64.from_u32(d))

# n / d and n mod d, for a 64-bit d
def KMath.div64_u64_rem(+n: W.W64, +d: W.W64) -> W.W64 & W.W64:
  W.W64.divmod(n, d)

def KMath.div64_u64(+n: W.W64, +d: W.W64) -> W.W64:
  W.W64.div(n, d)

def kdiv64.bit(b: Bool) -> U32:
  match b:
    case True{}:
      0
    case False{}:
      1

def kdiv64.up(p: W.W64 & W.W64) -> W.W64:
  (q, +r) = p
  W.W64.add(q, W.W64.from_u32(kdiv64.bit(W.W64.is_zero(r))))

# n / d rounded up (DIV_ROUND_UP), for a 64-bit d
def KMath.div64_u64_round_up(+n: W.W64, +d: W.W64) -> W.W64:
  kdiv64.up(W.W64.divmod(n, d))

def kdiv64.fst(p: W.W64 & W.W64) -> W.W64:
  (q, r) = p
  q

# Signed: the sign bit, the magnitude, and back

def kdiv64.neg(a: W.W64) -> W.W64:
  W.W64.sub(W.W64.zero(), a)

def kdiv64.is_neg(a: W.W64) -> Bool:
  U32.is_eq(U32.shrn(W.W64.hi(a), 31n), 1)

def kdiv64.abs.pick(neg: Bool, +a: W.W64) -> W.W64:
  match neg:
    case True{}:
      kdiv64.neg(a)
    case False{}:
      a

def kdiv64.abs(+a: W.W64) -> W.W64:
  kdiv64.abs.pick(kdiv64.is_neg(a), a)

def kdiv64.sign.pick(neg: Bool, a: W.W64) -> W.W64:
  match neg:
    case True{}:
      kdiv64.neg(a)
    case False{}:
      a

def kdiv64.s.fin(+nn: Bool, +nd: Bool, p: W.W64 & W.W64) -> W.W64 & W.W64:
  (q, r) = p
  (kdiv64.sign.pick(Bool.xor(nn, nd), q), kdiv64.sign.pick(nn, r))

# signed n / d and n mod d (64 by 64)
def KMath.div64_s64_rem(+n: W.W64, +d: W.W64) -> W.W64 & W.W64:
  kdiv64.s.fin(kdiv64.is_neg(n), kdiv64.is_neg(d), W.W64.divmod(kdiv64.abs(n), kdiv64.abs(d)))

def KMath.div64_s64(+n: W.W64, +d: W.W64) -> W.W64:
  kdiv64.fst(KMath.div64_s64_rem(n, d))

# signed n / d and n mod d, for a signed 32-bit d (the remainder as a
# signed 32-bit value)
def KMath.div_s64_rem(+n: W.W64, +d: U32) -> KDiv64:
  kdiv64.of(KMath.div64_s64_rem(n, W.W64.from_parts(U32.sub(0, U32.shrn(d, 31n)), d)))
