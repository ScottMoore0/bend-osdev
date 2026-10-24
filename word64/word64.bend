# bend-osdev-word64: unsigned 64-bit words for bend-osdev, wrapping on overflow.
#
# Every bend-osdev package that needs 64 bits uses W64, and only through these
# defs. A W64 is its two 32-bit halves, each a native U32, so a W64 costs two
# machine words (a Word(64n) of bits, used before, cost sixty-four, and records
# of several of them were more than Bend's C backend can compile:
# bendlang/bend#1069). When Base gains a native U64 (bendlang/bend#1027), only
# this file changes. The type is not named U64, so that it cannot clash with
# Base's when it arrives.
import Base

type W64 is Data:
  W64{hi: U32, lo: U32}

def W64.zero() -> W64:
  W64{0, 0}

def W64.one() -> W64:
  W64{0, 1}

def W64.max() -> W64:
  W64{4294967295, 4294967295}

# Conversions

def W64.from_u32(a: U32) -> W64:
  W64{0, a}

# Splitting a Word(m + n) into its low m and high n bits (bits are stored
# least significant first), and joining them back. Named under W64, not Word,
# so that they cannot clash with Base if it gains Word.lo, Word.hi or Word.cat.
def W64.bits.lo(m: Nat, n: Nat, w: Word(Nat.add(m, n))) -> Word(m):
  match m:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{h, t}:
          WCon{h, W64.bits.lo(p, n, t)}

def W64.bits.hi(m: Nat, n: Nat, w: Word(Nat.add(m, n))) -> Word(n):
  match m:
    case 0n:
      w
    case 1n+p:
      match w:
        case WCon{h, t}:
          W64.bits.hi(p, n, t)

def W64.bits.cat(m: Nat, n: Nat, a: Word(m), b: Word(n)) -> Word(Nat.add(m, n)):
  match m:
    case 0n:
      b
    case 1n+p:
      match a:
        case WCon{h, t}:
          WCon{h, W64.bits.cat(p, n, t, b)}

# the low 32 bits
def W64.lo(a: W64) -> U32:
  match a:
    case W64{h, l}:
      l

# the high 32 bits
def W64.hi(a: W64) -> U32:
  match a:
    case W64{h, l}:
      h

# the word whose high and low 32 bits are hi and lo
def W64.from_parts(hi: U32, lo: U32) -> W64:
  W64{hi, lo}

# 2^32, built from literals Bend reads (a literal is at most 2^32 - 1)
def W64.two32() -> Nat:
  Nat.add(4294967295n, 1n)

# x * 2^n: x doubled n times
def W64.dbl(n: Nat, x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+p:
      Nat.double(W64.dbl(p, x))

# lo + hi * 2^32. The high half's weight is 32 doublings of its value, not a
# product with the closed number 2^32: the checkers count a Nat in unary, so
# a proof that unfolds to_nat on unknown halves stays symbolic this way
# (see README.md, Laws).
def W64.to_nat(a: W64) -> Nat:
  match a:
    case W64{h, l}:
      Nat.add(U32.to_nat(l), W64.dbl(32n, U32.to_nat(h)))

def W64.from_nat.pair(qr: Nat & Nat) -> W64:
  (q, r) = qr
  W64{U32.from_nat(q), U32.from_nat(r)}

# k mod 2^64
def W64.from_nat(k: Nat) -> W64:
  W64.from_nat.pair(Nat.divmod(k, W64.two32()))

# Selecting without branching on a computed value in a recursive def

def W64.bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def W64.sel(b: Bool, x: W64, y: W64) -> W64:
  match b:
    case True{}:
      x
    case False{}:
      y

# Arithmetic, modulo 2^64

def W64.add.go(+al: U32, ah: U32, bh: U32, +l: U32) -> W64:
  W64{U32.add(U32.add(ah, bh), W64.bit(U32.is_lt(l, al))), l}

def W64.add(a: W64, b: W64) -> W64:
  match a b:
    case W64{ah, +al} W64{bh, bl}:
      W64.add.go(al, ah, bh, U32.add(al, bl))

def W64.sub(a: W64, b: W64) -> W64:
  match a b:
    case W64{ah, +al} W64{bh, +bl}:
      W64{U32.sub(U32.sub(ah, bh), W64.bit(U32.is_lt(al, bl))), U32.sub(al, bl)}

# the high 32 bits of the 64-bit product of two 32-bit words, from their
# 16-bit halves (every partial product fits in 32 bits)
def W64.mulhi.go(+p00: U32, +p01: U32, +p10: U32, p11: U32) -> U32:
  +mid = U32.add(U32.add(U32.shrn(p00, 16n), U32.and(p01, 65535)), U32.and(p10, 65535))
  U32.add(U32.add(U32.add(p11, U32.shrn(p01, 16n)), U32.shrn(p10, 16n)), U32.shrn(mid, 16n))

def W64.mulhi(+a: U32, +b: U32) -> U32:
  +a0 = U32.and(a, 65535)
  +a1 = U32.shrn(a, 16n)
  +b0 = U32.and(b, 65535)
  +b1 = U32.shrn(b, 16n)
  W64.mulhi.go(U32.mul(a0, b0), U32.mul(a0, b1), U32.mul(a1, b0), U32.mul(a1, b1))

def W64.mul(a: W64, b: W64) -> W64:
  match a b:
    case W64{ah, +al} W64{bh, +bl}:
      W64{U32.add(U32.add(W64.mulhi(al, bl), U32.mul(al, bh)), U32.mul(ah, bl)), U32.mul(al, bl)}

# Bits

def W64.and(a: W64, b: W64) -> W64:
  match a b:
    case W64{ah, al} W64{bh, bl}:
      W64{U32.and(ah, bh), U32.and(al, bl)}

def W64.or(a: W64, b: W64) -> W64:
  match a b:
    case W64{ah, al} W64{bh, bl}:
      W64{U32.or(ah, bh), U32.or(al, bl)}

def W64.xor(a: W64, b: W64) -> W64:
  match a b:
    case W64{ah, al} W64{bh, bl}:
      W64{U32.xor(ah, bh), U32.xor(al, bl)}

def W64.not(a: W64) -> W64:
  match a:
    case W64{h, l}:
      W64{U32.not(h), U32.not(l)}

# shifts by k bits: 0 leaves the word, 64 or more gives 0
def W64.shl.pick(z: Bool, lt32: Bool, lt64: Bool, +k: Nat, a: W64) -> W64:
  match z lt32 lt64:
    case True{} _ _:
      a
    case False{} True{} _:
      match a:
        case W64{h, +l}:
          W64{U32.or(U32.shln(h, k), U32.shrn(l, Nat.sub(32n, k))), U32.shln(l, k)}
    case False{} False{} True{}:
      match a:
        case W64{h, l}:
          W64{U32.shln(l, Nat.sub(k, 32n)), 0}
    case False{} False{} False{}:
      W64.zero()

def W64.shl(a: W64, +k: Nat) -> W64:
  W64.shl.pick(Nat.is_eq(k, 0n), Nat.is_lt(k, 32n), Nat.is_lt(k, 64n), k, a)

def W64.shr.pick(z: Bool, lt32: Bool, lt64: Bool, +k: Nat, a: W64) -> W64:
  match z lt32 lt64:
    case True{} _ _:
      a
    case False{} True{} _:
      match a:
        case W64{+h, l}:
          W64{U32.shrn(h, k), U32.or(U32.shrn(l, k), U32.shln(h, Nat.sub(32n, k)))}
    case False{} False{} True{}:
      match a:
        case W64{h, l}:
          W64{0, U32.shrn(h, Nat.sub(k, 32n))}
    case False{} False{} False{}:
      W64.zero()

def W64.shr(a: W64, +k: Nat) -> W64:
  W64.shr.pick(Nat.is_eq(k, 0n), Nat.is_lt(k, 32n), Nat.is_lt(k, 64n), k, a)

# Comparisons

def W64.cmp.pick(c: Cmp, al: U32, bl: U32) -> Cmp:
  match c:
    case EQ{}:
      U32.cmp(al, bl)
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def W64.cmp(a: W64, b: W64) -> Cmp:
  match a b:
    case W64{ah, al} W64{bh, bl}:
      W64.cmp.pick(U32.cmp(ah, bh), al, bl)

def W64.is_eq(a: W64, b: W64) -> Bool:
  Cmp.is_eq(W64.cmp(a, b))

def W64.is_lt(a: W64, b: W64) -> Bool:
  Cmp.is_lt(W64.cmp(a, b))

def W64.is_le(a: W64, b: W64) -> Bool:
  Cmp.is_le(W64.cmp(a, b))

def W64.is_gt(a: W64, b: W64) -> Bool:
  Cmp.is_gt(W64.cmp(a, b))

def W64.is_ge(a: W64, b: W64) -> Bool:
  Cmp.is_ge(W64.cmp(a, b))

def W64.is_zero(a: W64) -> Bool:
  W64.is_eq(a, W64.zero())

# Division: shift-and-subtract over the 64 bits of a, most significant first.
# r stays below b; when doubling r overflows 64 bits (its top bit was set),
# the true value is past b, and the wrapping subtraction is still exact.

#
# The loop runs over the bits of a's two halves (as Base's U32.divmod.go
# does over a word), not over a count: on an unknown dividend it is stuck
# at once, so a proof checker never unrolls its 64 steps.

# one step: the bit x comes in below r
def W64.div.step(x: Bool, +b: W64, qr: W64 & W64) -> W64 & W64:
  (+q, +r) = qr
  +r2 = W64.or(W64.shl(r, 1n), W64.from_u32(W64.bit(x)))
  +ge = Bool.or(U32.is_eq(U32.shrn(W64.hi(r), 31n), 1), W64.is_ge(r2, b))
  (W64.or(W64.shl(q, 1n), W64.from_u32(W64.bit(ge))), W64.sel(ge, W64.sub(r2, b), r2))

# the m bits of w (least significant first) read onto qr, most significant
# first
def W64.div.bits(m: Nat, w: Word(m), +b: W64, qr: W64 & W64) -> W64 & W64:
  match m w:
    case 0n WNil{}:
      qr
    case 1n+p WCon{x, hi}:
      W64.div.step(x, b, W64.div.bits(p, hi, b, qr))

def W64.div.go(a: W64, +b: W64) -> W64 & W64:
  match a:
    case W64{U32{hw}, U32{lw}}:
      W64.div.bits(32n, lw, b, W64.div.bits(32n, hw, b, (W64.zero(), W64.zero())))

def W64.divmod.pick(z: Bool, +a: W64, +b: W64) -> W64 & W64:
  match z:
    case True{}:
      (W64.zero(), a)
    case False{}:
      W64.div.go(a, b)

# the quotient and the remainder; by zero, the quotient is 0 and the
# remainder is a (as bend-kit-int's U64, used before, answered)
def W64.divmod(+a: W64, +b: W64) -> W64 & W64:
  W64.divmod.pick(W64.is_zero(b), a, b)

def W64.fst(p: W64 & W64) -> W64:
  (x, y) = p
  x

def W64.snd(p: W64 & W64) -> W64:
  (x, y) = p
  y

def W64.div(+a: W64, +b: W64) -> W64:
  W64.fst(W64.divmod(a, b))

def W64.mod(+a: W64, +b: W64) -> W64:
  W64.snd(W64.divmod(a, b))

# Text

# a divided by a small d (1 to 65536) and the remainder, through the four
# 16-bit pieces of a, most significant first: every step fits in 32 bits
def W64.small.step(+d: U32, qr: U32 & U32, +c: U32) -> U32 & U32:
  (q, r) = qr
  +v = U32.add(U32.mul(r, 65536), c)
  (U32.or(U32.shln(q, 16n), U32.div(v, d)), U32.mod(v, d))

# a quotient and a small remainder
type W64Small is Data:
  W64Small{q: W64, r: U32}

def W64.small.join(qhi: U32, ql: U32 & U32) -> W64Small:
  (qlo, r) = ql
  W64Small{W64{qhi, qlo}, r}

def W64.small.fin(qh: U32 & U32, +d: U32, +l: U32) -> W64Small:
  (qhi, r) = qh
  W64.small.join(qhi, W64.small.step(d, W64.small.step(d, (0, r), U32.shrn(l, 16n)), U32.and(l, 65535)))

def W64.small.divmod(a: W64, +d: U32) -> W64Small:
  match a:
    case W64{+h, l}:
      W64.small.fin(W64.small.step(d, W64.small.step(d, (0, 0), U32.shrn(h, 16n)), U32.and(h, 65535)), d, l)

def W64.digit(+d: U32) -> Char:
  Chr{U32.add(48, d)}

def W64.show.push(z: Bool, acc: String, +d: U32) -> String:
  match z:
    case True{}:
      acc
    case False{}:
      SCon{W64.digit(d), acc}

def W64.small.q(p: W64Small) -> W64:
  match p:
    case W64Small{q, r}:
      q

def W64.small.r(p: W64Small) -> U32:
  match p:
    case W64Small{q, r}:
      r

# the decimal digits of a, consuming one of 20 steps per digit (after a
# reaches 0 the steps add nothing)
def W64.show.go(n: Nat, +a: W64, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      +dm = W64.small.divmod(a, 10)
      W64.show.go(p, W64.small.q(dm), W64.show.push(W64.is_zero(a), acc, W64.small.r(dm)))

def W64.show.pick(z: Bool, +a: W64) -> String:
  match z:
    case True{}:
      "0"
    case False{}:
      W64.show.go(20n, a, "")

def W64.show(+a: W64) -> String:
  W64.show.pick(W64.is_zero(a), a)

# the 16 hex digits, lower case, most significant first
def W64.hex.pick(lt: Bool, d: U32) -> Char:
  match lt:
    case True{}:
      Chr{U32.add(48, d)}
    case False{}:
      Chr{U32.add(87, d)}

def W64.hex.digit(+d: U32) -> Char:
  W64.hex.pick(U32.is_lt(d, 10), d)

def W64.hex.go(n: Nat, +a: W64, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      W64.hex.go(p, W64.shr(a, 4n), SCon{W64.hex.digit(U32.and(W64.lo(a), 15)), acc})

def W64.show_hex(a: W64) -> String:
  W64.hex.go(16n, a, "")
