# bend-osdev-gf, GF(2^m) for small m (2 to 16): the fields BCH codes work
# in (Lin and Costello, "Error Control Coding", chapters 2 and 6).
#
# An element is a number below 2^m held in U32 (bit i the coefficient of
# x^i; arguments are read modulo 2^m). A GfmField names m and the reduction
# polynomial with all its bits (x^m included). The named fields use
# primitive polynomials, so x (2) generates the multiplicative group and
# Gfm.exp / Gfm.log are to base x.
import Base

type GfmField is Data:
  GfmField{m: Nat, poly: U32}

# x^4 + x + 1
def Gfm.gf16() -> GfmField:
  GfmField{4n, 19}

# x^5 + x^2 + 1
def Gfm.gf32() -> GfmField:
  GfmField{5n, 37}

# x^13 + x^4 + x^3 + x + 1 (0x201B), for BCH over 8191-bit codewords
def Gfm.bch13() -> GfmField:
  GfmField{13n, 8219}

# x^14 + x^10 + x^6 + x + 1 (0x4443)
def Gfm.bch14() -> GfmField:
  GfmField{14n, 17475}

def Gfm.m(f: GfmField) -> Nat:
  match f:
    case GfmField{m, poly}:
      m

# 2^m - 1, and the number of nonzero elements
def Gfm.mask(f: GfmField) -> U32:
  match f:
    case GfmField{m, poly}:
      U32.sub(U32.shln(1, m), 1)

def Gfm.elt(f: GfmField, a: U32) -> U32:
  U32.and(Gfm.mask(f), a)

def Gfm.add(+f: GfmField, a: U32, b: U32) -> U32:
  Gfm.elt(f, U32.xor(a, b))

# all ones if the low bit of b is set, else 0
def gfm.mask(b: U32) -> U32:
  U32.sub(0, U32.and(b, 1))

# a * x for a below 2^m: shift, and reduce if x^m appeared
def gfm.x(+m: Nat, +poly: U32, a: U32) -> U32:
  +s = U32.shl(a)
  U32.xor(s, U32.and(poly, gfm.mask(U32.shrn(s, m))))

def Gfm.xtime(+f: GfmField, a: U32) -> U32:
  match f:
    case GfmField{+m, +poly}:
      gfm.x(m, poly, Gfm.elt(GfmField{m, poly}, a))

# the product, over the m bits of b from the bottom: p += a * bit; a *= x
def gfm.mul.go(n: Nat, +m: Nat, +poly: U32, +a: U32, +b: U32, p: U32) -> U32:
  match n:
    case 0n:
      p
    case 1n+k:
      gfm.mul.go(k, m, poly, gfm.x(m, poly, a), U32.shr(b), U32.xor(p, U32.and(a, gfm.mask(b))))

# the product of a and b, both below 2^m (matching both first, so that the
# product of unknown values stays a small term for the proof checkers)
def gfm.mul.raw(f: GfmField, a: U32, b: U32) -> U32:
  match f a b:
    case GfmField{+m, +poly} U32{wa} U32{wb}:
      gfm.mul.go(m, m, poly, U32{wa}, U32{wb}, 0)

def Gfm.mul(+f: GfmField, a: U32, b: U32) -> U32:
  gfm.mul.raw(f, Gfm.elt(f, a), Gfm.elt(f, b))

# a^e by squaring, over the 32 bits of e from the top
def gfm.pow.go(n: Nat, +f: GfmField, +a: U32, +e: U32, +r: U32) -> U32:
  match n:
    case 0n:
      r
    case 1n+k:
      +sq = Gfm.mul(f, r, r)
      gfm.pow.go(k, f, a, U32.shl(e), Gfm.mul(f, sq, U32.or(U32.and(a, gfm.mask(U32.shrn(e, 31n))), U32.and(1, U32.not(gfm.mask(U32.shrn(e, 31n)))))))

def gfm.pow.start(+f: GfmField, x: U32, e: U32) -> U32:
  match x:
    case U32{w}:
      gfm.pow.go(32n, f, U32{w}, e, 1)

# a^e (a^0 = 1)
def Gfm.pow(+f: GfmField, +a: U32, e: U32) -> U32:
  gfm.pow.start(f, Gfm.elt(f, a), e)

# a^-1 = a^(2^m - 2); the inverse of 0 is 0
def Gfm.inv(+f: GfmField, +a: U32) -> U32:
  Gfm.pow(f, a, U32.sub(Gfm.mask(f), 1))

def Gfm.div(+f: GfmField, a: U32, +b: U32) -> U32:
  Gfm.mul(f, a, Gfm.inv(f, b))

# x^i
def Gfm.exp(+f: GfmField, i: U32) -> U32:
  Gfm.pow(f, 2, i)

# the least i with x^i = a, searching i below 2^m - 1 (0 for a = 0)
def Gfm.log.go(n: Nat, hit: Bool, +f: GfmField, +a: U32, +cur: U32, +i: U32) -> U32:
  match n hit:
    case _ True{}:
      i
    case 0n False{}:
      0
    case 1n+k False{}:
      +nxt = Gfm.xtime(f, cur)
      Gfm.log.go(k, U32.is_eq(nxt, a), f, a, nxt, U32.add(i, 1))

def Gfm.log(+f: GfmField, a: U32) -> U32:
  +e = Gfm.elt(f, a)
  Gfm.log.go(U32.to_nat(Gfm.mask(f)), U32.is_eq(1, e), f, e, 1, 0)
