# bend-osdev-gf: arithmetic in the finite field GF(2^8), with the reduction
# polynomial as a parameter.
#
# GF(2^8) is GF(2)[x] modulo a polynomial of degree 8. An element is a
# byte: bit i is the coefficient of x^i. Addition is XOR; multiplication is
# the product of the polynomials, reduced modulo the field's polynomial
# (FIPS 197, section 4; any algebra text). A Gf8Field names the polynomial
# (all nine bits, so 0x11B is 283) and a generator of the multiplicative
# group, used for the exponential and logarithm.
#
# Elements are held in U32; only the low 8 bits of an argument are read, and
# every result is below 256. Inside, a byte is its eight bits (Gf8Bits), and
# the product is computed by Horner's rule over the bits of the first factor:
# acc := x * acc + bit * b, from the top bit down. Computing on bits keeps
# the code short and branch-free, and lets the laws be proved for every
# polynomial (see LAWS.bend).
import Base

type Gf8Field is Data:
  Gf8Field{poly: U32, gen: U32}

# The named fields

# AES (FIPS 197): x^8 + x^4 + x^3 + x + 1 (0x11B), generator x + 1 (3)
def Gf8.aes() -> Gf8Field:
  Gf8Field{283, 3}

# Reed-Solomon and RAID-6: x^8 + x^4 + x^3 + x^2 + 1 (0x11D), generator x (2)
def Gf8.rs() -> Gf8Field:
  Gf8Field{285, 2}

def Gf8.raid6() -> Gf8Field:
  Gf8.rs()

def Gf8.poly(f: Gf8Field) -> U32:
  match f:
    case Gf8Field{poly, gen}:
      poly

def Gf8.gen(f: Gf8Field) -> U32:
  match f:
    case Gf8Field{poly, gen}:
      gen

# A byte as its eight bits, b0 the least significant

type Gf8Bits is Data:
  Gf8Bits{b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool}

# the low 8 bits of a
def Gf8Bits.of(a: U32) -> Gf8Bits:
  match a:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      Gf8Bits{b0, b1, b2, b3, b4, b5, b6, b7}

def Gf8Bits.to(r: Gf8Bits) -> U32:
  match r:
    case Gf8Bits{b0, b1, b2, b3, b4, b5, b6, b7}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

def Gf8Bits.zero() -> Gf8Bits:
  Gf8Bits{False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}}

def Gf8Bits.xor(a: Gf8Bits, b: Gf8Bits) -> Gf8Bits:
  match a b:
    case Gf8Bits{a0, a1, a2, a3, a4, a5, a6, a7} Gf8Bits{c0, c1, c2, c3, c4, c5, c6, c7}:
      Gf8Bits{Bool.xor(a0, c0), Bool.xor(a1, c1), Bool.xor(a2, c2), Bool.xor(a3, c3), Bool.xor(a4, c4), Bool.xor(a5, c5), Bool.xor(a6, c6), Bool.xor(a7, c7)}

# a if t, else zero
def Gf8Bits.sel(t: Bool, a: Gf8Bits) -> Gf8Bits:
  match t:
    case True{}:
      a
    case False{}:
      Gf8Bits.zero()

# a times x, where p holds the low 8 bits of the polynomial: shift up one
# place, and if the coefficient of x^8 was set, add p (x^8 = p in the field)
def Gf8Bits.x(a: Gf8Bits, p: Gf8Bits) -> Gf8Bits:
  match a p:
    case Gf8Bits{a0, a1, a2, a3, a4, a5, a6, +a7} Gf8Bits{p0, p1, p2, p3, p4, p5, p6, p7}:
      Gf8Bits{Bool.and(a7, p0), Bool.xor(a0, Bool.and(a7, p1)), Bool.xor(a1, Bool.and(a7, p2)), Bool.xor(a2, Bool.and(a7, p3)), Bool.xor(a3, Bool.and(a7, p4)), Bool.xor(a4, Bool.and(a7, p5)), Bool.xor(a5, Bool.and(a7, p6)), Bool.xor(a6, Bool.and(a7, p7))}

# one step of Horner's rule: x * acc + t * b
def Gf8Bits.step(t: Bool, acc: Gf8Bits, +b: Gf8Bits, +p: Gf8Bits) -> Gf8Bits:
  Gf8Bits.xor(Gf8Bits.x(acc, p), Gf8Bits.sel(t, b))

# Horner's rule over the bits ts, most significant first
def Gf8Bits.horner(ts: List<&2, Bool>, acc: Gf8Bits, +b: Gf8Bits, +p: Gf8Bits) -> Gf8Bits:
  match ts:
    case Nil{}:
      acc
    case Con{t, rest}:
      Gf8Bits.horner(rest, Gf8Bits.step(t, acc, b, p), b, p)

# the bits of a, most significant first
def Gf8Bits.top(a: Gf8Bits) -> List<&2, Bool>:
  match a:
    case Gf8Bits{b0, b1, b2, b3, b4, b5, b6, b7}:
      [b7, b6, b5, b4, b3, b2, b1, b0]

def Gf8Bits.mul(a: Gf8Bits, +b: Gf8Bits, +p: Gf8Bits) -> Gf8Bits:
  Gf8Bits.horner(Gf8Bits.top(a), Gf8Bits.zero(), b, p)

# The field operations, on bytes held in U32

# the element a: its low 8 bits
def Gf8.elt(a: U32) -> U32:
  Gf8Bits.to(Gf8Bits.of(a))

# whether a is the zero element (its low 8 bits are all 0)
def Gf8Bits.is_zero(a: Gf8Bits) -> Bool:
  match a:
    case Gf8Bits{b0, b1, b2, b3, b4, b5, b6, b7}:
      Bool.not(Bool.or(b0, Bool.or(b1, Bool.or(b2, Bool.or(b3, Bool.or(b4, Bool.or(b5, Bool.or(b6, b7))))))))

def Gf8.is_zero(a: U32) -> Bool:
  Gf8Bits.is_zero(Gf8Bits.of(a))

def Gf8.add(a: U32, b: U32) -> U32:
  Gf8Bits.to(Gf8Bits.xor(Gf8Bits.of(a), Gf8Bits.of(b)))

# subtraction is addition in characteristic 2
def Gf8.sub(a: U32, b: U32) -> U32:
  Gf8.add(a, b)

def Gf8.mul(f: Gf8Field, a: U32, b: U32) -> U32:
  match f:
    case Gf8Field{poly, gen}:
      Gf8Bits.to(Gf8Bits.mul(Gf8Bits.of(a), Gf8Bits.of(b), Gf8Bits.of(poly)))

# a times x (FIPS 197's xtime)
def Gf8.xtime(f: Gf8Field, a: U32) -> U32:
  match f:
    case Gf8Field{poly, gen}:
      Gf8Bits.to(Gf8Bits.x(Gf8Bits.of(a), Gf8Bits.of(poly)))

# a^n, with a^0 = 1 (also for a = 0)
def Gf8.pow(+f: Gf8Field, +a: U32, n: Nat) -> U32:
  match n:
    case 0n:
      1
    case 1n+k:
      Gf8.mul(f, a, Gf8.pow(f, a, k))

# the inverse a^254 (a^255 = 1 for a nonzero); the inverse of 0 is 0, as in
# the AES S-box
def Gf8.inv(+f: Gf8Field, +a: U32) -> U32:
  Gf8.pow(f, a, 254n)

# a / b = a * b^-1 (and a / 0 = 0)
def Gf8.div(+f: Gf8Field, a: U32, +b: U32) -> U32:
  Gf8.mul(f, a, Gf8.inv(f, b))

# The exponential and logarithm to the field's generator

# gen^i
def Gf8.exp(+f: Gf8Field, i: Nat) -> U32:
  Gf8.pow(f, Gf8.gen(f), i)

# the least i with gen^i = a (searching i = 0 to 254); 0 for a = 0, or when
# gen does not generate a
def Gf8.log.go(n: Nat, hit: Bool, +f: Gf8Field, +a: U32, +cur: U32, +i: Nat) -> Nat:
  match n hit:
    case _ True{}:
      i
    case 0n False{}:
      0n
    case 1n+k False{}:
      +nxt = Gf8.mul(f, Gf8.gen(f), cur)
      Gf8.log.go(k, U32.is_eq(nxt, a), f, a, nxt, 1n+i)

def Gf8.log(+f: Gf8Field, a: U32) -> Nat:
  +e = Gf8.elt(a)
  Gf8.log.go(254n, U32.is_eq(1, e), f, e, 1, 0n)
