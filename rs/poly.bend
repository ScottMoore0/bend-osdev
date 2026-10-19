# bend-osdev-rs, polynomials over GF(2^m): the arithmetic the Reed-Solomon
# and BCH decoders need (Berlekamp-Massey, Chien search, Forney's formula).
#
# A polynomial is a List<&2, U32> of coefficients, lowest degree first:
# [c0, c1, c2] is c0 + c1 x + c2 x^2. Trailing zero coefficients are
# allowed (RsPoly.norm removes them). The field is a parameter (bend-osdev-
# gf's GfmField); coefficients are read modulo 2^m by the field's
# operations.
import Base
import ../gf/gfm.bend as M

# p + q (coefficientwise; the shorter counts as padded with zeros)
def RsPoly.add(+f: M.GfmField, p: List<&2, U32>, q: List<&2, U32>) -> List<&2, U32>:
  match p q:
    case Nil{} _:
      q
    case Con{a, s} Nil{}:
      Con{a, s}
    case Con{a, s} Con{b, t}:
      Con{M.Gfm.add(f, a, b), RsPoly.add(f, s, t)}

# c p
def RsPoly.scale(+f: M.GfmField, +c: U32, p: List<&2, U32>) -> List<&2, U32>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, s}:
      Con{M.Gfm.mul(f, c, a), RsPoly.scale(f, c, s)}

# x^k p
def RsPoly.shift(k: Nat, p: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      p
    case 1n+j:
      Con{0, RsPoly.shift(j, p)}

# p q
def RsPoly.mul(+f: M.GfmField, p: List<&2, U32>, +q: List<&2, U32>) -> List<&2, U32>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, s}:
      RsPoly.add(f, RsPoly.scale(f, a, q), Con{0, RsPoly.mul(f, s, q)})

# p mod x^n: the first n coefficients
def RsPoly.trunc(n: Nat, p: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      match p:
        case Nil{}:
          Nil{}
        case Con{a, s}:
          Con{a, RsPoly.trunc(k, s)}

# p(x), by Horner's rule from the highest coefficient
def RsPoly.eval(+f: M.GfmField, p: List<&2, U32>, +x: U32) -> U32:
  match p:
    case Nil{}:
      0
    case Con{a, s}:
      M.Gfm.add(f, a, M.Gfm.mul(f, x, RsPoly.eval(f, s, x)))

# the formal derivative: in characteristic 2 the coefficient of x^i is
# c_(i+1) when i + 1 is odd, else 0. odd says whether the head of p has an
# odd power.
def rspoly.deriv.go(p: List<&2, U32>, odd: Bool) -> List<&2, U32>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, s}:
      match odd:
        case True{}:
          Con{a, rspoly.deriv.go(s, False{})}
        case False{}:
          Con{0, rspoly.deriv.go(s, True{})}

def RsPoly.deriv(p: List<&2, U32>) -> List<&2, U32>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, s}:
      rspoly.deriv.go(s, True{})

# whether every coefficient is 0
def RsPoly.is_zero(+f: M.GfmField, p: List<&2, U32>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{a, s}:
      Bool.and(U32.is_eq(M.Gfm.elt(f, a), 0), RsPoly.is_zero(f, s))

# trailing zero coefficients removed
def rspoly.norm.one(z: Bool, +a: U32) -> List<&2, U32>:
  match z:
    case True{}:
      Nil{}
    case False{}:
      [a]

def rspoly.norm.cons(+a: U32, s: List<&2, U32>) -> List<&2, U32>:
  match s:
    case Nil{}:
      rspoly.norm.one(U32.is_eq(a, 0), a)
    case Con{b, t}:
      Con{a, Con{b, t}}

def rspoly.norm.go(p: List<&2, U32>, +f: M.GfmField) -> List<&2, U32>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, s}:
      rspoly.norm.cons(M.Gfm.elt(f, a), rspoly.norm.go(s, f))

def RsPoly.norm(+f: M.GfmField, p: List<&2, U32>) -> List<&2, U32>:
  rspoly.norm.go(p, f)

# the degree of a normalised polynomial (0 for the zero polynomial)
def RsPoly.deg(p: List<&2, U32>) -> Nat:
  match p:
    case Nil{}:
      0n
    case Con{a, s}:
      List.length(&2, U32, s)

# the product of (1 + r x) over the elements r (an erasure or error locator
# with the given locators)
def RsPoly.locator(+f: M.GfmField, rs: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      [1]
    case Con{r, t}:
      RsPoly.mul(f, [1, r], RsPoly.locator(f, t))

# the product of (x + r) over the elements r (the monic polynomial with
# these roots)
def RsPoly.from_roots(+f: M.GfmField, rs: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      [1]
    case Con{r, t}:
      RsPoly.mul(f, [r, 1], RsPoly.from_roots(f, t))
