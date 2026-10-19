# The Jacobi symbol (a/n) for odd n > 0, by the law of quadratic reciprocity
# (the algorithm of FIPS 186-5, Appendix B.5, "Jacobi symbol"): reduce a
# modulo n, take out the factors 2 of a (each flips the sign when n is 3 or
# 5 modulo 8), swap a and n (flipping when both are 3 modulo 4), and repeat.
# For a prime n it is the Legendre symbol: 1 for a quadratic residue, -1
# for a non-residue, 0 for a multiple of n. It needs no exponentiation, so
# a residuosity test of a 2048-bit number costs far less than x^((n-1)/2).
import Base
import ./bignum.bend as N
import ./prime.bend as Pr

# The symbol's value (open)
type BnJacobi is Data:
  BnJacZero{}
  BnJacPlus{}
  BnJacMinus{}

def bn.jac.sign(neg: Bool) -> BnJacobi:
  match neg:
    case True{}:
      BnJacMinus{}
    case False{}:
      BnJacPlus{}

def bn.jac.end(one: Bool, neg: Bool) -> BnJacobi:
  match one:
    case True{}:
      bn.jac.sign(neg)
    case False{}:
      BnJacZero{}

def bn.low(+x: N.BnNat, +m: U32) -> U32:
  U32.and(m, N.BnNat.to_u32(x))

# a reduced modulo n (z: a is 0), the sign so far
def bn.jac.go(f: Nat, z: Bool, +a: N.BnNat, +n: N.BnNat, neg: Bool) -> BnJacobi:
  match f:
    case 0n:
      BnJacZero{}
    case 1n+p:
      match z:
        case True{}:
          bn.jac.end(N.BnNat.is_eq(n, N.BnNat.one()), neg)
        case False{}:
          +e = Pr.BnNat.trailing_zeros(a)
          +a1 = N.BnNat.shr(a, e)
          +n8 = bn.low(n, 7)
          +f1 = Bool.and(Nat.is_eq(Nat.mod(e, 2n), 1n), Bool.or(U32.is_eq(n8, 3), U32.is_eq(n8, 5)))
          +f2 = Bool.and(U32.is_eq(bn.low(n, 3), 3), U32.is_eq(bn.low(a1, 3), 3))
          +r = N.BnNat.mod(n, a1)
          bn.jac.go(p, N.BnNat.is_zero(r), r, a1, Bool.xor(neg, Bool.xor(f1, f2)))

def bn.jac.pick(ok: Bool, a: N.BnNat, +n: N.BnNat) -> Maybe<&2, BnJacobi>:
  match ok:
    case True{}:
      +r = N.BnNat.mod(a, n)
      Some{bn.jac.go(Nat.add(Nat.mul(2n, N.BnNat.bit_len(n)), 4n), N.BnNat.is_zero(r), r, n, False{})}
    case False{}:
      None{}

# (a/n), or None when n is even
def BnNat.jacobi(a: N.BnNat, +n: N.BnNat) -> Maybe<&2, BnJacobi>:
  bn.jac.pick(N.BnNat.is_odd(n), a, n)
