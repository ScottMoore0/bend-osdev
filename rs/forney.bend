# bend-osdev-rs, Forney's formula for the error values.
#
# From Massey (1969), section V, equations 24 to 29: with the error
# locators X_i, error values Y_i and syndromes S_m0, S_(m0+1), ...,
#   S(D) = sum_j S_(m0+j) D^j = P(D) / C(D),
#   C(D) = prod_i (1 - X_i D),
#   P(D) = sum_i Y_i X_i^m0 prod_(k != i) (1 - X_k D),
# so P(D) = S(D) C(D) mod D^(2t), and since C'(X_i^-1) = -X_i prod_(k != i)
# (1 - X_k X_i^-1),
#   Y_i = -X_i^(1 - m0) P(X_i^-1) / C'(X_i^-1)
# (the formula of G. D. Forney, "On decoding BCH codes", IEEE Trans. IT-11,
# October 1965, which was not read; the derivation above is Massey's
# equations). In GF(2^m) the sign is irrelevant. P is often called the
# error evaluator Omega; m0 is the first consecutive root FCR. With
# erasures, C is the product of the error and erasure locators.
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./arith.bend as A

# X^(1 - fcr), from X = beta^p and its inverse
def rsforney.xpow(zero: Bool, +f: M.GfmField, +x: U32, +xinv: U32, +fcr: U32) -> U32:
  match zero:
    case True{}:
      x
    case False{}:
      A.RsGf.pow_nat(f, xinv, U32.to_nat(U32.sub(fcr, 1)))

def rsforney.fin(z: Bool, +f: M.GfmField, +num: U32, +den: U32) -> Maybe<&2, U32>:
  match z:
    case True{}:
      None{}
    case False{}:
      Some{A.RsGf.div(f, num, den)}

# the error value at position p (locator X = beta^p), with Omega and the
# derivative of the full locator; None if the derivative vanishes there
def RsForney.value(+f: M.GfmField, +omega: List<&2, U32>, +dpsi: List<&2, U32>, +fcr: U32, +beta: U32, +binv: U32, +p: U32) -> Maybe<&2, U32>:
  +xinv = A.RsGf.pow_nat(f, binv, U32.to_nat(p))
  +den = P.RsPoly.eval(f, dpsi, xinv)
  +num = M.Gfm.mul(f, rsforney.xpow(U32.is_eq(fcr, 0), f, A.RsGf.pow_nat(f, beta, U32.to_nat(p)), xinv, fcr), P.RsPoly.eval(f, omega, xinv))
  rsforney.fin(U32.is_eq(den, 0), f, num, den)
