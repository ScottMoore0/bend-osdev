# bend-osdev-rs, the Chien search: the roots of a locator polynomial among
# the inverses of the code's locators, found by trying each in turn
# (Geisel, NASA TM-102162, section 4.4.1; Massey, 1969, section V, citing
# R. T. Chien, "Cyclic decoding procedures for the Bose-Chaudhuri-
# Hocquenghem codes", IEEE Trans. IT-10, October 1964, which was not read).
#
# Position p (the power of X: the last symbol of a word is position 0) has
# locator beta^p, and is in error when Lambda(beta^-p) = 0. The search walks
# z = beta^-p from p = 0, multiplying by beta^-1 each step.
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P

def rschien.keep(hit: Bool, +p: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match hit:
    case True{}:
      Con{p, acc}
    case False{}:
      acc

def rschien.go(k: Nat, +f: M.GfmField, +lam: List<&2, U32>, +binv: U32, +z: U32, +p: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+j:
      rschien.go(j, f, lam, binv, M.Gfm.mul(f, z, binv), U32.add(p, 1), rschien.keep(U32.is_eq(P.RsPoly.eval(f, lam, z), 0), p, acc))

# the positions p in 0 .. npos - 1 with lam(binv^p) = 0, in increasing order
def RsChien.roots(+f: M.GfmField, +lam: List<&2, U32>, +binv: U32, npos: U32) -> List<&2, U32>:
  rschien.go(U32.to_nat(npos), f, lam, binv, 1, 0, Nil{})
