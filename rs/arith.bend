# bend-osdev-rs, the powers and inverses the decoders use, computed with
# bend-osdev-gf's multiplication (Gfm.mul) in as few products as the
# exponents need:
#   * a^k by k multiplications (exponents here are small: positions, the
#     first root, the root spacing);
#   * a^-1 = a^(2^m - 2) = a^2 a^4 ... a^(2^(m-1)), by m - 1 squarings and
#     m - 2 further products (every nonzero element has a^(2^m - 1) = 1;
#     the inverse of 0 is 0, as in gf).
# The inverse is proved to be one on GF(8) and GF(16) (laws inv_gf8 and
# inv_gf16) and checked against gf's Gfm.inv in GF(2^13) (v_inv_bch13).
import Base
import ../gf/gfm.bend as M

# a^k
def RsGf.pow_nat(+f: M.GfmField, +a: U32, k: Nat) -> U32:
  match k:
    case 0n:
      1
    case 1n+j:
      M.Gfm.mul(f, a, RsGf.pow_nat(f, a, j))

# s holds a^(2^i); acc the product of the squares taken so far
def rsgf.inv.go(k: Nat, +f: M.GfmField, +s: U32, acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+j:
      +s2 = M.Gfm.mul(f, s, s)
      rsgf.inv.go(j, f, s2, M.Gfm.mul(f, acc, s2))

# a^-1 (0 for 0)
def RsGf.inv(+f: M.GfmField, +a: U32) -> U32:
  rsgf.inv.go(Nat.sub(M.Gfm.m(f), 1n), f, M.Gfm.elt(f, a), 1)

# a / b
def RsGf.div(+f: M.GfmField, a: U32, +b: U32) -> U32:
  M.Gfm.mul(f, a, RsGf.inv(f, b))
