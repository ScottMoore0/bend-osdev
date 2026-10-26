# GF(2^m) (gfm.bend), for every field and every input: a product is the
# product of its factors' elements (Gfm.elt), so a factor may be reduced
# first. In a pair of its own, with no table proofs, so that a proof
# elsewhere (rs) can use it without importing PROOF.bend.
import Base
import ./gfm.bend as M

law gfm_mul_elt:
  for +f: M.GfmField
  for +a: U32
  for +b: U32
  {M.Gfm.mul(f, M.Gfm.elt(f, a), b) == M.Gfm.mul(f, a, b) : U32}
