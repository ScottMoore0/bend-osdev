# Proofs of LAWS.bend (CMAC).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../mode-core/mode-core.bend as M
import ./cmac.bend as CM
import ./LAWS.bend as Laws

# CMAC: the state after a ++ b is the state after a, then b

def cmacp.feed(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, xs: List<&2, U32>, s: CM.CmacState, ys: List<&2, U32>) -> {CM.cmac.feed(~K, ~enc, k, B.append(xs, ys), s) == CM.cmac.feed(~K, ~enc, k, ys, CM.cmac.feed(~K, ~enc, k, xs, s)) : CM.CmacState}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      cmacp.feed(~K, ~enc, k, t, CM.cmac.step(~K, ~enc, k, s, h), ys)

def Laws.cmac_streaming(K, enc, k, s, a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {CM.cmac.feed(~K, ~enc, k, _, s) == CM.cmac.feed(~K, ~enc, k, B.Octets.to_list(b), CM.cmac.feed(~K, ~enc, k, B.Octets.to_list(a), s)) : CM.CmacState}
  cmacp.feed(~K, ~enc, k, B.Octets.to_list(a), s, B.Octets.to_list(b))
