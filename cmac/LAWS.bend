# Laws about CMAC (cmac.bend), for every cipher given as the template
# arguments ~K, ~enc.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./cmac.bend as CM

# CMAC in pieces: the state after a ++ b is the state after a, then b, for
# every cipher, key and state (so start, update .. update, finish is the MAC
# of the pieces joined)
law cmac_streaming:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for s: CM.CmacState
  for +a: B.Octets
  for +b: B.Octets
  {CM.Cmac.update(~K, ~enc, k, s, B.Octets.append(a, b)) == CM.Cmac.update(~K, ~enc, k, CM.Cmac.update(~K, ~enc, k, s, a), b) : CM.CmacState}
