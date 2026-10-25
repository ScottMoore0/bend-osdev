# Laws about CCM (ccm.bend), for every cipher given as the template
# arguments ~K, ~enc (CCM only encrypts, so there is no hypothesis).
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./ccm.bend as CC

# CCM: decryption accepts what encryption produced and gives the message
# back, for every cipher, key, tag length, nonce, associated data and
# message; when the parameters are refused, both refuse alike
law ccm_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +m: Nat
  for +nonce: B.Octets
  for +aad: B.Octets
  for +p: B.Octets
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CC.Ccm.encrypt(~K, ~enc, k, m, nonce, aad, p), c => CC.Ccm.decrypt(~K, ~enc, k, m, nonce, aad, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, CC.Ccm.encrypt(~K, ~enc, k, m, nonce, aad, p)) : Result<&2, &2, M.CmError, B.Octets>}
