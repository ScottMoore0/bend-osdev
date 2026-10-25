# Laws about Twofish (twofish.bend): for every key (every key size) and
# block, decryption undoes encryption and encryption undoes decryption. The
# paper's vectors run in check.bend (README.md, Laws).
import Base
import ../mode-core/mode-core.bend as M
import ./twofish.bend as F

# Twofish (Schneier et al.), every key size

law twofish_round_trip:
  for k: F.LcTwofishKey
  for +b: M.CmBlock
  {F.LcTwofish.decrypt(k, F.LcTwofish.encrypt(k, b)) == b : M.CmBlock}

law twofish_round_trip_dual:
  for k: F.LcTwofishKey
  for +b: M.CmBlock
  {F.LcTwofish.encrypt(k, F.LcTwofish.decrypt(k, b)) == b : M.CmBlock}
