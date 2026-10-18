# CMAC as a MAC: cipher-modes' CMAC (NIST SP 800-38B, RFC 4493) over any
# 128-bit block cipher (~K, ~key, ~enc). The instance:
#   ~K, ~key, ~CrCmac.mac(~K, ~enc), ~CrCmac.verify(~K, ~enc)
# for example AES-CMAC:
#   ~X.CmAesKey, ~CrAes.key, ~CrCmac.mac(~X.CmAesKey, ~X.CmAes.encrypt),
#   ~CrCmac.verify(~X.CmAesKey, ~X.CmAes.encrypt)
# verify is the interface's named default (mac.bend: CrMac.verify_tag), so
# its laws hold for CMAC by the generic proof; cipher-modes' own
# Cmac.verify does the same comparison, but no law of cipher-modes ties it
# to Cmac.mac.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/cmac.bend as CMc
import ./mac.bend as Mc

# the 16-byte tag of m
def CrCmac.mac(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, k: K, m: B.Octets) -> B.Octets:
  CMc.Cmac.mac(~K, ~enc, k, m)

# whether t is m's tag (every byte compared)
def CrCmac.verify(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, k: K, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~K, ~CrCmac.mac(~K, ~enc), k, m, t)
