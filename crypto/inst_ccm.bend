# CCM as an AEAD: cipher-modes' CCM (NIST SP 800-38C, RFC 3610) over any
# 128-bit block cipher, with a tag of tlen bytes (4, 6, ..., 16) and a nonce
# of 7 to 13 bytes. The instance over a block cipher (~K, ~key, ~enc):
#   ~K, ~key, ~CrCcm.seal(~K, ~enc, ~tlen), ~CrCcm.open(~K, ~enc, ~tlen)
# for example AES-CCM with a 16-byte tag:
#   ~X.CmAesKey, ~CrAes.key, ~CrCcm.seal(~X.CmAesKey, ~X.CmAes.encrypt, ~16n),
#   ~CrCcm.open(~X.CmAesKey, ~X.CmAes.encrypt, ~16n)
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/ccm.bend as CC
import ./crypto.bend as Cr
import ./inst_cm.bend as CM

# the ciphertext of p, then the tlen-byte tag
def CrCcm.seal(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~tlen: Nat, k: K, nonce: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CM.CrCm.lift(~B.Octets, CC.Ccm.encrypt(~K, ~enc, k, tlen, nonce, aad, p))

# the plaintext of c (the ciphertext, then the tag), or CrTagMismatch
def CrCcm.open(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~tlen: Nat, k: K, nonce: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CM.CrCm.lift(~B.Octets, CC.Ccm.decrypt(~K, ~enc, k, tlen, nonce, aad, c))
