# AES as a block cipher: cipher-modes' AES-128 and AES-256 (FIPS 197;
# encryption from bend-collections, decryption in cipher-modes), with its
# key schedule's decryption round keys computed once (CmAes.prepare). The
# instance:
#   ~X.CmAesKey, ~M.CmBlock, ~16n, ~CrAes.key, ~X.CmAes.encrypt,
#   ~X.CmAes.decrypt, ~CrBlk128.of_octets, ~CrBlk128.to_octets, ~CrBlk128.xor
# and, for a mode that only encrypts (CTR, CMAC, CCM), the same with
# ~CrAes.key_enc in place of ~CrAes.key, which skips the decryption round
# keys.
# This is the only file of the package that imports cipher-modes' aes.bend,
# and so bend-collections.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/aes.bend as X
import ./crypto.bend as Cr
import ./inst_cm.bend as CM

# a 16- or 32-byte key (AES-128 or AES-256), with its decryption round keys;
# CrBadKeyLength for any other length
def CrAes.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, X.CmAesKey>:
  CM.CrCm.lift(~X.CmAesKey, Result.map(&2, &2, M.CmError, X.CmAesKey, X.CmAesKey, X.CmAes.prepare, X.CmAes.key(o)))

# the same without the decryption round keys, for uses that only encrypt
# (CTR, CMAC, CCM): a key made this way still decrypts, deriving those round
# keys again for every block
def CrAes.key_enc(o: B.Octets) -> Result<&2, &2, Cr.CrError, X.CmAesKey>:
  CM.CrCm.lift(~X.CmAesKey, X.CmAes.key(o))
