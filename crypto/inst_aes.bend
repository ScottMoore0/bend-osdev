# AES as a block cipher: the aes package's AES-128 and AES-256 (FIPS 197;
# encryption from bend-collections, decryption in the aes package, proved to
# undo it: aes' aes_round_trip). The instance:
#   ~X.CmAesKey, ~M.CmBlock, ~16n, ~CrAes.key, ~X.CmAes.encrypt,
#   ~X.CmAes.decrypt, ~CrBlk128.of_octets, ~CrBlk128.to_octets, ~CrBlk128.xor
# or the same with ~CrAes.key_enc in place of ~CrAes.key: the two give the
# same key now (aes decrypts with the encryption schedule, so
# CmAes.prepare has nothing to compute), and both are kept as the interface's
# names.
# This is the only file of the package that imports the aes package's aes.bend,
# and so bend-collections.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ../aes/aes.bend as X
import ./crypto.bend as Cr
import ./inst_cm.bend as CM

# a 16- or 32-byte key (AES-128 or AES-256); CrBadKeyLength for any other
# length
def CrAes.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, X.CmAesKey>:
  CM.CrCm.lift(~X.CmAesKey, Result.map(&2, &2, M.CmError, X.CmAesKey, X.CmAesKey, X.CmAes.prepare, X.CmAes.key(o)))

# the same key (once without CmAes.prepare, which computed decryption round
# keys in earlier versions of bend-osdev-cipher-modes)
def CrAes.key_enc(o: B.Octets) -> Result<&2, &2, Cr.CrError, X.CmAesKey>:
  CM.CrCm.lift(~X.CmAesKey, X.CmAes.key(o))
