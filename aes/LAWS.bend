# Laws about AES (aes.bend): its decryption undoes its encryption for
# every key and block, and FIPS 197's C.1 vector.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./aes.bend as X

# AES (aes.bend): decryption undoes encryption, for every key (every value
# of CmAesKey, whatever its number of rounds and round keys: AES-128, AES-192
# and AES-256 among them) and every block
law aes_round_trip:
  for k: X.CmAesKey
  for +b: M.CmBlock
  {X.CmAes.decrypt(k, X.CmAes.encrypt(k, b)) == b : M.CmBlock}

# Vectors: the specifications' own test values, proved by computation. The
# checker evaluates AES slowly and keeps what it evaluates, so only these fit
# in its memory; every other vector of the four specifications (all of SP
# 800-38A F.2.1, F.2.2, F.2.5 and F.2.6; IEEE 1619 vectors 2 and 15 to 18;
# RFC 3610 packets 1 to 3; RFC 4493 examples 2 to 4; and every decryption)
# runs compiled in check.bend.

# FIPS 197 Appendix C.1: the named default cipher (AES-128) encrypts one block
law aes128_fips197_c1:
  {Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.encrypt(k, M.CmBlock{1122867, 1146447479, 2291772091, 3437096703})), X.CmAes.key128(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]))) == Done{B.Octets.of_list([105, 196, 224, 216, 106, 123, 4, 48, 216, 205, 183, 128, 112, 180, 197, 90])} : Result<&2, &2, M.CmError, B.Octets>}
