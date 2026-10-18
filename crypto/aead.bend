# The AEAD interface (authenticated encryption with associated data, in the
# shape of RFC 5116).
#
# An AEAD (template arguments, in this order):
#   ~K: Data                                       its key, prepared
#   ~key: B.Octets -> Result<&2, &2, CrError, K>   the key of a raw key
#   ~seal: K -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, CrError, B.Octets>
#                                                  key, nonce, associated
#                                                  data, plaintext: the
#                                                  ciphertext with its tag,
#                                                  or the refusal of a bad
#                                                  nonce or length
#   ~open: K -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, CrError, B.Octets>
#                                                  key, nonce, associated
#                                                  data, ciphertext with tag:
#                                                  the plaintext, or
#                                                  CrTagMismatch (no
#                                                  plaintext released)
# Laws (README.md, "Laws"):
#   round_trip  open accepts what seal produced and gives the plaintext
#               back; when seal refuses, open-after-seal refuses alike:
#               bind(seal(k, n, a, p), c => open(k, n, a, c)) ==
#               map(c => p, seal(k, n, a, p))
#   tamper      a changed tag, ciphertext or associated data is refused
#               (CrTagMismatch): tested (a forgery succeeds with
#               probability 2^-8tlen, so it is not a law for every input)
#
# The instances: CCM over any 128-bit block cipher (inst_ccm.bend).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

# p sealed under a raw key
def CrAead.seal_with(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~seal: K -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, key_o: B.Octets, nonce: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, K, B.Octets, key(key_o), k => seal(k, nonce, aad, p))

# c opened under a raw key
def CrAead.open_with(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~open: K -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, key_o: B.Octets, nonce: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, K, B.Octets, key(key_o), k => open(k, nonce, aad, c))
