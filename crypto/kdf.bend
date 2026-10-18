# The KDF interface (key derivation).
#
# A KDF (one template argument):
#   ~derive: B.Octets -> B.Octets -> B.Octets -> Nat -> Result<&2, &2, CrError, B.Octets>
#            secret, salt, context (info), length: that many bytes of keying
#            material, or the refusal of a length the KDF cannot give
#            (CrBadOutputLength)
# Laws (README.md, "Laws"):
#   length  a derivation that succeeds gives exactly the length asked for
#           (tested)
#   prefix  a shorter derivation is a prefix of a longer one with the same
#           inputs (tested)
#
# The instances: HKDF over any hash (hkdf.bend).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

# A key for any interface derived from a secret: n bytes, through that
# interface's key schedule ~key (a block cipher's, a MAC's, an AEAD's)
def CrKdf.derive_key(~K: Data, ~derive: B.Octets -> B.Octets -> B.Octets -> Nat -> Result<&2, &2, Cr.CrError, B.Octets>, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, secret: B.Octets, salt: B.Octets, info: B.Octets, n: Nat) -> Result<&2, &2, Cr.CrError, K>:
  Result.bind(&2, &2, Cr.CrError, B.Octets, K, derive(secret, salt, info, n), o => key(o))
