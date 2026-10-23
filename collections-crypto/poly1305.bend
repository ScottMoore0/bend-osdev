# Poly1305 (RFC 8439 section 2.5) as a MAC: bend-collections' Poly1305
# (poly1305/poly1305.bend's mac, which its laws prove equal to RFC 8439's
# for every key and message, 16 bytes long).
#
# Poly1305 is a one-time authenticator: a key must never authenticate two
# messages (RFC 8439 section 2.5); ChaCha20-Poly1305 (aead.bend) derives a
# fresh one per nonce. The verify is crypto's named default, which compares
# every byte (CrMac.verify_tag); bend-collections' own verify (subtle.eq)
# takes lists, and the interface's laws are stated for the default.
#
# The instance:
#   ~CcPolyKey, ~CcPoly1305.key, ~CcPoly1305.mac, ~CcPoly1305.verify
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/mac.bend as Mc
import bend-collections-laws-crypto@1.0.0.0/src/crypto/poly1305/poly1305.bend as P

# A Poly1305 key (opaque): r || s, 32 bytes
type CcPolyKey is Data:
  CcPolyKey{key: List<&2, U32>}

def cc.poly.key(ok: Bool, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcPolyKey>:
  match ok:
    case False{}:
      Fail{Cr.CrBadKeyLength{B.Octets.len(o)}}
    case True{}:
      Done{CcPolyKey{B.Octets.to_list(o)}}

def cc.poly.key_of(+o: B.Octets) -> Result<&2, &2, Cr.CrError, CcPolyKey>:
  cc.poly.key(Nat.is_eq(B.Octets.len(o), 32n), o)

# The key of 32 raw bytes (CrBadKeyLength otherwise)
def CcPoly1305.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcPolyKey>:
  cc.poly.key_of(o)

# the 16-byte tag
def CcPoly1305.mac(k: CcPolyKey, m: B.Octets) -> B.Octets:
  match k:
    case CcPolyKey{key}:
      B.Octets.of_list(P.mac(key, B.Octets.to_list(m)))

# whether t is m's tag (every byte compared)
def CcPoly1305.verify(k: CcPolyKey, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~CcPolyKey, ~CcPoly1305.mac, k, m, t)
