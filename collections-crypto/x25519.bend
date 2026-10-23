# X25519 (RFC 7748 sections 5 and 6.1) as a key agreement: bend-collections'
# key exchange (kex.bend), which its laws prove to be RFC 7748's X25519 for
# every pair of 32-byte strings, refusing an all-zero shared secret (a
# small-order peer key, section 6.1).
#
# Keys are 32 bytes: a secret key is a scalar (clamped inside X25519, as
# section 5 says), a public key a u-coordinate; the public key of a secret
# key is X25519(k, 9). The shared secret is keying material for a KDF
# (crypto's kdf.bend), not a key.
#
# The instance:
#   ~CcX25519Sk, ~CcX25519Pk, ~CcX25519.secret, ~CcX25519.public,
#   ~CcX25519.pk_of, ~CcX25519.pk_to, ~CcX25519.shared
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ./collections-crypto.bend as C
import bend-collections-laws-crypto@1.0.0.0/src/crypto/kex.bend as K
import bend-collections-laws-crypto@1.0.0.0/src/crypto/curve25519/x25519.bend as X

# A secret key (opaque): 32 bytes
type CcX25519Sk is Data:
  CcX25519Sk{key: List<&2, U32>}

# A public key (opaque): 32 bytes
type CcX25519Pk is Data:
  CcX25519Pk{key: B.Octets}

def cc.x25519.secret(ok: Bool, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcX25519Sk>:
  match ok:
    case False{}:
      Fail{Cr.CrBadKeyLength{B.Octets.len(o)}}
    case True{}:
      Done{CcX25519Sk{B.Octets.to_list(o)}}

def cc.x25519.secret_of(+o: B.Octets) -> Result<&2, &2, Cr.CrError, CcX25519Sk>:
  cc.x25519.secret(Nat.is_eq(B.Octets.len(o), 32n), o)

# The secret key of 32 raw bytes (CrBadKeyLength otherwise)
def CcX25519.secret(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcX25519Sk>:
  cc.x25519.secret_of(o)

# Its public key, X25519(k, 9)
def CcX25519.public(k: CcX25519Sk) -> CcX25519Pk:
  match k:
    case CcX25519Sk{key}:
      CcX25519Pk{C.CcRes.or_empty(X.x25519(key, X.base()))}

def cc.x25519.pk(ok: Bool, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcX25519Pk>:
  match ok:
    case False{}:
      Fail{Cr.CrBadPublicKey{}}
    case True{}:
      Done{CcX25519Pk{o}}

def cc.x25519.pk_of(+o: B.Octets) -> Result<&2, &2, Cr.CrError, CcX25519Pk>:
  cc.x25519.pk(Nat.is_eq(B.Octets.len(o), 32n), o)

# A peer's public key of 32 bytes (CrBadPublicKey otherwise)
def CcX25519.pk_of(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcX25519Pk>:
  cc.x25519.pk_of(o)

# a public key's bytes
def CcX25519.pk_to(p: CcX25519Pk) -> B.Octets:
  match p:
    case CcX25519Pk{o}:
      o

# The shared secret X25519(k, u), refused (CrBadKey) when it is all zero
def CcX25519.shared(k: CcX25519Sk, p: CcX25519Pk) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match k p:
    case CcX25519Sk{key} CcX25519Pk{o}:
      C.CcRes.of_maybe(Cr.CrBadKey{}, K.shared_secret(key, B.Octets.to_list(o)))
