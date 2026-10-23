# AES-GCM (NIST SP 800-38D, 96-bit nonces, 128-bit tags), ChaCha20-Poly1305
# (RFC 8439 section 2.8) and XChaCha20-Poly1305 (draft-irtf-cfrg-xchacha-03)
# as AEADs: bend-collections' AEAD facade (aead.bend's encrypt and decrypt),
# whose laws prove each algorithm equal to its executable specification,
# decrypt(encrypt(x)) == Some(x) for every key, nonce, associated data and
# plaintext of the right lengths, and the refusal of every other tag.
#
# A key holds its algorithm, so one seal and one open serve all four. The
# ciphertext is the encrypted data followed by the 16-byte tag (RFC 5116's
# layout). A nonce of the wrong length is refused with CrBadNonceLength, a
# changed tag, ciphertext or associated data (or data shorter than a tag)
# with CrTagMismatch, before any plaintext is given out.
#
# The instances (K is CcAeadKey for all four):
#   AES-128-GCM:         ~CcAeadKey, ~CcGcm.key128, ~CcAead.seal, ~CcAead.open
#   AES-256-GCM:         ~CcAeadKey, ~CcGcm.key256, ~CcAead.seal, ~CcAead.open
#   ChaCha20-Poly1305:   ~CcAeadKey, ~CcChaPoly.key, ~CcAead.seal, ~CcAead.open
#   XChaCha20-Poly1305:  ~CcAeadKey, ~CcXChaPoly.key, ~CcAead.seal, ~CcAead.open
# with nonces of 12 bytes (GCM, ChaCha20-Poly1305) or 24 (XChaCha20-Poly1305).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ./collections-crypto.bend as C
import bend-collections-laws-crypto@1.0.0.0/src/crypto/aead.bend as A

# An AEAD key (opaque): the algorithm and its raw key
type CcAeadKey is Data:
  CcAeadKey{alg: A.Alg, key: List<&2, U32>}

def cc.aead.key(ok: Bool, +alg: A.Alg, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcAeadKey>:
  match ok:
    case False{}:
      Fail{Cr.CrBadKeyLength{B.Octets.len(o)}}
    case True{}:
      Done{CcAeadKey{alg, B.Octets.to_list(o)}}

def cc.aead.key_of(+alg: A.Alg, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcAeadKey>:
  cc.aead.key(Nat.is_eq(B.Octets.len(o), A.key_size(alg)), alg, o)

# The keys of raw bytes (CrBadKeyLength for any other length)
# AES-128-GCM: 16 bytes
def CcGcm.key128(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcAeadKey>:
  cc.aead.key_of(A.AES_128_GCM{}, o)

# AES-256-GCM: 32 bytes
def CcGcm.key256(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcAeadKey>:
  cc.aead.key_of(A.AES_256_GCM{}, o)

# ChaCha20-Poly1305: 32 bytes
def CcChaPoly.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcAeadKey>:
  cc.aead.key_of(A.CHACHA20_POLY1305{}, o)

# XChaCha20-Poly1305: 32 bytes
def CcXChaPoly.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcAeadKey>:
  cc.aead.key_of(A.XCHACHA20_POLY1305{}, o)

# What bend-collections' encrypt answers for these arguments: the
# ciphertext and tag as a list of bytes, or None (a nonce of the wrong
# length)
def CcAead.sealed(k: CcAeadKey, n: B.Octets, a: B.Octets, p: B.Octets) -> Maybe<&2, List<&2, U32>>:
  match k:
    case CcAeadKey{alg, key}:
      A.encrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), B.Octets.to_list(p))

# What bend-collections' decrypt answers for a ciphertext and tag given as
# a list: the plaintext, or None
def CcAead.opened(k: CcAeadKey, n: B.Octets, a: B.Octets, c: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match k:
    case CcAeadKey{alg, key}:
      A.decrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), c)

def cc.aead.mask(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      Some{B.mask(c)}

# The same with every element masked to 8 bits: equal to CcAead.sealed
# exactly when bend-collections answered a byte string (LAWS.bend's round
# trip is stated given that equality; it holds on every test)
def CcAead.masked(k: CcAeadKey, n: B.Octets, a: B.Octets, p: B.Octets) -> Maybe<&2, List<&2, U32>>:
  cc.aead.mask(CcAead.sealed(k, n, a, p))

def cc.aead.seal(k: CcAeadKey, +n: B.Octets, a: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  C.CcRes.of_maybe(Cr.CrBadNonceLength{B.Octets.len(n)}, CcAead.sealed(k, n, a, p))

# p sealed under a nonce and associated data: the ciphertext and its tag
def CcAead.seal(k: CcAeadKey, n: B.Octets, a: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cc.aead.seal(k, n, a, p)

def cc.aead.open(ok: Bool, +alg: A.Alg, +key: List<&2, U32>, +n: B.Octets, +a: B.Octets, +c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match ok:
    case False{}:
      Fail{Cr.CrBadNonceLength{B.Octets.len(n)}}
    case True{}:
      C.CcRes.of_maybe(Cr.CrTagMismatch{}, A.decrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), B.Octets.to_list(c)))

def cc.aead.open_key(k: CcAeadKey, +n: B.Octets, a: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match k:
    case CcAeadKey{+alg, key}:
      cc.aead.open(Nat.is_eq(List.length(&2, U32, B.Octets.to_list(n)), A.nonce_size(alg)), alg, key, n, a, c)

# the plaintext of a ciphertext and tag, or CrTagMismatch
def CcAead.open(k: CcAeadKey, n: B.Octets, a: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cc.aead.open_key(k, n, a, c)
