# bend-osdev-collections-crypto: bend-collections' cryptography as instances
# of bend-osdev-crypto's interfaces, the way kitbytes adapts bend-kit's
# bytes. The code is bend-collections@1.0.0.0's src/crypto, imported from
# bend-collections-laws-crypto@1.0.0.0, which ships the same files with
# their proofs: Bend names a def by the package it comes from, so those
# proofs are about that package's copy, and the adapters use it so that
# LAWS.bend can cite them (crypto's inst_sha2.bend does the same).
#
# No other package of bend-osdev sees bend-collections' types: bytes cross
# as Octets, keys and states are this package's opaque types, and every
# refusal is a crypto CrError. The adapters, one file per concern:
#
#   aead.bend      AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305 and
#                  XChaCha20-Poly1305 as AEADs
#   gmac.bend      GMAC (AES-128, AES-256) as a MAC
#   poly1305.bend  Poly1305 as a MAC
#   chacha.bend    ChaCha20 (any round count) and XChaCha20 as stream ciphers
#   blake.bend     BLAKE2b-512, BLAKE2s-256 and BLAKE3-256 as hashes
#   keccak.bend    Keccak-256 (the original padding) as a hash
#   x25519.bend    X25519 as a key agreement
#   ed25519.bend   Ed25519 as a signature scheme
#
# This file holds what they share: a Maybe of bend-collections' as a
# Result, and the state of a hash whose code is one-shot (CcBuf).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr

# bend-collections' answer (a list of bytes, or None) as a Result: None is
# the given error
def CcRes.of_maybe(e: Cr.CrError, m: Maybe<&2, List<&2, U32>>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match m:
    case None{}:
      Fail{e}
    case Some{xs}:
      Done{B.Octets.of_list(xs)}

# bend-collections' answer as bytes, empty for None
def CcRes.or_empty(m: Maybe<&2, List<&2, U32>>) -> B.Octets:
  match m:
    case None{}:
      B.Octets.empty()
    case Some{xs}:
      B.Octets.of_list(xs)

# Buffered hashing. bend-collections' BLAKE and Keccak code is one-shot (a
# packed array and its length), so the streaming interface keeps the bytes
# so far and hashes them at the end: the state is the bytes, last first, so
# that an update costs the length of its piece (opaque type).
type CcBuf is Data:
  CcBuf{rev: List<&2, U32>}

def CcBuf.init() -> CcBuf:
  CcBuf{Nil{}}

# the state after more bytes
def CcBuf.update(s: CcBuf, o: B.Octets) -> CcBuf:
  match s:
    case CcBuf{r}:
      CcBuf{B.rev_onto(B.Octets.to_list(o), r)}

# the bytes so far
def CcBuf.bytes(s: CcBuf) -> B.Octets:
  match s:
    case CcBuf{r}:
      B.Octets.of_list(B.rev_onto(r, Nil{}))

# the digest of the bytes so far, by any one-shot digest
def CcBuf.final(~digest: B.Octets -> B.Octets, s: CcBuf) -> B.Octets:
  digest(CcBuf.bytes(s))
