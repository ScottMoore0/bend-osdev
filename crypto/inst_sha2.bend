# SHA-256 and SHA-512 (FIPS 180-4) as hashes: bend-collections' hashes,
# adapted to Octets. The code is bend-collections@1.0.0.0's src/crypto
# (hash.bend and the sha, sha512 and keccak files it imports), imported from
# bend-collections-laws-crypto@1.0.0.0, which ships the same files with
# their proofs: Bend names a def by the package it comes from, so those
# proofs (Split.sha256, Incremental.sha256, Sha256.length, ...) are about
# that package's copy, and this adapter uses it so that LAWS.bend can cite
# them. No other file of bend-osdev sees bend-collections' types: the state
# is wrapped in CrSha2State, and bytes cross as Octets.
#
# The instances (block size 64 and 128 bytes, digest 32 and 64):
#   ~CrSha2State, ~64n, ~32n, ~CrSha2.init256(), ~CrSha2.update,
#   ~CrSha2.final, ~CrSha2.sha256
#   ~CrSha2State, ~128n, ~64n, ~CrSha2.init512(), ~CrSha2.update,
#   ~CrSha2.final, ~CrSha2.sha512
import Base
import ../bytes/bytes.bend as B
import bend-collections-laws-crypto@1.0.0.0/src/crypto/hash.bend as Hc

# A hash state (opaque): which hash, its chaining value, the bytes of the
# unfinished block, and the length so far
type CrSha2State is Data:
  CrSha2State{h: Hc.Hasher}

def CrSha2.init256() -> CrSha2State:
  CrSha2State{Hc.new_sha256()}

def CrSha2.init512() -> CrSha2State:
  CrSha2State{Hc.new_sha512()}

# the state after more bytes (either hash: the state knows which it is)
def CrSha2.update(s: CrSha2State, o: B.Octets) -> CrSha2State:
  match s:
    case CrSha2State{h}:
      CrSha2State{Hc.update(h, B.Octets.to_list(o))}

# the digest of the bytes so far
def CrSha2.final(s: CrSha2State) -> B.Octets:
  match s:
    case CrSha2State{h}:
      B.Octets.of_list(Hc.digest(h))

# The digests in one call
def CrSha2.sha256(o: B.Octets) -> B.Octets:
  B.Octets.of_list(Hc.sha256(B.Octets.to_list(o)))

def CrSha2.sha512(o: B.Octets) -> B.Octets:
  B.Octets.of_list(Hc.sha512(B.Octets.to_list(o)))
