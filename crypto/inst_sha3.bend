# SHA3-256 (FIPS 202) as a hash: bend-collections' SHA3-256, adapted to
# Octets, as inst_sha2.bend adapts SHA-256 and SHA-512. The code is
# bend-collections@1.0.0.0's src/crypto (hash.bend and the keccak and sha3
# files it imports), imported from bend-collections-laws-crypto@1.0.0.0,
# which ships the same files with their proofs (Split.sha3_256,
# Incremental.sha3_256, Sha3_256.length, Sha3_256.value); LAWS.bend cites
# them. The state is wrapped in CrSha3State, and bytes cross as Octets.
#
# The instance (block size 136 bytes, the SHA3-256 rate, which is HMAC's
# B for SHA3-256; digest 32):
#   ~CrSha3State, ~136n, ~32n, ~CrSha3.init(), ~CrSha3.update,
#   ~CrSha3.final, ~CrSha3.sha3_256
import Base
import ../bytes/bytes.bend as B
import bend-collections-laws-crypto@1.0.0.0/src/crypto/hash.bend as Hc

# A hash state (opaque): the Keccak state, the bytes of the unfinished
# block, and the length so far
type CrSha3State is Data:
  CrSha3State{h: Hc.Hasher}

def CrSha3.init() -> CrSha3State:
  CrSha3State{Hc.new_sha3_256()}

# the state after more bytes
def CrSha3.update(s: CrSha3State, o: B.Octets) -> CrSha3State:
  match s:
    case CrSha3State{h}:
      CrSha3State{Hc.update(h, B.Octets.to_list(o))}

# the digest of the bytes so far
def CrSha3.final(s: CrSha3State) -> B.Octets:
  match s:
    case CrSha3State{h}:
      B.Octets.of_list(Hc.digest(h))

# the digest in one call
def CrSha3.sha3_256(o: B.Octets) -> B.Octets:
  B.Octets.of_list(Hc.sha3_256(B.Octets.to_list(o)))
