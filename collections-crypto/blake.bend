# BLAKE2b, BLAKE2s (RFC 7693) and BLAKE3 as hashes: bend-collections'
# BLAKE code, adapted to Octets. bend-collections hashes a packed array (four
# little-endian bytes per word) and its length in one call, and proves each
# equal to its executable specification for every array and length
# (blake2b_correct, blake2s, blake3_correct); its digest is an array of
# little-endian words. Here a message is packed with bend-collections' own
# packing (blake2b/sized.bend's pack, which its Argon2 uses), and the digest
# words are written out as bytes.
#
# The instances (a buffered state, collections-crypto.bend's CcBuf):
#   BLAKE2b-512:  ~CcBuf, ~128n, ~64n, ~CcBuf.init(), ~CcBuf.update,
#                 ~CcBuf.final(~CcBlake.blake2b), ~CcBlake.blake2b
#   BLAKE2b-n:    ~CcBuf, ~128n, ~nn, ~CcBuf.init(), ~CcBuf.update,
#                 ~CcBuf.final(~CcBlake.blake2b_n(~nn)), ~CcBlake.blake2b_n(~nn)
#                 for a digest of nn bytes, 1 to 64 (BLAKE2b-256:
#                 CcBlake.blake2b_256, BLAKE2b-384: CcBlake.blake2b_384)
#   BLAKE2s-256:  ~CcBuf, ~64n, ~32n, ... ~CcBlake.blake2s
#   BLAKE3-256:   ~CcBuf, ~64n, ~32n, ... ~CcBlake.blake3
# Unkeyed only: bend-collections has no keyed BLAKE2 (RFC 7693's key
# parameter) and no keyed, key-derivation or extended-output BLAKE3 mode.
import Base
import ../bytes/bytes.bend as B
import bend-collections-laws-crypto@1.0.0.0/src/crypto/blake/blake2b/blake2b.bend as I2b
import bend-collections-laws-crypto@1.0.0.0/src/crypto/blake/blake2b/sized.bend as Z
import bend-collections-laws-crypto@1.0.0.0/src/crypto/blake/blake2s/blake2s.bend as I2s
import bend-collections-laws-crypto@1.0.0.0/src/crypto/blake/blake3/blake3.bend as I3

# the little-endian bytes of the word read at index i (r) and of the n words
# after it
def cc.blake.go(n: Nat, +i: U32, r: Array<U32> & U32) -> List<&2, U32>:
  match n:
    case 0n:
      (a, x) = r
      B.le32(x)
    case 1n+p:
      (a, x) = r
      B.append(B.le32(x), cc.blake.go(p, U32.add(i, 1), Array.get(U32, a, U32.add(i, 1))))

# the little-endian bytes of an array's first n words
def cc.blake.words(n: Nat, a: Array<U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      cc.blake.go(p, 0, Array.get(U32, a, 0))

# A message as bend-collections' hashes take it: its bytes packed four to a
# little-endian word (the last zero-padded), in an array of a power-of-two
# size
def CcBlake.pack(o: B.Octets) -> Array<U32>:
  Z.pack(B.Octets.to_list(o))

# bend-collections' digest (n little-endian words) as bytes; empty for None,
# which a message packed by CcBlake.pack never gives
def CcBlake.out(n: Nat, m: Maybe<&1, Array<U32>>) -> B.Octets:
  match m:
    case None{}:
      B.Octets.empty()
    case Some{a}:
      B.Octets.of_list(cc.blake.words(n, a))

# BLAKE2b-512 (RFC 7693), 64 bytes
def cc.blake.blake2b(+o: B.Octets) -> B.Octets:
  CcBlake.out(16n, I2b.blake2b(CcBlake.pack(o), B.Octets.len(o)))

def CcBlake.blake2b(o: B.Octets) -> B.Octets:
  cc.blake.blake2b(o)

# BLAKE2s-256 (RFC 7693), 32 bytes
def cc.blake.blake2s(+o: B.Octets) -> B.Octets:
  CcBlake.out(8n, I2s.blake2s(CcBlake.pack(o), B.Octets.len(o)))

def CcBlake.blake2s(o: B.Octets) -> B.Octets:
  cc.blake.blake2s(o)

# BLAKE3 (its specification's hash mode), 32 bytes
def cc.blake.blake3(+o: B.Octets) -> B.Octets:
  CcBlake.out(8n, I3.blake3(CcBlake.pack(o), B.Octets.len(o)))

def CcBlake.blake3(o: B.Octets) -> B.Octets:
  cc.blake.blake3(o)

# BLAKE2b with an nn-byte digest, 1 <= nn <= 64 (RFC 7693 section 2.5: the
# parameter block's digest length; bend-collections' blake2b/sized.bend)
def CcBlake.blake2b_n(~nn: Nat, o: B.Octets) -> B.Octets:
  B.Octets.of_list(Z.hash(nn, B.Octets.to_list(o)))

# the named lengths
def CcBlake.blake2b_256(o: B.Octets) -> B.Octets:
  CcBlake.blake2b_n(~32n, o)

def CcBlake.blake2b_384(o: B.Octets) -> B.Octets:
  CcBlake.blake2b_n(~48n, o)
