# bend-osdev-kithash: bend-kit-hash's unkeyed hashes as instances of
# crypto's hash interface (crypto/hash.bend). None is a cryptographic hash:
# CRC-32 and Adler-32 are checksums, FNV-1a and xxHash fast hashes for
# tables and integrity checks, as crypto's CRC instances are.
#
# bend-kit-hash computes in one call only, so the state is the bytes so far
# (KhBuf) and the digest is computed at the end: the streaming and split
# laws then hold for every digest function (LAWS.bend), and the state costs
# the memory of the message. For long data in pieces, the agreeing
# streaming implementations are crc's CRC-32 (crypto's CrCrc32), deflate's
# Adler-32 and zstd's XXH64 (LAWS.bend: the agreement laws).
#
# The digest is the value big-endian: 4 bytes, or 8 for FNV-1a 64 and XXH64
# (crypto's CRC-32 digest, and xxHash's canonical form). The block size is a
# parameter of HMAC only; 64 is the named default, as for crypto's CRCs.
# The instances:
#   CRC-32     ~KhBuf, ~64n, ~4n, ~KhBuf.init(), ~KhBuf.update, ~KhBuf.final(~KhCrc32.digest), ~KhCrc32.digest
#   Adler-32   ~KhBuf, ~64n, ~4n, ~KhBuf.init(), ~KhBuf.update, ~KhBuf.final(~KhAdler32.digest), ~KhAdler32.digest
#   FNV-1a 32  ~KhBuf, ~64n, ~4n, ..., ~KhFnv1a32.digest
#   FNV-1a 64  ~KhBuf, ~64n, ~8n, ..., ~KhFnv1a64.digest
#   XXH32      ~KhBuf, ~64n, ~4n, ..., ~KhXxh32.digest(~seed)   (seed: U32)
#   XXH64      ~KhBuf, ~64n, ~8n, ..., ~KhXxh64.digest(~seed)   (seed: W64)
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./kithash.bend as K

# The state: the bytes so far

type KhBuf is Data:
  KhBuf{bytes: B.Octets}

def KhBuf.init() -> KhBuf:
  KhBuf{B.Octets.empty()}

def KhBuf.update(s: KhBuf, o: B.Octets) -> KhBuf:
  match s:
    case KhBuf{b}:
      KhBuf{B.Octets.append(b, o)}

# the digest of the bytes so far, by any one-shot digest
def KhBuf.final(~digest: B.Octets -> B.Octets, s: KhBuf) -> B.Octets:
  match s:
    case KhBuf{b}:
      digest(b)

# the bytes so far
def KhBuf.bytes(s: KhBuf) -> B.Octets:
  match s:
    case KhBuf{b}:
      b

# The digests

def KhCrc32.digest(o: B.Octets) -> B.Octets:
  B.Octets.be32(K.KhCrc32.value(o))

def KhAdler32.digest(o: B.Octets) -> B.Octets:
  B.Octets.be32(K.KhAdler32.value(o))

def KhFnv1a32.digest(o: B.Octets) -> B.Octets:
  B.Octets.be32(K.KhFnv1a32.value(o))

def KhFnv1a64.digest(o: B.Octets) -> B.Octets:
  B.Octets.be64(K.KhFnv1a64.value(o))

def KhXxh32.digest(~seed: U32, o: B.Octets) -> B.Octets:
  B.Octets.be32(K.KhXxh32.value(seed, o))

def KhXxh64.digest(~seed: W.W64, o: B.Octets) -> B.Octets:
  B.Octets.be64(K.KhXxh64.value(seed, o))
