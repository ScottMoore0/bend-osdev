# bend-osdev-xz: the integrity checks of .xz blocks ("The .xz File Format",
# 2.1.1.2 and 3.4): none, CRC32, CRC64 or SHA-256, computed over the block's
# uncompressed data, in pieces as the data is decoded.
#
# CRC32 and CRC64 (CRC-64/XZ) come from bend-osdev-crc, SHA-256 from
# bend-collections. The check field stores a CRC little-endian, and a SHA-256
# digest as its 32 bytes.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../crc/crc.bend as C
import bend-collections@1.0.0.0/src/crypto/sha/sha256.bend as Sha

# A check in progress: the CRC register, or the pieces of data so far (most
# recent first) for SHA-256, which bend-collections computes in one go
type XzCheck is Data:
  XzCheckNone{}
  XzCheckCrc32{reg: U32}
  XzCheckCrc64{reg: W.W64}
  XzCheckSha256{pieces: List<&2, B.Octets>}

# The size of the check field for each of the 16 check IDs; the IDs that are
# not defined yet still have a size, so a decoder can skip them
def XzCheck.size.go(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      4n
    case 2n:
      4n
    case 3n:
      4n
    case 4n:
      8n
    case 5n:
      8n
    case 6n:
      8n
    case 7n:
      16n
    case 8n:
      16n
    case 9n:
      16n
    case 10n:
      32n
    case 11n:
      32n
    case 12n:
      32n
    case _:
      64n

def XzCheck.size(id: U32) -> Nat:
  XzCheck.size.go(U32.to_nat(U32.and(id, 15)))

# A new check of type id, if it is one this package computes: 0 (none),
# 1 (CRC32), 4 (CRC64) or 10 (SHA-256)
def XzCheck.start.go(n: Nat) -> Maybe<&2, XzCheck>:
  match n:
    case 0n:
      Some{XzCheckNone{}}
    case 1n:
      Some{XzCheckCrc32{C.Crc32Spec.start(C.crc32.spec())}}
    case 4n:
      Some{XzCheckCrc64{C.Crc64Spec.start(C.crc64_xz.spec())}}
    case 10n:
      Some{XzCheckSha256{Nil{}}}
    case _:
      None{}

def XzCheck.start(id: U32) -> Maybe<&2, XzCheck>:
  XzCheck.start.go(U32.to_nat(id))

# More data
def XzCheck.update(c: XzCheck, o: B.Octets) -> XzCheck:
  match c:
    case XzCheckNone{}:
      XzCheckNone{}
    case XzCheckCrc32{reg}:
      XzCheckCrc32{C.Crc32Spec.update(C.crc32.spec(), reg, o)}
    case XzCheckCrc64{reg}:
      XzCheckCrc64{C.Crc64Spec.update(C.crc64_xz.spec(), reg, o)}
    case XzCheckSha256{pieces}:
      XzCheckSha256{Con{o, pieces}}

# The check field, as the .xz file stores it
def XzCheck.finish(c: XzCheck) -> B.Octets:
  match c:
    case XzCheckNone{}:
      B.Octets.empty()
    case XzCheckCrc32{reg}:
      B.Octets.le32(C.Crc32Spec.finish(C.crc32.spec(), reg))
    case XzCheckCrc64{reg}:
      B.Octets.le64(C.Crc64Spec.finish(C.crc64_xz.spec(), reg))
    case XzCheckSha256{pieces}:
      B.Octets.of_list(Sha.sha256_bytes(B.Octets.to_list(B.Octets.concat(List.reverse(&2, B.Octets, pieces)))))

# The check field of type id over the whole of o, if id is supported
def XzCheck.compute.go(m: Maybe<&2, XzCheck>, o: B.Octets) -> Maybe<&2, B.Octets>:
  match m:
    case Some{c}:
      Some{XzCheck.finish(XzCheck.update(c, o))}
    case None{}:
      None{}

def XzCheck.compute(id: U32, o: B.Octets) -> Maybe<&2, B.Octets>:
  XzCheck.compute.go(XzCheck.start(id), o)
