# CRCs as hashes: bend-osdev-crc's CRC-32 family (any Crc32Spec: widths 8 to
# 32) and CRC-64 family (any Crc64Spec), through its streaming interface
# (start, update, finish; the bitwise reference engine). A CRC is not a
# cryptographic hash: these instances are for checksums, and for exercising
# the generic algorithms (HMAC, HKDF) over a second and third hash.
#
# The state is the register; the digest is the final value, big-endian (4
# bytes for CRC-32, 8 for CRC-64; a CRC narrower than 32 bits has leading
# zero bytes). The block size is a parameter of HMAC only (a CRC has none);
# 64 is the named default. The instance for the CRC-32 of spec:
#   ~U32, ~64n, ~4n, ~CrCrc32.init(~spec), ~CrCrc32.update(~spec),
#   ~CrCrc32.final(~spec), ~CrCrc32.digest(~spec)
# with spec C.crc32.spec(), C.crc32c.spec(), ...; for CRC-64:
#   ~W.W64, ~64n, ~8n, ~CrCrc64.init(~spec), ~CrCrc64.update(~spec),
#   ~CrCrc64.final(~spec), ~CrCrc64.digest(~spec)
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../crc/crc.bend as C

def CrCrc32.init(~spec: C.Crc32Spec) -> U32:
  C.Crc32Spec.start(spec)

def CrCrc32.update(~spec: C.Crc32Spec, c: U32, o: B.Octets) -> U32:
  C.Crc32Spec.update(spec, c, o)

def CrCrc32.final(~spec: C.Crc32Spec, c: U32) -> B.Octets:
  B.Octets.be32(C.Crc32Spec.finish(spec, c))

def CrCrc32.digest(~spec: C.Crc32Spec, o: B.Octets) -> B.Octets:
  CrCrc32.final(~spec, CrCrc32.update(~spec, CrCrc32.init(~spec), o))

def CrCrc64.init(~spec: C.Crc64Spec) -> W.W64:
  C.Crc64Spec.start(spec)

def CrCrc64.update(~spec: C.Crc64Spec, c: W.W64, o: B.Octets) -> W.W64:
  C.Crc64Spec.update(spec, c, o)

def CrCrc64.final(~spec: C.Crc64Spec, c: W.W64) -> B.Octets:
  B.Octets.be64(C.Crc64Spec.finish(spec, c))

def CrCrc64.digest(~spec: C.Crc64Spec, o: B.Octets) -> B.Octets:
  CrCrc64.final(~spec, CrCrc64.update(~spec, CrCrc64.init(~spec), o))
