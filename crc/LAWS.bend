# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input: a CRC computed in pieces is the CRC of the
# whole, for every parameter set, at both word sizes. The register passes from
# one piece to the next through update; start and finish apply once.
#
# Vectors: every named CRC gives the reveng catalogue's check value on the
# nine bytes "123456789".
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./crc.bend as C

law streaming32:
  for spec: C.Crc32Spec
  for c: U32
  for +a: B.Octets
  for +b: B.Octets
  {C.Crc32Spec.update(spec, c, B.Octets.append(a, b)) == C.Crc32Spec.update(spec, C.Crc32Spec.update(spec, c, a), b) : U32}

law streaming64:
  for spec: C.Crc64Spec
  for c: W.W64
  for +a: B.Octets
  for +b: B.Octets
  {C.Crc64Spec.update(spec, c, B.Octets.append(a, b)) == C.Crc64Spec.update(spec, C.Crc64Spec.update(spec, c, a), b) : W.W64}

# check values (reveng): 0xE3069283, 0xCBF43926, 0xBB3D, 0xD0DB
law check_crc32c:
  {C.crc32c(B.Octets.of_string("123456789")) == 3808858755 : U32}

law check_crc32:
  {C.crc32(B.Octets.of_string("123456789")) == 3421780262 : U32}

law check_crc16:
  {C.crc16(B.Octets.of_string("123456789")) == 47933 : U32}

law check_crc_t10dif:
  {C.crc_t10dif(B.Octets.of_string("123456789")) == 53467 : U32}

# 0x6C40DF5F0B497347, 0x995DC9BBDF1939FA, 0xAE8B14860A799888
law check_crc64_ecma:
  {C.crc64_ecma(B.Octets.of_string("123456789")) == W.W64.from_parts(1816190815, 189363015) : W.W64}

law check_crc64_xz:
  {C.crc64_xz(B.Octets.of_string("123456789")) == W.W64.from_parts(2573060539, 3742972410) : W.W64}

law check_crc64_nvme:
  {C.crc64_nvme(B.Octets.of_string("123456789")) == W.W64.from_parts(2928350342, 175741064) : W.W64}

# the empty input: init XOR xorout
law empty_crc32c:
  {C.crc32c(B.Octets.empty()) == 0 : U32}

law empty_crc_t10dif:
  {C.crc_t10dif(B.Octets.empty()) == 0 : U32}
