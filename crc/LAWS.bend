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
import ./table.bend as T

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

# The table-driven fast path (table.bend) gives the same check values, and
# agrees with the reference on a longer input. Vectors only: a law for every
# input would need lemmas about Array's internals.

law fast_crc32c:
  {T.Crc32Spec.compute_fast(C.crc32c.spec(), B.Octets.of_string("123456789")) == 3808858755 : U32}

law fast_crc16:
  {T.Crc32Spec.compute_fast(C.crc16.spec(), B.Octets.of_string("123456789")) == 47933 : U32}

law fast_crc_t10dif:
  {T.Crc32Spec.compute_fast(C.crc_t10dif.spec(), B.Octets.of_string("123456789")) == 53467 : U32}

law fast_crc64_ecma:
  {T.Crc64Spec.compute_fast(C.crc64_ecma.spec(), B.Octets.of_string("123456789")) == W.W64.from_parts(1816190815, 189363015) : W.W64}

law fast_crc64_xz:
  {T.Crc64Spec.compute_fast(C.crc64_xz.spec(), B.Octets.of_string("123456789")) == W.W64.from_parts(2573060539, 3742972410) : W.W64}

law fast_agrees_crc32c:
  {T.Crc32Spec.compute_fast(C.crc32c.spec(), B.Octets.of_string("bend-osdev: componentised, changeable, proved")) == C.crc32c(B.Octets.of_string("bend-osdev: componentised, changeable, proved")) : U32}

# More named CRCs from the reveng catalogue, with their check values: CRC-4/
# G-704 0x7, CRC-7/MMC 0x75, CRC-8/SMBUS 0xF4, CRC-8/I-432-1 0xA1,
# CRC-8/MAXIM-DOW 0xA1, CRC-8/DVB-S2 0xBC, CRC-8/AUTOSAR 0xDF, CRC-16/KERMIT
# 0x2189, CRC-16/IBM-3740 0x29B1, CRC-16/XMODEM 0x31C3

law check_crc4_itu:
  {C.crc4_itu(B.Octets.of_string("123456789")) == 7 : U32}

law check_crc7_mmc:
  {C.crc7_mmc(B.Octets.of_string("123456789")) == 117 : U32}

law check_crc8_smbus:
  {C.crc8_smbus(B.Octets.of_string("123456789")) == 244 : U32}

law check_crc8_itu:
  {C.crc8_itu(B.Octets.of_string("123456789")) == 161 : U32}

law check_crc8_maxim:
  {C.crc8_maxim(B.Octets.of_string("123456789")) == 161 : U32}

law check_crc8_dvb_s2:
  {C.crc8_dvb_s2(B.Octets.of_string("123456789")) == 188 : U32}

law check_crc8_autosar:
  {C.crc8_autosar(B.Octets.of_string("123456789")) == 223 : U32}

law check_crc16_kermit:
  {C.crc16_kermit(B.Octets.of_string("123456789")) == 8585 : U32}

law check_crc16_ccitt_false:
  {C.crc16_ccitt_false(B.Octets.of_string("123456789")) == 10673 : U32}

law check_crc16_xmodem:
  {C.crc16_xmodem(B.Octets.of_string("123456789")) == 12739 : U32}

law fast_crc7_mmc:
  {T.Crc32Spec.compute_fast(C.crc7_mmc.spec(), B.Octets.of_string("123456789")) == 117 : U32}

law fast_crc4_itu:
  {T.Crc32Spec.compute_fast(C.crc4_itu.spec(), B.Octets.of_string("123456789")) == 7 : U32}

law fast_crc16_xmodem:
  {T.Crc32Spec.compute_fast(C.crc16_xmodem.spec(), B.Octets.of_string("123456789")) == 12739 : U32}
