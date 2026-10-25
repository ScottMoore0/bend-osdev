# Laws about the named defaults (aes-modes.bend): the modes with AES. The
# checker evaluates AES slowly and keeps what it evaluates, so only these
# vectors fit in its memory; every other vector of the specifications (all
# of SP 800-38A F.2.1, F.2.2, F.2.5 and F.2.6; IEEE 1619 vectors 2 and 15 to
# 18; RFC 3610 packets 1 to 3; RFC 4493 examples 2 to 4; and every
# decryption) runs compiled in check.bend. The modes' laws for every input
# are in their own packages (bend-osdev-cbc, -xts, -ccm, -cmac), and AES's
# round trip in bend-osdev-aes; bend-osdev-cm-instances states the mode laws
# at AES with no hypothesis.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ../aes/aes.bend as X
import ../cmac/cmac.bend as CM
import ./aes-modes.bend as D

# a key of a length AES-128 and AES-256 do not have is refused
law aes_bad_key_length:
  {D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42])) == Fail{M.CmBadKeyLength{15n}} : Result<&2, &2, M.CmError, B.Octets>}

# NIST SP 800-38A Appendix F.2.1, CBC-AES128: its first block
law cbc_sp800_38a_f21_block1:
  {D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42])) == Done{B.Octets.of_list([118, 73, 171, 172, 129, 25, 178, 70, 206, 233, 142, 155, 18, 233, 25, 125])} : Result<&2, &2, M.CmError, B.Octets>}

# the byte layer refuses a message that is not whole blocks, and a short IV
law cbc_not_whole_blocks:
  {D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42, 174])) == Fail{M.CmNotBlockMultiple{17n}} : Result<&2, &2, M.CmError, B.Octets>}

law cbc_short_iv:
  {D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42])) == Fail{M.CmBadIvLength{15n}} : Result<&2, &2, M.CmError, B.Octets>}

# a data unit shorter than a block is refused
law xts_short:
  {D.CmAes.xts_encrypt(B.Octets.of_list([255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176]), B.Octets.of_list([154, 120, 86, 52, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) == Fail{M.CmTooShort{15n}} : Result<&2, &2, M.CmError, B.Octets>}

# a tag of odd length, and a nonce of 6 bytes, are refused
law ccm_bad_tag_length:
  {D.CmAes.ccm_encrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 7n, B.Octets.of_list([0, 0, 0, 3, 2, 1, 0, 160, 161, 162, 163, 164, 165]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30])) == Fail{M.CmBadTagLength{7n}} : Result<&2, &2, M.CmError, B.Octets>}

law ccm_bad_nonce_length:
  {D.CmAes.ccm_encrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 8n, B.Octets.of_list([0, 0, 0, 3, 2, 1]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30])) == Fail{M.CmBadNonceLength{6n}} : Result<&2, &2, M.CmError, B.Octets>}

# RFC 4493 section 4: the AES-CMAC subkey K1
law cmac_rfc4493_k1:
  {Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(CM.Cmac.subkey1(~X.CmAesKey, ~X.CmAes.encrypt, k)), X.CmAes.key128(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]))) == Done{B.Octets.of_list([251, 238, 214, 24, 53, 113, 51, 102, 124, 133, 224, 143, 114, 54, 168, 222])} : Result<&2, &2, M.CmError, B.Octets>}
