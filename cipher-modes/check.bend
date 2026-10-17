# The specifications' vectors that LAWS.bend cannot hold, run compiled: the
# checker evaluates AES slowly and keeps what it evaluates, so a proof file
# with more than a few AES blocks runs out of memory (see the README). Here:
# FIPS 197 C.1 and C.3 (both directions), NIST SP 800-38A F.2.1, F.2.2, F.2.5
# and F.2.6 (CBC), IEEE 1619 vectors 1, 2 and 15 to 18 (XTS, with ciphertext
# stealing), RFC 3610 packets 1 to 3 (CCM, with decryption and a tampered
# tag) and RFC 4493 examples 1 to 4 and K2 (CMAC).
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M
import ./aes.bend as X
import ./cmac.bend as CM
import ./aes_modes.bend as D

def err(e: M.CmError) -> String:
  match e:
    case M.CmBadKeyLength{n}:
      "CmBadKeyLength"
    case M.CmBadIvLength{n}:
      "CmBadIvLength"
    case M.CmBadTweakLength{n}:
      "CmBadTweakLength"
    case M.CmBadNonceLength{n}:
      "CmBadNonceLength"
    case M.CmBadTagLength{n}:
      "CmBadTagLength"
    case M.CmBadBlockSize{n}:
      "CmBadBlockSize"
    case M.CmNotBlockMultiple{n}:
      "CmNotBlockMultiple"
    case M.CmTooShort{n}:
      "CmTooShort"
    case M.CmTooLong{n}:
      "CmTooLong"
    case M.CmBadPadding{}:
      "CmBadPadding"
    case M.CmTagMismatch{}:
      "CmTagMismatch"

def res(r: Result<&2, &2, M.CmError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ err(e)
    case Done{v}:
      B.Octets.hex(v)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("aes128_fips197_c1_inverse " ++ res(Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.decrypt(k, M.CmBlock{1774510296, 1786446896, 3637360512, 1890895194})), X.CmAes.key128(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])))))
    IO.print("aes256_fips197_c3 " ++ res(Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.encrypt(k, M.CmBlock{1122867, 1146447479, 2291772091, 3437096703})), X.CmAes.key256(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])))))
    IO.print("aes256_fips197_c3_inverse " ++ res(Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.decrypt(k, M.CmBlock{2393028554, 1365722559, 3942402448, 1263100041})), X.CmAes.key256(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])))))
    IO.print("cbc_sp800_38a_f21 " ++ res(D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42, 174, 45, 138, 87, 30, 3, 172, 156, 158, 183, 111, 172, 69, 175, 142, 81, 48, 200, 28, 70, 163, 92, 228, 17, 229, 251, 193, 25, 26, 10, 82, 239, 246, 159, 36, 69, 223, 79, 155, 23, 173, 43, 65, 123, 230, 108, 55, 16]))))
    IO.print("cbc_sp800_38a_f22 " ++ res(D.CmAes.cbc_decrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([118, 73, 171, 172, 129, 25, 178, 70, 206, 233, 142, 155, 18, 233, 25, 125, 80, 134, 203, 155, 80, 114, 25, 238, 149, 219, 17, 58, 145, 118, 120, 178, 115, 190, 214, 184, 227, 193, 116, 59, 113, 22, 230, 158, 34, 34, 149, 22, 63, 241, 202, 161, 104, 31, 172, 9, 18, 14, 202, 48, 117, 134, 225, 167]))))
    IO.print("cbc_sp800_38a_f25 " ++ res(D.CmAes.cbc_encrypt(B.Octets.of_list([96, 61, 235, 16, 21, 202, 113, 190, 43, 115, 174, 240, 133, 125, 119, 129, 31, 53, 44, 7, 59, 97, 8, 215, 45, 152, 16, 163, 9, 20, 223, 244]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42, 174, 45, 138, 87, 30, 3, 172, 156, 158, 183, 111, 172, 69, 175, 142, 81, 48, 200, 28, 70, 163, 92, 228, 17, 229, 251, 193, 25, 26, 10, 82, 239, 246, 159, 36, 69, 223, 79, 155, 23, 173, 43, 65, 123, 230, 108, 55, 16]))))
    IO.print("cbc_sp800_38a_f26 " ++ res(D.CmAes.cbc_decrypt(B.Octets.of_list([96, 61, 235, 16, 21, 202, 113, 190, 43, 115, 174, 240, 133, 125, 119, 129, 31, 53, 44, 7, 59, 97, 8, 215, 45, 152, 16, 163, 9, 20, 223, 244]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([245, 140, 76, 4, 214, 229, 241, 186, 119, 158, 171, 251, 95, 123, 251, 214, 156, 252, 78, 150, 126, 219, 128, 141, 103, 159, 119, 123, 198, 112, 44, 125, 57, 242, 51, 105, 169, 217, 186, 207, 165, 48, 226, 99, 4, 35, 20, 97, 178, 235, 5, 226, 195, 155, 233, 252, 218, 108, 25, 7, 140, 106, 157, 27]))))
    IO.print("cbc_padded_f21 " ++ res(Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => B.Octets.take(64n, c), D.CmAes.cbc_encrypt_padded(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42, 174, 45, 138, 87, 30, 3, 172, 156, 158, 183, 111, 172, 69, 175, 142, 81, 48, 200, 28, 70, 163, 92, 228, 17, 229, 251, 193, 25, 26, 10, 82, 239, 246, 159, 36, 69, 223, 79, 155, 23, 173, 43, 65, 123, 230, 108, 55, 16])))))
    IO.print("xts_ieee1619_v1 " ++ res(D.CmAes.xts_encrypt(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))
    IO.print("xts_ieee1619_v2 " ++ res(D.CmAes.xts_encrypt(B.Octets.of_list([17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34]), B.Octets.of_list([51, 51, 51, 51, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68]))))
    IO.print("xts_ieee1619_v2_inverse " ++ res(D.CmAes.xts_decrypt(B.Octets.of_list([17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34]), B.Octets.of_list([51, 51, 51, 51, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([196, 84, 24, 94, 106, 22, 147, 110, 57, 51, 64, 56, 172, 239, 131, 139, 251, 24, 111, 255, 116, 128, 173, 196, 40, 147, 130, 236, 214, 211, 148, 240]))))
    IO.print("xts_ieee1619_v15 " ++ res(D.CmAes.xts_encrypt(B.Octets.of_list([255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176]), B.Octets.of_list([154, 120, 86, 52, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]))))
    IO.print("xts_ieee1619_v15_inverse " ++ res(D.CmAes.xts_decrypt(B.Octets.of_list([255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176]), B.Octets.of_list([154, 120, 86, 52, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([108, 22, 37, 219, 70, 113, 82, 45, 61, 117, 153, 96, 29, 231, 202, 9, 237]))))
    IO.print("xts_ieee1619_v16 " ++ res(D.CmAes.xts_encrypt(B.Octets.of_list([255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176]), B.Octets.of_list([154, 120, 86, 52, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]))))
    IO.print("xts_ieee1619_v17 " ++ res(D.CmAes.xts_encrypt(B.Octets.of_list([255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176]), B.Octets.of_list([154, 120, 86, 52, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]))))
    IO.print("xts_ieee1619_v18 " ++ res(D.CmAes.xts_encrypt(B.Octets.of_list([255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176]), B.Octets.of_list([154, 120, 86, 52, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]))))
    IO.print("xts_ieee1619_v18_inverse " ++ res(D.CmAes.xts_decrypt(B.Octets.of_list([255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176]), B.Octets.of_list([154, 120, 86, 52, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([157, 132, 200, 19, 247, 25, 170, 44, 123, 227, 246, 97, 113, 199, 197, 194, 237, 191, 157, 172]))))
    IO.print("ccm_rfc3610_p1 " ++ res(D.CmAes.ccm_encrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 8n, B.Octets.of_list([0, 0, 0, 3, 2, 1, 0, 160, 161, 162, 163, 164, 165]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]))))
    IO.print("ccm_rfc3610_p1_inverse " ++ res(D.CmAes.ccm_decrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 8n, B.Octets.of_list([0, 0, 0, 3, 2, 1, 0, 160, 161, 162, 163, 164, 165]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([88, 140, 151, 154, 97, 198, 99, 210, 240, 102, 208, 194, 192, 249, 137, 128, 109, 95, 107, 97, 218, 195, 132, 23, 232, 209, 44, 253, 249, 38, 224]))))
    IO.print("ccm_rfc3610_p1_tampered " ++ res(D.CmAes.ccm_decrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 8n, B.Octets.of_list([0, 0, 0, 3, 2, 1, 0, 160, 161, 162, 163, 164, 165]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([88, 140, 151, 154, 97, 198, 99, 210, 240, 102, 208, 194, 192, 249, 137, 128, 109, 95, 107, 97, 218, 195, 132, 23, 232, 209, 44, 253, 249, 38, 225]))))
    IO.print("ccm_rfc3610_p2 " ++ res(D.CmAes.ccm_encrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 8n, B.Octets.of_list([0, 0, 0, 4, 3, 2, 1, 160, 161, 162, 163, 164, 165]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]))))
    IO.print("ccm_rfc3610_p3 " ++ res(D.CmAes.ccm_encrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 8n, B.Octets.of_list([0, 0, 0, 5, 4, 3, 2, 160, 161, 162, 163, 164, 165]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]))))
    IO.print("cmac_rfc4493_ex1 " ++ res(D.CmAes.cmac(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([]))))
    IO.print("cmac_rfc4493_ex2 " ++ res(D.CmAes.cmac(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42]))))
    IO.print("cmac_rfc4493_ex3 " ++ res(D.CmAes.cmac(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42, 174, 45, 138, 87, 30, 3, 172, 156, 158, 183, 111, 172, 69, 175, 142, 81, 48, 200, 28, 70, 163, 92, 228, 17]))))
    IO.print("cmac_rfc4493_ex4 " ++ res(D.CmAes.cmac(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42, 174, 45, 138, 87, 30, 3, 172, 156, 158, 183, 111, 172, 69, 175, 142, 81, 48, 200, 28, 70, 163, 92, 228, 17, 229, 251, 193, 25, 26, 10, 82, 239, 246, 159, 36, 69, 223, 79, 155, 23, 173, 43, 65, 123, 230, 108, 55, 16]))))
    IO.print("cmac_rfc4493_k2 " ++ res(Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(CM.Cmac.subkey2(~X.CmAesKey, ~X.CmAes.encrypt, k)), X.CmAes.key128(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60])))))

#|aes128_fips197_c1_inverse 00112233445566778899aabbccddeeff
#|aes256_fips197_c3 8ea2b7ca516745bfeafc49904b496089
#|aes256_fips197_c3_inverse 00112233445566778899aabbccddeeff
#|cbc_sp800_38a_f21 7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b273bed6b8e3c1743b7116e69e222295163ff1caa1681fac09120eca307586e1a7
#|cbc_sp800_38a_f22 6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710
#|cbc_sp800_38a_f25 f58c4c04d6e5f1ba779eabfb5f7bfbd69cfc4e967edb808d679f777bc6702c7d39f23369a9d9bacfa530e26304231461b2eb05e2c39be9fcda6c19078c6a9d1b
#|cbc_sp800_38a_f26 6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710
#|cbc_padded_f21 7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b273bed6b8e3c1743b7116e69e222295163ff1caa1681fac09120eca307586e1a7
#|xts_ieee1619_v1 917cf69ebd68b2ec9b9fe9a3eadda692cd43d2f59598ed858c02c2652fbf922e
#|xts_ieee1619_v2 c454185e6a16936e39334038acef838bfb186fff7480adc4289382ecd6d394f0
#|xts_ieee1619_v2_inverse 4444444444444444444444444444444444444444444444444444444444444444
#|xts_ieee1619_v15 6c1625db4671522d3d7599601de7ca09ed
#|xts_ieee1619_v15_inverse 000102030405060708090a0b0c0d0e0f10
#|xts_ieee1619_v16 d069444b7a7e0cab09e24447d24deb1fedbf
#|xts_ieee1619_v17 e5df1351c0544ba1350b3363cd8ef4beedbf9d
#|xts_ieee1619_v18 9d84c813f719aa2c7be3f66171c7c5c2edbf9dac
#|xts_ieee1619_v18_inverse 000102030405060708090a0b0c0d0e0f10111213
#|ccm_rfc3610_p1 588c979a61c663d2f066d0c2c0f989806d5f6b61dac38417e8d12cfdf926e0
#|ccm_rfc3610_p1_inverse 08090a0b0c0d0e0f101112131415161718191a1b1c1d1e
#|ccm_rfc3610_p1_tampered fail CmTagMismatch
#|ccm_rfc3610_p2 72c91a36e135f8cf291ca894085c87e3cc15c439c9e43a3ba091d56e10400916
#|ccm_rfc3610_p3 51b1e5f44a197d1da46b0f8e2d282ae871e838bb64da8596574adaa76fbd9fb0c5
#|cmac_rfc4493_ex1 bb1d6929e95937287fa37d129b756746
#|cmac_rfc4493_ex2 070a16b46b4d4144f79bdd9dd04a287c
#|cmac_rfc4493_ex3 dfa66747de9ae63030ca32611497c827
#|cmac_rfc4493_ex4 51f0bebf7e3b9d92fc49741779363cfe
#|cmac_rfc4493_k2 f7ddac306ae266ccf90bc11ee46d513b
