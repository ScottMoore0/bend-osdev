# FIPS 197 (2001) Appendix C: C.1 (AES-128) decryption, C.2 (AES-192) and
# C.3 (AES-256) both ways, run compiled (C.1's encryption is a law,
# aes128_fips197_c1). The checker evaluates AES slowly and keeps what it
# evaluates, so these are not laws.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./aes.bend as X

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
    IO.print("aes192_fips197_c2 " ++ res(Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.encrypt(k, M.CmBlock{1122867, 1146447479, 2291772091, 3437096703})), X.CmAes.key192(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23])))))
    IO.print("aes192_fips197_c2_inverse " ++ res(Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.decrypt(k, M.CmBlock{3718872228, 2253184992, 1856991392, 3960304017})), X.CmAes.key192(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23])))))
    IO.print("aes256_fips197_c3 " ++ res(Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.encrypt(k, M.CmBlock{1122867, 1146447479, 2291772091, 3437096703})), X.CmAes.key256(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])))))
    IO.print("aes256_fips197_c3_inverse " ++ res(Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.decrypt(k, M.CmBlock{2393028554, 1365722559, 3942402448, 1263100041})), X.CmAes.key256(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])))))

#|aes128_fips197_c1_inverse 00112233445566778899aabbccddeeff
#|aes192_fips197_c2 dda97ca4864cdfe06eaf70a0ec0d7191
#|aes192_fips197_c2_inverse 00112233445566778899aabbccddeeff
#|aes256_fips197_c3 8ea2b7ca516745bfeafc49904b496089
#|aes256_fips197_c3_inverse 00112233445566778899aabbccddeeff
