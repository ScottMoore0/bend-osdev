# PKCS #7 padding (RFC 5652, 6.3): padding to 16 and to 8 bytes, unpadding
# back, and every refusal: bad padding, a bad block size, a padded message
# that is not whole blocks, and an empty one.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./pkcs7.bend as P

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

# whether r is m
def back(r: Result<&2, &2, M.CmError, B.Octets>, +m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail " ++ err(e)
    case Done{o}:
      Bool.show(B.Octets.is_eq(o, m))

# n pseudo-random bytes (a linear congruential generator)
def bytes.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bytes.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def msg(n: Nat) -> B.Octets:
  B.Octets.of_list(bytes.go(n, 7, Nil{}))

def iv() -> B.Octets:
  B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])

def main() -> IO(Unit):
  +m15 = msg(15n)
  +m1000 = msg(1000n)
  do IO<Unit>:
    IO.print("pad_16_empty " ++ res(P.Pkcs7.pad(16n, B.Octets.empty())))
    IO.print("pad_16_15 " ++ res(P.Pkcs7.pad(16n, m15)))
    IO.print("pad_8_5 " ++ res(P.Pkcs7.pad(8n, msg(5n))))
    IO.print("unpad_16_15 " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, P.Pkcs7.pad(16n, m15), c => P.Pkcs7.unpad(16n, c)), m15))
    IO.print("unpad_255_1000 " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, P.Pkcs7.pad(255n, m1000), c => P.Pkcs7.unpad(255n, c)), m1000))
    IO.print("pad_0 " ++ res(P.Pkcs7.pad(0n, m15)))
    IO.print("pad_256 " ++ res(P.Pkcs7.pad(256n, m15)))
    IO.print("unpad_zero " ++ res(P.Pkcs7.unpad(16n, B.Octets.append(m15, B.Octets.of_list([0])))))
    IO.print("unpad_mixed " ++ res(P.Pkcs7.unpad(16n, B.Octets.append(B.Octets.take(13n, m15), B.Octets.of_list([2, 3, 3])))))
    IO.print("unpad_not_whole " ++ res(P.Pkcs7.unpad(16n, m15)))
    IO.print("unpad_empty " ++ res(P.Pkcs7.unpad(16n, B.Octets.empty())))

#|pad_16_empty 10101010101010101010101010101010
#|pad_16_15 ed12be13cda1312e22251392744e6c01
#|pad_8_5 1392744e6c030303
#|unpad_16_15 True
#|unpad_255_1000 True
#|pad_0 fail CmBadBlockSize
#|pad_256 fail CmBadBlockSize
#|unpad_zero fail CmBadPadding
#|unpad_mixed fail CmBadPadding
#|unpad_not_whole fail CmNotBlockMultiple
#|unpad_empty fail CmTooShort
