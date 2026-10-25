# XTS over a toy permutation (below): whole blocks and ciphertext
# stealing both ways, multiplication by alpha, sector numbers, and the
# refusals; and 32 KB and 5 bytes through XTS and back. IEEE 1619's vectors
# run over AES in bend-osdev-aes-modes' check.bend.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../mode-core/mode-core.bend as M
import ./xts.bend as T

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

# A toy permutation of blocks, NOT a cipher: the words rotated, then XOR
# with the key block. Enough to run the mode's code paths (encryption and
# decryption differ, so mixing them up shows); the mode is tested against
# its specification over AES in bend-osdev-aes-modes (the specifications'
# vectors) and in ref/ (against Python's cryptography).
def toy.rot(b: M.CmBlock) -> M.CmBlock:
  match b:
    case M.CmBlock{w0, w1, w2, w3}:
      M.CmBlock{w1, w2, w3, w0}

def toy.unrot(b: M.CmBlock) -> M.CmBlock:
  match b:
    case M.CmBlock{w0, w1, w2, w3}:
      M.CmBlock{w3, w0, w1, w2}

def toy.enc(k: M.CmBlock, b: M.CmBlock) -> M.CmBlock:
  M.CmBlock.xor(k, toy.rot(b))

def toy.dec(k: M.CmBlock, c: M.CmBlock) -> M.CmBlock:
  toy.unrot(M.CmBlock.xor(k, c))

def key() -> M.CmBlock:
  M.CmBlock{19088743, 2309737967, 4275878552, 1985229328}

def key2() -> M.CmBlock:
  M.CmBlock{2882400001, 305419896, 3735928559, 4027432973}

def hexs(bs: List<&2, M.CmBlock>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{b, t}:
      M.CmBlock.hex(b) ++ hexs(t)

def main() -> IO(Unit):
  +m32 = msg(32n)
  +m21 = msg(21n)
  +big = msg(32773n)
  do IO<Unit>:
    IO.print("mul_alpha " ++ M.CmBlock.hex(T.Xts.mul_alpha(M.CmBlock{2147483648, 0, 0, 1})))
    IO.print("tweak " ++ M.CmBlock.hex(T.Xts.tweak(~M.CmBlock, ~toy.enc, key2(), M.CmBlock{1, 2, 3, 4})))
    IO.print("xts_blocks_back " ++ hexs(T.Xts.decrypt_blocks(~M.CmBlock, ~toy.dec, key(), key2(), T.Xts.encrypt_blocks(~M.CmBlock, ~toy.enc, key(), key2(), [key(), M.CmBlock.zero()]))))
    IO.print("xts_enc " ++ res(T.Xts.encrypt(~M.CmBlock, ~toy.enc, key(), key2(), iv(), m32)))
    IO.print("xts_back " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.Xts.encrypt(~M.CmBlock, ~toy.enc, key(), key2(), iv(), m32), c => T.Xts.decrypt(~M.CmBlock, ~toy.enc, ~toy.dec, key(), key2(), iv(), c)), m32))
    IO.print("xts_steal_enc " ++ res(T.Xts.encrypt(~M.CmBlock, ~toy.enc, key(), key2(), iv(), m21)))
    IO.print("xts_steal_back " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.Xts.encrypt(~M.CmBlock, ~toy.enc, key(), key2(), iv(), m21), c => T.Xts.decrypt(~M.CmBlock, ~toy.enc, ~toy.dec, key(), key2(), iv(), c)), m21))
    IO.print("xts_sector " ++ B.Octets.hex(T.Xts.sector(W.W64.from_parts(0, 2591577138))))
    IO.print("xts_short " ++ res(T.Xts.encrypt(~M.CmBlock, ~toy.enc, key(), key2(), iv(), msg(15n))))
    IO.print("xts_bad_tweak " ++ res(T.Xts.encrypt(~M.CmBlock, ~toy.enc, key(), key2(), B.Octets.take(15n, iv()), m32)))
    IO.print("xts_32k_5 " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.Xts.encrypt(~M.CmBlock, ~toy.enc, key(), key2(), iv(), big), c => T.Xts.decrypt(~M.CmBlock, ~toy.enc, ~toy.dec, key(), key2(), iv(), c)), big))

#|mul_alpha 00010000000000000000000000000002
#|tweak abcdef031234567bdeadbeebf00dc00c
#|xts_blocks_back 0123456789abcdeffedcba987654321000000000000000000000000000000000
#|xts_enc d541d09f9be10280f8beae1f47051f7278058fbd37b231db29f011288b3177be
#|xts_back True
#|xts_steal_enc 07edc251f4cefe9b6e30883ada4e114edd941d00ff
#|xts_steal_back True
#|xts_sector 3254789a000000000000000000000000
#|xts_short fail CmTooShort
#|xts_bad_tweak fail CmBadTweakLength
#|xts_32k_5 True
