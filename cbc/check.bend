# CBC over a toy permutation (below): the block and byte layers both ways,
# padding, and the refusals; and 32 KB through CBC and back. The
# specification's vectors (SP 800-38A F.2) run over AES in
# bend-osdev-aes-modes' check.bend.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./cbc.bend as C

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
  +b1 : M.CmBlock = M.CmBlock{1122867, 1146447479, 2291772091, 3437096703}
  +b2 : M.CmBlock = M.CmBlock{1, 2, 3, 4}
  +m48 = msg(48n)
  +m21 = msg(21n)
  +big = msg(32768n)
  do IO<Unit>:
    IO.print("cbc_blocks " ++ hexs(C.Cbc.encrypt_blocks(~M.CmBlock, ~toy.enc, key(), key2(), [b1, b2])))
    IO.print("cbc_blocks_back " ++ hexs(C.Cbc.decrypt_blocks(~M.CmBlock, ~toy.dec, key(), key2(), C.Cbc.encrypt_blocks(~M.CmBlock, ~toy.enc, key(), key2(), [b1, b2]))))
    IO.print("cbc_enc " ++ res(C.Cbc.encrypt(~M.CmBlock, ~toy.enc, key(), iv(), m48)))
    IO.print("cbc_back " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.Cbc.encrypt(~M.CmBlock, ~toy.enc, key(), iv(), m48), c => C.Cbc.decrypt(~M.CmBlock, ~toy.dec, key(), iv(), c)), m48))
    IO.print("cbc_padded_enc " ++ res(C.Cbc.encrypt_padded(~M.CmBlock, ~toy.enc, key(), iv(), m21)))
    IO.print("cbc_padded_back " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.Cbc.encrypt_padded(~M.CmBlock, ~toy.enc, key(), iv(), m21), c => C.Cbc.decrypt_padded(~M.CmBlock, ~toy.dec, key(), iv(), c)), m21))
    IO.print("cbc_padded_empty_back " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.Cbc.encrypt_padded(~M.CmBlock, ~toy.enc, key(), iv(), B.Octets.empty()), c => C.Cbc.decrypt_padded(~M.CmBlock, ~toy.dec, key(), iv(), c)), B.Octets.empty()))
    IO.print("cbc_not_whole_blocks " ++ res(C.Cbc.encrypt(~M.CmBlock, ~toy.enc, key(), iv(), msg(17n))))
    IO.print("cbc_short_iv " ++ res(C.Cbc.encrypt(~M.CmBlock, ~toy.enc, key(), B.Octets.take(15n, iv()), m48)))
    IO.print("cbc_padded_empty_ciphertext " ++ res(C.Cbc.decrypt_padded(~M.CmBlock, ~toy.dec, key(), iv(), B.Octets.empty())))
    IO.print("cbc_bad_padding " ++ res(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.Cbc.encrypt(~M.CmBlock, ~toy.enc, key(), iv(), B.Octets.zeros(16n)), c => C.Cbc.decrypt_padded(~M.CmBlock, ~toy.dec, key(), iv(), c))))
    IO.print("cbc_32k " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.Cbc.encrypt(~M.CmBlock, ~toy.enc, key(), iv(), big), c => C.Cbc.decrypt(~M.CmBlock, ~toy.dec, key(), iv(), c)), big))

#|cbc_blocks 57427568df9fd9bbc20c946add88ff22debc9cde4ba75986235445be21164779
#|cbc_blocks_back 00112233445566778899aabbccddeeff00000001000000020000000300000004
#|cbc_enc 581a5d37558aaff7f1053e55b60b5efd353eca1da279d0466c19820c40db694db0973410cb906af02c739db90187eab3
#|cbc_back True
#|cbc_padded_enc 6c64ae723fb10a45c3ff96b28a71fe7552994429415f50567fa64fe609a2e82c
#|cbc_padded_back True
#|cbc_padded_empty_back True
#|cbc_not_whole_blocks fail CmNotBlockMultiple
#|cbc_short_iv fail CmBadIvLength
#|cbc_padded_empty_ciphertext fail CmTooShort
#|cbc_bad_padding fail CmBadPadding
#|cbc_32k True
