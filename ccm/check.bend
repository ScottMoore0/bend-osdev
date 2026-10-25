# CCM over a toy permutation (below): encryption, decryption, a tampered
# tag refused, an empty message, and the refused parameters; and 32 KB
# through CCM and back. RFC 3610's packets run over AES in
# bend-osdev-aes-modes' check.bend.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./ccm.bend as CC

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

def nonce() -> B.Octets:
  B.Octets.of_list([0, 0, 0, 3, 2, 1, 0, 160, 161, 162, 163, 164, 165])

def aad() -> B.Octets:
  B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7])

def tamper(r: Result<&2, &2, M.CmError, B.Octets>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+c}:
      Done{B.Octets.append(B.Octets.take(Nat.sub(B.Octets.len(c), 1n), c), B.Octets.of_list([0]))}

def main() -> IO(Unit):
  +p = msg(23n)
  +big = msg(32768n)
  do IO<Unit>:
    IO.print("ccm_enc " ++ res(CC.Ccm.encrypt(~M.CmBlock, ~toy.enc, key(), 8n, nonce(), aad(), p)))
    IO.print("ccm_back " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CC.Ccm.encrypt(~M.CmBlock, ~toy.enc, key(), 8n, nonce(), aad(), p), c => CC.Ccm.decrypt(~M.CmBlock, ~toy.enc, key(), 8n, nonce(), aad(), c)), p))
    IO.print("ccm_tampered " ++ res(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, tamper(CC.Ccm.encrypt(~M.CmBlock, ~toy.enc, key(), 8n, nonce(), aad(), p)), c => CC.Ccm.decrypt(~M.CmBlock, ~toy.enc, key(), 8n, nonce(), aad(), c))))
    IO.print("ccm_empty_back " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CC.Ccm.encrypt(~M.CmBlock, ~toy.enc, key(), 16n, nonce(), B.Octets.empty(), B.Octets.empty()), c => CC.Ccm.decrypt(~M.CmBlock, ~toy.enc, key(), 16n, nonce(), B.Octets.empty(), c)), B.Octets.empty()))
    IO.print("ccm_bad_tag_length " ++ res(CC.Ccm.encrypt(~M.CmBlock, ~toy.enc, key(), 7n, nonce(), aad(), p)))
    IO.print("ccm_bad_nonce_length " ++ res(CC.Ccm.encrypt(~M.CmBlock, ~toy.enc, key(), 8n, B.Octets.take(6n, nonce()), aad(), p)))
    IO.print("ccm_32k " ++ back(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CC.Ccm.encrypt(~M.CmBlock, ~toy.enc, key(), 8n, nonce(), aad(), big), c => CC.Ccm.decrypt(~M.CmBlock, ~toy.enc, key(), 8n, nonce(), aad(), c)), big))

#|ccm_enc d502b843e76c060eb76b048abaf5033e200457f55d4403c27d9674e7a15f63
#|ccm_back True
#|ccm_tampered fail CmTagMismatch
#|ccm_empty_back True
#|ccm_bad_tag_length fail CmBadTagLength
#|ccm_bad_nonce_length fail CmBadNonceLength
#|ccm_32k True
