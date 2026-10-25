# CMAC over a toy permutation (below): the subkeys, MACs of messages of
# no, one and several blocks, the streaming interface against the one-call
# MAC, and tag checks. RFC 4493's examples run over AES in
# bend-osdev-aes-modes' check.bend.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./cmac.bend as CM

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

def pieces(+m: B.Octets, +n: Nat) -> B.Octets:
  CM.Cmac.finish(~M.CmBlock, ~toy.enc, key(), CM.Cmac.update(~M.CmBlock, ~toy.enc, key(), CM.Cmac.update(~M.CmBlock, ~toy.enc, key(), CM.Cmac.start(), B.Octets.take(n, m)), B.Octets.drop(n, m)))

def main() -> IO(Unit):
  +m40 = msg(40n)
  do IO<Unit>:
    IO.print("dbl " ++ M.CmBlock.hex(CM.Cmac.dbl(M.CmBlock{2147483648, 0, 0, 1})))
    IO.print("subkey1 " ++ M.CmBlock.hex(CM.Cmac.subkey1(~M.CmBlock, ~toy.enc, key())))
    IO.print("subkey2 " ++ M.CmBlock.hex(CM.Cmac.subkey2(~M.CmBlock, ~toy.enc, key())))
    IO.print("cmac_empty " ++ B.Octets.hex(CM.Cmac.mac(~M.CmBlock, ~toy.enc, key(), B.Octets.empty())))
    IO.print("cmac_16 " ++ B.Octets.hex(CM.Cmac.mac(~M.CmBlock, ~toy.enc, key(), msg(16n))))
    IO.print("cmac_40 " ++ B.Octets.hex(CM.Cmac.mac(~M.CmBlock, ~toy.enc, key(), m40)))
    IO.print("cmac_pieces " ++ Bool.show(B.Octets.is_eq(pieces(m40, 13n), CM.Cmac.mac(~M.CmBlock, ~toy.enc, key(), m40))))
    IO.print("cmac_verify " ++ Bool.show(CM.Cmac.verify(~M.CmBlock, ~toy.enc, key(), m40, CM.Cmac.mac(~M.CmBlock, ~toy.enc, key(), m40))))
    IO.print("cmac_verify_other " ++ Bool.show(CM.Cmac.verify(~M.CmBlock, ~toy.enc, key(), m40, CM.Cmac.mac(~M.CmBlock, ~toy.enc, key(), msg(41n)))))

#|dbl 00000000000000000000000000000085
#|subkey1 02468acf13579bdffdb97530eca86420
#|subkey2 048d159e26af37bffb72ea61d950c840
#|cmac_empty 278c72d872d9278e278c72d8f2d9278e
#|cmac_16 01b97f895a309dcc800090d436ffaa61
#|cmac_40 e1f579f0bdb4662489f8ac919e28ea16
#|cmac_pieces True
#|cmac_verify True
#|cmac_verify_other False
