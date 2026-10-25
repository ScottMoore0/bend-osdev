# mode-core on its own: a block's hex and byte forms, XOR, the round-trip
# hypothesis over a toy permutation, and the refusal of a byte string that
# is not 16 bytes. The modes' own packages test the modes.
import Base
import ../bytes/bytes.bend as B
import ./mode-core.bend as M

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

def maybe(m: Maybe<&2, M.CmBlock>) -> String:
  match m:
    case None{}:
      "none"
    case Some{b}:
      M.CmBlock.hex(b)

def main() -> IO(Unit):
  +b : M.CmBlock = M.CmBlock{1122867, 1146447479, 2291772091, 3437096703}
  do IO<Unit>:
    IO.print("zero " ++ M.CmBlock.hex(M.CmBlock.zero()))
    IO.print("block " ++ M.CmBlock.hex(b))
    IO.print("xor " ++ M.CmBlock.hex(M.CmBlock.xor(b, key())))
    IO.print("to_octets " ++ B.Octets.hex(M.CmBlock.to_octets(b)))
    IO.print("of_octets " ++ maybe(M.CmBlock.of_octets(M.CmBlock.to_octets(b))))
    IO.print("of_octets_15 " ++ maybe(M.CmBlock.of_octets(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]))))
    IO.print("dec_enc " ++ hexs(M.CmBlock.dec_enc(~M.CmBlock, ~toy.enc, ~toy.dec, key(), [b, key(), M.CmBlock.zero()])))

#|zero 00000000000000000000000000000000
#|block 00112233445566778899aabbccddeeff
#|xor 01326754cdfeab9876451023ba89dcef
#|to_octets 00112233445566778899aabbccddeeff
#|of_octets 00112233445566778899aabbccddeeff
#|of_octets_15 none
#|dec_enc 00112233445566778899aabbccddeeff0123456789abcdeffedcba987654321000000000000000000000000000000000
