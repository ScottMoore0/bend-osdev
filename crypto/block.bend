# The block-cipher interface.
#
# A block cipher (template arguments, in this order):
#   ~K: Data                                    its key schedule
#   ~Blk: Data                                  a block
#   ~bsize: Nat                                 the block size in bytes
#   ~key: B.Octets -> Result<&2, &2, CrError, K>
#                                               the key schedule of a raw
#                                               key, refusing a key of a
#                                               length the cipher does not
#                                               take (CrBadKeyLength{got})
#   ~enc: K -> Blk -> Blk                       encrypt one block
#   ~dec: K -> Blk -> Blk                       decrypt one block
# and its block format, the bytes of a block:
#   ~blk_of: B.Octets -> Maybe<&2, Blk>         bsize bytes as a block (None
#                                               for any other length)
#   ~blk_to: Blk -> B.Octets                    the bsize bytes of a block
#   ~bxor: Blk -> Blk -> Blk                    two blocks XORed
# A generic algorithm takes only the arguments it uses (CBC encryption: ~K,
# ~Blk, ~enc, ~bxor). A value of K is only ever made by ~key, so every K is a
# valid key, and every value of Blk is a block.
#
# Laws, for every key schedule and block (README.md, "Laws"):
#   round_trip       dec(k, enc(k, b)) == b
#   round_trip_dual  enc(k, dec(k, b)) == b   (the cipher is a permutation;
#                                             where the cipher proves it)
#   format           blk_of(blk_to(b)) == Some{b}
#   xor              bxor(bxor(a, b), b) == a
#   key_length       a key of a length the cipher does not take is refused
#
# The formats of the existing ciphers: inst_cm.bend (cipher-modes' 128-bit
# CmBlock) and inst_lc.bend (legacy-ciphers' 64-bit LcBlock64). Modes over
# any block cipher are in modes.bend.
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

def cr.blk.enc(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_to: Blk -> B.Octets, m: Maybe<&2, Blk>, +k: K, +n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match m:
    case None{}:
      Fail{Cr.CrBadBlockSize{n}}
    case Some{b}:
      Done{blk_to(enc(k, b))}

# One block of bytes encrypted (CrBadBlockSize for another length)
def CrBlockCipher.encrypt_octets(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +o: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cr.blk.enc(~K, ~Blk, ~enc, ~blk_to, blk_of(o), k, B.Octets.len(o))

# One block of bytes decrypted
def CrBlockCipher.decrypt_octets(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +o: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cr.blk.enc(~K, ~Blk, ~dec, ~blk_to, blk_of(o), k, B.Octets.len(o))

# The key schedule of a raw key, then one block of bytes encrypted
def CrBlockCipher.encrypt_with(~K: Data, ~Blk: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, key_o: B.Octets, +o: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, K, B.Octets, key(key_o), k => CrBlockCipher.encrypt_octets(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, o))
