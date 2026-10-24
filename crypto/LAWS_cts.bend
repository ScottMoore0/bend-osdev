# The CBC-CS3 round trip (cts.bend): decryption undoes encryption, for every
# block cipher over one of the two block formats (inst_cm.bend's 128-bit
# CmBlock, legacy-ciphers' 64-bit LcBlock64), every key, IV and message. In
# a pair of its own (CONVENTIONS.md, Laws): the proofs rest on bytes' laws,
# legacy-ciphers' block64_octets_round_trip (so they take in legacy-ciphers'
# proofs) and PROOF_bytes.bend's lemmas, and on no other package's.
#
# The cipher's property is the hypothesis inv on lists of blocks (as
# cipher-modes' laws take it: README.md, "How the laws are stated"): each
# block encrypted and decrypted back is itself. An instance whose package
# proves dec(k, enc(k, b)) == b for every block (its <c>_block_round_trip)
# gives it for every list by induction.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../legacy-ciphers/legacy-ciphers.bend as L
import ./crypto.bend as Cr
import ./cts.bend as Ct
import ./inst_cm.bend as CM

# each block of xs encrypted under k and decrypted again
def crcts.dec_enc(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, +k: K, xs: List<&2, Blk>) -> List<&2, Blk>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{dec(k, enc(k, x)), crcts.dec_enc(~K, ~Blk, ~enc, ~dec, k, t)}

# For every cipher and key with inv, every IV and every message: decryption
# gives back the message that encryption encrypted, and when encryption
# refuses (an IV that is not one block, a message shorter than a block),
# decryption is not reached and both refuse alike
law cmblock_cts_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for inv: @xs: List<&2, M.CmBlock> -> {crcts.dec_enc(~K, ~M.CmBlock, ~enc, ~dec, k, xs) == xs : List<&2, M.CmBlock>}
  for +iv: B.Octets
  for +m: B.Octets
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Ct.CrCts.encrypt(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, iv, m), c => Ct.CrCts.decrypt(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, iv, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => m, Ct.CrCts.encrypt(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, iv, m)) : Result<&2, &2, Cr.CrError, B.Octets>}

law lcblock64_cts_round_trip:
  for ~K: Data
  for ~enc: K -> L.LcBlock64 -> L.LcBlock64
  for ~dec: K -> L.LcBlock64 -> L.LcBlock64
  for +k: K
  for inv: @xs: List<&2, L.LcBlock64> -> {crcts.dec_enc(~K, ~L.LcBlock64, ~enc, ~dec, k, xs) == xs : List<&2, L.LcBlock64>}
  for +iv: B.Octets
  for +m: B.Octets
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Ct.CrCts.encrypt(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, iv, m), c => Ct.CrCts.decrypt(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, iv, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => m, Ct.CrCts.encrypt(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, iv, m)) : Result<&2, &2, Cr.CrError, B.Octets>}
