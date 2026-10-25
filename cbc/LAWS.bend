# Laws about CBC (cbc.bend), for every cipher given as the template
# arguments ~K, ~enc, ~dec. Laws that need decryption to undo encryption
# take that as a hypothesis, inv, at the law's key: for every list of blocks
# xs, CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs (each block encrypted and
# decrypted back is itself), so they hold for every cipher and key that
# satisfy it. The hypothesis is an ordinary one, used once (on the list of
# blocks the mode gives the cipher), which --verdict models; a cipher that
# proves dec(k, enc(k, b)) == b for every key and block as a law gives it
# for every list by induction (bend-osdev-cm-instances writes that out).
# Padded CBC's round trip is in LAWS_padded.bend.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./cbc.bend as C

law cbc_blocks_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for inv: @xs: List<&2, M.CmBlock> -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs : List<&2, M.CmBlock>}
  for iv: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {C.Cbc.decrypt_blocks(~K, ~dec, k, iv, C.Cbc.encrypt_blocks(~K, ~enc, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# CBC on bytes: for every 16-byte IV and every message of whole blocks,
# encryption succeeds and decryption gives the message back
law cbc_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for inv: @xs: List<&2, M.CmBlock> -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs : List<&2, M.CmBlock>}
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.Cbc.encrypt(~K, ~enc, k, iv, m), c => C.Cbc.decrypt(~K, ~dec, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
