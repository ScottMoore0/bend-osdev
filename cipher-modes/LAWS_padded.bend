# CBC with PKCS #7 padding (cbc.bend's encrypt_padded and decrypt_padded):
# decryption undoes encryption for every message, of any length. The law
# rests on LAWS.bend's cbc_round_trip and LAWS_pkcs7.bend's laws, so it is
# in a pair of its own (CONVENTIONS.md, Laws): a proof that uses only the
# padding laws takes in none of AES's proofs.
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M
import ./cbc.bend as C

# for every cipher and key with inv (as LAWS.bend's laws take it), every
# 16-byte IV and every message: encryption succeeds and decryption gives the
# message back
law cbc_padded_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for inv: @xs: List<&2, M.CmBlock> -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs : List<&2, M.CmBlock>}
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.Cbc.encrypt_padded(~K, ~enc, k, iv, m), c => C.Cbc.decrypt_padded(~K, ~dec, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
