# Laws about XTS (xts.bend), for every cipher given as the template
# arguments ~K, ~enc, ~dec. The round trips take decryption undoing
# encryption as the hypothesis inv at the data key k1 (as bend-osdev-cbc's
# laws do; see its LAWS.bend): for every list of blocks xs,
# CmBlock.dec_enc(~K, ~enc, ~dec, k1, xs) == xs.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../mode-core/mode-core.bend as M
import ./xts.bend as T

# XTS on blocks: decryption undoes encryption, for every data key and every
# starting tweak (T_0 = Xts.tweak(k2, i), so every k2 and i are covered)
law xts_blocks_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k1: K
  for inv: @xs: List<&2, M.CmBlock> -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k1, xs) == xs : List<&2, M.CmBlock>}
  for t: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {T.Xts.decrypt_blocks(~K, ~dec, k1, t, T.Xts.encrypt_blocks(~K, ~enc, k1, t, bs)) == bs : List<&2, M.CmBlock>}

# XTS on bytes, with ciphertext stealing: for every 16-byte sequence number
# and every data unit of at least 16 bytes, encryption succeeds and
# decryption gives the data unit back
law xts_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k1: K
  for +k2: K
  for inv: @xs: List<&2, M.CmBlock> -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k1, xs) == xs : List<&2, M.CmBlock>}
  for +i: B.Octets
  for +p: B.Octets
  for hi: {B.Octets.len(i) == 16n : Nat}
  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.Xts.encrypt(~K, ~enc, k1, k2, i, p), c => T.Xts.decrypt(~K, ~enc, ~dec, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}

# the sequence number of sector n: n little-endian, zero-filled to 16 bytes
law xts_sector:
  {T.Xts.sector(W.W64.from_parts(0, 2591577138)) == B.Octets.of_list([50, 84, 120, 154, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) : B.Octets}
