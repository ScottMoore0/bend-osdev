# Laws about the public interface of every mode. The block cipher is the
# template arguments ~K, ~enc, ~dec; laws that need decryption to undo
# encryption take that as a hypothesis, inv, at the law's key: for every list
# of blocks xs, CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs (each block
# encrypted and decrypted back is itself), so they hold for every cipher and
# key that satisfy it. The hypothesis is an ordinary one, used once (on the
# list of blocks the mode gives the cipher), which --verdict models; a cipher
# that proves dec(k, enc(k, b)) == b for every key and block as a law gives
# it for every list by induction (README.md, "Laws").
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./cipher-modes.bend as M
import ./aes.bend as X
import ./pkcs7.bend as P
import ./cbc.bend as C
import ./xts.bend as T
import ./ccm.bend as CC
import ./cmac.bend as CM
import ./aes_modes.bend as D

# Properties, for every input

# CBC on blocks: decryption undoes encryption, for every key, IV and message
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

# CMAC in pieces: the state after a ++ b is the state after a, then b, for
# every cipher, key and state (so start, update .. update, finish is the MAC
# of the pieces joined)
law cmac_streaming:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for s: CM.CmacState
  for +a: B.Octets
  for +b: B.Octets
  {CM.Cmac.update(~K, ~enc, k, s, B.Octets.append(a, b)) == CM.Cmac.update(~K, ~enc, k, CM.Cmac.update(~K, ~enc, k, s, a), b) : CM.CmacState}

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

# CCM: decryption accepts what encryption produced and gives the message
# back, for every cipher, key, tag length, nonce, associated data and
# message; when the parameters are refused, both refuse alike
law ccm_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +m: Nat
  for +nonce: B.Octets
  for +aad: B.Octets
  for +p: B.Octets
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CC.Ccm.encrypt(~K, ~enc, k, m, nonce, aad, p), c => CC.Ccm.decrypt(~K, ~enc, k, m, nonce, aad, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, CC.Ccm.encrypt(~K, ~enc, k, m, nonce, aad, p)) : Result<&2, &2, M.CmError, B.Octets>}

# AES (aes.bend): decryption undoes encryption, for every key (every value
# of CmAesKey, whatever its number of rounds and round keys: AES-128, AES-192
# and AES-256 among them) and every block
law aes_round_trip:
  for k: X.CmAesKey
  for +b: M.CmBlock
  {X.CmAes.decrypt(k, X.CmAes.encrypt(k, b)) == b : M.CmBlock}

# A block written as Octets reads back as the same block, for every block
law block_octets_round_trip:
  for +b: M.CmBlock
  {M.CmBlock.of_octets(M.CmBlock.to_octets(b)) == Some{b} : Maybe<&2, M.CmBlock>}

# Vectors: the specifications' own test values, proved by computation. The
# checker evaluates AES slowly and keeps what it evaluates, so only these fit
# in its memory; every other vector of the four specifications (all of SP
# 800-38A F.2.1, F.2.2, F.2.5 and F.2.6; IEEE 1619 vectors 2 and 15 to 18;
# RFC 3610 packets 1 to 3; RFC 4493 examples 2 to 4; and every decryption)
# runs compiled in check.bend.

# FIPS 197 Appendix C.1: the named default cipher (AES-128) encrypts one block
law aes128_fips197_c1:
  {Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(X.CmAes.encrypt(k, M.CmBlock{1122867, 1146447479, 2291772091, 3437096703})), X.CmAes.key128(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]))) == Done{B.Octets.of_list([105, 196, 224, 216, 106, 123, 4, 48, 216, 205, 183, 128, 112, 180, 197, 90])} : Result<&2, &2, M.CmError, B.Octets>}

# a key of a length AES-128 and AES-256 do not have is refused
law aes_bad_key_length:
  {D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42])) == Fail{M.CmBadKeyLength{15n}} : Result<&2, &2, M.CmError, B.Octets>}

# NIST SP 800-38A Appendix F.2.1, CBC-AES128: its first block
law cbc_sp800_38a_f21_block1:
  {D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42])) == Done{B.Octets.of_list([118, 73, 171, 172, 129, 25, 178, 70, 206, 233, 142, 155, 18, 233, 25, 125])} : Result<&2, &2, M.CmError, B.Octets>}

# the byte layer refuses a message that is not whole blocks, and a short IV
law cbc_not_whole_blocks:
  {D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42, 174])) == Fail{M.CmNotBlockMultiple{17n}} : Result<&2, &2, M.CmError, B.Octets>}

law cbc_short_iv:
  {D.CmAes.cbc_encrypt(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]), B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 42])) == Fail{M.CmBadIvLength{15n}} : Result<&2, &2, M.CmError, B.Octets>}

# PKCS #7 (RFC 5652, 6.3): the empty message becomes a whole block of 16s; 15 bytes gain one 1
law pkcs7_pad_empty:
  {P.Pkcs7.pad(16n, B.Octets.empty()) == Done{B.Octets.of_list([16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16])} : Result<&2, &2, M.CmError, B.Octets>}

law pkcs7_pad_15:
  {P.Pkcs7.pad(16n, B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23])) == Done{B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 1])} : Result<&2, &2, M.CmError, B.Octets>}

law pkcs7_unpad_15:
  {P.Pkcs7.unpad(16n, B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 1])) == Done{B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23])} : Result<&2, &2, M.CmError, B.Octets>}

# a last byte of 0, or one the bytes before it contradict, is bad padding
law pkcs7_unpad_zero:
  {P.Pkcs7.unpad(16n, B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 0])) == Fail{M.CmBadPadding{}} : Result<&2, &2, M.CmError, B.Octets>}

law pkcs7_unpad_mixed:
  {P.Pkcs7.unpad(16n, B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 2, 3, 3])) == Fail{M.CmBadPadding{}} : Result<&2, &2, M.CmError, B.Octets>}

# a data unit shorter than a block is refused
law xts_short:
  {D.CmAes.xts_encrypt(B.Octets.of_list([255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176]), B.Octets.of_list([154, 120, 86, 52, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) == Fail{M.CmTooShort{15n}} : Result<&2, &2, M.CmError, B.Octets>}

# the sequence number of sector n: n little-endian, zero-filled to 16 bytes
law xts_sector:
  {T.Xts.sector(W.W64.from_parts(0, 2591577138)) == B.Octets.of_list([50, 84, 120, 154, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) : B.Octets}

# a tag of odd length, and a nonce of 6 bytes, are refused
law ccm_bad_tag_length:
  {D.CmAes.ccm_encrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 7n, B.Octets.of_list([0, 0, 0, 3, 2, 1, 0, 160, 161, 162, 163, 164, 165]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30])) == Fail{M.CmBadTagLength{7n}} : Result<&2, &2, M.CmError, B.Octets>}

law ccm_bad_nonce_length:
  {D.CmAes.ccm_encrypt(B.Octets.of_list([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]), 8n, B.Octets.of_list([0, 0, 0, 3, 2, 1]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7]), B.Octets.of_list([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30])) == Fail{M.CmBadNonceLength{6n}} : Result<&2, &2, M.CmError, B.Octets>}

# RFC 4493 section 4: the AES-CMAC subkey K1
law cmac_rfc4493_k1:
  {Result.map(&2, &2, M.CmError, X.CmAesKey, B.Octets, k => M.CmBlock.to_octets(CM.Cmac.subkey1(~X.CmAesKey, ~X.CmAes.encrypt, k)), X.CmAes.key128(B.Octets.of_list([43, 126, 21, 22, 40, 174, 210, 166, 171, 247, 21, 136, 9, 207, 79, 60]))) == Done{B.Octets.of_list([251, 238, 214, 24, 53, 113, 51, 102, 124, 133, 224, 143, 114, 54, 168, 222])} : Result<&2, &2, M.CmError, B.Octets>}
