# Laws of cipher-modes' modes over each block cipher it runs over, written
# out per cipher by gen/instances.py (do not edit by hand: change the script
# and run it).
#
# For each cipher c: c_dec_enc, the cipher meets cipher-modes' round-trip
# hypothesis (CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs) at every key and
# list of blocks; and cipher-modes' four round-trip laws at c's template
# arguments, with no hypothesis: CBC on blocks for every key, IV and list of
# blocks; CBC on bytes for every key, 16-byte IV and message of whole blocks;
# XTS on blocks for every data key and starting tweak; XTS on bytes, with
# ciphertext stealing, for every pair of keys, 16-byte sequence number and
# data unit of at least 16 bytes.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/cbc.bend as CB
import ../cipher-modes/xts.bend as XT
import ../sm4/sm4.bend as S
import ../camellia/camellia.bend as Ca
import ../serpent/serpent.bend as Sp
import ../twofish/twofish.bend as Tf
import ../aria/aria.bend as Ar
import ../cast6/cast6.bend as C6
import ../cipher-modes/aes.bend as X

# SM4 (the sm4 package)

# meets cipher-modes' round-trip hypothesis at every key
law sm4_dec_enc:
  for +k: S.LcSm4Key
  for xs: List<&2, M.CmBlock>
  {M.CmBlock.dec_enc(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, xs) == xs : List<&2, M.CmBlock>}

law sm4_cbc_blocks_round_trip:
  for +k: S.LcSm4Key
  for iv: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {CB.Cbc.decrypt_blocks(~S.LcSm4Key, ~S.LcSm4.decrypt, k, iv, CB.Cbc.encrypt_blocks(~S.LcSm4Key, ~S.LcSm4.encrypt, k, iv, bs)) == bs : List<&2, M.CmBlock>}

law sm4_cbc_round_trip:
  for +k: S.LcSm4Key
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~S.LcSm4Key, ~S.LcSm4.encrypt, k, iv, m), c => CB.Cbc.decrypt(~S.LcSm4Key, ~S.LcSm4.decrypt, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}

law sm4_xts_blocks_round_trip:
  for +k1: S.LcSm4Key
  for t: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {XT.Xts.decrypt_blocks(~S.LcSm4Key, ~S.LcSm4.decrypt, k1, t, XT.Xts.encrypt_blocks(~S.LcSm4Key, ~S.LcSm4.encrypt, k1, t, bs)) == bs : List<&2, M.CmBlock>}

law sm4_xts_round_trip:
  for +k1: S.LcSm4Key
  for +k2: S.LcSm4Key
  for +i: B.Octets
  for +p: B.Octets
  for hi: {B.Octets.len(i) == 16n : Nat}
  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~S.LcSm4Key, ~S.LcSm4.encrypt, k1, k2, i, p), c => XT.Xts.decrypt(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}

# Camellia (the camellia package)

# meets cipher-modes' round-trip hypothesis at every key
law camellia_dec_enc:
  for +k: Ca.LcCamelliaKey
  for xs: List<&2, M.CmBlock>
  {M.CmBlock.dec_enc(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, xs) == xs : List<&2, M.CmBlock>}

law camellia_cbc_blocks_round_trip:
  for +k: Ca.LcCamelliaKey
  for iv: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {CB.Cbc.decrypt_blocks(~Ca.LcCamelliaKey, ~Ca.LcCamellia.decrypt, k, iv, CB.Cbc.encrypt_blocks(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, k, iv, bs)) == bs : List<&2, M.CmBlock>}

law camellia_cbc_round_trip:
  for +k: Ca.LcCamelliaKey
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, k, iv, m), c => CB.Cbc.decrypt(~Ca.LcCamelliaKey, ~Ca.LcCamellia.decrypt, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}

law camellia_xts_blocks_round_trip:
  for +k1: Ca.LcCamelliaKey
  for t: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {XT.Xts.decrypt_blocks(~Ca.LcCamelliaKey, ~Ca.LcCamellia.decrypt, k1, t, XT.Xts.encrypt_blocks(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, k1, t, bs)) == bs : List<&2, M.CmBlock>}

law camellia_xts_round_trip:
  for +k1: Ca.LcCamelliaKey
  for +k2: Ca.LcCamelliaKey
  for +i: B.Octets
  for +p: B.Octets
  for hi: {B.Octets.len(i) == 16n : Nat}
  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, k1, k2, i, p), c => XT.Xts.decrypt(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}

# Serpent (the serpent package)

# meets cipher-modes' round-trip hypothesis at every key
law serpent_dec_enc:
  for +k: Sp.LcSerpentKey
  for xs: List<&2, M.CmBlock>
  {M.CmBlock.dec_enc(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, xs) == xs : List<&2, M.CmBlock>}

law serpent_cbc_blocks_round_trip:
  for +k: Sp.LcSerpentKey
  for iv: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {CB.Cbc.decrypt_blocks(~Sp.LcSerpentKey, ~Sp.LcSerpent.decrypt, k, iv, CB.Cbc.encrypt_blocks(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, k, iv, bs)) == bs : List<&2, M.CmBlock>}

law serpent_cbc_round_trip:
  for +k: Sp.LcSerpentKey
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, k, iv, m), c => CB.Cbc.decrypt(~Sp.LcSerpentKey, ~Sp.LcSerpent.decrypt, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}

law serpent_xts_blocks_round_trip:
  for +k1: Sp.LcSerpentKey
  for t: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {XT.Xts.decrypt_blocks(~Sp.LcSerpentKey, ~Sp.LcSerpent.decrypt, k1, t, XT.Xts.encrypt_blocks(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, k1, t, bs)) == bs : List<&2, M.CmBlock>}

law serpent_xts_round_trip:
  for +k1: Sp.LcSerpentKey
  for +k2: Sp.LcSerpentKey
  for +i: B.Octets
  for +p: B.Octets
  for hi: {B.Octets.len(i) == 16n : Nat}
  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, k1, k2, i, p), c => XT.Xts.decrypt(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}

# Twofish (the twofish package)

# meets cipher-modes' round-trip hypothesis at every key
law twofish_dec_enc:
  for +k: Tf.LcTwofishKey
  for xs: List<&2, M.CmBlock>
  {M.CmBlock.dec_enc(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, xs) == xs : List<&2, M.CmBlock>}

law twofish_cbc_blocks_round_trip:
  for +k: Tf.LcTwofishKey
  for iv: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {CB.Cbc.decrypt_blocks(~Tf.LcTwofishKey, ~Tf.LcTwofish.decrypt, k, iv, CB.Cbc.encrypt_blocks(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, k, iv, bs)) == bs : List<&2, M.CmBlock>}

law twofish_cbc_round_trip:
  for +k: Tf.LcTwofishKey
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, k, iv, m), c => CB.Cbc.decrypt(~Tf.LcTwofishKey, ~Tf.LcTwofish.decrypt, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}

law twofish_xts_blocks_round_trip:
  for +k1: Tf.LcTwofishKey
  for t: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {XT.Xts.decrypt_blocks(~Tf.LcTwofishKey, ~Tf.LcTwofish.decrypt, k1, t, XT.Xts.encrypt_blocks(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, k1, t, bs)) == bs : List<&2, M.CmBlock>}

law twofish_xts_round_trip:
  for +k1: Tf.LcTwofishKey
  for +k2: Tf.LcTwofishKey
  for +i: B.Octets
  for +p: B.Octets
  for hi: {B.Octets.len(i) == 16n : Nat}
  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, k1, k2, i, p), c => XT.Xts.decrypt(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}

# ARIA (the aria package)

# meets cipher-modes' round-trip hypothesis at every key
law aria_dec_enc:
  for +k: Ar.LcAriaKey
  for xs: List<&2, M.CmBlock>
  {M.CmBlock.dec_enc(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, xs) == xs : List<&2, M.CmBlock>}

law aria_cbc_blocks_round_trip:
  for +k: Ar.LcAriaKey
  for iv: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {CB.Cbc.decrypt_blocks(~Ar.LcAriaKey, ~Ar.LcAria.decrypt, k, iv, CB.Cbc.encrypt_blocks(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, k, iv, bs)) == bs : List<&2, M.CmBlock>}

law aria_cbc_round_trip:
  for +k: Ar.LcAriaKey
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, k, iv, m), c => CB.Cbc.decrypt(~Ar.LcAriaKey, ~Ar.LcAria.decrypt, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}

law aria_xts_blocks_round_trip:
  for +k1: Ar.LcAriaKey
  for t: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {XT.Xts.decrypt_blocks(~Ar.LcAriaKey, ~Ar.LcAria.decrypt, k1, t, XT.Xts.encrypt_blocks(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, k1, t, bs)) == bs : List<&2, M.CmBlock>}

law aria_xts_round_trip:
  for +k1: Ar.LcAriaKey
  for +k2: Ar.LcAriaKey
  for +i: B.Octets
  for +p: B.Octets
  for hi: {B.Octets.len(i) == 16n : Nat}
  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, k1, k2, i, p), c => XT.Xts.decrypt(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}

# CAST-256 (the cast6 package)

# meets cipher-modes' round-trip hypothesis at every key
law cast6_dec_enc:
  for +k: C6.LcCast6Key
  for xs: List<&2, M.CmBlock>
  {M.CmBlock.dec_enc(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, xs) == xs : List<&2, M.CmBlock>}

law cast6_cbc_blocks_round_trip:
  for +k: C6.LcCast6Key
  for iv: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {CB.Cbc.decrypt_blocks(~C6.LcCast6Key, ~C6.LcCast6.decrypt, k, iv, CB.Cbc.encrypt_blocks(~C6.LcCast6Key, ~C6.LcCast6.encrypt, k, iv, bs)) == bs : List<&2, M.CmBlock>}

law cast6_cbc_round_trip:
  for +k: C6.LcCast6Key
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~C6.LcCast6Key, ~C6.LcCast6.encrypt, k, iv, m), c => CB.Cbc.decrypt(~C6.LcCast6Key, ~C6.LcCast6.decrypt, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}

law cast6_xts_blocks_round_trip:
  for +k1: C6.LcCast6Key
  for t: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {XT.Xts.decrypt_blocks(~C6.LcCast6Key, ~C6.LcCast6.decrypt, k1, t, XT.Xts.encrypt_blocks(~C6.LcCast6Key, ~C6.LcCast6.encrypt, k1, t, bs)) == bs : List<&2, M.CmBlock>}

law cast6_xts_round_trip:
  for +k1: C6.LcCast6Key
  for +k2: C6.LcCast6Key
  for +i: B.Octets
  for +p: B.Octets
  for hi: {B.Octets.len(i) == 16n : Nat}
  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~C6.LcCast6Key, ~C6.LcCast6.encrypt, k1, k2, i, p), c => XT.Xts.decrypt(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}

# AES-128, AES-192 and AES-256 (cipher-modes)

# meets cipher-modes' round-trip hypothesis at every key
law aes_dec_enc:
  for +k: X.CmAesKey
  for xs: List<&2, M.CmBlock>
  {M.CmBlock.dec_enc(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, xs) == xs : List<&2, M.CmBlock>}

law aes_cbc_blocks_round_trip:
  for +k: X.CmAesKey
  for iv: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {CB.Cbc.decrypt_blocks(~X.CmAesKey, ~X.CmAes.decrypt, k, iv, CB.Cbc.encrypt_blocks(~X.CmAesKey, ~X.CmAes.encrypt, k, iv, bs)) == bs : List<&2, M.CmBlock>}

law aes_cbc_round_trip:
  for +k: X.CmAesKey
  for +iv: B.Octets
  for +m: B.Octets
  for hi: {B.Octets.len(iv) == 16n : Nat}
  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~X.CmAesKey, ~X.CmAes.encrypt, k, iv, m), c => CB.Cbc.decrypt(~X.CmAesKey, ~X.CmAes.decrypt, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}

law aes_xts_blocks_round_trip:
  for +k1: X.CmAesKey
  for t: M.CmBlock
  for bs: List<&2, M.CmBlock>
  {XT.Xts.decrypt_blocks(~X.CmAesKey, ~X.CmAes.decrypt, k1, t, XT.Xts.encrypt_blocks(~X.CmAesKey, ~X.CmAes.encrypt, k1, t, bs)) == bs : List<&2, M.CmBlock>}

law aes_xts_round_trip:
  for +k1: X.CmAesKey
  for +k2: X.CmAesKey
  for +i: B.Octets
  for +p: B.Octets
  for hi: {B.Octets.len(i) == 16n : Nat}
  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~X.CmAesKey, ~X.CmAes.encrypt, k1, k2, i, p), c => XT.Xts.decrypt(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
