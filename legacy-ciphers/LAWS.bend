# Laws about the public interface of every cipher in the package.
#
# Properties, for every input: each block cipher's decryption undoes its
# encryption, and its encryption undoes its decryption, for every key and
# every block (so each is a permutation of the blocks), for the 128-bit
# ciphers (SM4, Camellia, Serpent, Twofish, ARIA, CAST-256) and the 64-bit
# ones (DES, 3DES, Blowfish, CAST-128, TEA, XTEA, FCrypt); the 64-bit modes undo
# themselves for DES and 3DES; RC4 applied twice from one state gives the
# data back, and RC4 in pieces is RC4 of the whole; 64-bit blocks survive
# their byte form.
#
# Vectors: the specifications' own test values, proved by computation (see
# the end of the file).
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ./legacy-ciphers.bend as L
import ./des.bend as D
import ./tdes.bend as T
import ./sm4.bend as S
import ./camellia.bend as C
import ./serpent.bend as P
import ./twofish.bend as F
import ./rc4.bend as R
import ./modes64.bend as X
import ./aria.bend as A
import ./cast6.bend as C6
import ./blowfish.bend as BF
import ./cast5.bend as C5
import ./tea.bend as TE
import ./xtea.bend as XT
import ./fcrypt.bend as FC

# DES (FIPS 46-3)

law des_round_trip:
  for k: D.LcDesKey
  for +b: L.LcBlock64
  {D.LcDes.decrypt(k, D.LcDes.encrypt(k, b)) == b : L.LcBlock64}

law des_round_trip_dual:
  for k: D.LcDesKey
  for +b: L.LcBlock64
  {D.LcDes.encrypt(k, D.LcDes.decrypt(k, b)) == b : L.LcBlock64}

# Triple DES (SP 800-67), for every key bundle (any three DES keys)

law tdes_round_trip:
  for k: T.LcTdesKey
  for +b: L.LcBlock64
  {T.LcTdes.decrypt(k, T.LcTdes.encrypt(k, b)) == b : L.LcBlock64}

law tdes_round_trip_dual:
  for k: T.LcTdesKey
  for +b: L.LcBlock64
  {T.LcTdes.encrypt(k, T.LcTdes.decrypt(k, b)) == b : L.LcBlock64}

# SM4 (GB/T 32907-2016)

law sm4_round_trip:
  for k: S.LcSm4Key
  for +b: M.CmBlock
  {S.LcSm4.decrypt(k, S.LcSm4.encrypt(k, b)) == b : M.CmBlock}

law sm4_round_trip_dual:
  for k: S.LcSm4Key
  for +b: M.CmBlock
  {S.LcSm4.encrypt(k, S.LcSm4.decrypt(k, b)) == b : M.CmBlock}

# Camellia (RFC 3713), every key size

law camellia_round_trip:
  for k: C.LcCamelliaKey
  for +b: M.CmBlock
  {C.LcCamellia.decrypt(k, C.LcCamellia.encrypt(k, b)) == b : M.CmBlock}

law camellia_round_trip_dual:
  for k: C.LcCamelliaKey
  for +b: M.CmBlock
  {C.LcCamellia.encrypt(k, C.LcCamellia.decrypt(k, b)) == b : M.CmBlock}

# Serpent (the AES submission), every key size

law serpent_round_trip:
  for k: P.LcSerpentKey
  for +b: M.CmBlock
  {P.LcSerpent.decrypt(k, P.LcSerpent.encrypt(k, b)) == b : M.CmBlock}

law serpent_round_trip_dual:
  for k: P.LcSerpentKey
  for +b: M.CmBlock
  {P.LcSerpent.encrypt(k, P.LcSerpent.decrypt(k, b)) == b : M.CmBlock}

# Twofish (Schneier et al.), every key size

law twofish_round_trip:
  for k: F.LcTwofishKey
  for +b: M.CmBlock
  {F.LcTwofish.decrypt(k, F.LcTwofish.encrypt(k, b)) == b : M.CmBlock}

law twofish_round_trip_dual:
  for k: F.LcTwofishKey
  for +b: M.CmBlock
  {F.LcTwofish.encrypt(k, F.LcTwofish.decrypt(k, b)) == b : M.CmBlock}

# ARIA (RFC 5794), every key size

law aria_round_trip:
  for k: A.LcAriaKey
  for +b: M.CmBlock
  {A.LcAria.decrypt(k, A.LcAria.encrypt(k, b)) == b : M.CmBlock}

law aria_round_trip_dual:
  for k: A.LcAriaKey
  for +b: M.CmBlock
  {A.LcAria.encrypt(k, A.LcAria.decrypt(k, b)) == b : M.CmBlock}

# CAST-256 (RFC 2612), every key size

law cast6_round_trip:
  for k: C6.LcCast6Key
  for +b: M.CmBlock
  {C6.LcCast6.decrypt(k, C6.LcCast6.encrypt(k, b)) == b : M.CmBlock}

law cast6_round_trip_dual:
  for k: C6.LcCast6Key
  for +b: M.CmBlock
  {C6.LcCast6.encrypt(k, C6.LcCast6.decrypt(k, b)) == b : M.CmBlock}

# Blowfish (Schneier), every key

law blowfish_round_trip:
  for k: BF.LcBlowfishKey
  for +b: L.LcBlock64
  {BF.LcBlowfish.decrypt(k, BF.LcBlowfish.encrypt(k, b)) == b : L.LcBlock64}

law blowfish_round_trip_dual:
  for k: BF.LcBlowfishKey
  for +b: L.LcBlock64
  {BF.LcBlowfish.encrypt(k, BF.LcBlowfish.decrypt(k, b)) == b : L.LcBlock64}

# CAST-128 (RFC 2144), every key size

law cast5_round_trip:
  for k: C5.LcCast5Key
  for +b: L.LcBlock64
  {C5.LcCast5.decrypt(k, C5.LcCast5.encrypt(k, b)) == b : L.LcBlock64}

law cast5_round_trip_dual:
  for k: C5.LcCast5Key
  for +b: L.LcBlock64
  {C5.LcCast5.encrypt(k, C5.LcCast5.decrypt(k, b)) == b : L.LcBlock64}

# TEA (Wheeler and Needham), every key, byte order and number of cycles

law tea_round_trip:
  for k: TE.LcTeaKey
  for +b: L.LcBlock64
  {TE.LcTea.decrypt(k, TE.LcTea.encrypt(k, b)) == b : L.LcBlock64}

law tea_round_trip_dual:
  for k: TE.LcTeaKey
  for +b: L.LcBlock64
  {TE.LcTea.encrypt(k, TE.LcTea.decrypt(k, b)) == b : L.LcBlock64}

# XTEA (Needham and Wheeler), every key, byte order and number of cycles

law xtea_round_trip:
  for k: XT.LcXteaKey
  for +b: L.LcBlock64
  {XT.LcXtea.decrypt(k, XT.LcXtea.encrypt(k, b)) == b : L.LcBlock64}

law xtea_round_trip_dual:
  for k: XT.LcXteaKey
  for +b: L.LcBlock64
  {XT.LcXtea.encrypt(k, XT.LcXtea.decrypt(k, b)) == b : L.LcBlock64}

# FCrypt (the AFS specification), every key

law fcrypt_round_trip:
  for k: FC.LcFcryptKey
  for +b: L.LcBlock64
  {FC.LcFcrypt.decrypt(k, FC.LcFcrypt.encrypt(k, b)) == b : L.LcBlock64}

law fcrypt_round_trip_dual:
  for k: FC.LcFcryptKey
  for +b: L.LcBlock64
  {FC.LcFcrypt.encrypt(k, FC.LcFcrypt.decrypt(k, b)) == b : L.LcBlock64}

# RC4 (RFC 6229), for every state (so for every key) and all data

# the cipher is its own inverse: from one state, applied twice, the data
# comes back
law rc4_involution:
  for +st: R.LcRc4State
  for +m: B.Octets
  {R.LcRc4.out_data(R.LcRc4.update(st, R.LcRc4.out_data(R.LcRc4.update(st, m)))) == m : B.Octets}

# data in pieces: the output of a ++ b is the output of a, then the output
# of b from the state after a; and the state after a ++ b is the state
# after a, then b
law rc4_streaming_data:
  for +st: R.LcRc4State
  for +a: B.Octets
  for +b: B.Octets
  {R.LcRc4.out_data(R.LcRc4.update(st, B.Octets.append(a, b))) == B.Octets.append(R.LcRc4.out_data(R.LcRc4.update(st, a)), R.LcRc4.out_data(R.LcRc4.update(R.LcRc4.out_state(R.LcRc4.update(st, a)), b))) : B.Octets}

law rc4_streaming_state:
  for +st: R.LcRc4State
  for +a: B.Octets
  for +b: B.Octets
  {R.LcRc4.out_state(R.LcRc4.update(st, B.Octets.append(a, b))) == R.LcRc4.out_state(R.LcRc4.update(R.LcRc4.out_state(R.LcRc4.update(st, a)), b)) : R.LcRc4State}

# 64-bit blocks as bytes: a block read back from its 8 bytes is itself, and
# a list of blocks read back from its bytes is itself
law block64_octets_round_trip:
  for +b: L.LcBlock64
  {L.LcBlock64.of_octets(L.LcBlock64.to_octets(b)) == Some{b} : Maybe<&2, L.LcBlock64>}

law blocks64_octets_round_trip:
  for +bs: List<&2, L.LcBlock64>
  {X.Lc64.blocks_of(X.Lc64.octets_of(bs)) == Done{bs} : Result<&2, &2, L.LcError, List<&2, L.LcBlock64>>}

# The 64-bit modes undo themselves for DES and 3DES, for every key, IV and
# message: on blocks, and on bytes (every message of whole blocks is the
# bytes of its blocks, Lc64.octets_of)

law des_ecb_round_trip:
  for +k: D.LcDesKey
  for +bs: List<&2, L.LcBlock64>
  {X.Lc64.ecb_decrypt_blocks(~D.LcDesKey, ~D.LcDes.decrypt, k, X.Lc64.ecb_encrypt_blocks(~D.LcDesKey, ~D.LcDes.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

law des_cbc_round_trip:
  for +k: D.LcDesKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {X.Lc64.cbc_decrypt_blocks(~D.LcDesKey, ~D.LcDes.decrypt, k, iv, X.Lc64.cbc_encrypt_blocks(~D.LcDesKey, ~D.LcDes.encrypt, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

law tdes_ecb_round_trip:
  for +k: T.LcTdesKey
  for +bs: List<&2, L.LcBlock64>
  {X.Lc64.ecb_decrypt_blocks(~T.LcTdesKey, ~T.LcTdes.decrypt, k, X.Lc64.ecb_encrypt_blocks(~T.LcTdesKey, ~T.LcTdes.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

law tdes_cbc_round_trip:
  for +k: T.LcTdesKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {X.Lc64.cbc_decrypt_blocks(~T.LcTdesKey, ~T.LcTdes.decrypt, k, iv, X.Lc64.cbc_encrypt_blocks(~T.LcTdesKey, ~T.LcTdes.encrypt, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

law des_cbc_octets_round_trip:
  for +k: D.LcDesKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, X.Lc64.cbc_encrypt(~D.LcDesKey, ~D.LcDes.encrypt, k, L.LcBlock64.to_octets(iv), X.Lc64.octets_of(bs)), c => X.Lc64.cbc_decrypt(~D.LcDesKey, ~D.LcDes.decrypt, k, L.LcBlock64.to_octets(iv), c)) == Done{X.Lc64.octets_of(bs)} : Result<&2, &2, L.LcError, B.Octets>}

law tdes_cbc_octets_round_trip:
  for +k: T.LcTdesKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, X.Lc64.cbc_encrypt(~T.LcTdesKey, ~T.LcTdes.encrypt, k, L.LcBlock64.to_octets(iv), X.Lc64.octets_of(bs)), c => X.Lc64.cbc_decrypt(~T.LcTdesKey, ~T.LcTdes.decrypt, k, L.LcBlock64.to_octets(iv), c)) == Done{X.Lc64.octets_of(bs)} : Result<&2, &2, L.LcError, B.Octets>}

law des_ecb_octets_round_trip:
  for +k: D.LcDesKey
  for +bs: List<&2, L.LcBlock64>
  {Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, X.Lc64.ecb_encrypt(~D.LcDesKey, ~D.LcDes.encrypt, k, X.Lc64.octets_of(bs)), c => X.Lc64.ecb_decrypt(~D.LcDesKey, ~D.LcDes.decrypt, k, c)) == Done{X.Lc64.octets_of(bs)} : Result<&2, &2, L.LcError, B.Octets>}

law tdes_ecb_octets_round_trip:
  for +k: T.LcTdesKey
  for +bs: List<&2, L.LcBlock64>
  {Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, X.Lc64.ecb_encrypt(~T.LcTdesKey, ~T.LcTdes.encrypt, k, X.Lc64.octets_of(bs)), c => X.Lc64.ecb_decrypt(~T.LcTdesKey, ~T.LcTdes.decrypt, k, c)) == Done{X.Lc64.octets_of(bs)} : Result<&2, &2, L.LcError, B.Octets>}

# Vectors: the specifications' own test values, proved by computation. Some
# run compiled in check.bend instead: the Twofish paper's (one Twofish key
# schedule takes about 2.5 GB in the checker), and DES's, 3DES's and RC4's
# (the checker proves them, but they run past the --verdict kernel's
# evaluation budget: RC4's 256-step key schedule does, 128 steps do not).

# BEGIN GENERATED by gen/vectors.py: vectors
# GB/T 32907-2016, Appendix A, example 1: key = plaintext =
# 0123456789ABCDEFFEDCBA9876543210, ciphertext 681EDF34D206965E86B3E94F536E4246
law sm4_gbt32907:
  {Result.map(&2, &2, L.LcError, S.LcSm4Key, M.CmBlock, k => S.LcSm4.encrypt(k, M.CmBlock{19088743, 2309737967, 4275878552, 1985229328}), S.LcSm4.key(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]))) == Done{M.CmBlock{1746853684, 3523647070, 2259937615, 1399734854}} : Result<&2, &2, L.LcError, M.CmBlock>}

# RFC 3713, Appendix A: Camellia-128, key = plaintext =
# 0123456789ABCDEFFEDCBA9876543210, ciphertext 67673138549669730857065648EABE43
law camellia_rfc3713:
  {Result.map(&2, &2, L.LcError, C.LcCamelliaKey, M.CmBlock, k => C.LcCamellia.encrypt(k, M.CmBlock{19088743, 2309737967, 4275878552, 1985229328}), C.LcCamellia.key(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]))) == Done{M.CmBlock{1734816056, 1419143539, 139920982, 1223343683}} : Result<&2, &2, L.LcError, M.CmBlock>}

# NESSIE Serpent-128 test vectors, set 3 vector 0: the zero key and the
# zero block, ciphertext 3620B17AE6A993D09618B8768266BAE9
law serpent_nessie:
  {Result.map(&2, &2, L.LcError, P.LcSerpentKey, M.CmBlock, k => P.LcSerpent.encrypt(k, M.CmBlock{0, 0, 0, 0}), P.LcSerpent.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) == Done{M.CmBlock{908112250, 3869873104, 2518202486, 2187770601}} : Result<&2, &2, L.LcError, M.CmBlock>}

# a DES key of 7 bytes is refused
law des_bad_key_length:
  {Result.map(&2, &2, L.LcError, D.LcDesKey, Unit, k => Unit{}, D.LcDes.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{7n}} : Result<&2, &2, L.LcError, Unit>}

# a TDEA key bundle of 8 bytes is refused (keying option 3 is not allowed)
law tdes_bad_key_length:
  {Result.map(&2, &2, L.LcError, T.LcTdesKey, Unit, k => Unit{}, T.LcTdes.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{8n}} : Result<&2, &2, L.LcError, Unit>}

# a Camellia key of 20 bytes is refused
law camellia_bad_key_length:
  {Result.map(&2, &2, L.LcError, C.LcCamelliaKey, Unit, k => Unit{}, C.LcCamellia.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{20n}} : Result<&2, &2, L.LcError, Unit>}

# a Serpent key longer than 256 bits is refused
law serpent_bad_key_length:
  {Result.map(&2, &2, L.LcError, P.LcSerpentKey, Unit, k => Unit{}, P.LcSerpent.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{33n}} : Result<&2, &2, L.LcError, Unit>}

# RFC 5794, Appendix A.1: ARIA-128, key 000102030405060708090A0B0C0D0E0F,
# plaintext 00112233445566778899AABBCCDDEEFF, ciphertext
# D718FBD6AB644C739DA95F3BE6451778
law aria_rfc5794:
  {Result.map(&2, &2, L.LcError, A.LcAriaKey, M.CmBlock, k => A.LcAria.encrypt(k, M.CmBlock{1122867, 1146447479, 2291772091, 3437096703}), A.LcAria.key(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]))) == Done{M.CmBlock{3608738774, 2875477107, 2645122875, 3863287672}} : Result<&2, &2, L.LcError, M.CmBlock>}

# RFC 2144, Appendix B.1: CAST-128 with the 128-bit key
# 0123456712345678234567893456789A, plaintext 0123456789ABCDEF, ciphertext
# 238B4FE5847E44B2
law cast5_rfc2144:
  {Result.map(&2, &2, L.LcError, C5.LcCast5Key, L.LcBlock64, k => C5.LcCast5.encrypt(k, L.LcBlock64{19088743, 2309737967}), C5.LcCast5.key(B.Octets.of_list([1, 35, 69, 103, 18, 52, 86, 120, 35, 69, 103, 137, 52, 86, 120, 154]))) == Done{L.LcBlock64{596332517, 2222867634}} : Result<&2, &2, L.LcError, L.LcBlock64>}

# the FCrypt specification's second vector: key 114477AADD003366,
# plaintext 123456789ABCDEF0, ciphertext D8ED787477EC0680
law fcrypt_spec:
  {Result.map(&2, &2, L.LcError, FC.LcFcryptKey, L.LcBlock64, k => FC.LcFcrypt.encrypt(k, L.LcBlock64{305419896, 2596069104}), FC.LcFcrypt.key(B.Octets.of_list([17, 68, 119, 170, 221, 0, 51, 102]))) == Done{L.LcBlock64{3639441524, 2011956864}} : Result<&2, &2, L.LcError, L.LcBlock64>}

# an ARIA key of 20 bytes is refused
law aria_bad_key_length:
  {Result.map(&2, &2, L.LcError, A.LcAriaKey, Unit, k => Unit{}, A.LcAria.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{20n}} : Result<&2, &2, L.LcError, Unit>}

# a CAST-256 key of 18 bytes is refused
law cast6_bad_key_length:
  {Result.map(&2, &2, L.LcError, C6.LcCast6Key, Unit, k => Unit{}, C6.LcCast6.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{18n}} : Result<&2, &2, L.LcError, Unit>}

# a Blowfish key of 3 bytes is refused (32 bits at least)
law blowfish_bad_key_length:
  {Result.map(&2, &2, L.LcError, BF.LcBlowfishKey, Unit, k => Unit{}, BF.LcBlowfish.key(B.Octets.of_list([0, 0, 0]))) == Fail{L.LcBadKeyLength{3n}} : Result<&2, &2, L.LcError, Unit>}

# a CAST-128 key of 4 bytes is refused (40 bits at least)
law cast5_bad_key_length:
  {Result.map(&2, &2, L.LcError, C5.LcCast5Key, Unit, k => Unit{}, C5.LcCast5.key(B.Octets.of_list([0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{4n}} : Result<&2, &2, L.LcError, Unit>}

# a TEA key of 15 bytes is refused
law tea_bad_key_length:
  {Result.map(&2, &2, L.LcError, TE.LcTeaKey, Unit, k => Unit{}, TE.LcTea.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{15n}} : Result<&2, &2, L.LcError, Unit>}

# an XTEA key of 17 bytes is refused
law xtea_bad_key_length:
  {Result.map(&2, &2, L.LcError, XT.LcXteaKey, Unit, k => Unit{}, XT.LcXtea.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{17n}} : Result<&2, &2, L.LcError, Unit>}

# an FCrypt key of 7 bytes is refused
law fcrypt_bad_key_length:
  {Result.map(&2, &2, L.LcError, FC.LcFcryptKey, Unit, k => Unit{}, FC.LcFcrypt.key(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0]))) == Fail{L.LcBadKeyLength{7n}} : Result<&2, &2, L.LcError, Unit>}

# an empty RC4 key is refused
law rc4_empty_key:
  {R.LcRc4.crypt(B.Octets.empty(), B.Octets.zeros(4n)) == Fail{L.LcBadKeyLength{0n}} : Result<&2, &2, L.LcError, B.Octets>}

# the 64-bit modes refuse a message that is not whole blocks
law modes64_not_whole_blocks:
  {Result.map(&2, &2, L.LcError, List<&2, L.LcBlock64>, Unit, bs => Unit{}, X.Lc64.blocks_of(B.Octets.zeros(12n))) == Fail{L.LcNotBlockMultiple{12n}} : Result<&2, &2, L.LcError, Unit>}

# END GENERATED: vectors
