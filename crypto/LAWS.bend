# Laws of the interfaces and of the generic algorithms built on them.
#
# Generic laws (first part) hold for every algorithm that has an interface's
# shape, so they are stated once over its template arguments: they need
# nothing from the algorithm but its type. A law that needs a property of the
# algorithm (a block cipher's decryption undoes its encryption, a hash in
# pieces is the hash of the whole) cannot take that property as a hypothesis
# and still pass --verdict (a template hypothesis has no model in the BendTT
# kernel, and an ordinary one is affine, so an induction cannot use it at
# every step). Those laws are stated once per instance instead, from the law
# schemas in gen/instances.py, which also writes their proofs (second part).
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/aes.bend as X
import ../cipher-modes/ccm.bend as MC
import ../legacy-ciphers/legacy-ciphers.bend as L
import ../legacy-ciphers/des.bend as D
import ../legacy-ciphers/tdes.bend as T
import ../legacy-ciphers/sm4.bend as S
import ../legacy-ciphers/camellia.bend as Ca
import ../legacy-ciphers/serpent.bend as Sp
import ../legacy-ciphers/twofish.bend as Tf
import ../legacy-ciphers/rc4.bend as R
import ../crc/crc.bend as C
import ./crypto.bend as Cr
import ./stream.bend as St
import ./block.bend as Bk
import ./modes.bend as Md
import ./hash.bend as H
import ./mac.bend as Mc
import ./hmac.bend as Hm
import ./hkdf.bend as Hk
import ./sign.bend as Sg
import ./kex.bend as Kx
import ./inst_cm.bend as CM
import ./inst_lc.bend as LC
import ./inst_aes.bend as A
import ./inst_rc4.bend as RC
import ./inst_ccm.bend as CC
import ./inst_cmac.bend as CMI
import ./inst_crc.bend as CR
import ./inst_sha2.bend as SH
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/sha.bend as F256
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/sha512.bend as F512

# Stream ciphers from keystream generators (stream.bend): for every keystream
# generator, CrXor satisfies the stream-cipher laws

# the cipher is its own inverse: from one state, applied twice, the data
# comes back
law xor_involution:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +m: B.Octets
  {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, m)))) == m : B.Octets}

# data in pieces: the output of a ++ b is the output of a, then the output of
# b from the state after a
law xor_streaming_data:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == B.Octets.append(St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, a)), St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, a)), b))) : B.Octets}

law xor_streaming_state:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, a)), b)) : S}

# CTR over any block cipher (modes.bend) is CrXor over its keystream
# generator, so it satisfies the stream-cipher laws for every block cipher

law ctr_involution:
  for ~K: Data
  for ~Blk: Data
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +s: Md.CrCtrState<K>
  for +m: B.Octets
  {St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, m)))) == m : B.Octets}

law ctr_streaming_data:
  for ~K: Data
  for ~Blk: Data
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +s: Md.CrCtrState<K>
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, B.Octets.append(a, b))) == B.Octets.append(St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, a)), St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, St.CrXor.out_state(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, a)), b))) : B.Octets}

law ctr_streaming_state:
  for ~K: Data
  for ~Blk: Data
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +s: Md.CrCtrState<K>
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_state(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, B.Octets.append(a, b))) == St.CrXor.out_state(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, St.CrXor.out_state(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, a)), b)) : Md.CrCtrState<K>}

# The block formats (inst_cm.bend, inst_lc.bend): a block read back from its
# bytes is itself, and XOR with the same block twice changes nothing

law cmblock_format:
  for +b: M.CmBlock
  {CM.CrBlk128.of_octets(CM.CrBlk128.to_octets(b)) == Some{b} : Maybe<&2, M.CmBlock>}

law cmblock_xor:
  for a: M.CmBlock
  for b: M.CmBlock
  {CM.CrBlk128.xor(CM.CrBlk128.xor(a, b), b) == a : M.CmBlock}

law lcblock64_format:
  for +b: L.LcBlock64
  {L.LcBlock64.of_octets(L.LcBlock64.to_octets(b)) == Some{b} : Maybe<&2, L.LcBlock64>}

law lcblock64_xor:
  for a: L.LcBlock64
  for b: L.LcBlock64
  {LC.CrBlk64.xor(LC.CrBlk64.xor(a, b), b) == a : L.LcBlock64}

# MACs (mac.bend): the named default verify accepts the computed tag, and
# exactly it, for every MAC; so HMAC over any hash, and CMAC over any 128-bit
# block cipher, accept what they compute

law mac_verify_tag_accepts:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for +k: K
  for +m: B.Octets
  {Mc.CrMac.verify_tag(~K, ~compute, k, m, compute(k, m)) == True{} : Bool}

law mac_verify_tag_agrees:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for +k: K
  for +m: B.Octets
  for t: B.Octets
  {Mc.CrMac.verify_tag(~K, ~compute, k, m, t) == B.Octets.is_eq(compute(k, m), t) : Bool}

law hmac_accepts:
  for ~digest: B.Octets -> B.Octets
  for +kk: Hm.CrHmacKey
  for +m: B.Octets
  {Hm.CrHmac.verify(~digest, kk, m, Hm.CrHmac.mac(~digest, kk, m)) == True{} : Bool}

law cmac_accepts:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +m: B.Octets
  {CMI.CrCmac.verify(~K, ~enc, k, m, CMI.CrCmac.mac(~K, ~enc, k, m)) == True{} : Bool}

# CRCs as hashes (inst_crc.bend), for every parameter set: the register in
# pieces is the register of the whole, and so the streaming digest of any
# split is the one-shot digest

law crc32_hash_streaming:
  for ~spec: C.Crc32Spec
  for c: U32
  for +a: B.Octets
  for +b: B.Octets
  {CR.CrCrc32.update(~spec, c, B.Octets.append(a, b)) == CR.CrCrc32.update(~spec, CR.CrCrc32.update(~spec, c, a), b) : U32}

law crc32_hash_split:
  for ~spec: C.Crc32Spec
  for +a: B.Octets
  for +b: B.Octets
  {CR.CrCrc32.final(~spec, CR.CrCrc32.update(~spec, CR.CrCrc32.update(~spec, CR.CrCrc32.init(~spec), a), b)) == CR.CrCrc32.digest(~spec, B.Octets.append(a, b)) : B.Octets}

law crc64_hash_streaming:
  for ~spec: C.Crc64Spec
  for c: W.W64
  for +a: B.Octets
  for +b: B.Octets
  {CR.CrCrc64.update(~spec, c, B.Octets.append(a, b)) == CR.CrCrc64.update(~spec, CR.CrCrc64.update(~spec, c, a), b) : W.W64}

law crc64_hash_split:
  for ~spec: C.Crc64Spec
  for +a: B.Octets
  for +b: B.Octets
  {CR.CrCrc64.final(~spec, CR.CrCrc64.update(~spec, CR.CrCrc64.update(~spec, CR.CrCrc64.init(~spec), a), b)) == CR.CrCrc64.digest(~spec, B.Octets.append(a, b)) : B.Octets}

# AEADs: an algorithm's round trip survives the mapping of its errors onto
# CrError, for every algorithm (r: its encryption's result, d: its
# decryption)

law lift_round_trip:
  for ~E: Data
  for ~f: E -> Cr.CrError
  for d: B.Octets -> Result<&2, &2, E, B.Octets>
  for r: Result<&2, &2, E, B.Octets>
  for +p: B.Octets
  for h: {Result.bind(&2, &2, E, B.Octets, B.Octets, r, d) == Result.map(&2, &2, E, B.Octets, B.Octets, c => p, r) : Result<&2, &2, E, B.Octets>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Cr.CrError.lift(~E, ~B.Octets, ~f, r), c => Cr.CrError.lift(~E, ~B.Octets, ~f, d(c))) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, Cr.CrError.lift(~E, ~B.Octets, ~f, r)) : Result<&2, &2, Cr.CrError, B.Octets>}

# CCM as an AEAD (inst_ccm.bend), for every 128-bit block cipher, key, tag
# length, nonce, associated data and message: the AEAD round trip, given
# cipher-modes' ccm_round_trip at the same arguments (h). cipher-modes
# proves h for every input, but a proof that imports its PROOF.bend fails
# --verdict (its laws with a template hypothesis), so the two are joined in
# README.md, not here.
law ccm_round_trip_if:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~tlen: Nat
  for +k: K
  for +nonce: B.Octets
  for +aad: B.Octets
  for +p: B.Octets
  for h: {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, MC.Ccm.encrypt(~K, ~enc, k, tlen, nonce, aad, p), c => MC.Ccm.decrypt(~K, ~enc, k, tlen, nonce, aad, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, MC.Ccm.encrypt(~K, ~enc, k, tlen, nonce, aad, p)) : Result<&2, &2, M.CmError, B.Octets>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, CC.CrCcm.seal(~K, ~enc, ~tlen, k, nonce, aad, p), c => CC.CrCcm.open(~K, ~enc, ~tlen, k, nonce, aad, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, CC.CrCcm.seal(~K, ~enc, ~tlen, k, nonce, aad, p)) : Result<&2, &2, Cr.CrError, B.Octets>}

# Signatures and key agreement (sign.bend, kex.bend): no algorithm of
# bend-osdev is one yet, so their interface laws (README.md) have no
# instance; what is proved here is that the generic helpers keep them. A
# signature checked from the public key's bytes is accepted, for every
# scheme, secret key and message, when the scheme's pk_format and accepts
# laws hold there (hf, ha)
law sign_verify_bytes_if:
  for ~SK: Data
  for ~PK: Data
  for ~public: SK -> PK
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~pk_to: PK -> B.Octets
  for ~sign: SK -> B.Octets -> B.Octets
  for ~verify: PK -> B.Octets -> B.Octets -> Bool
  for +sk: SK
  for +m: B.Octets
  for hf: {pk_of(pk_to(public(sk))) == Done{public(sk)} : Result<&2, &2, Cr.CrError, PK>}
  for ha: {verify(public(sk), m, sign(sk, m)) == True{} : Bool}
  {Sg.CrSign.verify_bytes(~PK, ~pk_of, ~verify, pk_to(public(sk)), m, sign(sk, m)) == True{} : Bool}

# two parties agree from each other's public-key bytes, for every scheme and
# pair of secret keys, when the keys parse (hx, hy), the public keys survive
# their bytes (hfx, hfy) and the scheme's agree law holds for them (h)
law kex_agree_if:
  for ~SK: Data
  for ~PK: Data
  for ~secret: B.Octets -> Result<&2, &2, Cr.CrError, SK>
  for ~public: SK -> PK
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~pk_to: PK -> B.Octets
  for ~shared: SK -> PK -> Result<&2, &2, Cr.CrError, B.Octets>
  for +a: B.Octets
  for +b: B.Octets
  for +x: SK
  for +y: SK
  for hx: {secret(a) == Done{x} : Result<&2, &2, Cr.CrError, SK>}
  for hy: {secret(b) == Done{y} : Result<&2, &2, Cr.CrError, SK>}
  for hfx: {pk_of(pk_to(public(x))) == Done{public(x)} : Result<&2, &2, Cr.CrError, PK>}
  for hfy: {pk_of(pk_to(public(y))) == Done{public(y)} : Result<&2, &2, Cr.CrError, PK>}
  for h: {shared(x, public(y)) == shared(y, public(x)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, a, pk_to(public(y))) == Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, b, pk_to(public(x))) : Result<&2, &2, Cr.CrError, B.Octets>}

# Vectors, proved by computation: CRC check values (the reveng catalogue)
# through the hash interface

law crc32_hash_check:
  {CR.CrCrc32.digest(~C.crc32.spec(), B.Octets.of_string("123456789")) == B.Octets.of_list([203, 244, 57, 38]) : B.Octets}

law crc32c_hash_check:
  {CR.CrCrc32.digest(~C.crc32c.spec(), B.Octets.of_string("123456789")) == B.Octets.of_list([227, 6, 146, 131]) : B.Octets}

law crc64_xz_hash_check:
  {CR.CrCrc64.digest(~C.crc64_xz.spec(), B.Octets.of_string("123456789")) == B.Octets.of_list([153, 93, 201, 187, 223, 25, 57, 250]) : B.Octets}

# a CRC-32 digest is 4 bytes, for every parameter set and register
law crc32_hash_length:
  for ~spec: C.Crc32Spec
  for c: U32
  {B.Octets.len(CR.CrCrc32.final(~spec, c)) == 4n : Nat}

# HMAC over CRC-32 (the key "key", the message "The quick brown fox"): the
# value of Python's hmac module over binascii.crc32 (ref/gen.py checks the
# same construction on random keys and messages)
law hmac_crc32_vector:
  {Hm.CrHmac.mac(~CR.CrCrc32.digest(~C.crc32.spec()), Hm.CrHmac.key(~64n, ~CR.CrCrc32.digest(~C.crc32.spec()), B.Octets.of_string("key")), B.Octets.of_string("The quick brown fox")) == B.Octets.of_list([69, 52, 205, 87]) : B.Octets}

# refusals: an RC4 key of 0 bytes, an IV given to RC4, a CTR counter block
# of the wrong length, bytes that are not whole blocks, and an HKDF output
# longer than 255 digests
law rc4_empty_key:
  {Result.map(&2, &2, Cr.CrError, R.LcRc4State, Unit, s => Unit{}, RC.CrRc4.start(B.Octets.empty(), B.Octets.empty())) == Fail{Cr.CrBadKeyLength{0n}} : Result<&2, &2, Cr.CrError, Unit>}

law rc4_iv_refused:
  {Result.map(&2, &2, Cr.CrError, R.LcRc4State, Unit, s => Unit{}, RC.CrRc4.start(B.Octets.empty(), B.Octets.zeros(1n))) == Fail{Cr.CrBadIvLength{1n}} : Result<&2, &2, Cr.CrError, Unit>}

law ctr_bad_iv:
  {Result.map(&2, &2, Cr.CrError, Md.CrCtrState<D.LcDesKey>, Unit, s => Unit{}, Md.CrCtr.start(~D.LcDesKey, ~8n, ~LC.CrLc.key(~D.LcDesKey, ~D.LcDes.key), B.Octets.zeros(8n), B.Octets.zeros(7n))) == Fail{Cr.CrBadIvLength{7n}} : Result<&2, &2, Cr.CrError, Unit>}

law blocks_of_not_whole:
  {Result.map(&2, &2, Cr.CrError, List<&2, L.LcBlock64>, Unit, bs => Unit{}, Md.CrModes.blocks_of(~L.LcBlock64, ~8n, ~L.LcBlock64.of_octets, B.Octets.zeros(12n))) == Fail{Cr.CrNotBlockMultiple{12n}} : Result<&2, &2, Cr.CrError, Unit>}

law hkdf_too_long:
  {Result.map(&2, &2, Cr.CrError, B.Octets, Unit, o => Unit{}, Hk.CrHkdf.derive(~64n, ~4n, ~CR.CrCrc32.digest(~C.crc32.spec()), B.Octets.of_string("ikm"), B.Octets.empty(), B.Octets.empty(), 1021n)) == Fail{Cr.CrBadOutputLength{1021n}} : Result<&2, &2, Cr.CrError, Unit>}

# FIPS 197 Appendix C.1 through the block-cipher interface: AES-128, its
# encryption key schedule then one block of bytes (with CrAes.key, which
# computes the decryption round keys too, the vector checks but runs past
# --verdict's kernel; check.bend runs it both ways)
law aes_fips197_c1:
  {Bk.CrBlockCipher.encrypt_with(~X.CmAesKey, ~M.CmBlock, ~A.CrAes.key_enc, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255])) == Done{B.Octets.of_list([105, 196, 224, 216, 106, 123, 4, 48, 216, 205, 183, 128, 112, 180, 197, 90])} : Result<&2, &2, Cr.CrError, B.Octets>}

# A CRC in three pieces is the CRC of the whole, for every parameter set

law crc32_hash_split3:
  for ~spec: C.Crc32Spec
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {CR.CrCrc32.final(~spec, CR.CrCrc32.update(~spec, CR.CrCrc32.update(~spec, CR.CrCrc32.update(~spec, CR.CrCrc32.init(~spec), a), b), c)) == CR.CrCrc32.digest(~spec, B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

law crc64_hash_split3:
  for ~spec: C.Crc64Spec
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {CR.CrCrc64.final(~spec, CR.CrCrc64.update(~spec, CR.CrCrc64.update(~spec, CR.CrCrc64.update(~spec, CR.CrCrc64.init(~spec), a), b), c)) == CR.CrCrc64.digest(~spec, B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# SHA-256 and SHA-512 as hashes (inst_sha2.bend), from
# bend-collections-laws-crypto's laws: the one-shot digest is FIPS 180-4's
# executable specification (in that package's spec/), the streaming digest
# of any split into two or three pieces is the one-shot digest, and a
# digest is 32 (64) bytes. bend-collections proves the pieces only from the
# start (new_sha256()), so the stronger streaming law (for every state) is
# tested, not proved.

law sha256_spec:
  for +o: B.Octets
  {SH.CrSha2.sha256(o) == B.Octets.of_list(F256.sha256_bytes(B.Octets.to_list(o))) : B.Octets}

law sha256_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init256(), a), b)) == SH.CrSha2.sha256(B.Octets.append(a, b)) : B.Octets}

law sha256_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init256(), a), b), c)) == SH.CrSha2.sha256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

law sha256_hash_length:
  for +o: B.Octets
  {B.Octets.len(SH.CrSha2.sha256(o)) == 32n : Nat}

law sha512_spec:
  for +o: B.Octets
  {SH.CrSha2.sha512(o) == B.Octets.of_list(F512.sha512_bytes(B.Octets.to_list(o))) : B.Octets}

law sha512_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init512(), a), b)) == SH.CrSha2.sha512(B.Octets.append(a, b)) : B.Octets}

law sha512_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init512(), a), b), c)) == SH.CrSha2.sha512(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

law sha512_hash_length:
  for +o: B.Octets
  {B.Octets.len(SH.CrSha2.sha512(o)) == 64n : Nat}

# HKDF over SHA-256 refuses more than 255 digests (8160 bytes)
law hkdf_sha256_too_long:
  {Result.map(&2, &2, Cr.CrError, B.Octets, Unit, o => Unit{}, Hk.CrHkdf.derive(~64n, ~32n, ~SH.CrSha2.sha256, B.Octets.of_string("ikm"), B.Octets.empty(), B.Octets.empty(), 8161n)) == Fail{Cr.CrBadOutputLength{8161n}} : Result<&2, &2, Cr.CrError, Unit>}

# FIPS 180-4's example "abc" (NIST's SHA examples), through the hash
# interface
law sha256_abc:
  {SH.CrSha2.sha256(B.Octets.of_string("abc")) == B.Octets.of_list([186, 120, 22, 191, 143, 1, 207, 234, 65, 65, 64, 222, 93, 174, 34, 35, 176, 3, 97, 163, 150, 23, 122, 156, 180, 16, 255, 97, 242, 0, 21, 173]) : B.Octets}

# RFC 4231 test case 2: HMAC-SHA-256 with the key "Jefe"
law hmac_sha256_rfc4231_2:
  {Hm.CrHmac.mac(~SH.CrSha2.sha256, Hm.CrHmac.key(~64n, ~SH.CrSha2.sha256, B.Octets.of_string("Jefe")), B.Octets.of_string("what do ya want for nothing?")) == B.Octets.of_list([91, 220, 193, 70, 191, 96, 117, 78, 106, 4, 36, 38, 8, 149, 117, 199, 90, 0, 63, 8, 157, 39, 57, 131, 157, 236, 88, 185, 100, 236, 56, 67]) : B.Octets}

# Per-instance laws, from the law schemas (gen/instances.py)

# BEGIN GENERATED by gen/instances.py: laws
# DES (legacy-ciphers): decryption undoes encryption, for every key and block
law des_block_round_trip:
  for k: D.LcDesKey
  for +b: L.LcBlock64
  {D.LcDes.decrypt(k, D.LcDes.encrypt(k, b)) == b : L.LcBlock64}

# DES (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law des_block_round_trip_dual:
  for k: D.LcDesKey
  for +b: L.LcBlock64
  {D.LcDes.encrypt(k, D.LcDes.decrypt(k, b)) == b : L.LcBlock64}

# DES (legacy-ciphers): a key of 7 bytes is refused
law des_key_length:
  {Result.map(&2, &2, Cr.CrError, D.LcDesKey, Unit, k => Unit{}, LC.CrLc.key(~D.LcDesKey, ~D.LcDes.key, B.Octets.zeros(7n))) == Fail{Cr.CrBadKeyLength{7n}} : Result<&2, &2, Cr.CrError, Unit>}

# DES (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law des_ecb_round_trip:
  for +k: D.LcDesKey
  for +bs: List<&2, L.LcBlock64>
  {Md.CrEcb.decrypt_blocks(~D.LcDesKey, ~L.LcBlock64, ~D.LcDes.decrypt, k, Md.CrEcb.encrypt_blocks(~D.LcDesKey, ~L.LcBlock64, ~D.LcDes.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

# DES (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law des_cbc_round_trip:
  for +k: D.LcDesKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Md.CrCbc.decrypt_blocks(~D.LcDesKey, ~L.LcBlock64, ~D.LcDes.decrypt, ~LC.CrBlk64.xor, k, iv, Md.CrCbc.encrypt_blocks(~D.LcDesKey, ~L.LcBlock64, ~D.LcDes.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# Triple DES (legacy-ciphers): decryption undoes encryption, for every key and block
law tdes_block_round_trip:
  for k: T.LcTdesKey
  for +b: L.LcBlock64
  {T.LcTdes.decrypt(k, T.LcTdes.encrypt(k, b)) == b : L.LcBlock64}

# Triple DES (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law tdes_block_round_trip_dual:
  for k: T.LcTdesKey
  for +b: L.LcBlock64
  {T.LcTdes.encrypt(k, T.LcTdes.decrypt(k, b)) == b : L.LcBlock64}

# Triple DES (legacy-ciphers): a key of 8 bytes is refused
law tdes_key_length:
  {Result.map(&2, &2, Cr.CrError, T.LcTdesKey, Unit, k => Unit{}, LC.CrLc.key(~T.LcTdesKey, ~T.LcTdes.key, B.Octets.zeros(8n))) == Fail{Cr.CrBadKeyLength{8n}} : Result<&2, &2, Cr.CrError, Unit>}

# Triple DES (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law tdes_ecb_round_trip:
  for +k: T.LcTdesKey
  for +bs: List<&2, L.LcBlock64>
  {Md.CrEcb.decrypt_blocks(~T.LcTdesKey, ~L.LcBlock64, ~T.LcTdes.decrypt, k, Md.CrEcb.encrypt_blocks(~T.LcTdesKey, ~L.LcBlock64, ~T.LcTdes.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

# Triple DES (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law tdes_cbc_round_trip:
  for +k: T.LcTdesKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Md.CrCbc.decrypt_blocks(~T.LcTdesKey, ~L.LcBlock64, ~T.LcTdes.decrypt, ~LC.CrBlk64.xor, k, iv, Md.CrCbc.encrypt_blocks(~T.LcTdesKey, ~L.LcBlock64, ~T.LcTdes.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# SM4 (legacy-ciphers): decryption undoes encryption, for every key and block
law sm4_block_round_trip:
  for k: S.LcSm4Key
  for +b: M.CmBlock
  {S.LcSm4.decrypt(k, S.LcSm4.encrypt(k, b)) == b : M.CmBlock}

# SM4 (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law sm4_block_round_trip_dual:
  for k: S.LcSm4Key
  for +b: M.CmBlock
  {S.LcSm4.encrypt(k, S.LcSm4.decrypt(k, b)) == b : M.CmBlock}

# SM4 (legacy-ciphers): a key of 15 bytes is refused
law sm4_key_length:
  {Result.map(&2, &2, Cr.CrError, S.LcSm4Key, Unit, k => Unit{}, LC.CrLc.key(~S.LcSm4Key, ~S.LcSm4.key, B.Octets.zeros(15n))) == Fail{Cr.CrBadKeyLength{15n}} : Result<&2, &2, Cr.CrError, Unit>}

# SM4 (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law sm4_ecb_round_trip:
  for +k: S.LcSm4Key
  for +bs: List<&2, M.CmBlock>
  {Md.CrEcb.decrypt_blocks(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.decrypt, k, Md.CrEcb.encrypt_blocks(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.encrypt, k, bs)) == bs : List<&2, M.CmBlock>}

# SM4 (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law sm4_cbc_round_trip:
  for +k: S.LcSm4Key
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Md.CrCbc.decrypt_blocks(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.decrypt, ~CM.CrBlk128.xor, k, iv, Md.CrCbc.encrypt_blocks(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# Camellia (legacy-ciphers): decryption undoes encryption, for every key and block
law camellia_block_round_trip:
  for k: Ca.LcCamelliaKey
  for +b: M.CmBlock
  {Ca.LcCamellia.decrypt(k, Ca.LcCamellia.encrypt(k, b)) == b : M.CmBlock}

# Camellia (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law camellia_block_round_trip_dual:
  for k: Ca.LcCamelliaKey
  for +b: M.CmBlock
  {Ca.LcCamellia.encrypt(k, Ca.LcCamellia.decrypt(k, b)) == b : M.CmBlock}

# Camellia (legacy-ciphers): a key of 20 bytes is refused
law camellia_key_length:
  {Result.map(&2, &2, Cr.CrError, Ca.LcCamelliaKey, Unit, k => Unit{}, LC.CrLc.key(~Ca.LcCamelliaKey, ~Ca.LcCamellia.key, B.Octets.zeros(20n))) == Fail{Cr.CrBadKeyLength{20n}} : Result<&2, &2, Cr.CrError, Unit>}

# Camellia (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law camellia_ecb_round_trip:
  for +k: Ca.LcCamelliaKey
  for +bs: List<&2, M.CmBlock>
  {Md.CrEcb.decrypt_blocks(~Ca.LcCamelliaKey, ~M.CmBlock, ~Ca.LcCamellia.decrypt, k, Md.CrEcb.encrypt_blocks(~Ca.LcCamelliaKey, ~M.CmBlock, ~Ca.LcCamellia.encrypt, k, bs)) == bs : List<&2, M.CmBlock>}

# Camellia (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law camellia_cbc_round_trip:
  for +k: Ca.LcCamelliaKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Md.CrCbc.decrypt_blocks(~Ca.LcCamelliaKey, ~M.CmBlock, ~Ca.LcCamellia.decrypt, ~CM.CrBlk128.xor, k, iv, Md.CrCbc.encrypt_blocks(~Ca.LcCamelliaKey, ~M.CmBlock, ~Ca.LcCamellia.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# Serpent (legacy-ciphers): decryption undoes encryption, for every key and block
law serpent_block_round_trip:
  for k: Sp.LcSerpentKey
  for +b: M.CmBlock
  {Sp.LcSerpent.decrypt(k, Sp.LcSerpent.encrypt(k, b)) == b : M.CmBlock}

# Serpent (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law serpent_block_round_trip_dual:
  for k: Sp.LcSerpentKey
  for +b: M.CmBlock
  {Sp.LcSerpent.encrypt(k, Sp.LcSerpent.decrypt(k, b)) == b : M.CmBlock}

# Serpent (legacy-ciphers): a key of 33 bytes is refused
law serpent_key_length:
  {Result.map(&2, &2, Cr.CrError, Sp.LcSerpentKey, Unit, k => Unit{}, LC.CrLc.key(~Sp.LcSerpentKey, ~Sp.LcSerpent.key, B.Octets.zeros(33n))) == Fail{Cr.CrBadKeyLength{33n}} : Result<&2, &2, Cr.CrError, Unit>}

# Serpent (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law serpent_ecb_round_trip:
  for +k: Sp.LcSerpentKey
  for +bs: List<&2, M.CmBlock>
  {Md.CrEcb.decrypt_blocks(~Sp.LcSerpentKey, ~M.CmBlock, ~Sp.LcSerpent.decrypt, k, Md.CrEcb.encrypt_blocks(~Sp.LcSerpentKey, ~M.CmBlock, ~Sp.LcSerpent.encrypt, k, bs)) == bs : List<&2, M.CmBlock>}

# Serpent (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law serpent_cbc_round_trip:
  for +k: Sp.LcSerpentKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Md.CrCbc.decrypt_blocks(~Sp.LcSerpentKey, ~M.CmBlock, ~Sp.LcSerpent.decrypt, ~CM.CrBlk128.xor, k, iv, Md.CrCbc.encrypt_blocks(~Sp.LcSerpentKey, ~M.CmBlock, ~Sp.LcSerpent.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# Twofish (legacy-ciphers): decryption undoes encryption, for every key and block
law twofish_block_round_trip:
  for k: Tf.LcTwofishKey
  for +b: M.CmBlock
  {Tf.LcTwofish.decrypt(k, Tf.LcTwofish.encrypt(k, b)) == b : M.CmBlock}

# Twofish (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law twofish_block_round_trip_dual:
  for k: Tf.LcTwofishKey
  for +b: M.CmBlock
  {Tf.LcTwofish.encrypt(k, Tf.LcTwofish.decrypt(k, b)) == b : M.CmBlock}

# Twofish (legacy-ciphers): a key of 20 bytes is refused
law twofish_key_length:
  {Result.map(&2, &2, Cr.CrError, Tf.LcTwofishKey, Unit, k => Unit{}, LC.CrLc.key(~Tf.LcTwofishKey, ~Tf.LcTwofish.key, B.Octets.zeros(20n))) == Fail{Cr.CrBadKeyLength{20n}} : Result<&2, &2, Cr.CrError, Unit>}

# Twofish (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law twofish_ecb_round_trip:
  for +k: Tf.LcTwofishKey
  for +bs: List<&2, M.CmBlock>
  {Md.CrEcb.decrypt_blocks(~Tf.LcTwofishKey, ~M.CmBlock, ~Tf.LcTwofish.decrypt, k, Md.CrEcb.encrypt_blocks(~Tf.LcTwofishKey, ~M.CmBlock, ~Tf.LcTwofish.encrypt, k, bs)) == bs : List<&2, M.CmBlock>}

# Twofish (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law twofish_cbc_round_trip:
  for +k: Tf.LcTwofishKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Md.CrCbc.decrypt_blocks(~Tf.LcTwofishKey, ~M.CmBlock, ~Tf.LcTwofish.decrypt, ~CM.CrBlk128.xor, k, iv, Md.CrCbc.encrypt_blocks(~Tf.LcTwofishKey, ~M.CmBlock, ~Tf.LcTwofish.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# AES-128 and AES-256 (cipher-modes): a key of 24 bytes is refused
law aes_key_length:
  {Result.map(&2, &2, Cr.CrError, X.CmAesKey, Unit, k => Unit{}, A.CrAes.key(B.Octets.zeros(24n))) == Fail{Cr.CrBadKeyLength{24n}} : Result<&2, &2, Cr.CrError, Unit>}

# AES, encryption key schedule only (cipher-modes): a key of 20 bytes is refused
law aes_enc_key_length:
  {Result.map(&2, &2, Cr.CrError, X.CmAesKey, Unit, k => Unit{}, A.CrAes.key_enc(B.Octets.zeros(20n))) == Fail{Cr.CrBadKeyLength{20n}} : Result<&2, &2, Cr.CrError, Unit>}

# RC4 (legacy-ciphers): from one state, applied twice, the data comes back
law rc4_stream_involution:
  for +s: R.LcRc4State
  for +m: B.Octets
  {R.LcRc4.out_data(R.LcRc4.update(s, R.LcRc4.out_data(R.LcRc4.update(s, m)))) == m : B.Octets}

# RC4 (legacy-ciphers): the output of a ++ b is the output of a, then of b from the state after a
law rc4_stream_streaming_data:
  for +s: R.LcRc4State
  for +a: B.Octets
  for +b: B.Octets
  {R.LcRc4.out_data(R.LcRc4.update(s, B.Octets.append(a, b))) == B.Octets.append(R.LcRc4.out_data(R.LcRc4.update(s, a)), R.LcRc4.out_data(R.LcRc4.update(R.LcRc4.out_state(R.LcRc4.update(s, a)), b))) : B.Octets}

# RC4 (legacy-ciphers): the state after a ++ b is the state after a, then b
law rc4_stream_streaming_state:
  for +s: R.LcRc4State
  for +a: B.Octets
  for +b: B.Octets
  {R.LcRc4.out_state(R.LcRc4.update(s, B.Octets.append(a, b))) == R.LcRc4.out_state(R.LcRc4.update(R.LcRc4.out_state(R.LcRc4.update(s, a)), b)) : R.LcRc4State}

# HMAC over CRC-32 of any parameter set (crc): the state after a ++ b is the state after a, then b
law hmac_crc32_streaming:
  for ~spec: C.Crc32Spec
  for s: Hm.CrHmacState<U32>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~U32, ~CR.CrCrc32.update(~spec), s, B.Octets.append(a, b)) == Hm.CrHmac.update(~U32, ~CR.CrCrc32.update(~spec), Hm.CrHmac.update(~U32, ~CR.CrCrc32.update(~spec), s, a), b) : Hm.CrHmacState<U32>}

# HMAC over CRC-32 of any parameter set (crc): the tag in pieces is the tag in one call, for every split
law hmac_crc32_split:
  for ~spec: C.Crc32Spec
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~U32, ~CR.CrCrc32.init(~spec), ~CR.CrCrc32.update(~spec), ~CR.CrCrc32.final(~spec), Hm.CrHmac.update(~U32, ~CR.CrCrc32.update(~spec), Hm.CrHmac.update(~U32, ~CR.CrCrc32.update(~spec), Hm.CrHmac.start(~U32, ~CR.CrCrc32.init(~spec), ~CR.CrCrc32.update(~spec), kk), a), b)) == Hm.CrHmac.mac(~CR.CrCrc32.digest(~spec), kk, B.Octets.append(a, b)) : B.Octets}

# HMAC over CRC-64 of any parameter set (crc): the state after a ++ b is the state after a, then b
law hmac_crc64_streaming:
  for ~spec: C.Crc64Spec
  for s: Hm.CrHmacState<W.W64>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~W.W64, ~CR.CrCrc64.update(~spec), s, B.Octets.append(a, b)) == Hm.CrHmac.update(~W.W64, ~CR.CrCrc64.update(~spec), Hm.CrHmac.update(~W.W64, ~CR.CrCrc64.update(~spec), s, a), b) : Hm.CrHmacState<W.W64>}

# HMAC over CRC-64 of any parameter set (crc): the tag in pieces is the tag in one call, for every split
law hmac_crc64_split:
  for ~spec: C.Crc64Spec
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~W.W64, ~CR.CrCrc64.init(~spec), ~CR.CrCrc64.update(~spec), ~CR.CrCrc64.final(~spec), Hm.CrHmac.update(~W.W64, ~CR.CrCrc64.update(~spec), Hm.CrHmac.update(~W.W64, ~CR.CrCrc64.update(~spec), Hm.CrHmac.start(~W.W64, ~CR.CrCrc64.init(~spec), ~CR.CrCrc64.update(~spec), kk), a), b)) == Hm.CrHmac.mac(~CR.CrCrc64.digest(~spec), kk, B.Octets.append(a, b)) : B.Octets}

# HMAC over SHA-256 (bend-collections): the tag in pieces is the tag in one call, for every split
law hmac_sha256_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~SH.CrSha2State, ~SH.CrSha2.init256(), ~SH.CrSha2.update, ~SH.CrSha2.final, Hm.CrHmac.update(~SH.CrSha2State, ~SH.CrSha2.update, Hm.CrHmac.update(~SH.CrSha2State, ~SH.CrSha2.update, Hm.CrHmac.start(~SH.CrSha2State, ~SH.CrSha2.init256(), ~SH.CrSha2.update, kk), a), b)) == Hm.CrHmac.mac(~SH.CrSha2.sha256, kk, B.Octets.append(a, b)) : B.Octets}

# HMAC over SHA-512 (bend-collections): the tag in pieces is the tag in one call, for every split
law hmac_sha512_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~SH.CrSha2State, ~SH.CrSha2.init512(), ~SH.CrSha2.update, ~SH.CrSha2.final, Hm.CrHmac.update(~SH.CrSha2State, ~SH.CrSha2.update, Hm.CrHmac.update(~SH.CrSha2State, ~SH.CrSha2.update, Hm.CrHmac.start(~SH.CrSha2State, ~SH.CrSha2.init512(), ~SH.CrSha2.update, kk), a), b)) == Hm.CrHmac.mac(~SH.CrSha2.sha512, kk, B.Octets.append(a, b)) : B.Octets}
# END GENERATED: laws
