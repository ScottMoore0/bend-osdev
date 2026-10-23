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
import ../legacy-ciphers/aria.bend as Ar
import ../legacy-ciphers/cast6.bend as C6
import ../legacy-ciphers/blowfish.bend as Bf
import ../legacy-ciphers/cast5.bend as C5
import ../legacy-ciphers/tea.bend as Te
import ../legacy-ciphers/xtea.bend as Xt
import ../legacy-ciphers/fcrypt.bend as Fc
import ../crc/crc.bend as C
import ./crypto.bend as Cr
import ./stream.bend as St
import ./block.bend as Bk
import ./modes.bend as Md
import ./pcbc.bend as Pc
import ./lrw.bend as Lw
import ./xcbc.bend as Xc
import ./vmac.bend as Vm
import ./cts.bend as Ct
import ./octets.bend as Oc
import ../gf/gf128.bend as G
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
import ./inst_sha3.bend as S3
import ../hashes/hashes.bend as Hs
import ../hashes/md4.bend as HM4
import ../hashes/md5.bend as HM5
import ../hashes/sha1.bend as HS1
import ../hashes/ripemd160.bend as HRM
import ../hashes/sm3.bend as HSM
import ../hashes/streebog.bend as HST
import ../hashes/michael.bend as HMI
import ./inst_michael.bend as MIC
import ./pbkdf2.bend as Pb
import ./inst_pbkdf2.bend as PbI
import ./kbkdf.bend as Kb
import ./inst_kbkdf.bend as KbI
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/sha.bend as F256
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/sha512.bend as F512
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/sha3.bend as F202

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

# XCBC-MAC over every block cipher (xcbc.bend) accepts what it computes
law xcbc_accepts:
  for ~K: Data
  for ~Blk: Data
  for ~bsize: Nat
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +kk: Xc.CrXcbcKey<K>
  for +m: B.Octets
  {Xc.CrXcbc.verify(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, m, Xc.CrXcbc.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, m)) == True{} : Bool}

# VMAC over every block cipher and nonce length (vmac.bend) accepts what it
# computes
law vmac_accepts:
  for ~K: Data
  for ~Blk: Data
  for ~bsize: Nat
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for ~nlen: Nat
  for +kk: Vm.CrVmacKey<K>
  for +m: B.Octets
  {Vm.CrVmac.verify(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, ~nlen, kk, m, Vm.CrVmac.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, ~nlen, kk, m)) == True{} : Bool}

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
# cipher-modes' ccm_round_trip at the same arguments (h); and, since
# cipher-modes proves h for every input, the AEAD round trip with no
# hypothesis (ccm_aead_round_trip)
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

law ccm_aead_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~tlen: Nat
  for +k: K
  for +nonce: B.Octets
  for +aad: B.Octets
  for +p: B.Octets
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, CC.CrCcm.seal(~K, ~enc, ~tlen, k, nonce, aad, p), c => CC.CrCcm.open(~K, ~enc, ~tlen, k, nonce, aad, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, CC.CrCcm.seal(~K, ~enc, ~tlen, k, nonce, aad, p)) : Result<&2, &2, Cr.CrError, B.Octets>}

# Signatures and key agreement (sign.bend, kex.bend): the generic helpers
# keep the interface laws (README.md); the instances (RSA, DH, ECDSA, ECDH,
# SM2, EC-RDSA) and their laws are in bend-osdev-pubkey. A signature
# checked from the public key's bytes is accepted, for every scheme, secret
# key and message, when the scheme's pk_format and accepts laws hold there
# (hf, ha)
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

# SHA3-256 as a hash (inst_sha3.bend), from bend-collections-laws-crypto's
# laws, as for SHA-2: the one-shot digest is FIPS 202's executable
# specification (that package's spec/crypto/sha3.bend), the streaming
# digest of any split into two or three pieces is the one-shot digest, and
# a digest is 32 bytes. As for SHA-2, the streaming law for every state is
# tested, not proved.

law sha3_256_spec:
  for +o: B.Octets
  {S3.CrSha3.sha3_256(o) == B.Octets.of_list(F202.sha3_256(B.Octets.to_list(o))) : B.Octets}

law sha3_256_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {S3.CrSha3.final(S3.CrSha3.update(S3.CrSha3.update(S3.CrSha3.init(), a), b)) == S3.CrSha3.sha3_256(B.Octets.append(a, b)) : B.Octets}

law sha3_256_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {S3.CrSha3.final(S3.CrSha3.update(S3.CrSha3.update(S3.CrSha3.update(S3.CrSha3.init(), a), b), c)) == S3.CrSha3.sha3_256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

law sha3_256_hash_length:
  for +o: B.Octets
  {B.Octets.len(S3.CrSha3.sha3_256(o)) == 32n : Nat}

# HKDF over SHA-256 refuses more than 255 digests (8160 bytes)
law hkdf_sha256_too_long:
  {Result.map(&2, &2, Cr.CrError, B.Octets, Unit, o => Unit{}, Hk.CrHkdf.derive(~64n, ~32n, ~SH.CrSha2.sha256, B.Octets.of_string("ikm"), B.Octets.empty(), B.Octets.empty(), 8161n)) == Fail{Cr.CrBadOutputLength{8161n}} : Result<&2, &2, Cr.CrError, Unit>}

# FIPS 180-4's example "abc" (NIST's SHA examples), through the hash
# interface
law sha256_abc:
  {SH.CrSha2.sha256(B.Octets.of_string("abc")) == B.Octets.of_list([186, 120, 22, 191, 143, 1, 207, 234, 65, 65, 64, 222, 93, 174, 34, 35, 176, 3, 97, 163, 150, 23, 122, 156, 180, 16, 255, 97, 242, 0, 21, 173]) : B.Octets}

# FIPS 202's SHA3-256 of "abc" (NIST's SHA-3 examples), through the hash
# interface
law sha3_256_abc:
  {S3.CrSha3.sha3_256(B.Octets.of_string("abc")) == B.Octets.of_list([58, 152, 93, 167, 79, 226, 37, 178, 4, 92, 23, 45, 107, 211, 144, 189, 133, 95, 8, 110, 62, 157, 82, 91, 70, 191, 226, 69, 17, 67, 21, 50]) : B.Octets}

# RFC 4231 test case 2: HMAC-SHA-256 with the key "Jefe"
law hmac_sha256_rfc4231_2:
  {Hm.CrHmac.mac(~SH.CrSha2.sha256, Hm.CrHmac.key(~64n, ~SH.CrSha2.sha256, B.Octets.of_string("Jefe")), B.Octets.of_string("what do ya want for nothing?")) == B.Octets.of_list([91, 220, 193, 70, 191, 96, 117, 78, 106, 4, 36, 38, 8, 149, 117, 199, 90, 0, 63, 8, 157, 39, 57, 131, 157, 236, 88, 185, 100, 236, 56, 67]) : B.Octets}

# Michael as a MAC (inst_michael.bend): it accepts what it computes, for
# every key and message (it uses the named default verify); a key of
# another length than 8 bytes is refused; the sixth test vector recalled as
# IEEE 802.11i's, through the MAC interface (not checked against a published
# copy: hashes/README.md)
law michael_accepts:
  for +k: Hs.HsW2
  for +m: B.Octets
  {MIC.CrMichael.verify(k, m, HMI.HsMichael.mic(k, m)) == True{} : Bool}

law michael_key_length:
  {Result.map(&2, &2, Cr.CrError, Hs.HsW2, Unit, k => Unit{}, MIC.CrMichael.key(B.Octets.zeros(16n))) == Fail{Cr.CrBadKeyLength{16n}} : Result<&2, &2, Cr.CrError, Unit>}

law michael_mac_vector:
  {Mc.CrMac.compute_with(~Hs.HsW2, ~MIC.CrMichael.key, ~HMI.HsMichael.mic, B.Octets.of_list([213, 94, 16, 5, 16, 18, 137, 134]), B.Octets.of_string("Michael")) == Done{B.Octets.of_list([10, 148, 43, 18, 78, 202, 165, 70])} : Result<&2, &2, Cr.CrError, B.Octets>}

# PBKDF2 over any MAC (pbkdf2.bend), for every MAC, password, salt,
# iteration count and length: a derivation that succeeds gives exactly the
# length asked for (the KDF interface's length law); the unchecked stream
# has that length, and a shorter stream is a prefix of a longer (the KDF
# interface's prefix law)
law pbkdf2_length:
  for ~K: Data
  for ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>
  for ~compute: K -> B.Octets -> B.Octets
  for ~hlen: Nat
  for +p: B.Octets
  for +salt: B.Octets
  for +c: U32
  for +n: Nat
  {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Pb.CrPbkdf2.pbkdf2(~K, ~key, ~compute, ~hlen, p, salt, c, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Pb.CrPbkdf2.pbkdf2(~K, ~key, ~compute, ~hlen, p, salt, c, n)) : Result<&2, &2, Cr.CrError, Nat>}

law pbkdf2_stream_length:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for +k: K
  for +salt: B.Octets
  for +c: U32
  for +n: Nat
  {B.Octets.len(Pb.CrPbkdf2.stream(~K, ~compute, k, salt, c, n)) == n : Nat}

law pbkdf2_stream_prefix:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for +k: K
  for +salt: B.Octets
  for +c: U32
  for +n: Nat
  for +j: Nat
  {B.Octets.take(n, Pb.CrPbkdf2.stream(~K, ~compute, k, salt, c, Nat.add(n, j))) == Pb.CrPbkdf2.stream(~K, ~compute, k, salt, c, n) : B.Octets}

# PBKDF2 refuses an iteration count of 0 (over HMAC-SHA-1)
law pbkdf2_zero_iterations:
  {Result.map(&2, &2, Cr.CrError, B.Octets, Unit, o => Unit{}, PbI.CrPbkdf2.hmac_sha1(B.Octets.of_string("password"), B.Octets.of_string("salt"), 0, 20n)) == Fail{Cr.CrTooShort{0n}} : Result<&2, &2, Cr.CrError, Unit>}

# RFC 6070 test cases 1 and 2: PBKDF2-HMAC-SHA1, P = "password",
# S = "salt", c = 1 and 2, dkLen = 20
law pbkdf2_hmac_sha1_rfc6070_1:
  {PbI.CrPbkdf2.hmac_sha1(B.Octets.of_string("password"), B.Octets.of_string("salt"), 1, 20n) == Done{B.Octets.of_list([12, 96, 200, 15, 150, 31, 14, 113, 243, 169, 181, 36, 175, 96, 18, 6, 47, 224, 55, 166])} : Result<&2, &2, Cr.CrError, B.Octets>}

law pbkdf2_hmac_sha1_rfc6070_2:
  {PbI.CrPbkdf2.hmac_sha1(B.Octets.of_string("password"), B.Octets.of_string("salt"), 2, 20n) == Done{B.Octets.of_list([234, 108, 1, 77, 199, 45, 111, 140, 205, 30, 217, 42, 206, 29, 65, 240, 216, 222, 137, 87])} : Result<&2, &2, Cr.CrError, B.Octets>}

# RFC 7914, section 11: PBKDF2-HMAC-SHA256, P = "passwd", S = "salt",
# c = 1: the first 32 of its 64 bytes (a shorter output is a prefix of a
# longer, pbkdf2_stream_prefix; all 64 bytes, two blocks, run past
# --verdict's kernel fuel, and check.bend computes them)
law pbkdf2_hmac_sha256_rfc7914_1:
  {PbI.CrPbkdf2.hmac_sha256(B.Octets.of_string("passwd"), B.Octets.of_string("salt"), 1, 32n) == Done{B.Octets.of_list([85, 172, 4, 110, 86, 227, 8, 159, 236, 22, 145, 194, 37, 68, 182, 5, 249, 65, 133, 33, 109, 222, 4, 101, 230, 139, 157, 87, 194, 13, 172, 188])} : Result<&2, &2, Cr.CrError, B.Octets>}

# SP 800-108 KDFs over any MAC (kbkdf.bend), for every MAC, key, fixed
# input data and length: each stream has the length asked for, a shorter
# stream is a prefix of a longer one with the same fixed input (and IV), and
# a derivation that succeeds has the length asked for. (The interface's
# prefix law holds of the streams: a derivation binds its length L into
# the fixed input, so derivations of two lengths differ.)
law kbkdf_counter_stream_length:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for ~rlen: Nat
  for +k: K
  for +fixed: B.Octets
  for +n: Nat
  {B.Octets.len(Kb.CrKbkdf.counter_stream(~K, ~compute, ~rlen, k, fixed, n)) == n : Nat}

law kbkdf_counter_stream_prefix:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for ~rlen: Nat
  for +k: K
  for +fixed: B.Octets
  for +n: Nat
  for +j: Nat
  {B.Octets.take(n, Kb.CrKbkdf.counter_stream(~K, ~compute, ~rlen, k, fixed, Nat.add(n, j))) == Kb.CrKbkdf.counter_stream(~K, ~compute, ~rlen, k, fixed, n) : B.Octets}

law kbkdf_feedback_stream_length:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for ~rlen: Nat
  for +k: K
  for +iv: B.Octets
  for +fixed: B.Octets
  for +n: Nat
  {B.Octets.len(Kb.CrKbkdf.feedback_stream(~K, ~compute, ~rlen, k, iv, fixed, n)) == n : Nat}

law kbkdf_feedback_stream_prefix:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for ~rlen: Nat
  for +k: K
  for +iv: B.Octets
  for +fixed: B.Octets
  for +n: Nat
  for +j: Nat
  {B.Octets.take(n, Kb.CrKbkdf.feedback_stream(~K, ~compute, ~rlen, k, iv, fixed, Nat.add(n, j))) == Kb.CrKbkdf.feedback_stream(~K, ~compute, ~rlen, k, iv, fixed, n) : B.Octets}

law kbkdf_counter_length:
  for ~K: Data
  for ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>
  for ~compute: K -> B.Octets -> B.Octets
  for ~hlen: Nat
  for ~rlen: Nat
  for ~llen: Nat
  for +ki: B.Octets
  for +label: B.Octets
  for +context: B.Octets
  for +n: Nat
  {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Kb.CrKbkdf.counter_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, label, context, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Kb.CrKbkdf.counter_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, label, context, n)) : Result<&2, &2, Cr.CrError, Nat>}

law kbkdf_feedback_length:
  for ~K: Data
  for ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>
  for ~compute: K -> B.Octets -> B.Octets
  for ~hlen: Nat
  for ~rlen: Nat
  for ~llen: Nat
  for +ki: B.Octets
  for +iv: B.Octets
  for +label: B.Octets
  for +context: B.Octets
  for +n: Nat
  {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Kb.CrKbkdf.feedback_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, iv, label, context, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Kb.CrKbkdf.feedback_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, iv, label, context, n)) : Result<&2, &2, Cr.CrError, Nat>}

# KBKDF in counter mode over HMAC-SHA-256 (32-bit counter and [L]_2), the
# key "secret key bytes", Label "label", Context "context", 32 bytes:
# Python's cryptography's KBKDFHMAC gives this value. Stated on the stream
# (what CrKbkdf.counter_kdf returns once its length checks pass): those
# checks compare with 2^32, which --verdict's kernel cannot compute in time;
# check.bend runs the checked derivation
law kbkdf_hmac_sha256_vector:
  {Kb.CrKbkdf.counter_stream(~Hm.CrHmacKey, ~Hm.CrHmac.mac(~SH.CrSha2.sha256), ~4n, Hm.CrHmac.key(~64n, ~SH.CrSha2.sha256, B.Octets.of_string("secret key bytes")), Kb.CrKbkdf.fixed(~4n, B.Octets.of_string("label"), B.Octets.of_string("context"), 32n), 32n) == B.Octets.of_list([36, 187, 186, 187, 150, 131, 248, 143, 109, 68, 1, 79, 191, 147, 235, 99, 232, 125, 99, 110, 60, 243, 238, 232, 217, 114, 189, 30, 217, 156, 9, 202]) : B.Octets}

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

# DES (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law des_pcbc_round_trip:
  for +k: D.LcDesKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Pc.CrPcbc.decrypt_blocks(~D.LcDesKey, ~L.LcBlock64, ~D.LcDes.decrypt, ~LC.CrBlk64.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~D.LcDesKey, ~L.LcBlock64, ~D.LcDes.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

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

# Triple DES (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law tdes_pcbc_round_trip:
  for +k: T.LcTdesKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Pc.CrPcbc.decrypt_blocks(~T.LcTdesKey, ~L.LcBlock64, ~T.LcTdes.decrypt, ~LC.CrBlk64.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~T.LcTdesKey, ~L.LcBlock64, ~T.LcTdes.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

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

# SM4 (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law sm4_pcbc_round_trip:
  for +k: S.LcSm4Key
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Pc.CrPcbc.decrypt_blocks(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.decrypt, ~CM.CrBlk128.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# SM4 (legacy-ciphers) in LRW (lrw.bend): decryption undoes encryption, for every key, tweak key, index and list of blocks
law sm4_lrw_round_trip:
  for +k: S.LcSm4Key
  for +k2: G.Gf128
  for +i: G.Gf128
  for +bs: List<&2, M.CmBlock>
  {Lw.CrLrw.decrypt_blocks(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, Lw.CrLrw.encrypt_blocks(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)) == bs : List<&2, M.CmBlock>}

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

# Camellia (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law camellia_pcbc_round_trip:
  for +k: Ca.LcCamelliaKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Pc.CrPcbc.decrypt_blocks(~Ca.LcCamelliaKey, ~M.CmBlock, ~Ca.LcCamellia.decrypt, ~CM.CrBlk128.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~Ca.LcCamelliaKey, ~M.CmBlock, ~Ca.LcCamellia.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# Camellia (legacy-ciphers) in LRW (lrw.bend): decryption undoes encryption, for every key, tweak key, index and list of blocks
law camellia_lrw_round_trip:
  for +k: Ca.LcCamelliaKey
  for +k2: G.Gf128
  for +i: G.Gf128
  for +bs: List<&2, M.CmBlock>
  {Lw.CrLrw.decrypt_blocks(~Ca.LcCamelliaKey, ~M.CmBlock, ~Ca.LcCamellia.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, Lw.CrLrw.encrypt_blocks(~Ca.LcCamelliaKey, ~M.CmBlock, ~Ca.LcCamellia.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)) == bs : List<&2, M.CmBlock>}

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

# Serpent (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law serpent_pcbc_round_trip:
  for +k: Sp.LcSerpentKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Pc.CrPcbc.decrypt_blocks(~Sp.LcSerpentKey, ~M.CmBlock, ~Sp.LcSerpent.decrypt, ~CM.CrBlk128.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~Sp.LcSerpentKey, ~M.CmBlock, ~Sp.LcSerpent.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# Serpent (legacy-ciphers) in LRW (lrw.bend): decryption undoes encryption, for every key, tweak key, index and list of blocks
law serpent_lrw_round_trip:
  for +k: Sp.LcSerpentKey
  for +k2: G.Gf128
  for +i: G.Gf128
  for +bs: List<&2, M.CmBlock>
  {Lw.CrLrw.decrypt_blocks(~Sp.LcSerpentKey, ~M.CmBlock, ~Sp.LcSerpent.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, Lw.CrLrw.encrypt_blocks(~Sp.LcSerpentKey, ~M.CmBlock, ~Sp.LcSerpent.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)) == bs : List<&2, M.CmBlock>}

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

# Twofish (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law twofish_pcbc_round_trip:
  for +k: Tf.LcTwofishKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Pc.CrPcbc.decrypt_blocks(~Tf.LcTwofishKey, ~M.CmBlock, ~Tf.LcTwofish.decrypt, ~CM.CrBlk128.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~Tf.LcTwofishKey, ~M.CmBlock, ~Tf.LcTwofish.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# Twofish (legacy-ciphers) in LRW (lrw.bend): decryption undoes encryption, for every key, tweak key, index and list of blocks
law twofish_lrw_round_trip:
  for +k: Tf.LcTwofishKey
  for +k2: G.Gf128
  for +i: G.Gf128
  for +bs: List<&2, M.CmBlock>
  {Lw.CrLrw.decrypt_blocks(~Tf.LcTwofishKey, ~M.CmBlock, ~Tf.LcTwofish.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, Lw.CrLrw.encrypt_blocks(~Tf.LcTwofishKey, ~M.CmBlock, ~Tf.LcTwofish.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)) == bs : List<&2, M.CmBlock>}

# ARIA (legacy-ciphers): decryption undoes encryption, for every key and block
law aria_block_round_trip:
  for k: Ar.LcAriaKey
  for +b: M.CmBlock
  {Ar.LcAria.decrypt(k, Ar.LcAria.encrypt(k, b)) == b : M.CmBlock}

# ARIA (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law aria_block_round_trip_dual:
  for k: Ar.LcAriaKey
  for +b: M.CmBlock
  {Ar.LcAria.encrypt(k, Ar.LcAria.decrypt(k, b)) == b : M.CmBlock}

# ARIA (legacy-ciphers): a key of 20 bytes is refused
law aria_key_length:
  {Result.map(&2, &2, Cr.CrError, Ar.LcAriaKey, Unit, k => Unit{}, LC.CrLc.key(~Ar.LcAriaKey, ~Ar.LcAria.key, B.Octets.zeros(20n))) == Fail{Cr.CrBadKeyLength{20n}} : Result<&2, &2, Cr.CrError, Unit>}

# ARIA (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law aria_ecb_round_trip:
  for +k: Ar.LcAriaKey
  for +bs: List<&2, M.CmBlock>
  {Md.CrEcb.decrypt_blocks(~Ar.LcAriaKey, ~M.CmBlock, ~Ar.LcAria.decrypt, k, Md.CrEcb.encrypt_blocks(~Ar.LcAriaKey, ~M.CmBlock, ~Ar.LcAria.encrypt, k, bs)) == bs : List<&2, M.CmBlock>}

# ARIA (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law aria_cbc_round_trip:
  for +k: Ar.LcAriaKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Md.CrCbc.decrypt_blocks(~Ar.LcAriaKey, ~M.CmBlock, ~Ar.LcAria.decrypt, ~CM.CrBlk128.xor, k, iv, Md.CrCbc.encrypt_blocks(~Ar.LcAriaKey, ~M.CmBlock, ~Ar.LcAria.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# ARIA (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law aria_pcbc_round_trip:
  for +k: Ar.LcAriaKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Pc.CrPcbc.decrypt_blocks(~Ar.LcAriaKey, ~M.CmBlock, ~Ar.LcAria.decrypt, ~CM.CrBlk128.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~Ar.LcAriaKey, ~M.CmBlock, ~Ar.LcAria.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# ARIA (legacy-ciphers) in LRW (lrw.bend): decryption undoes encryption, for every key, tweak key, index and list of blocks
law aria_lrw_round_trip:
  for +k: Ar.LcAriaKey
  for +k2: G.Gf128
  for +i: G.Gf128
  for +bs: List<&2, M.CmBlock>
  {Lw.CrLrw.decrypt_blocks(~Ar.LcAriaKey, ~M.CmBlock, ~Ar.LcAria.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, Lw.CrLrw.encrypt_blocks(~Ar.LcAriaKey, ~M.CmBlock, ~Ar.LcAria.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)) == bs : List<&2, M.CmBlock>}

# CAST-256 (legacy-ciphers): decryption undoes encryption, for every key and block
law cast6_block_round_trip:
  for k: C6.LcCast6Key
  for +b: M.CmBlock
  {C6.LcCast6.decrypt(k, C6.LcCast6.encrypt(k, b)) == b : M.CmBlock}

# CAST-256 (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law cast6_block_round_trip_dual:
  for k: C6.LcCast6Key
  for +b: M.CmBlock
  {C6.LcCast6.encrypt(k, C6.LcCast6.decrypt(k, b)) == b : M.CmBlock}

# CAST-256 (legacy-ciphers): a key of 18 bytes is refused
law cast6_key_length:
  {Result.map(&2, &2, Cr.CrError, C6.LcCast6Key, Unit, k => Unit{}, LC.CrLc.key(~C6.LcCast6Key, ~C6.LcCast6.key, B.Octets.zeros(18n))) == Fail{Cr.CrBadKeyLength{18n}} : Result<&2, &2, Cr.CrError, Unit>}

# CAST-256 (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law cast6_ecb_round_trip:
  for +k: C6.LcCast6Key
  for +bs: List<&2, M.CmBlock>
  {Md.CrEcb.decrypt_blocks(~C6.LcCast6Key, ~M.CmBlock, ~C6.LcCast6.decrypt, k, Md.CrEcb.encrypt_blocks(~C6.LcCast6Key, ~M.CmBlock, ~C6.LcCast6.encrypt, k, bs)) == bs : List<&2, M.CmBlock>}

# CAST-256 (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law cast6_cbc_round_trip:
  for +k: C6.LcCast6Key
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Md.CrCbc.decrypt_blocks(~C6.LcCast6Key, ~M.CmBlock, ~C6.LcCast6.decrypt, ~CM.CrBlk128.xor, k, iv, Md.CrCbc.encrypt_blocks(~C6.LcCast6Key, ~M.CmBlock, ~C6.LcCast6.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# CAST-256 (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law cast6_pcbc_round_trip:
  for +k: C6.LcCast6Key
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Pc.CrPcbc.decrypt_blocks(~C6.LcCast6Key, ~M.CmBlock, ~C6.LcCast6.decrypt, ~CM.CrBlk128.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~C6.LcCast6Key, ~M.CmBlock, ~C6.LcCast6.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# CAST-256 (legacy-ciphers) in LRW (lrw.bend): decryption undoes encryption, for every key, tweak key, index and list of blocks
law cast6_lrw_round_trip:
  for +k: C6.LcCast6Key
  for +k2: G.Gf128
  for +i: G.Gf128
  for +bs: List<&2, M.CmBlock>
  {Lw.CrLrw.decrypt_blocks(~C6.LcCast6Key, ~M.CmBlock, ~C6.LcCast6.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, Lw.CrLrw.encrypt_blocks(~C6.LcCast6Key, ~M.CmBlock, ~C6.LcCast6.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)) == bs : List<&2, M.CmBlock>}

# Blowfish (legacy-ciphers): decryption undoes encryption, for every key and block
law blowfish_block_round_trip:
  for k: Bf.LcBlowfishKey
  for +b: L.LcBlock64
  {Bf.LcBlowfish.decrypt(k, Bf.LcBlowfish.encrypt(k, b)) == b : L.LcBlock64}

# Blowfish (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law blowfish_block_round_trip_dual:
  for k: Bf.LcBlowfishKey
  for +b: L.LcBlock64
  {Bf.LcBlowfish.encrypt(k, Bf.LcBlowfish.decrypt(k, b)) == b : L.LcBlock64}

# Blowfish (legacy-ciphers): a key of 3 bytes is refused
law blowfish_key_length:
  {Result.map(&2, &2, Cr.CrError, Bf.LcBlowfishKey, Unit, k => Unit{}, LC.CrLc.key(~Bf.LcBlowfishKey, ~Bf.LcBlowfish.key, B.Octets.zeros(3n))) == Fail{Cr.CrBadKeyLength{3n}} : Result<&2, &2, Cr.CrError, Unit>}

# Blowfish (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law blowfish_ecb_round_trip:
  for +k: Bf.LcBlowfishKey
  for +bs: List<&2, L.LcBlock64>
  {Md.CrEcb.decrypt_blocks(~Bf.LcBlowfishKey, ~L.LcBlock64, ~Bf.LcBlowfish.decrypt, k, Md.CrEcb.encrypt_blocks(~Bf.LcBlowfishKey, ~L.LcBlock64, ~Bf.LcBlowfish.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

# Blowfish (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law blowfish_cbc_round_trip:
  for +k: Bf.LcBlowfishKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Md.CrCbc.decrypt_blocks(~Bf.LcBlowfishKey, ~L.LcBlock64, ~Bf.LcBlowfish.decrypt, ~LC.CrBlk64.xor, k, iv, Md.CrCbc.encrypt_blocks(~Bf.LcBlowfishKey, ~L.LcBlock64, ~Bf.LcBlowfish.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# Blowfish (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law blowfish_pcbc_round_trip:
  for +k: Bf.LcBlowfishKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Pc.CrPcbc.decrypt_blocks(~Bf.LcBlowfishKey, ~L.LcBlock64, ~Bf.LcBlowfish.decrypt, ~LC.CrBlk64.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~Bf.LcBlowfishKey, ~L.LcBlock64, ~Bf.LcBlowfish.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# CAST-128 (legacy-ciphers): decryption undoes encryption, for every key and block
law cast5_block_round_trip:
  for k: C5.LcCast5Key
  for +b: L.LcBlock64
  {C5.LcCast5.decrypt(k, C5.LcCast5.encrypt(k, b)) == b : L.LcBlock64}

# CAST-128 (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law cast5_block_round_trip_dual:
  for k: C5.LcCast5Key
  for +b: L.LcBlock64
  {C5.LcCast5.encrypt(k, C5.LcCast5.decrypt(k, b)) == b : L.LcBlock64}

# CAST-128 (legacy-ciphers): a key of 4 bytes is refused
law cast5_key_length:
  {Result.map(&2, &2, Cr.CrError, C5.LcCast5Key, Unit, k => Unit{}, LC.CrLc.key(~C5.LcCast5Key, ~C5.LcCast5.key, B.Octets.zeros(4n))) == Fail{Cr.CrBadKeyLength{4n}} : Result<&2, &2, Cr.CrError, Unit>}

# CAST-128 (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law cast5_ecb_round_trip:
  for +k: C5.LcCast5Key
  for +bs: List<&2, L.LcBlock64>
  {Md.CrEcb.decrypt_blocks(~C5.LcCast5Key, ~L.LcBlock64, ~C5.LcCast5.decrypt, k, Md.CrEcb.encrypt_blocks(~C5.LcCast5Key, ~L.LcBlock64, ~C5.LcCast5.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

# CAST-128 (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law cast5_cbc_round_trip:
  for +k: C5.LcCast5Key
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Md.CrCbc.decrypt_blocks(~C5.LcCast5Key, ~L.LcBlock64, ~C5.LcCast5.decrypt, ~LC.CrBlk64.xor, k, iv, Md.CrCbc.encrypt_blocks(~C5.LcCast5Key, ~L.LcBlock64, ~C5.LcCast5.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# CAST-128 (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law cast5_pcbc_round_trip:
  for +k: C5.LcCast5Key
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Pc.CrPcbc.decrypt_blocks(~C5.LcCast5Key, ~L.LcBlock64, ~C5.LcCast5.decrypt, ~LC.CrBlk64.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~C5.LcCast5Key, ~L.LcBlock64, ~C5.LcCast5.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# TEA, little-endian words (legacy-ciphers): decryption undoes encryption, for every key and block
law tea_block_round_trip:
  for k: Te.LcTeaKey
  for +b: L.LcBlock64
  {Te.LcTea.decrypt(k, Te.LcTea.encrypt(k, b)) == b : L.LcBlock64}

# TEA, little-endian words (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law tea_block_round_trip_dual:
  for k: Te.LcTeaKey
  for +b: L.LcBlock64
  {Te.LcTea.encrypt(k, Te.LcTea.decrypt(k, b)) == b : L.LcBlock64}

# TEA, little-endian words (legacy-ciphers): a key of 15 bytes is refused
law tea_key_length:
  {Result.map(&2, &2, Cr.CrError, Te.LcTeaKey, Unit, k => Unit{}, LC.CrLc.key(~Te.LcTeaKey, ~Te.LcTea.key, B.Octets.zeros(15n))) == Fail{Cr.CrBadKeyLength{15n}} : Result<&2, &2, Cr.CrError, Unit>}

# TEA, little-endian words (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law tea_ecb_round_trip:
  for +k: Te.LcTeaKey
  for +bs: List<&2, L.LcBlock64>
  {Md.CrEcb.decrypt_blocks(~Te.LcTeaKey, ~L.LcBlock64, ~Te.LcTea.decrypt, k, Md.CrEcb.encrypt_blocks(~Te.LcTeaKey, ~L.LcBlock64, ~Te.LcTea.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

# TEA, little-endian words (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law tea_cbc_round_trip:
  for +k: Te.LcTeaKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Md.CrCbc.decrypt_blocks(~Te.LcTeaKey, ~L.LcBlock64, ~Te.LcTea.decrypt, ~LC.CrBlk64.xor, k, iv, Md.CrCbc.encrypt_blocks(~Te.LcTeaKey, ~L.LcBlock64, ~Te.LcTea.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# TEA, little-endian words (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law tea_pcbc_round_trip:
  for +k: Te.LcTeaKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Pc.CrPcbc.decrypt_blocks(~Te.LcTeaKey, ~L.LcBlock64, ~Te.LcTea.decrypt, ~LC.CrBlk64.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~Te.LcTeaKey, ~L.LcBlock64, ~Te.LcTea.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# XTEA, little-endian words (legacy-ciphers): decryption undoes encryption, for every key and block
law xtea_block_round_trip:
  for k: Xt.LcXteaKey
  for +b: L.LcBlock64
  {Xt.LcXtea.decrypt(k, Xt.LcXtea.encrypt(k, b)) == b : L.LcBlock64}

# XTEA, little-endian words (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law xtea_block_round_trip_dual:
  for k: Xt.LcXteaKey
  for +b: L.LcBlock64
  {Xt.LcXtea.encrypt(k, Xt.LcXtea.decrypt(k, b)) == b : L.LcBlock64}

# XTEA, little-endian words (legacy-ciphers): a key of 17 bytes is refused
law xtea_key_length:
  {Result.map(&2, &2, Cr.CrError, Xt.LcXteaKey, Unit, k => Unit{}, LC.CrLc.key(~Xt.LcXteaKey, ~Xt.LcXtea.key, B.Octets.zeros(17n))) == Fail{Cr.CrBadKeyLength{17n}} : Result<&2, &2, Cr.CrError, Unit>}

# XTEA, little-endian words (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law xtea_ecb_round_trip:
  for +k: Xt.LcXteaKey
  for +bs: List<&2, L.LcBlock64>
  {Md.CrEcb.decrypt_blocks(~Xt.LcXteaKey, ~L.LcBlock64, ~Xt.LcXtea.decrypt, k, Md.CrEcb.encrypt_blocks(~Xt.LcXteaKey, ~L.LcBlock64, ~Xt.LcXtea.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

# XTEA, little-endian words (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law xtea_cbc_round_trip:
  for +k: Xt.LcXteaKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Md.CrCbc.decrypt_blocks(~Xt.LcXteaKey, ~L.LcBlock64, ~Xt.LcXtea.decrypt, ~LC.CrBlk64.xor, k, iv, Md.CrCbc.encrypt_blocks(~Xt.LcXteaKey, ~L.LcBlock64, ~Xt.LcXtea.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# XTEA, little-endian words (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law xtea_pcbc_round_trip:
  for +k: Xt.LcXteaKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Pc.CrPcbc.decrypt_blocks(~Xt.LcXteaKey, ~L.LcBlock64, ~Xt.LcXtea.decrypt, ~LC.CrBlk64.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~Xt.LcXteaKey, ~L.LcBlock64, ~Xt.LcXtea.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# FCrypt (legacy-ciphers): decryption undoes encryption, for every key and block
law fcrypt_block_round_trip:
  for k: Fc.LcFcryptKey
  for +b: L.LcBlock64
  {Fc.LcFcrypt.decrypt(k, Fc.LcFcrypt.encrypt(k, b)) == b : L.LcBlock64}

# FCrypt (legacy-ciphers): encryption undoes decryption (a permutation of the blocks)
law fcrypt_block_round_trip_dual:
  for k: Fc.LcFcryptKey
  for +b: L.LcBlock64
  {Fc.LcFcrypt.encrypt(k, Fc.LcFcrypt.decrypt(k, b)) == b : L.LcBlock64}

# FCrypt (legacy-ciphers): a key of 7 bytes is refused
law fcrypt_key_length:
  {Result.map(&2, &2, Cr.CrError, Fc.LcFcryptKey, Unit, k => Unit{}, LC.CrLc.key(~Fc.LcFcryptKey, ~Fc.LcFcrypt.key, B.Octets.zeros(7n))) == Fail{Cr.CrBadKeyLength{7n}} : Result<&2, &2, Cr.CrError, Unit>}

# FCrypt (legacy-ciphers) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law fcrypt_ecb_round_trip:
  for +k: Fc.LcFcryptKey
  for +bs: List<&2, L.LcBlock64>
  {Md.CrEcb.decrypt_blocks(~Fc.LcFcryptKey, ~L.LcBlock64, ~Fc.LcFcrypt.decrypt, k, Md.CrEcb.encrypt_blocks(~Fc.LcFcryptKey, ~L.LcBlock64, ~Fc.LcFcrypt.encrypt, k, bs)) == bs : List<&2, L.LcBlock64>}

# FCrypt (legacy-ciphers) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law fcrypt_cbc_round_trip:
  for +k: Fc.LcFcryptKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Md.CrCbc.decrypt_blocks(~Fc.LcFcryptKey, ~L.LcBlock64, ~Fc.LcFcrypt.decrypt, ~LC.CrBlk64.xor, k, iv, Md.CrCbc.encrypt_blocks(~Fc.LcFcryptKey, ~L.LcBlock64, ~Fc.LcFcrypt.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# FCrypt (legacy-ciphers) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law fcrypt_pcbc_round_trip:
  for +k: Fc.LcFcryptKey
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Pc.CrPcbc.decrypt_blocks(~Fc.LcFcryptKey, ~L.LcBlock64, ~Fc.LcFcrypt.decrypt, ~LC.CrBlk64.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~Fc.LcFcryptKey, ~L.LcBlock64, ~Fc.LcFcrypt.encrypt, ~LC.CrBlk64.xor, k, iv, bs)) == bs : List<&2, L.LcBlock64>}

# AES-128 and AES-256 (cipher-modes): decryption undoes encryption, for every key and block
law aes_block_round_trip:
  for k: X.CmAesKey
  for +b: M.CmBlock
  {X.CmAes.decrypt(k, X.CmAes.encrypt(k, b)) == b : M.CmBlock}

# AES-128 and AES-256 (cipher-modes): a key of 24 bytes is refused
law aes_key_length:
  {Result.map(&2, &2, Cr.CrError, X.CmAesKey, Unit, k => Unit{}, A.CrAes.key(B.Octets.zeros(24n))) == Fail{Cr.CrBadKeyLength{24n}} : Result<&2, &2, Cr.CrError, Unit>}

# AES-128 and AES-256 (cipher-modes) in ECB (modes.bend): decryption undoes encryption, for every key and list of blocks
law aes_ecb_round_trip:
  for +k: X.CmAesKey
  for +bs: List<&2, M.CmBlock>
  {Md.CrEcb.decrypt_blocks(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.decrypt, k, Md.CrEcb.encrypt_blocks(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, k, bs)) == bs : List<&2, M.CmBlock>}

# AES-128 and AES-256 (cipher-modes) in CBC (modes.bend): decryption undoes encryption, for every key, IV and list of blocks
law aes_cbc_round_trip:
  for +k: X.CmAesKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Md.CrCbc.decrypt_blocks(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.decrypt, ~CM.CrBlk128.xor, k, iv, Md.CrCbc.encrypt_blocks(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# AES-128 and AES-256 (cipher-modes) in PCBC (pcbc.bend): decryption undoes encryption, for every key, IV and list of blocks
law aes_pcbc_round_trip:
  for +k: X.CmAesKey
  for +iv: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  {Pc.CrPcbc.decrypt_blocks(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.decrypt, ~CM.CrBlk128.xor, k, iv, Pc.CrPcbc.encrypt_blocks(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.xor, k, iv, bs)) == bs : List<&2, M.CmBlock>}

# AES-128 and AES-256 (cipher-modes) in LRW (lrw.bend): decryption undoes encryption, for every key, tweak key, index and list of blocks
law aes_lrw_round_trip:
  for +k: X.CmAesKey
  for +k2: G.Gf128
  for +i: G.Gf128
  for +bs: List<&2, M.CmBlock>
  {Lw.CrLrw.decrypt_blocks(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, Lw.CrLrw.encrypt_blocks(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)) == bs : List<&2, M.CmBlock>}

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

# HMAC over SHA3-256 (bend-collections): the tag in pieces is the tag in one call, for every split
law hmac_sha3_256_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~S3.CrSha3State, ~S3.CrSha3.init(), ~S3.CrSha3.update, ~S3.CrSha3.final, Hm.CrHmac.update(~S3.CrSha3State, ~S3.CrSha3.update, Hm.CrHmac.update(~S3.CrSha3State, ~S3.CrSha3.update, Hm.CrHmac.start(~S3.CrSha3State, ~S3.CrSha3.init(), ~S3.CrSha3.update, kk), a), b)) == Hm.CrHmac.mac(~S3.CrSha3.sha3_256, kk, B.Octets.append(a, b)) : B.Octets}

# MD4 (hashes): update over a ++ b is update over a, then b, for every state
law md4_hash_streaming:
  for s: Hs.HsMdState<Hs.HsW4>
  for +a: B.Octets
  for +b: B.Octets
  {HM4.HsMd4.update(s, B.Octets.append(a, b)) == HM4.HsMd4.update(HM4.HsMd4.update(s, a), b) : Hs.HsMdState<Hs.HsW4>}

# MD4 (hashes): streaming equals one-shot, for every split
law md4_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {HM4.HsMd4.final(HM4.HsMd4.update(HM4.HsMd4.update(HM4.HsMd4.init(), a), b)) == HM4.HsMd4.digest(B.Octets.append(a, b)) : B.Octets}

# MD4 (hashes): and for every split into three
law md4_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {HM4.HsMd4.final(HM4.HsMd4.update(HM4.HsMd4.update(HM4.HsMd4.update(HM4.HsMd4.init(), a), b), c)) == HM4.HsMd4.digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# MD4 (hashes): final(s) has 16 bytes, for every state
law md4_hash_length:
  for +s: Hs.HsMdState<Hs.HsW4>
  {B.Octets.len(HM4.HsMd4.final(s)) == 16n : Nat}

# HMAC over MD4 (hashes): the state after a ++ b is the state after a, then b
law hmac_md4_streaming:
  for s: Hm.CrHmacState<Hs.HsMdState<Hs.HsW4>>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM4.HsMd4.update, s, B.Octets.append(a, b)) == Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM4.HsMd4.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM4.HsMd4.update, s, a), b) : Hm.CrHmacState<Hs.HsMdState<Hs.HsW4>>}

# HMAC over MD4 (hashes): the tag in pieces is the tag in one call, for every split
law hmac_md4_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~Hs.HsMdState<Hs.HsW4>, ~HM4.HsMd4.init(), ~HM4.HsMd4.update, ~HM4.HsMd4.final, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM4.HsMd4.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM4.HsMd4.update, Hm.CrHmac.start(~Hs.HsMdState<Hs.HsW4>, ~HM4.HsMd4.init(), ~HM4.HsMd4.update, kk), a), b)) == Hm.CrHmac.mac(~HM4.HsMd4.digest, kk, B.Octets.append(a, b)) : B.Octets}

# MD5 (hashes): update over a ++ b is update over a, then b, for every state
law md5_hash_streaming:
  for s: Hs.HsMdState<Hs.HsW4>
  for +a: B.Octets
  for +b: B.Octets
  {HM5.HsMd5.update(s, B.Octets.append(a, b)) == HM5.HsMd5.update(HM5.HsMd5.update(s, a), b) : Hs.HsMdState<Hs.HsW4>}

# MD5 (hashes): streaming equals one-shot, for every split
law md5_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {HM5.HsMd5.final(HM5.HsMd5.update(HM5.HsMd5.update(HM5.HsMd5.init(), a), b)) == HM5.HsMd5.digest(B.Octets.append(a, b)) : B.Octets}

# MD5 (hashes): and for every split into three
law md5_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {HM5.HsMd5.final(HM5.HsMd5.update(HM5.HsMd5.update(HM5.HsMd5.update(HM5.HsMd5.init(), a), b), c)) == HM5.HsMd5.digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# MD5 (hashes): final(s) has 16 bytes, for every state
law md5_hash_length:
  for +s: Hs.HsMdState<Hs.HsW4>
  {B.Octets.len(HM5.HsMd5.final(s)) == 16n : Nat}

# HMAC over MD5 (hashes): the state after a ++ b is the state after a, then b
law hmac_md5_streaming:
  for s: Hm.CrHmacState<Hs.HsMdState<Hs.HsW4>>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM5.HsMd5.update, s, B.Octets.append(a, b)) == Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM5.HsMd5.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM5.HsMd5.update, s, a), b) : Hm.CrHmacState<Hs.HsMdState<Hs.HsW4>>}

# HMAC over MD5 (hashes): the tag in pieces is the tag in one call, for every split
law hmac_md5_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~Hs.HsMdState<Hs.HsW4>, ~HM5.HsMd5.init(), ~HM5.HsMd5.update, ~HM5.HsMd5.final, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM5.HsMd5.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW4>, ~HM5.HsMd5.update, Hm.CrHmac.start(~Hs.HsMdState<Hs.HsW4>, ~HM5.HsMd5.init(), ~HM5.HsMd5.update, kk), a), b)) == Hm.CrHmac.mac(~HM5.HsMd5.digest, kk, B.Octets.append(a, b)) : B.Octets}

# SHA-1 (hashes): update over a ++ b is update over a, then b, for every state
law sha1_hash_streaming:
  for s: Hs.HsMdState<Hs.HsW5>
  for +a: B.Octets
  for +b: B.Octets
  {HS1.HsSha1.update(s, B.Octets.append(a, b)) == HS1.HsSha1.update(HS1.HsSha1.update(s, a), b) : Hs.HsMdState<Hs.HsW5>}

# SHA-1 (hashes): streaming equals one-shot, for every split
law sha1_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {HS1.HsSha1.final(HS1.HsSha1.update(HS1.HsSha1.update(HS1.HsSha1.init(), a), b)) == HS1.HsSha1.digest(B.Octets.append(a, b)) : B.Octets}

# SHA-1 (hashes): and for every split into three
law sha1_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {HS1.HsSha1.final(HS1.HsSha1.update(HS1.HsSha1.update(HS1.HsSha1.update(HS1.HsSha1.init(), a), b), c)) == HS1.HsSha1.digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# SHA-1 (hashes): final(s) has 20 bytes, for every state
law sha1_hash_length:
  for +s: Hs.HsMdState<Hs.HsW5>
  {B.Octets.len(HS1.HsSha1.final(s)) == 20n : Nat}

# HMAC over SHA-1 (hashes): the state after a ++ b is the state after a, then b
law hmac_sha1_streaming:
  for s: Hm.CrHmacState<Hs.HsMdState<Hs.HsW5>>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HS1.HsSha1.update, s, B.Octets.append(a, b)) == Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HS1.HsSha1.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HS1.HsSha1.update, s, a), b) : Hm.CrHmacState<Hs.HsMdState<Hs.HsW5>>}

# HMAC over SHA-1 (hashes): the tag in pieces is the tag in one call, for every split
law hmac_sha1_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~Hs.HsMdState<Hs.HsW5>, ~HS1.HsSha1.init(), ~HS1.HsSha1.update, ~HS1.HsSha1.final, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HS1.HsSha1.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HS1.HsSha1.update, Hm.CrHmac.start(~Hs.HsMdState<Hs.HsW5>, ~HS1.HsSha1.init(), ~HS1.HsSha1.update, kk), a), b)) == Hm.CrHmac.mac(~HS1.HsSha1.digest, kk, B.Octets.append(a, b)) : B.Octets}

# RIPEMD-160 (hashes): update over a ++ b is update over a, then b, for every state
law ripemd160_hash_streaming:
  for s: Hs.HsMdState<Hs.HsW5>
  for +a: B.Octets
  for +b: B.Octets
  {HRM.HsRipemd160.update(s, B.Octets.append(a, b)) == HRM.HsRipemd160.update(HRM.HsRipemd160.update(s, a), b) : Hs.HsMdState<Hs.HsW5>}

# RIPEMD-160 (hashes): streaming equals one-shot, for every split
law ripemd160_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {HRM.HsRipemd160.final(HRM.HsRipemd160.update(HRM.HsRipemd160.update(HRM.HsRipemd160.init(), a), b)) == HRM.HsRipemd160.digest(B.Octets.append(a, b)) : B.Octets}

# RIPEMD-160 (hashes): and for every split into three
law ripemd160_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {HRM.HsRipemd160.final(HRM.HsRipemd160.update(HRM.HsRipemd160.update(HRM.HsRipemd160.update(HRM.HsRipemd160.init(), a), b), c)) == HRM.HsRipemd160.digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# RIPEMD-160 (hashes): final(s) has 20 bytes, for every state
law ripemd160_hash_length:
  for +s: Hs.HsMdState<Hs.HsW5>
  {B.Octets.len(HRM.HsRipemd160.final(s)) == 20n : Nat}

# HMAC over RIPEMD-160 (hashes): the state after a ++ b is the state after a, then b
law hmac_ripemd160_streaming:
  for s: Hm.CrHmacState<Hs.HsMdState<Hs.HsW5>>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HRM.HsRipemd160.update, s, B.Octets.append(a, b)) == Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HRM.HsRipemd160.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HRM.HsRipemd160.update, s, a), b) : Hm.CrHmacState<Hs.HsMdState<Hs.HsW5>>}

# HMAC over RIPEMD-160 (hashes): the tag in pieces is the tag in one call, for every split
law hmac_ripemd160_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~Hs.HsMdState<Hs.HsW5>, ~HRM.HsRipemd160.init(), ~HRM.HsRipemd160.update, ~HRM.HsRipemd160.final, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HRM.HsRipemd160.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW5>, ~HRM.HsRipemd160.update, Hm.CrHmac.start(~Hs.HsMdState<Hs.HsW5>, ~HRM.HsRipemd160.init(), ~HRM.HsRipemd160.update, kk), a), b)) == Hm.CrHmac.mac(~HRM.HsRipemd160.digest, kk, B.Octets.append(a, b)) : B.Octets}

# SM3 (hashes): update over a ++ b is update over a, then b, for every state
law sm3_hash_streaming:
  for s: Hs.HsMdState<Hs.HsW8>
  for +a: B.Octets
  for +b: B.Octets
  {HSM.HsSm3.update(s, B.Octets.append(a, b)) == HSM.HsSm3.update(HSM.HsSm3.update(s, a), b) : Hs.HsMdState<Hs.HsW8>}

# SM3 (hashes): streaming equals one-shot, for every split
law sm3_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {HSM.HsSm3.final(HSM.HsSm3.update(HSM.HsSm3.update(HSM.HsSm3.init(), a), b)) == HSM.HsSm3.digest(B.Octets.append(a, b)) : B.Octets}

# SM3 (hashes): and for every split into three
law sm3_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {HSM.HsSm3.final(HSM.HsSm3.update(HSM.HsSm3.update(HSM.HsSm3.update(HSM.HsSm3.init(), a), b), c)) == HSM.HsSm3.digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# SM3 (hashes): final(s) has 32 bytes, for every state
law sm3_hash_length:
  for +s: Hs.HsMdState<Hs.HsW8>
  {B.Octets.len(HSM.HsSm3.final(s)) == 32n : Nat}

# HMAC over SM3 (hashes): the state after a ++ b is the state after a, then b
law hmac_sm3_streaming:
  for s: Hm.CrHmacState<Hs.HsMdState<Hs.HsW8>>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW8>, ~HSM.HsSm3.update, s, B.Octets.append(a, b)) == Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW8>, ~HSM.HsSm3.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW8>, ~HSM.HsSm3.update, s, a), b) : Hm.CrHmacState<Hs.HsMdState<Hs.HsW8>>}

# HMAC over SM3 (hashes): the tag in pieces is the tag in one call, for every split
law hmac_sm3_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~Hs.HsMdState<Hs.HsW8>, ~HSM.HsSm3.init(), ~HSM.HsSm3.update, ~HSM.HsSm3.final, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW8>, ~HSM.HsSm3.update, Hm.CrHmac.update(~Hs.HsMdState<Hs.HsW8>, ~HSM.HsSm3.update, Hm.CrHmac.start(~Hs.HsMdState<Hs.HsW8>, ~HSM.HsSm3.init(), ~HSM.HsSm3.update, kk), a), b)) == Hm.CrHmac.mac(~HSM.HsSm3.digest, kk, B.Octets.append(a, b)) : B.Octets}

# Streebog-256 (hashes): update over a ++ b is update over a, then b, for every state
law streebog256_hash_streaming:
  for s: Hs.HsMdState<HST.HsStbCv>
  for +a: B.Octets
  for +b: B.Octets
  {HST.HsStreebog.update(s, B.Octets.append(a, b)) == HST.HsStreebog.update(HST.HsStreebog.update(s, a), b) : Hs.HsMdState<HST.HsStbCv>}

# Streebog-256 (hashes): streaming equals one-shot, for every split
law streebog256_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {HST.HsStreebog.final256(HST.HsStreebog.update(HST.HsStreebog.update(HST.HsStreebog.init256(), a), b)) == HST.HsStreebog.digest256(B.Octets.append(a, b)) : B.Octets}

# Streebog-256 (hashes): and for every split into three
law streebog256_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {HST.HsStreebog.final256(HST.HsStreebog.update(HST.HsStreebog.update(HST.HsStreebog.update(HST.HsStreebog.init256(), a), b), c)) == HST.HsStreebog.digest256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# Streebog-256 (hashes): final(s) has 32 bytes, for every state
law streebog256_hash_length:
  for +s: Hs.HsMdState<HST.HsStbCv>
  {B.Octets.len(HST.HsStreebog.final256(s)) == 32n : Nat}

# HMAC over Streebog-256 (hashes): the state after a ++ b is the state after a, then b
law hmac_streebog256_streaming:
  for s: Hm.CrHmacState<Hs.HsMdState<HST.HsStbCv>>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, s, B.Octets.append(a, b)) == Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, s, a), b) : Hm.CrHmacState<Hs.HsMdState<HST.HsStbCv>>}

# HMAC over Streebog-256 (hashes): the tag in pieces is the tag in one call, for every split
law hmac_streebog256_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.init256(), ~HST.HsStreebog.update, ~HST.HsStreebog.final256, Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, Hm.CrHmac.start(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.init256(), ~HST.HsStreebog.update, kk), a), b)) == Hm.CrHmac.mac(~HST.HsStreebog.digest256, kk, B.Octets.append(a, b)) : B.Octets}

# Streebog-512 (hashes): update over a ++ b is update over a, then b, for every state
law streebog512_hash_streaming:
  for s: Hs.HsMdState<HST.HsStbCv>
  for +a: B.Octets
  for +b: B.Octets
  {HST.HsStreebog.update(s, B.Octets.append(a, b)) == HST.HsStreebog.update(HST.HsStreebog.update(s, a), b) : Hs.HsMdState<HST.HsStbCv>}

# Streebog-512 (hashes): streaming equals one-shot, for every split
law streebog512_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {HST.HsStreebog.final512(HST.HsStreebog.update(HST.HsStreebog.update(HST.HsStreebog.init512(), a), b)) == HST.HsStreebog.digest512(B.Octets.append(a, b)) : B.Octets}

# Streebog-512 (hashes): and for every split into three
law streebog512_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {HST.HsStreebog.final512(HST.HsStreebog.update(HST.HsStreebog.update(HST.HsStreebog.update(HST.HsStreebog.init512(), a), b), c)) == HST.HsStreebog.digest512(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# Streebog-512 (hashes): final(s) has 64 bytes, for every state
law streebog512_hash_length:
  for +s: Hs.HsMdState<HST.HsStbCv>
  {B.Octets.len(HST.HsStreebog.final512(s)) == 64n : Nat}

# HMAC over Streebog-512 (hashes): the state after a ++ b is the state after a, then b
law hmac_streebog512_streaming:
  for s: Hm.CrHmacState<Hs.HsMdState<HST.HsStbCv>>
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, s, B.Octets.append(a, b)) == Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, s, a), b) : Hm.CrHmacState<Hs.HsMdState<HST.HsStbCv>>}

# HMAC over Streebog-512 (hashes): the tag in pieces is the tag in one call, for every split
law hmac_streebog512_split:
  for +kk: Hm.CrHmacKey
  for +a: B.Octets
  for +b: B.Octets
  {Hm.CrHmac.finish(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.init512(), ~HST.HsStreebog.update, ~HST.HsStreebog.final512, Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, Hm.CrHmac.update(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.update, Hm.CrHmac.start(~Hs.HsMdState<HST.HsStbCv>, ~HST.HsStreebog.init512(), ~HST.HsStreebog.update, kk), a), b)) == Hm.CrHmac.mac(~HST.HsStreebog.digest512, kk, B.Octets.append(a, b)) : B.Octets}
# END GENERATED: laws
