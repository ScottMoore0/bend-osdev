# Laws of bend-collections' SHA-256, SHA-512 and SHA3-256 as hashes
# (inst_sha2.bend, inst_sha3.bend), from bend-collections-laws-crypto's
# laws, and of HMAC, HKDF, PBKDF2 and the SP 800-108 KDFs over them. The
# generic laws are in LAWS.bend.
#
# A law that needs a property of the algorithm (a hash in pieces is the hash
# of the whole) cannot take that property as a hypothesis and still pass
# --verdict (a template hypothesis has no model in the BendTT kernel, and an
# ordinary one is affine, so an induction cannot use it at every step).
# Those laws are stated once per instance instead, from the law schemas in
# gen/instances.py, which also writes their proofs (the generated regions
# here and in the proof file).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./hmac.bend as Hm
import ./hkdf.bend as Hk
import ./inst_sha2.bend as SH
import ./inst_sha3.bend as S3
import ./inst_pbkdf2.bend as PbI
import ./kbkdf.bend as Kb
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/sha.bend as F256
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/sha512.bend as F512
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/sha3.bend as F202

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

# RFC 7914, section 11: PBKDF2-HMAC-SHA256, P = "passwd", S = "salt",
# c = 1: the first 32 of its 64 bytes (a shorter output is a prefix of a
# longer, LAWS.bend's pbkdf2_stream_prefix; all 64 bytes, two blocks, run
# past --verdict's kernel fuel, and check.bend computes them)
law pbkdf2_hmac_sha256_rfc7914_1:
  {PbI.CrPbkdf2.hmac_sha256(B.Octets.of_string("passwd"), B.Octets.of_string("salt"), 1, 32n) == Done{B.Octets.of_list([85, 172, 4, 110, 86, 227, 8, 159, 236, 22, 145, 194, 37, 68, 182, 5, 249, 65, 133, 33, 109, 222, 4, 101, 230, 139, 157, 87, 194, 13, 172, 188])} : Result<&2, &2, Cr.CrError, B.Octets>}

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
# END GENERATED: laws
