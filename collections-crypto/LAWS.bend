# The laws of collections-crypto: crypto's interface laws for each instance
# of bend-collections' cryptography (README.md, "Laws").
#
# Proved for every input: the hash laws of the buffered state (streaming for
# every state, split, split3, and the digest of one update), for every
# one-shot digest, so for BLAKE2b, BLAKE2s, BLAKE3, BLAKE2b-n and Keccak-256;
# the three stream laws of ChaCha (every round count, so ChaCha20, XChaCha20,
# ChaCha12, ChaCha8), as crypto proves them for every keystream generator;
# the MAC laws of Poly1305 and GMAC (crypto's named default verify); the
# public-key format of X25519 and Ed25519.
#
# Conditional (a property of the algorithm at the very arguments used, as
# an ordinary hypothesis used once): the AEAD round trip, given
# bend-collections' own round trip at those arguments (hr, which
# bend-collections-laws-crypto proves for every input, in a proof file that
# fails --verdict: README.md) and that its answer is a byte string (h, tested
# on every vector and differential case); Ed25519's verify-from-bytes and
# X25519's agreement, given that the scheme accepts its own signatures and
# that both parties' secrets agree (number theory; bend-collections proves
# its code equal to RFC 8032's and RFC 7748's, not those identities).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/stream.bend as St
import ../crypto/mac.bend as Mc
import ../crypto/sign.bend as Sg
import ../crypto/kex.bend as Kx
import ./collections-crypto.bend as C
import ./aead.bend as Ad
import ./gmac.bend as Gm
import ./poly1305.bend as Po
import ./chacha.bend as Ch
import ./blake.bend as Bl
import ./keccak.bend as Kc
import ./x25519.bend as Xx
import ./ed25519.bend as Ed
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/keccak/main.bend as KS
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/poly1305.bend as PR
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/curve25519/field.bend as FS
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/curve25519/x25519.bend as SX
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/kex.bend as SKX
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/ed25519.bend as SE

# Buffered hashing (collections-crypto.bend's CcBuf), for every one-shot
# digest: the hash interface's streaming law for every state, ...
law buf_streaming:
  for +s: C.CcBuf
  for +a: B.Octets
  for +b: B.Octets
  {C.CcBuf.update(s, B.Octets.append(a, b)) == C.CcBuf.update(C.CcBuf.update(s, a), b) : C.CcBuf}

# ... the digest of one update is the one-shot digest, ...
law buf_final:
  for ~digest: B.Octets -> B.Octets
  for +m: B.Octets
  {C.CcBuf.final(~digest, C.CcBuf.update(C.CcBuf.init(), m)) == digest(m) : B.Octets}

# ... and the split laws: streaming in two and three pieces is one-shot
law buf_split:
  for ~digest: B.Octets -> B.Octets
  for +a: B.Octets
  for +b: B.Octets
  {C.CcBuf.final(~digest, C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b)) == digest(B.Octets.append(a, b)) : B.Octets}

law buf_split3:
  for ~digest: B.Octets -> B.Octets
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {C.CcBuf.final(~digest, C.CcBuf.update(C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b), c)) == digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# The AEAD round trip (crypto's aead.bend), for every key (all four
# algorithms), nonce, associated data and plaintext: open accepts what seal
# produced and gives the plaintext back, and refuses alike when seal
# refuses, given bend-collections' round trip at these arguments (hr:
# decrypt after encrypt gives the plaintext back, or None after None) and
# that its ciphertext is a byte string (h), so that it survives Octets
law aead_round_trip_if:
  for +k: Ad.CcAeadKey
  for +n: B.Octets
  for +a: B.Octets
  for +p: B.Octets
  for hr: {Maybe.bind(&2, List<&2, U32>, List<&2, U32>, Ad.CcAead.sealed(k, n, a, p), c => Ad.CcAead.opened(k, n, a, c)) == Maybe.map(&2, List<&2, U32>, List<&2, U32>, c => B.Octets.to_list(p), Ad.CcAead.sealed(k, n, a, p)) : Maybe<&2, List<&2, U32>>}
  for h: {Ad.CcAead.masked(k, n, a, p) == Ad.CcAead.sealed(k, n, a, p) : Maybe<&2, List<&2, U32>>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Ad.CcAead.seal(k, n, a, p), c => Ad.CcAead.open(k, n, a, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, Ad.CcAead.seal(k, n, a, p)) : Result<&2, &2, Cr.CrError, B.Octets>}

# The specifications, through the interfaces, from bend-collections-laws-
# crypto's laws (those whose proofs pass --verdict: Keccak, Poly1305, X25519
# and Ed25519; README.md lists the others). The executable specifications
# (spec/...) are bend-collections-laws-crypto's transcriptions of FIPS 202,
# RFC 8439, RFC 7748 and RFC 8032. `one` is their symbolic 1 (h1: one == 1),
# which keeps the checker from expanding the curve's constants.

# Keccak-256 is the Keccak sponge KECCAK[512] of FIPS 202 section 5.2, as
# bend-collections specifies it, of the packed message, for every message
law keccak256_spec:
  for +o: B.Octets
  {Kc.CcKeccak.keccak256(o) == Bl.CcBlake.out(8n, KS.keccak256_rounds(24n, Bl.CcBlake.pack(o), B.Octets.len(o))) : B.Octets}

# X25519's public key of a 32-byte secret key is X25519(k, 9) (RFC 7748
# section 6.1), for every key
law x25519_public_spec:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +o: B.Octets
  for +h: {B.Octets.len(o) == 32n : Nat}
  {Result.map(&2, &2, Cr.CrError, Xx.CcX25519Sk, B.Octets, k => Xx.CcX25519.pk_to(Xx.CcX25519.public(k)), Xx.CcX25519.secret(o)) == Done{B.Octets.of_list(SX.x25519(one, B.Octets.to_list(o), SKX.base()))} : Result<&2, &2, Cr.CrError, B.Octets>}

# X25519's agreement from bytes is RFC 7748's X25519(k, u), refused when it
# is all zero (section 6.1), for every two 32-byte strings
law x25519_shared_spec:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +a: B.Octets
  for +u: B.Octets
  for +ha: {B.Octets.len(a) == 32n : Nat}
  for +hu: {B.Octets.len(u) == 32n : Nat}
  {Kx.CrKex.agree(~Xx.CcX25519Sk, ~Xx.CcX25519Pk, ~Xx.CcX25519.secret, ~Xx.CcX25519.pk_of, ~Xx.CcX25519.shared, a, u) == C.CcRes.of_maybe(Cr.CrBadKey{}, SKX.unless_zero(SX.x25519(one, B.Octets.to_list(a), B.Octets.to_list(u)), Nat.is_eq(FS.value(SX.x25519(one, B.Octets.to_list(a), B.Octets.to_list(u))), 0n))) : Result<&2, &2, Cr.CrError, B.Octets>}

# Ed25519's public key, signature and verdict are RFC 8032 section 5.1's
# (5.1.5, 5.1.6, 5.1.7), for every 32-byte seed or public key, message and
# 64-byte signature
law ed25519_public_spec:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +o: B.Octets
  for +h: {B.Octets.len(o) == 32n : Nat}
  {Result.map(&2, &2, Cr.CrError, Ed.CcEdSk, B.Octets, k => Ed.CcEd25519.pk_to(Ed.CcEd25519.public(k)), Ed.CcEd25519.secret(o)) == Done{B.Octets.of_list(SE.public_key(one, B.Octets.to_list(o)))} : Result<&2, &2, Cr.CrError, B.Octets>}

law ed25519_sign_spec:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +o: B.Octets
  for +m: B.Octets
  for +h: {B.Octets.len(o) == 32n : Nat}
  {Result.map(&2, &2, Cr.CrError, Ed.CcEdSk, B.Octets, k => Ed.CcEd25519.sign(k, m), Ed.CcEd25519.secret(o)) == Done{B.Octets.of_list(SE.sign(one, B.Octets.to_list(o), B.Octets.to_list(m)))} : Result<&2, &2, Cr.CrError, B.Octets>}

law ed25519_verify_spec:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +pk: B.Octets
  for +m: B.Octets
  for +s: B.Octets
  for +hp: {B.Octets.len(pk) == 32n : Nat}
  for +hs: {B.Octets.len(s) == 64n : Nat}
  {Sg.CrSign.verify_bytes(~Ed.CcEdPk, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.verify, pk, m, s) == SE.verify(one, B.Octets.to_list(pk), B.Octets.to_list(m), B.Octets.to_list(s)) : Bool}

# Vectors, proved by computation: RFC 8439's ChaCha20 block (2.3.2, through
# the stream interface: the keystream of block 1) and Poly1305 (2.5.2),
# RFC 7693's BLAKE2s-256 of "abc" (appendix B), BLAKE3 of the empty message
# (the BLAKE3 team's test vectors); and refusals of the wrong lengths

law chacha20_rfc8439_block:
  {Result.map(&2, &2, Cr.CrError, B.Octets, String, o => B.Octets.hex(o), St.CrStream.crypt(~Ch.CcChaState, ~St.CrXorOut<Ch.CcChaState>, ~Ch.CcChacha.start, ~Ch.CcChacha.chacha20_update, ~Ch.CcChacha.out_data, B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]), B.Octets.of_list([1, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 74, 0, 0, 0, 0]), B.Octets.zeros(64n))) == Done{"10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e"} : Result<&2, &2, Cr.CrError, String>}

law poly1305_rfc8439:
  {Result.map(&2, &2, Cr.CrError, B.Octets, String, o => B.Octets.hex(o), Mc.CrMac.compute_with(~Po.CcPolyKey, ~Po.CcPoly1305.key, ~Po.CcPoly1305.mac, B.Octets.of_list([133, 214, 190, 120, 87, 85, 109, 51, 127, 68, 82, 254, 66, 213, 6, 168, 1, 3, 128, 138, 251, 13, 178, 253, 74, 191, 246, 175, 65, 73, 245, 27]), B.Octets.of_string("Cryptographic Forum Research Group"))) == Done{"a8061dc1305136c6c22b8baf0c0127a9"} : Result<&2, &2, Cr.CrError, String>}

law blake2s_rfc7693:
  {B.Octets.hex(Bl.CcBlake.blake2s(B.Octets.of_string("abc"))) == "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982" : String}

law blake3_empty:
  {B.Octets.hex(Bl.CcBlake.blake3(B.Octets.empty())) == "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262" : String}

law chacha20_key_length:
  {Ch.CcChacha.start(B.Octets.zeros(31n), B.Octets.zeros(16n)) == Fail{Cr.CrBadKeyLength{31n}} : Result<&2, &2, Cr.CrError, Ch.CcChaState>}

law gcm_key_length:
  {Ad.CcGcm.key128(B.Octets.zeros(32n)) == Fail{Cr.CrBadKeyLength{32n}} : Result<&2, &2, Cr.CrError, Ad.CcAeadKey>}

law x25519_pk_length:
  {Xx.CcX25519.pk_of(B.Octets.zeros(31n)) == Fail{Cr.CrBadPublicKey{}} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}

# The instances

# BEGIN GENERATED by gen/instances.py: laws
# BLAKE2b-512 as a hash (buffered): streaming in two pieces is the one-shot
# digest, for every split
law blake2b_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {C.CcBuf.final(~Bl.CcBlake.blake2b, C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b)) == Bl.CcBlake.blake2b(B.Octets.append(a, b)) : B.Octets}

# BLAKE2b-512 as a hash (buffered): streaming in three pieces is the one-shot
# digest
law blake2b_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {C.CcBuf.final(~Bl.CcBlake.blake2b, C.CcBuf.update(C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b), c)) == Bl.CcBlake.blake2b(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# BLAKE2s-256 as a hash (buffered): streaming in two pieces is the one-shot
# digest, for every split
law blake2s_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {C.CcBuf.final(~Bl.CcBlake.blake2s, C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b)) == Bl.CcBlake.blake2s(B.Octets.append(a, b)) : B.Octets}

# BLAKE2s-256 as a hash (buffered): streaming in three pieces is the one-shot
# digest
law blake2s_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {C.CcBuf.final(~Bl.CcBlake.blake2s, C.CcBuf.update(C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b), c)) == Bl.CcBlake.blake2s(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# BLAKE3-256 as a hash (buffered): streaming in two pieces is the one-shot
# digest, for every split
law blake3_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {C.CcBuf.final(~Bl.CcBlake.blake3, C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b)) == Bl.CcBlake.blake3(B.Octets.append(a, b)) : B.Octets}

# BLAKE3-256 as a hash (buffered): streaming in three pieces is the one-shot
# digest
law blake3_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {C.CcBuf.final(~Bl.CcBlake.blake3, C.CcBuf.update(C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b), c)) == Bl.CcBlake.blake3(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# BLAKE2b with an nn-byte digest, for every nn as a hash (buffered): streaming
# in two pieces is the one-shot digest, for every split
law blake2b_n_hash_split:
  for ~nn: Nat
  for +a: B.Octets
  for +b: B.Octets
  {C.CcBuf.final(~Bl.CcBlake.blake2b_n(~nn), C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b)) == Bl.CcBlake.blake2b_n(~nn, B.Octets.append(a, b)) : B.Octets}

# BLAKE2b with an nn-byte digest, for every nn as a hash (buffered): streaming
# in three pieces is the one-shot digest
law blake2b_n_hash_split3:
  for ~nn: Nat
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {C.CcBuf.final(~Bl.CcBlake.blake2b_n(~nn), C.CcBuf.update(C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b), c)) == Bl.CcBlake.blake2b_n(~nn, B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# Keccak-256 as a hash (buffered): streaming in two pieces is the one-shot
# digest, for every split
law keccak256_hash_split:
  for +a: B.Octets
  for +b: B.Octets
  {C.CcBuf.final(~Kc.CcKeccak.keccak256, C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b)) == Kc.CcKeccak.keccak256(B.Octets.append(a, b)) : B.Octets}

# Keccak-256 as a hash (buffered): streaming in three pieces is the one-shot
# digest
law keccak256_hash_split3:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {C.CcBuf.final(~Kc.CcKeccak.keccak256, C.CcBuf.update(C.CcBuf.update(C.CcBuf.update(C.CcBuf.init(), a), b), c)) == Kc.CcKeccak.keccak256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}

# ChaCha with r double rounds, for every r (ChaCha20 and XChaCha20: r = 10) as
# a stream cipher: decryption is encryption, for every state and data
law chacha_stream_involution:
  for ~r: Nat
  for +s: Ch.CcChaState
  for +m: B.Octets
  {Ch.CcChacha.out_data(Ch.CcChacha.update(~r, s, Ch.CcChacha.out_data(Ch.CcChacha.update(~r, s, m)))) == m : B.Octets}

# ChaCha with r double rounds, for every r (ChaCha20 and XChaCha20: r = 10):
# the data a ++ b gives the output of a, then the output of b from the state
# after a
law chacha_stream_streaming_data:
  for ~r: Nat
  for +s: Ch.CcChaState
  for +a: B.Octets
  for +b: B.Octets
  {Ch.CcChacha.out_data(Ch.CcChacha.update(~r, s, B.Octets.append(a, b))) == B.Octets.append(Ch.CcChacha.out_data(Ch.CcChacha.update(~r, s, a)), Ch.CcChacha.out_data(Ch.CcChacha.update(~r, Ch.CcChacha.out_state(Ch.CcChacha.update(~r, s, a)), b))) : B.Octets}

# ChaCha with r double rounds, for every r (ChaCha20 and XChaCha20: r = 10):
# the state after a ++ b is the state after a, then b
law chacha_stream_streaming_state:
  for ~r: Nat
  for +s: Ch.CcChaState
  for +a: B.Octets
  for +b: B.Octets
  {Ch.CcChacha.out_state(Ch.CcChacha.update(~r, s, B.Octets.append(a, b))) == Ch.CcChacha.out_state(Ch.CcChacha.update(~r, Ch.CcChacha.out_state(Ch.CcChacha.update(~r, s, a)), b)) : Ch.CcChaState}

# Poly1305 as a MAC: verify accepts the computed tag, for every key and
# message
law poly1305_accepts:
  for +k: Po.CcPolyKey
  for +m: B.Octets
  {Po.CcPoly1305.verify(k, m, Po.CcPoly1305.mac(k, m)) == True{} : Bool}

# Poly1305: verify accepts exactly the computed tag, comparing every byte
law poly1305_agrees:
  for +k: Po.CcPolyKey
  for +m: B.Octets
  for t: B.Octets
  {Po.CcPoly1305.verify(k, m, t) == B.Octets.is_eq(Po.CcPoly1305.mac(k, m), t) : Bool}

# GMAC (AES-128 and AES-256) as a MAC: verify accepts the computed tag, for
# every key and message
law gmac_accepts:
  for +k: Gm.CcGmacKey
  for +m: B.Octets
  {Gm.CcGmac.verify(k, m, Gm.CcGmac.mac(k, m)) == True{} : Bool}

# GMAC (AES-128 and AES-256): verify accepts exactly the computed tag,
# comparing every byte
law gmac_agrees:
  for +k: Gm.CcGmacKey
  for +m: B.Octets
  for t: B.Octets
  {Gm.CcGmac.verify(k, m, t) == B.Octets.is_eq(Gm.CcGmac.mac(k, m), t) : Bool}

# Ed25519 (crypto's sign_verify_bytes_if): a signature checked from the public
# key's bytes is accepted, for every key and message, when the public key
# survives its bytes (hf) and the scheme accepts the signature (ha)
law ed25519_verify_bytes_if:
  for +sk: Ed.CcEdSk
  for +m: B.Octets
  for hf: {Ed.CcEd25519.pk_of(Ed.CcEd25519.pk_to(Ed.CcEd25519.public(sk))) == Done{Ed.CcEd25519.public(sk)} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}
  for ha: {Ed.CcEd25519.verify(Ed.CcEd25519.public(sk), m, Ed.CcEd25519.sign(sk, m)) == True{} : Bool}
  {Sg.CrSign.verify_bytes(~Ed.CcEdPk, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.verify, Ed.CcEd25519.pk_to(Ed.CcEd25519.public(sk)), m, Ed.CcEd25519.sign(sk, m)) == True{} : Bool}

# X25519 (crypto's kex_agree_if): two parties agree from each other's public-
# key bytes, for every pair of keys, when the keys parse (hx, hy), the public
# keys survive their bytes (hfx, hfy) and the shared secrets agree (h)
law x25519_agree_if:
  for +a: B.Octets
  for +b: B.Octets
  for +x: Xx.CcX25519Sk
  for +y: Xx.CcX25519Sk
  for hx: {Xx.CcX25519.secret(a) == Done{x} : Result<&2, &2, Cr.CrError, Xx.CcX25519Sk>}
  for hy: {Xx.CcX25519.secret(b) == Done{y} : Result<&2, &2, Cr.CrError, Xx.CcX25519Sk>}
  for hfx: {Xx.CcX25519.pk_of(Xx.CcX25519.pk_to(Xx.CcX25519.public(x))) == Done{Xx.CcX25519.public(x)} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}
  for hfy: {Xx.CcX25519.pk_of(Xx.CcX25519.pk_to(Xx.CcX25519.public(y))) == Done{Xx.CcX25519.public(y)} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}
  for h: {Xx.CcX25519.shared(x, Xx.CcX25519.public(y)) == Xx.CcX25519.shared(y, Xx.CcX25519.public(x)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Kx.CrKex.agree(~Xx.CcX25519Sk, ~Xx.CcX25519Pk, ~Xx.CcX25519.secret, ~Xx.CcX25519.pk_of, ~Xx.CcX25519.shared, a, Xx.CcX25519.pk_to(Xx.CcX25519.public(y))) == Kx.CrKex.agree(~Xx.CcX25519Sk, ~Xx.CcX25519Pk, ~Xx.CcX25519.secret, ~Xx.CcX25519.pk_of, ~Xx.CcX25519.shared, b, Xx.CcX25519.pk_to(Xx.CcX25519.public(x))) : Result<&2, &2, Cr.CrError, B.Octets>}

# X25519's public keys: a public key read from bytes is read again from the
# bytes written for it, for every input
law x25519_pk_format:
  for +o: B.Octets
  for +p: Xx.CcX25519Pk
  for h: {Xx.CcX25519.pk_of(o) == Done{p} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}
  {Xx.CcX25519.pk_of(Xx.CcX25519.pk_to(p)) == Done{p} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}

# Ed25519's public keys: a public key read from bytes is read again from the
# bytes written for it, for every input
law ed25519_pk_format:
  for +o: B.Octets
  for +p: Ed.CcEdPk
  for h: {Ed.CcEd25519.pk_of(o) == Done{p} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}
  {Ed.CcEd25519.pk_of(Ed.CcEd25519.pk_to(p)) == Done{p} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}
# END GENERATED: laws
