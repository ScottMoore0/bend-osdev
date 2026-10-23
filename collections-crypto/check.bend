# Every instance through crypto's interfaces, on its specification's own
# vectors: ChaCha20 (RFC 8439 2.3.2, 2.4.2 whole, in pieces and back, 2.6.2's
# Poly1305 key), Poly1305 (2.5.2), ChaCha20-Poly1305 (2.8.2), XChaCha20 and
# XChaCha20-Poly1305 (draft-irtf-cfrg-xchacha-03 A.3.2.1 and A.3.1), AES-GCM
# (the GCM specification's test cases 1 to 4 and 13 to 16) and GMAC (its
# test cases 1 and 13, which seal nothing), X25519 (RFC 7748 5.2 and 6.1),
# Ed25519 (RFC 8032 7.1's TEST 1, 2, 3 and SHA(abc)), BLAKE2b-512 and
# BLAKE2s-256 (RFC 7693 appendices A and B), BLAKE3 (the BLAKE3 team's
# test_vectors.json, hash mode), Keccak-256 (ref/gen.py's model, which is
# checked against hashlib's SHA-3 first: no published Keccak-256 vector was
# read); every refusal; and, for each AEAD vector, that bend-collections'
# answer is a byte string (the hypothesis of LAWS.bend's round trip).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/stream.bend as St
import ../crypto/hash.bend as H
import ../crypto/mac.bend as Mc
import ../crypto/aead.bend as Ae
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

# ---------------------------------------------------------------- helpers

def ck.base(digit: Bool) -> U32:
  match digit:
    case True{}:
      48
    case False{}:
      87

def ck.nib(+c: U32) -> U32:
  U32.sub(c, ck.base(U32.is_lt(c, 58)))

def ck.hex(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Con{a, Con{b, t}}:
      ck.hex(t, Con{U32.add(U32.mul(ck.nib(a), 16), ck.nib(b)), acc})
    case _:
      B.rev(acc)

def hx(s: String) -> B.Octets:
  B.Octets.of_list(ck.hex(B.Octets.to_list(B.Octets.of_string(s)), Nil{}))

def str(s: String) -> B.Octets:
  B.Octets.of_string(s)

def yn(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def err(e: Cr.CrError) -> String:
  match e:
    case Cr.CrBadKeyLength{n}:
      "bad key length " ++ Nat.show(n)
    case Cr.CrBadIvLength{n}:
      "bad IV length " ++ Nat.show(n)
    case Cr.CrBadNonceLength{n}:
      "bad nonce length " ++ Nat.show(n)
    case Cr.CrTagMismatch{}:
      "tag mismatch"
    case Cr.CrBadKey{}:
      "bad key"
    case Cr.CrBadPublicKey{}:
      "bad public key"
    case _:
      "other refusal"

def show(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      err(e)

# the message of RFC 8439 2.4.2 and 2.8.2
def sunscreen() -> B.Octets:
  str("Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.")

# n bytes 0, 1, ..., 250, 0, 1, ... (the BLAKE3 vectors' input)
def ck.ramp(n: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      B.rev(acc)
    case 1n+p:
      ck.ramp(p, U32.mod(U32.add(i, 1), 251), Con{i, acc})

def ramp(n: Nat) -> B.Octets:
  B.Octets.of_list(ck.ramp(n, 0, Nil{}))

# ---------------------------------------------------------------- ChaCha20

def cha.key() -> B.Octets:
  hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")

def cha.ks(r: Result<&2, &2, Cr.CrError, Ch.CcChaState>, n: Nat) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{s}:
      B.Octets.hex(St.CrStream.keystream(~Ch.CcChaState, ~St.CrXorOut<Ch.CcChaState>, ~Ch.CcChacha.chacha20_update, ~Ch.CcChacha.out_data, s, n))

def cha.two.go(o: St.CrXorOut<Ch.CcChaState>, b: B.Octets) -> B.Octets:
  match o:
    case St.CrXorOut{s, d}:
      B.Octets.append(d, Ch.CcChacha.out_data(Ch.CcChacha.chacha20_update(s, b)))

# the data in two pieces, cut after k bytes
def cha.two(r: Result<&2, &2, Cr.CrError, Ch.CcChaState>, +k: Nat, +m: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{s}:
      B.Octets.hex(cha.two.go(Ch.CcChacha.chacha20_update(s, B.Octets.take(k, m)), B.Octets.drop(k, m)))

def cha.crypt(key: B.Octets, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  St.CrStream.crypt(~Ch.CcChaState, ~St.CrXorOut<Ch.CcChaState>, ~Ch.CcChacha.start, ~Ch.CcChacha.chacha20_update, ~Ch.CcChacha.out_data, key, iv, m)

def cha.back(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{c}:
      B.Octets.to_string(Result.default(&2, &2, Cr.CrError, B.Octets, cha.crypt(cha.key(), hx("01000000000000000000004a00000000"), c), B.Octets.empty()))

def chacha_lines() -> List<&2, String>:
  [
    "chacha20 rfc8439 2.3.2 block " ++ cha.ks(Ch.CcChacha.start(cha.key(), hx("01000000000000090000004a00000000")), 64n),
    "chacha20 rfc8439 2.4.2 " ++ show(cha.crypt(cha.key(), hx("01000000000000000000004a00000000"), sunscreen())),
    "chacha20 rfc8439 2.4.2 in pieces " ++ cha.two(Ch.CcChacha.start(cha.key(), hx("01000000000000000000004a00000000")), 37n, sunscreen()),
    "chacha20 rfc8439 2.4.2 decrypted " ++ cha.back(cha.crypt(cha.key(), hx("01000000000000000000004a00000000"), sunscreen())),
    "chacha20 rfc8439 2.6.2 poly1305 key " ++ cha.ks(Ch.CcChacha.start(hx("808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"), hx("00000000000000000001020304050607")), 32n),
    "chacha20 refusals " ++ show(cha.crypt(B.Octets.zeros(31n), B.Octets.zeros(16n), str("m"))) ++ ", " ++ show(cha.crypt(B.Octets.zeros(32n), B.Octets.zeros(12n), str("m")))
  ]

# XChaCha20: draft-irtf-cfrg-xchacha-03 A.3.2.1 (block counter 0)
def xcha.pt() -> B.Octets:
  hx("5468652064686f6c65202870726f6e6f756e6365642022646f6c65222920697320616c736f206b6e6f776e2061732074686520417369617469632077696c6420646f672c2072656420646f672c20616e642077686973746c696e6720646f672e2049742069732061626f7574207468652073697a65206f662061204765726d616e20736865706865726420627574206c6f6f6b73206d6f7265206c696b652061206c6f6e672d6c656767656420666f782e205468697320686967686c7920656c757369766520616e6420736b696c6c6564206a756d70657220697320636c6173736966696564207769746820776f6c7665732c20636f796f7465732c206a61636b616c732c20616e6420666f78657320696e20746865207461786f6e6f6d69632066616d696c792043616e696461652e")

def xchacha_lines() -> List<&2, String>:
  +k = hx("808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f")
  +n = hx("404142434445464748494a4b4c4d4e4f5051525354555658")
  [
    "xchacha20 draft A.3.2.1 " ++ show(St.CrStream.crypt(~Ch.CcChaState, ~St.CrXorOut<Ch.CcChaState>, ~Ch.CcChacha.xchacha20_start, ~Ch.CcChacha.chacha20_update, ~Ch.CcChacha.out_data, k, n, xcha.pt())),
    "xchacha20 refusals " ++ show(St.CrStream.crypt(~Ch.CcChaState, ~St.CrXorOut<Ch.CcChaState>, ~Ch.CcChacha.xchacha20_start, ~Ch.CcChacha.chacha20_update, ~Ch.CcChacha.out_data, k, B.Octets.zeros(12n), str("m")))
  ]

# ---------------------------------------------------------------- MACs

def poly.k() -> B.Octets:
  hx("85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b")

def poly.v(r: Result<&2, &2, Cr.CrError, Po.CcPolyKey>, m: B.Octets, t: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{k}:
      yn(Po.CcPoly1305.verify(k, m, t))

def gmac.v(r: Result<&2, &2, Cr.CrError, Gm.CcGmacKey>, m: B.Octets, t: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{k}:
      yn(Gm.CcGmac.verify(k, m, t))

def mac_lines() -> List<&2, String>:
  +m = str("Cryptographic Forum Research Group")
  [
    "poly1305 rfc8439 2.5.2 " ++ show(Mc.CrMac.compute_with(~Po.CcPolyKey, ~Po.CcPoly1305.key, ~Po.CcPoly1305.mac, poly.k(), m)),
    "poly1305 verify " ++ poly.v(Po.CcPoly1305.key(poly.k()), m, hx("a8061dc1305136c6c22b8baf0c0127a9")) ++ ", changed tag " ++ poly.v(Po.CcPoly1305.key(poly.k()), m, hx("a8061dc1305136c6c22b8baf0c0127a8")) ++ ", changed message " ++ poly.v(Po.CcPoly1305.key(poly.k()), str("Cryptographic Forum Research Grouq"), hx("a8061dc1305136c6c22b8baf0c0127a9")),
    "poly1305 refusal " ++ show(Mc.CrMac.compute_with(~Po.CcPolyKey, ~Po.CcPoly1305.key, ~Po.CcPoly1305.mac, B.Octets.zeros(16n), m)),
    "gmac-aes-128 gcm test case 1 " ++ show(Mc.CrMac.compute_with(~Gm.CcGmacKey, ~Gm.CcGmac.key128, ~Gm.CcGmac.mac, B.Octets.zeros(16n), B.Octets.zeros(12n))),
    "gmac-aes-256 gcm test case 13 " ++ show(Mc.CrMac.compute_with(~Gm.CcGmacKey, ~Gm.CcGmac.key256, ~Gm.CcGmac.mac, B.Octets.zeros(32n), B.Octets.zeros(12n))),
    "gmac verify " ++ gmac.v(Gm.CcGmac.key128(B.Octets.zeros(16n)), B.Octets.zeros(12n), hx("58e2fccefa7e3061367f1d57a4e7455a")) ++ ", changed tag " ++ gmac.v(Gm.CcGmac.key128(B.Octets.zeros(16n)), B.Octets.zeros(12n), hx("58e2fccefa7e3061367f1d57a4e7455b")) ++ ", changed message " ++ gmac.v(Gm.CcGmac.key128(B.Octets.zeros(16n)), B.Octets.zeros(13n), hx("58e2fccefa7e3061367f1d57a4e7455a")),
    "gmac refusal " ++ show(Mc.CrMac.compute_with(~Gm.CcGmacKey, ~Gm.CcGmac.key256, ~Gm.CcGmac.mac, B.Octets.zeros(16n), B.Octets.zeros(12n)))
  ]

# ---------------------------------------------------------------- AEADs

# whether bend-collections' answer is a byte string (LAWS.bend's h)
def ck.same(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      B.list_eq(x, y)
    case _ _:
      False{}

def ck.bytes.go(r: Result<&2, &2, Cr.CrError, Ad.CcAeadKey>, +n: B.Octets, +a: B.Octets, +p: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{+k}:
      yn(ck.same(Ad.CcAead.masked(k, n, a, p), Ad.CcAead.sealed(k, n, a, p)))

def seal(~key: B.Octets -> Result<&2, &2, Cr.CrError, Ad.CcAeadKey>, +k: B.Octets, +n: B.Octets, +a: B.Octets, +p: B.Octets) -> String:
  show(Ae.CrAead.seal_with(~Ad.CcAeadKey, ~key, ~Ad.CcAead.seal, k, n, a, p)) ++ " bytes " ++ ck.bytes.go(key(k), n, a, p)

def open(~key: B.Octets -> Result<&2, &2, Cr.CrError, Ad.CcAeadKey>, k: B.Octets, n: B.Octets, a: B.Octets, c: B.Octets) -> String:
  show(Ae.CrAead.open_with(~Ad.CcAeadKey, ~key, ~Ad.CcAead.open, k, n, a, c))

def gcm.k1() -> B.Octets:
  hx("feffe9928665731c6d6a8f9467308308")

def gcm.k2() -> B.Octets:
  hx("feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308")

def gcm.iv() -> B.Octets:
  hx("cafebabefacedbaddecaf888")

def gcm.p64() -> B.Octets:
  hx("d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255")

def gcm.p60() -> B.Octets:
  hx("d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39")

def gcm.a() -> B.Octets:
  hx("feedfacedeadbeeffeedfacedeadbeefabaddad2")

def gcm_lines() -> List<&2, String>:
  [
    "aes-128-gcm test case 1 " ++ seal(~Ad.CcGcm.key128, B.Octets.zeros(16n), B.Octets.zeros(12n), B.Octets.empty(), B.Octets.empty()),
    "aes-128-gcm test case 2 " ++ seal(~Ad.CcGcm.key128, B.Octets.zeros(16n), B.Octets.zeros(12n), B.Octets.empty(), B.Octets.zeros(16n)),
    "aes-128-gcm test case 3 " ++ seal(~Ad.CcGcm.key128, gcm.k1(), gcm.iv(), B.Octets.empty(), gcm.p64()),
    "aes-128-gcm test case 4 " ++ seal(~Ad.CcGcm.key128, gcm.k1(), gcm.iv(), gcm.a(), gcm.p60()),
    "aes-128-gcm test case 4 opened " ++ open(~Ad.CcGcm.key128, gcm.k1(), gcm.iv(), gcm.a(), hx("42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e0915bc94fbc3221a5db94fae95ae7121a47")),
    "aes-128-gcm changed tag " ++ open(~Ad.CcGcm.key128, gcm.k1(), gcm.iv(), gcm.a(), hx("42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e0915bc94fbc3221a5db94fae95ae7121a46")) ++ ", changed data " ++ open(~Ad.CcGcm.key128, gcm.k1(), gcm.iv(), gcm.a(), hx("43831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e0915bc94fbc3221a5db94fae95ae7121a47")) ++ ", changed associated data " ++ open(~Ad.CcGcm.key128, gcm.k1(), gcm.iv(), hx("feedfacedeadbeeffeedfacedeadbeefabaddad3"), hx("42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e0915bc94fbc3221a5db94fae95ae7121a47")),
    "aes-256-gcm test case 13 " ++ seal(~Ad.CcGcm.key256, B.Octets.zeros(32n), B.Octets.zeros(12n), B.Octets.empty(), B.Octets.empty()),
    "aes-256-gcm test case 14 " ++ seal(~Ad.CcGcm.key256, B.Octets.zeros(32n), B.Octets.zeros(12n), B.Octets.empty(), B.Octets.zeros(16n)),
    "aes-256-gcm test case 15 " ++ seal(~Ad.CcGcm.key256, gcm.k2(), gcm.iv(), B.Octets.empty(), gcm.p64()),
    "aes-256-gcm test case 16 " ++ seal(~Ad.CcGcm.key256, gcm.k2(), gcm.iv(), gcm.a(), gcm.p60()),
    "aes-256-gcm test case 16 opened " ++ open(~Ad.CcGcm.key256, gcm.k2(), gcm.iv(), gcm.a(), hx("522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f66276fc6ece0f4e1768cddf8853bb2d551b")),
    "aes-gcm refusals " ++ seal(~Ad.CcGcm.key128, B.Octets.zeros(24n), B.Octets.zeros(12n), B.Octets.empty(), B.Octets.empty()) ++ ", " ++ seal(~Ad.CcGcm.key256, B.Octets.zeros(32n), B.Octets.zeros(16n), B.Octets.empty(), B.Octets.empty()) ++ ", " ++ open(~Ad.CcGcm.key128, B.Octets.zeros(16n), B.Octets.zeros(12n), B.Octets.empty(), B.Octets.zeros(15n))
  ]

def cp.k() -> B.Octets:
  hx("808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f")

def chapoly_lines() -> List<&2, String>:
  +aad = hx("50515253c0c1c2c3c4c5c6c7")
  +c = hx("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b61161ae10b594f09e26a7e902ecbd0600691")
  +xc = hx("bd6d179d3e83d43b9576579493c0e939572a1700252bfaccbed2902c21396cbb731c7f1b0b4aa6440bf3a82f4eda7e39ae64c6708c54c216cb96b72e1213b4522f8c9ba40db5d945b11b69b982c1bb9e3f3fac2bc369488f76b2383565d3fff921f9664c97637da9768812f615c68b13b52ec0875924c1c7987947deafd8780acf49")
  +xn = hx("404142434445464748494a4b4c4d4e4f5051525354555657")
  [
    "chacha20-poly1305 rfc8439 2.8.2 " ++ seal(~Ad.CcChaPoly.key, cp.k(), hx("070000004041424344454647"), aad, sunscreen()),
    "chacha20-poly1305 opened " ++ open(~Ad.CcChaPoly.key, cp.k(), hx("070000004041424344454647"), aad, c),
    "chacha20-poly1305 changed associated data " ++ open(~Ad.CcChaPoly.key, cp.k(), hx("070000004041424344454647"), hx("50515253c0c1c2c3c4c5c6c6"), c) ++ ", other nonce " ++ open(~Ad.CcChaPoly.key, cp.k(), hx("070000004041424344454648"), aad, c),
    "xchacha20-poly1305 draft A.3.1 " ++ seal(~Ad.CcXChaPoly.key, cp.k(), xn, aad, sunscreen()),
    "xchacha20-poly1305 opened " ++ open(~Ad.CcXChaPoly.key, cp.k(), xn, aad, xc),
    "chacha20-poly1305 refusals " ++ seal(~Ad.CcChaPoly.key, cp.k(), xn, aad, sunscreen()) ++ ", " ++ open(~Ad.CcXChaPoly.key, cp.k(), hx("070000004041424344454647"), aad, xc) ++ ", " ++ seal(~Ad.CcXChaPoly.key, B.Octets.zeros(16n), xn, aad, sunscreen())
  ]

# ---------------------------------------------------------------- X25519

def x.pub(r: Result<&2, &2, Cr.CrError, Xx.CcX25519Sk>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{k}:
      B.Octets.hex(Xx.CcX25519.pk_to(Xx.CcX25519.public(k)))

def x.agree(k: B.Octets, u: B.Octets) -> String:
  show(Kx.CrKex.agree(~Xx.CcX25519Sk, ~Xx.CcX25519Pk, ~Xx.CcX25519.secret, ~Xx.CcX25519.pk_of, ~Xx.CcX25519.shared, k, u))

def x25519_lines() -> List<&2, String>:
  +a = hx("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
  +b = hx("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
  +nine = hx("0900000000000000000000000000000000000000000000000000000000000000")
  [
    "x25519 rfc7748 5.2 vector 1 " ++ x.agree(hx("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"), hx("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c")),
    "x25519 rfc7748 5.2 vector 2 " ++ x.agree(hx("4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"), hx("e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493")),
    "x25519 rfc7748 5.2 one iteration " ++ x.agree(nine, nine),
    "x25519 rfc7748 6.1 public keys " ++ x.pub(Xx.CcX25519.secret(a)) ++ " " ++ x.pub(Xx.CcX25519.secret(b)),
    "x25519 rfc7748 6.1 shared " ++ x.agree(a, hx("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")) ++ " " ++ x.agree(b, hx("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")),
    "x25519 refusals " ++ x.agree(a, B.Octets.zeros(32n)) ++ ", " ++ x.agree(B.Octets.zeros(31n), nine) ++ ", " ++ x.agree(a, B.Octets.zeros(33n))
  ]

# ---------------------------------------------------------------- Ed25519

def ed.go(r: Result<&2, &2, Cr.CrError, Sg.CrKeypair<Ed.CcEdSk, Ed.CcEdPk>>, +m: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{kp}:
      match kp:
        case Sg.CrKeypair{sk, +pk}:
          +s = Ed.CcEd25519.sign(sk, m)
          B.Octets.hex(Ed.CcEd25519.pk_to(pk)) ++ " " ++ B.Octets.hex(s) ++ " " ++ yn(Sg.CrSign.verify_bytes(~Ed.CcEdPk, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.verify, Ed.CcEd25519.pk_to(pk), m, s)) ++ " " ++ yn(Sg.CrSign.verify_bytes(~Ed.CcEdPk, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.verify, Ed.CcEd25519.pk_to(pk), B.Octets.append(m, str("!")), s))

def ed(k: B.Octets, m: B.Octets) -> String:
  ed.go(Sg.CrSign.keypair(~Ed.CcEdSk, ~Ed.CcEdPk, ~Ed.CcEd25519.secret, ~Ed.CcEd25519.public, k), m)

def ed25519_lines() -> List<&2, String>:
  [
    "ed25519 rfc8032 test 1 " ++ ed(hx("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"), B.Octets.empty()),
    "ed25519 rfc8032 test 2 " ++ ed(hx("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"), hx("72")),
    "ed25519 rfc8032 test 3 " ++ ed(hx("c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7"), hx("af82")),
    "ed25519 rfc8032 test sha(abc) " ++ ed(hx("833fe62409237b9d62ec77587520911e9a759cec1d19755b7da901b96dca3d42"), hx("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")),
    "ed25519 refusals " ++ ed(B.Octets.zeros(31n), B.Octets.empty()) ++ ", " ++ yn(Sg.CrSign.verify_bytes(~Ed.CcEdPk, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.verify, B.Octets.zeros(31n), B.Octets.empty(), B.Octets.zeros(64n)))
  ]

# ---------------------------------------------------------------- hashes

def pieces(~digest: B.Octets -> B.Octets, ps: List<&2, B.Octets>) -> String:
  B.Octets.hex(H.CrHash.of_pieces(~C.CcBuf, ~C.CcBuf.init(), ~C.CcBuf.update, ~C.CcBuf.final(~digest), ps))

def b3(+n: Nat) -> String:
  "blake3 " ++ Nat.show(n) ++ " " ++ B.Octets.hex(Bl.CcBlake.blake3(ramp(n)))

def hash_lines() -> List<&2, String>:
  [
    "blake2b-512 rfc7693 a " ++ B.Octets.hex(Bl.CcBlake.blake2b(str("abc"))) ++ " in pieces " ++ pieces(~Bl.CcBlake.blake2b, [str("a"), str(""), str("bc")]),
    "blake2s-256 rfc7693 b " ++ B.Octets.hex(Bl.CcBlake.blake2s(str("abc"))) ++ " in pieces " ++ pieces(~Bl.CcBlake.blake2s, [str("ab"), str("c")]),
    "blake2b-256 of abc " ++ B.Octets.hex(Bl.CcBlake.blake2b_256(str("abc"))),
    "blake2b-384 of abc " ++ B.Octets.hex(Bl.CcBlake.blake2b_384(str("abc"))),
    b3(0n),
    b3(1n),
    b3(1023n),
    b3(1024n),
    b3(1025n),
    b3(2048n),
    b3(2049n),
    b3(3072n),
    b3(3073n),
    b3(4096n),
    b3(4097n),
    b3(8192n),
    b3(8193n),
    b3(31744n),
    "blake3 1025 in pieces " ++ pieces(~Bl.CcBlake.blake3, [ramp(1000n), B.Octets.drop(1000n, ramp(1025n))]),
    "keccak-256 empty " ++ B.Octets.hex(Kc.CcKeccak.keccak256(B.Octets.empty())) ++ " abc " ++ pieces(~Kc.CcKeccak.keccak256, [str("a"), str("bc")])
  ]

def ck.print(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        ck.print(t)

def main() -> IO(Unit):
  do IO<Unit>:
    ck.print(chacha_lines())
    ck.print(xchacha_lines())
    ck.print(mac_lines())
    ck.print(gcm_lines())
    ck.print(chapoly_lines())
    ck.print(x25519_lines())
    ck.print(ed25519_lines())
    ck.print(hash_lines())
#|chacha20 rfc8439 2.3.2 block 10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e
#|chacha20 rfc8439 2.4.2 6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d
#|chacha20 rfc8439 2.4.2 in pieces 6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d
#|chacha20 rfc8439 2.4.2 decrypted Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.
#|chacha20 rfc8439 2.6.2 poly1305 key 8ad5a08b905f81cc815040274ab29471a833b637e3fd0da508dbb8e2fdd1a646
#|chacha20 refusals bad key length 31, bad IV length 12
#|xchacha20 draft A.3.2.1 4559abba4e48c16102e8bb2c05e6947f50a786de162f9b0b7e592a9b53d0d4e98d8d6410d540a1a6375b26d80dace4fab52384c731acbf16a5923c0c48d3575d4d0d2c673b666faa731061277701093a6bf7a158a8864292a41c48e3a9b4c0daece0f8d98d0d7e05b37a307bbb66333164ec9e1b24ea0d6c3ffddcec4f68e7443056193a03c810e11344ca06d8ed8a2bfb1e8d48cfa6bc0eb4e2464b748142407c9f431aee769960e15ba8b96890466ef2457599852385c661f752ce20f9da0c09ab6b19df74e76a95967446f8d0fd415e7bee2a12a114c20eb5292ae7a349ae577820d5520a1f3fb62a17ce6a7e68fa7c79111d8860920bc048ef43fe84486ccb87c25f0ae045f0cce1e7989a9aa220a28bdd4827e751a24a6d5c62d790a66393b93111c1a55dd7421a10184974c7c5
#|xchacha20 refusals bad IV length 12
#|poly1305 rfc8439 2.5.2 a8061dc1305136c6c22b8baf0c0127a9
#|poly1305 verify yes, changed tag no, changed message no
#|poly1305 refusal bad key length 16
#|gmac-aes-128 gcm test case 1 58e2fccefa7e3061367f1d57a4e7455a
#|gmac-aes-256 gcm test case 13 530f8afbc74536b9a963b4f1c4cb738b
#|gmac verify yes, changed tag no, changed message no
#|gmac refusal bad key length 16
#|aes-128-gcm test case 1 58e2fccefa7e3061367f1d57a4e7455a bytes yes
#|aes-128-gcm test case 2 0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf bytes yes
#|aes-128-gcm test case 3 42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f59854d5c2af327cd64a62cf35abd2ba6fab4 bytes yes
#|aes-128-gcm test case 4 42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e0915bc94fbc3221a5db94fae95ae7121a47 bytes yes
#|aes-128-gcm test case 4 opened d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39
#|aes-128-gcm changed tag tag mismatch, changed data tag mismatch, changed associated data tag mismatch
#|aes-256-gcm test case 13 530f8afbc74536b9a963b4f1c4cb738b bytes yes
#|aes-256-gcm test case 14 cea7403d4d606b6e074ec5d3baf39d18d0d1c8a799996bf0265b98b5d48ab919 bytes yes
#|aes-256-gcm test case 15 522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015adb094dac5d93471bdec1a502270e3cc6c bytes yes
#|aes-256-gcm test case 16 522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f66276fc6ece0f4e1768cddf8853bb2d551b bytes yes
#|aes-256-gcm test case 16 opened d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39
#|aes-gcm refusals bad key length 24 bytes bad key length 24, bad nonce length 16 bytes yes, tag mismatch
#|chacha20-poly1305 rfc8439 2.8.2 d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b61161ae10b594f09e26a7e902ecbd0600691 bytes yes
#|chacha20-poly1305 opened 4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e
#|chacha20-poly1305 changed associated data tag mismatch, other nonce tag mismatch
#|xchacha20-poly1305 draft A.3.1 bd6d179d3e83d43b9576579493c0e939572a1700252bfaccbed2902c21396cbb731c7f1b0b4aa6440bf3a82f4eda7e39ae64c6708c54c216cb96b72e1213b4522f8c9ba40db5d945b11b69b982c1bb9e3f3fac2bc369488f76b2383565d3fff921f9664c97637da9768812f615c68b13b52ec0875924c1c7987947deafd8780acf49 bytes yes
#|xchacha20-poly1305 opened 4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e
#|chacha20-poly1305 refusals bad nonce length 24 bytes yes, bad nonce length 12, bad key length 16 bytes bad key length 16
#|x25519 rfc7748 5.2 vector 1 c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552
#|x25519 rfc7748 5.2 vector 2 95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957
#|x25519 rfc7748 5.2 one iteration 422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079
#|x25519 rfc7748 6.1 public keys 8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f
#|x25519 rfc7748 6.1 shared 4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742 4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742
#|x25519 refusals bad key, bad key length 31, bad public key
#|ed25519 rfc8032 test 1 d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b yes no
#|ed25519 rfc8032 test 2 3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c 92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00 yes no
#|ed25519 rfc8032 test 3 fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025 6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a yes no
#|ed25519 rfc8032 test sha(abc) ec172b93ad5e563bf4932c70e1245034c35467ef2efd4d64ebf819683467e2bf dc2a4459e7369633a52b1bf277839a00201009a3efbf3ecb69bea2186c26b58909351fc9ac90b3ecfdfbc7c66431e0303dca179c138ac17ad9bef1177331a704 yes no
#|ed25519 refusals bad key length 31, no
#|blake2b-512 rfc7693 a ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923 in pieces ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923
#|blake2s-256 rfc7693 b 508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982 in pieces 508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982
#|blake2b-256 of abc bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319
#|blake2b-384 of abc 6f56a82c8e7ef526dfe182eb5212f7db9df1317e57815dbda46083fc30f54ee6c66ba83be64b302d7cba6ce15bb556f4
#|blake3 0 af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262
#|blake3 1 2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213
#|blake3 1023 10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11
#|blake3 1024 42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7
#|blake3 1025 d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444
#|blake3 2048 e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a
#|blake3 2049 5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030
#|blake3 3072 b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2
#|blake3 3073 7124b49501012f81cc7f11ca069ec9226cecb8a2c850cfe644e327d22d3e1cd3
#|blake3 4096 015094013f57a5277b59d8475c0501042c0b642e531b0a1c8f58d2163229e969
#|blake3 4097 9b4052b38f1c5fc8b1f9ff7ac7b27cd242487b3d890d15c96a1c25b8aa0fb995
#|blake3 8192 aae792484c8efe4f19e2ca7d371d8c467ffb10748d8a5a1ae579948f718a2a63
#|blake3 8193 bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b
#|blake3 31744 62b6960e1a44bcc1eb1a611a8d6235b6b4b78f32e7abc4fb4c6cdcce94895c47
#|blake3 1025 in pieces d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444
#|keccak-256 empty c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 abc 4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
