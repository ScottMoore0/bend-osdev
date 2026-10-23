# Every construction on its specification's vectors, or on values from
# outside this package: RFC 10032's AESRound vector (A.1); AEGIS-128 on the
# four test vectors of Wu and Preneel's SAC 2013 paper (Appendix A.1), sealed
# and opened back; AEGIS-128 sealed and opened back on four more inputs, a
# changed tag and a changed ciphertext byte refused, and the refusals of a
# short key and nonce (values from ref/model.py, which shares this package's
# author and agrees with the paper's vectors); Encrypt-then-MAC on RFC 7518's Appendix B.1
# (AES_128_CBC_HMAC_SHA_256, the McGrew draft's construction, with
# AdAuthenc.input_mcgrew and PKCS #7 padding), and in the Linux kernel's
# authenc(hmac(sha256), cbc(aes)) layout (the kernel's value, through
# AF_ALG), with a changed tag refused; ESSIV over AES-CBC with SHA-256 (the
# kernel's essiv(cbc(aes), sha256)); seqiv over AES-CCM (values from
# cryptography's AESCCM), with a changed IV byte and a short message
# refused; echainiv over authenc(hmac(sha256), cbc(aes)) (values from the
# kernel's authenc and cryptography's AES), with a changed IV byte refused.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/aes.bend as X
import ../crypto/crypto.bend as Cr
import ../crypto/inst_cm.bend as CM
import ../crypto/inst_aes.bend as A
import ../crypto/inst_ccm.bend as CC
import ../crypto/inst_sha2.bend as SH
import ../crypto/hmac.bend as Hm
import ./aesround.bend as R
import ./aegis128.bend as Ae
import ./authenc.bend as Au
import ./ivcipher.bend as Iv
import ./essiv.bend as Es
import ./seqiv.bend as Sq
import ./echainiv.bend as Ec

def cat(a: String, b: String) -> String:
  a ++ b

def err(e: Cr.CrError) -> String:
  match e:
    case Cr.CrBadKeyLength{n}:
      cat("bad key length ", Nat.show(n))
    case Cr.CrBadIvLength{n}:
      cat("bad iv length ", Nat.show(n))
    case Cr.CrBadNonceLength{n}:
      cat("bad nonce length ", Nat.show(n))
    case Cr.CrNotBlockMultiple{n}:
      cat("not whole blocks ", Nat.show(n))
    case Cr.CrTagMismatch{}:
      "tag mismatch"
    case Cr.CrTooShort{n}:
      cat("too short ", Nat.show(n))
    case _:
      "other error"

def show(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      err(e)

def ad.check.base(digit: Bool) -> U32:
  match digit:
    case True{}:
      48
    case False{}:
      87

def ad.check.nib(+c: U32) -> U32:
  U32.sub(c, ad.check.base(U32.is_lt(c, 58)))

def ad.check.hex(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Con{a, Con{b, t}}:
      ad.check.hex(t, Con{U32.add(U32.mul(ad.check.nib(a), 16), ad.check.nib(b)), acc})
    case _:
      B.rev(acc)

def hx(s: String) -> B.Octets:
  B.Octets.of_list(ad.check.hex(B.Octets.to_list(B.Octets.of_string(s)), Nil{}))

# sealed (or encrypted), then opened back: "<sealed> <opened>"
def both(e: Result<&2, &2, Cr.CrError, B.Octets>, d: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  cat(show(e), cat(" ", show(d)))

# AEGIS-128

def aegis(+k: B.Octets, +n: B.Octets, +a: B.Octets, +p: B.Octets) -> String:
  +r = Ae.AdAegis128.key(k)
  +c = Result.bind(&2, &2, Cr.CrError, Ae.AdAegisKey, B.Octets, r, kk => Ae.AdAegis128.seal(kk, n, a, p))
  both(c, Result.bind(&2, &2, Cr.CrError, Ae.AdAegisKey, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Ae.AdAegis128.open(kk, n, a, x))))

def aegis_seal(+k: B.Octets, +n: B.Octets, +a: B.Octets, +p: B.Octets) -> String:
  show(Result.bind(&2, &2, Cr.CrError, Ae.AdAegisKey, B.Octets, Ae.AdAegis128.key(k), kk => Ae.AdAegis128.seal(kk, n, a, p)))

def aegis_open(+k: B.Octets, +n: B.Octets, +a: B.Octets, +c: B.Octets) -> String:
  show(Result.bind(&2, &2, Cr.CrError, Ae.AdAegisKey, B.Octets, Ae.AdAegis128.key(k), kk => Ae.AdAegis128.open(kk, n, a, c)))

# Encrypt-then-MAC: AES-CBC and HMAC-SHA-256

def au.enc(k: X.CmAesKey, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Iv.AdCbc.encrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, iv, m)

def au.dec(k: X.CmAesKey, iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Iv.AdCbc.decrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, iv, c)

def au.encp(k: X.CmAesKey, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Iv.AdCbc.encrypt_padded(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, iv, m)

def au.decp(k: X.CmAesKey, iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Iv.AdCbc.decrypt_padded(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, iv, c)

def au.mac(k: Hm.CrHmacKey, m: B.Octets) -> B.Octets:
  Hm.CrHmac.mac(~SH.CrSha2.sha256, k, m)

def au.mkey(o: B.Octets) -> Result<&2, &2, Cr.CrError, Hm.CrHmacKey>:
  Hm.CrHmac.key_of(~64n, ~SH.CrSha2.sha256, o)

def au.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>>:
  Au.AdAuthenc.key(~X.CmAesKey, ~Hm.CrHmacKey, ~A.CrAes.key, ~au.mkey, ~16n, o)

# the kernel's authenc(hmac(sha256), cbc(aes)): A || C authenticated, the whole tag
def au.seal_k(k: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, iv: B.Octets, a: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Au.AdAuthenc.seal(~X.CmAesKey, ~Hm.CrHmacKey, ~au.enc, ~au.mac, ~Au.AdAuthenc.input_kernel, ~32n, k, iv, a, p)

def au.open_k(k: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, iv: B.Octets, a: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Au.AdAuthenc.open(~X.CmAesKey, ~Hm.CrHmacKey, ~au.dec, ~au.mac, ~Au.AdAuthenc.input_kernel, ~32n, k, iv, a, c)

# RFC 7518's AES_128_CBC_HMAC_SHA_256: A || IV || C || AL, a 16-byte tag
def au.seal_m(k: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, iv: B.Octets, a: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Au.AdAuthenc.seal(~X.CmAesKey, ~Hm.CrHmacKey, ~au.encp, ~au.mac, ~Au.AdAuthenc.input_mcgrew, ~16n, k, iv, a, p)

def au.open_m(k: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, iv: B.Octets, a: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Au.AdAuthenc.open(~X.CmAesKey, ~Hm.CrHmacKey, ~au.decp, ~au.mac, ~Au.AdAuthenc.input_mcgrew, ~16n, k, iv, a, c)

def authenc(~seal: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey> -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~open: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey> -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: B.Octets, +iv: B.Octets, +a: B.Octets, +p: B.Octets) -> String:
  +r = au.key(k)
  +c = Result.bind(&2, &2, Cr.CrError, Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, B.Octets, r, kk => seal(kk, iv, a, p))
  both(c, Result.bind(&2, &2, Cr.CrError, Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => open(kk, iv, a, x))))

def authenc_open(~open: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey> -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: B.Octets, +iv: B.Octets, +a: B.Octets, +c: B.Octets) -> String:
  show(Result.bind(&2, &2, Cr.CrError, Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, B.Octets, au.key(k), kk => open(kk, iv, a, c)))

# ESSIV over AES-CBC, the salt SHA-256 of the key and its cipher AES-256

def es.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, Es.AdEssivKey<X.CmAesKey, X.CmAesKey>>:
  Es.AdEssiv.key(~X.CmAesKey, ~X.CmAesKey, ~A.CrAes.key, ~A.CrAes.key, ~SH.CrSha2.sha256, o)

def es.enc(k: Es.AdEssivKey<X.CmAesKey, X.CmAesKey>, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Es.AdEssiv.encrypt(~X.CmAesKey, ~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~au.enc, k, iv, m)

def es.dec(k: Es.AdEssivKey<X.CmAesKey, X.CmAesKey>, iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Es.AdEssiv.decrypt(~X.CmAesKey, ~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~au.dec, k, iv, c)

def essiv(+k: B.Octets, +iv: B.Octets, +p: B.Octets) -> String:
  +r = es.key(k)
  +c = Result.bind(&2, &2, Cr.CrError, Es.AdEssivKey<X.CmAesKey, X.CmAesKey>, B.Octets, r, kk => es.enc(kk, iv, p))
  both(c, Result.bind(&2, &2, Cr.CrError, Es.AdEssivKey<X.CmAesKey, X.CmAesKey>, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => es.dec(kk, iv, x))))

# seqiv over AES-CCM (16-byte tags), 12-byte IVs

def ccm.seal(k: X.CmAesKey, n: B.Octets, a: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CC.CrCcm.seal(~X.CmAesKey, ~X.CmAes.encrypt, ~16n, k, n, a, p)

def ccm.open(k: X.CmAesKey, n: B.Octets, a: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CC.CrCcm.open(~X.CmAesKey, ~X.CmAes.encrypt, ~16n, k, n, a, c)

def sq.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, Sq.AdSeqivKey<X.CmAesKey>>:
  Sq.AdSeqiv.key(~X.CmAesKey, ~A.CrAes.key, ~12n, o)

def seqiv(+k: B.Octets, +seq: B.Octets, +a: B.Octets, +p: B.Octets) -> String:
  +r = sq.key(k)
  +c = Result.bind(&2, &2, Cr.CrError, Sq.AdSeqivKey<X.CmAesKey>, B.Octets, r, kk => Sq.AdSeqiv.seal(~X.CmAesKey, ~ccm.seal, kk, seq, a, p))
  both(c, Result.bind(&2, &2, Cr.CrError, Sq.AdSeqivKey<X.CmAesKey>, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Sq.AdSeqiv.open(~X.CmAesKey, ~ccm.open, ~12n, kk, seq, a, x))))

def seqiv_open(+k: B.Octets, +seq: B.Octets, +a: B.Octets, +c: B.Octets) -> String:
  show(Result.bind(&2, &2, Cr.CrError, Sq.AdSeqivKey<X.CmAesKey>, B.Octets, sq.key(k), kk => Sq.AdSeqiv.open(~X.CmAesKey, ~ccm.open, ~12n, kk, seq, a, c)))

# echainiv over the kernel's authenc(hmac(sha256), cbc(aes)), the IV cipher AES

def ec.key(ak: B.Octets, ck: B.Octets, salt: B.Octets) -> Result<&2, &2, Cr.CrError, Ec.AdEchainivKey<Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, X.CmAesKey>>:
  Ec.AdEchainiv.key(~Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, ~X.CmAesKey, ~au.key, ~A.CrAes.key, ak, ck, salt)

def echainiv(+ak: B.Octets, +ck: B.Octets, +salt: B.Octets, +seq: B.Octets, +a: B.Octets, +p: B.Octets) -> String:
  +r = ec.key(ak, ck, salt)
  +c = Result.bind(&2, &2, Cr.CrError, Ec.AdEchainivKey<Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, X.CmAesKey>, B.Octets, r, kk => Ec.AdEchainiv.seal(~Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, ~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~au.seal_k, kk, seq, a, p))
  both(c, Result.bind(&2, &2, Cr.CrError, Ec.AdEchainivKey<Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, X.CmAesKey>, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Ec.AdEchainiv.open(~Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, ~X.CmAesKey, ~au.open_k, ~16n, kk, seq, a, x))))

def echainiv_open(+ak: B.Octets, +ck: B.Octets, +salt: B.Octets, +seq: B.Octets, +a: B.Octets, +c: B.Octets) -> String:
  show(Result.bind(&2, &2, Cr.CrError, Ec.AdEchainivKey<Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, X.CmAesKey>, B.Octets, ec.key(ak, ck, salt), kk => Ec.AdEchainiv.open(~Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, ~X.CmAesKey, ~au.open_k, ~16n, kk, seq, a, c)))

def main() -> IO(Unit):
  +z16 = B.Octets.zeros(16n)
  +k = hx("000102030405060708090a0b0c0d0e0f")
  +n = hx("101112131415161718191a1b1c1d1e1f")
  +kr = hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
  +pr = B.Octets.of_string("A cipher system must not be required to be secret, and it must be able to fall into the hands of the enemy without inconvenience")
  +ivr = hx("1af38c2dc2b96ffdd86694092341bc04")
  +ar = B.Octets.of_string("The second principle of Auguste Kerckhoffs")
  +ak = hx("202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f000102030405060708090a0b0c0d0e0f")
  +m32 = hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
  +sk = hx("000102030405060708090a0b0c0d0e0fa0a1a2a3a4a5a6a7a8a9aaab")
  do IO<Unit>:
    IO.print(R.AdBlk.hex(R.AdAes.round(R.AdAes.sbox(), R.AdBlk.of_octets(hx("000102030405060708090a0b0c0d0e0f")), R.AdBlk.of_octets(hx("101112131415161718191a1b1c1d1e1f")))))
    IO.print(aegis(z16, z16, B.Octets.empty(), B.Octets.empty()))
    IO.print(aegis(z16, z16, B.Octets.empty(), z16))
    IO.print(aegis(z16, z16, z16, z16))
    IO.print(aegis(hx("00010000000000000000000000000000"), hx("00000200000000000000000000000000"), hx("00010203"), z16))
    IO.print(aegis(hx("10010000000000000000000000000000"), hx("10000200000000000000000000000000"), hx("0001020304050607"), m32))
    IO.print(aegis(k, n, hx("0001020304050607"), m32))
    IO.print(aegis(k, n, hx("00010203"), hx("000102030405060708090a0b0c")))
    IO.print(aegis(k, n, B.Octets.of_string("associated data, two blocks long"), B.Octets.of_string("a message of sixty-one bytes, which ends in a partial block...")))
    IO.print(aegis_open(k, n, hx("00010203"), hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c")))
    IO.print(aegis_seal(hx("000102030405060708090a0b0c0d0e"), n, B.Octets.empty(), B.Octets.empty()))
    IO.print(aegis_seal(k, hx("101112131415161718191a1b1c1d1e"), B.Octets.empty(), B.Octets.empty()))
    IO.print(aegis_open(k, n, B.Octets.empty(), hx("000102030405060708090a0b0c0d0e")))
    IO.print(authenc(~au.seal_m, ~au.open_m, kr, ivr, ar, pr))
    IO.print(authenc(~au.seal_k, ~au.open_k, kr, ivr, ar, m32))
    IO.print(authenc_open(~au.open_m, kr, ivr, ar, hx("c80edfa32ddf39d5ef00c0b468834279a2e46a1b8049f792f76bfe54b903a9c9a94ac9b47ad2655c5f10f9aef71427e2fc6f9b3f399a221489f16362c703233609d45ac69864e3321cf82935ac4096c86e133314c54019e8ca7980dfa4b9cf1b384c486f3a54c51078158ee5d79de59fbd34d848b3d69550a67646344427ade54b8851ffb598f7f80074b9473c82e2db652c3fa36b0a7c5b3219fab3a30bc1c5")))
    IO.print(authenc_open(~au.open_k, kr, ivr, ar, hx("00")))
    IO.print(essiv(kr, hx("00000000000000000000000000000000"), m32))
    IO.print(essiv(k, hx("07000000000000000000000000000000"), B.Octets.zeros(64n)))
    IO.print(seqiv(sk, hx("0000000000000001"), hx("0001020304050607"), B.Octets.of_string("seqiv over AES-CCM")))
    IO.print(seqiv(sk, hx("00000000000000ff00000002"), B.Octets.empty(), B.Octets.empty()))
    IO.print(seqiv_open(sk, hx("0000000000000001"), hx("0001020304050607"), hx("a1a1a2a3a4a5a6a7a8a9aaaa0d0593fbd64079e780eac7a612cbc2c361abf939db30bd025719f04d7e5611335a36")))
    IO.print(seqiv_open(sk, hx("0000000000000001"), hx("0001020304050607"), hx("a0a1a2a3a4a5")))
    IO.print(echainiv(ak, k, n, hx("0000000000000001"), hx("0001020304050607"), m32))
    IO.print(echainiv(ak, k, n, hx("0000000000000002"), B.Octets.empty(), B.Octets.zeros(48n)))
    IO.print(echainiv_open(ak, k, n, hx("0000000000000001"), hx("0001020304050607"), hx("5f7ed55606bdb961c1821f3964f0677519fae8ab350e663f77fc5e7c714699385a8f006affb14b20ca29241a76851a0baf0e8efc707dcaf9a1b324015191ccebd83f61f0f2787a85a647e10061197f69")))
#|7a7b4e5638782546a8c0477a3b813f43
#|242d8006b64d87c36cb35714af7121f9 
#|951b050fa72b1a2fc16d2e1f01b07d7ea7d2a99773249542f422217ee888d5f1 00000000000000000000000000000000
#|10b0dee65a97d751205c128a992473a146dcb9ee93c46cf13731d41b9646c131 00000000000000000000000000000000
#|2b78f5c1618da39afbb2920f5dae02b074759cd0e19314650d6c635b563d80fd 00000000000000000000000000000000
#|e08ec10685d63c7364eca78ff6e1a1ddfdfc15d5311a7f2988a0471a13973fd727e84b6c4cc46cb6ece8f1f3e4aa0e78 000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
#|1136818fa157709bc6259a110f3caab7bb9c8051a611411b9068f48f6cddd1fa661595fb87f02c6601fecab6c097e5ae 000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
#|1136818fa157709bc6259a110f225c4b57acfac2aa2e0563b72a74e9ea 000102030405060708090a0b0c
#|8a968f312470f5f463cf9014120b18b16b679dc1b35bdaa972417cdaa9186ec4460dcef5a5564e6fcb8bb2889d9a6f363f6acee7178a551445a82771587953e8d9cee414547bae20c567b6518924 61206d657373616765206f662073697874792d6f6e652062797465732c20776869636820656e647320696e2061207061727469616c20626c6f636b2e2e2e
#|tag mismatch
#|bad key length 15
#|bad nonce length 15
#|too short 15
#|c80edfa32ddf39d5ef00c0b468834279a2e46a1b8049f792f76bfe54b903a9c9a94ac9b47ad2655c5f10f9aef71427e2fc6f9b3f399a221489f16362c703233609d45ac69864e3321cf82935ac4096c86e133314c54019e8ca7980dfa4b9cf1b384c486f3a54c51078158ee5d79de59fbd34d848b3d69550a67646344427ade54b8851ffb598f7f80074b9473c82e2db652c3fa36b0a7c5b3219fab3a30bc1c4 41206369706865722073797374656d206d757374206e6f7420626520726571756972656420746f206265207365637265742c20616e64206974206d7573742062652061626c6520746f2066616c6c20696e746f207468652068616e6473206f662074686520656e656d7920776974686f757420696e636f6e76656e69656e6365
#|6d9eb67d25e4f39d903975f45a0f9412dc624c9fbe103814cdb3355f3f5189332cc14a5668bef980fc3c1aadb15f318bb0729ca4b5321f59cd79647bde3bd470 000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
#|tag mismatch
#|too short 1
#|06c5a8be287fd6971791889950eccfb26334d4e1d30e345c664f4c320efc9c84 000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
#|97cb4c2d1a8db6986d9cb45dcdc073bcedb3ef41e90aa48e0efd40c678d2d5a5647c8d92e67909492eceb7f10085fced737132e7911baec1f9a23140a81e39fa 00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
#|a0a1a2a3a4a5a6a7a8a9aaaa0d0593fbd64079e780eac7a612cbc2c361abf939db30bd025719f04d7e5611335a36 7365716976206f766572204145532d43434d
#|a0a1a2a3a4a5a658a8a9aaa9f3c6e2ad4b3328eab0276ab267c11b09 
#|tag mismatch
#|too short 6
#|5e7ed55606bdb961c1821f3964f0677519fae8ab350e663f77fc5e7c714699385a8f006affb14b20ca29241a76851a0baf0e8efc707dcaf9a1b324015191ccebd83f61f0f2787a85a647e10061197f69 000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
#|da99ccd4917577f22eaf1264c78a223511dfb2d5c7a61a59160fc21dca57ce24cead300258c919b8789eda4e1be3e8e23c5aa85b6a54a4a9e64d04baea3fa20801aba8006f75113ffff192528c201ebcd9978fbf9b6c07d76e4b99e52bccbddf 000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
#|tag mismatch
