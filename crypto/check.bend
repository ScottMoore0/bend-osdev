# Every instance through its interface, on the specifications' own vectors:
# each block cipher's vector both ways (encryption, then decryption back),
# the modes over the interface (SP 800-38A's ECB, CBC and CTR vectors, and
# 3DES CBC from SP 800-67), RC4 (RFC 6229) whole and in pieces, CMAC
# (RFC 4493), CCM (RFC 3610) with tampered input refused, the CRC check
# values, HMAC and HKDF over CRC-32 (values from Python's hmac, which
# ref/gen.py also checks), long messages both ways, and the refusals.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/aes.bend as X
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
import ./aead.bend as Ae
import ./inst_cm.bend as CM
import ./inst_lc.bend as LC
import ./inst_aes.bend as A
import ./inst_rc4.bend as RC
import ./inst_ccm.bend as CC
import ./inst_cmac.bend as CMI
import ./inst_crc.bend as CR

def cat(a: String, b: String) -> String:
  a ++ b

def err(e: Cr.CrError) -> String:
  match e:
    case Cr.CrBadKeyLength{n}:
      cat("bad key length ", Nat.show(n))
    case Cr.CrBadIvLength{n}:
      cat("bad iv length ", Nat.show(n))
    case Cr.CrNotBlockMultiple{n}:
      cat("not whole blocks ", Nat.show(n))
    case Cr.CrBadBlockSize{n}:
      cat("bad block size ", Nat.show(n))
    case Cr.CrTagMismatch{}:
      "tag mismatch"
    case Cr.CrBadOutputLength{n}:
      cat("bad output length ", Nat.show(n))
    case _:
      "other error"

def show(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      err(e)

def cr.check.base(digit: Bool) -> U32:
  match digit:
    case True{}:
      48
    case False{}:
      87

def cr.check.nib(+c: U32) -> U32:
  U32.sub(c, cr.check.base(U32.is_lt(c, 58)))

def cr.check.hex(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Con{a, Con{b, t}}:
      cr.check.hex(t, Con{U32.add(U32.mul(cr.check.nib(a), 16), cr.check.nib(b)), acc})
    case _:
      B.rev(acc)

def yes_no(b: Bool) -> String:
  match b:
    case True{}:
      "accepted"
    case False{}:
      "refused"

def cr.check.two.go(~S: Data, ~update: S -> B.Octets -> St.CrXorOut<S>, o: St.CrXorOut<S>, b: B.Octets) -> B.Octets:
  match o:
    case St.CrXorOut{s, d}:
      B.Octets.append(d, St.CrXor.out_data(~S, update(s, b)))

def cr.check.two(~S: Data, ~update: S -> B.Octets -> St.CrXorOut<S>, s: S, a: B.Octets, b: B.Octets) -> B.Octets:
  cr.check.two.go(~S, ~update, update(s, a), b)

def cr.check.rc4two(+o: R.LcRc4Out) -> B.Octets:
  B.Octets.append(R.LcRc4.out_data(o), R.LcRc4.out_data(R.LcRc4.update(R.LcRc4.out_state(o), B.Octets.zeros(11n))))

def cr.check.verify(r: Result<&2, &2, Cr.CrError, Bool>) -> String:
  match r:
    case Done{b}:
      cat(" ", yes_no(b))
    case Fail{e}:
      " failed"

def hx(s: String) -> B.Octets:
  B.Octets.of_list(cr.check.hex(B.Octets.to_list(B.Octets.of_string(s)), Nil{}))

# encryption, then decryption back: "<ciphertext> <plaintext again>"
def both(e: Result<&2, &2, Cr.CrError, B.Octets>, d: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  cat(show(e), cat(" ", show(d)))

def ok_if(same: Bool, tail: B.Octets) -> String:
  match same:
    case True{}:
      cat(B.Octets.hex(tail), " ok")
    case False{}:
      "MISMATCH"

# the last 16 bytes of c, and whether d gave the message back
def round(+m: B.Octets, c: Result<&2, &2, Cr.CrError, B.Octets>, d: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match c d:
    case Done{+x} Done{y}:
      ok_if(B.Octets.is_eq(y, m), B.Octets.drop(Nat.sub(B.Octets.len(x), 16n), x))
    case _ _:
      "failed"

# Block ciphers, one block through the interface (key schedule, then bytes)

def aes(+k: B.Octets, +p: B.Octets) -> String:
  both(Bk.CrBlockCipher.encrypt_with(~X.CmAesKey, ~M.CmBlock, ~A.CrAes.key, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, p), Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Bk.CrBlockCipher.encrypt_with(~X.CmAesKey, ~M.CmBlock, ~A.CrAes.key, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, p), c => Bk.CrBlockCipher.encrypt_with(~X.CmAesKey, ~M.CmBlock, ~A.CrAes.key, ~X.CmAes.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, c)))

def lc128(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: B.Octets, +p: B.Octets) -> String:
  +c = Bk.CrBlockCipher.encrypt_with(~K, ~M.CmBlock, ~key, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, p)
  both(c, Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Bk.CrBlockCipher.encrypt_with(~K, ~M.CmBlock, ~key, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, x)))

def lc64(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> L.LcBlock64 -> L.LcBlock64, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: B.Octets, +p: B.Octets) -> String:
  +c = Bk.CrBlockCipher.encrypt_with(~K, ~L.LcBlock64, ~key, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, p)
  both(c, Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Bk.CrBlockCipher.encrypt_with(~K, ~L.LcBlock64, ~key, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, x)))

# Modes over the interface

def aes_ecb(+k: B.Octets, +m: B.Octets) -> String:
  +r = A.CrAes.key(k)
  +c = Result.bind(&2, &2, Cr.CrError, X.CmAesKey, B.Octets, r, kk => Md.CrEcb.encrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, m))
  both(c, Result.bind(&2, &2, Cr.CrError, X.CmAesKey, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Md.CrEcb.decrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, x))))

def aes_cbc_c(+k: B.Octets, +iv: B.Octets, +m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, X.CmAesKey, B.Octets, A.CrAes.key(k), kk => Md.CrCbc.encrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, iv, m))

def aes_cbc_d(+k: B.Octets, +iv: B.Octets, c: Result<&2, &2, Cr.CrError, B.Octets>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, X.CmAesKey, B.Octets, A.CrAes.key(k), kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Md.CrCbc.decrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, iv, x)))

def aes_cbc(+k: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  +c = aes_cbc_c(k, iv, m)
  both(c, aes_cbc_d(k, iv, c))

def tdes_cbc(+k: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  +r = LC.CrLc.key(~T.LcTdesKey, ~T.LcTdes.key, k)
  +c = Result.bind(&2, &2, Cr.CrError, T.LcTdesKey, B.Octets, r, kk => Md.CrCbc.encrypt(~T.LcTdesKey, ~L.LcBlock64, ~8n, ~T.LcTdes.encrypt, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, kk, iv, m))
  both(c, Result.bind(&2, &2, Cr.CrError, T.LcTdesKey, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Md.CrCbc.decrypt(~T.LcTdesKey, ~L.LcBlock64, ~8n, ~T.LcTdes.decrypt, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, kk, iv, x))))

# CTR-AES as a stream cipher through the stream interface
def aes_ctr(+k: B.Octets, +iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  St.CrStream.crypt(~Md.CrCtrState<X.CmAesKey>, ~St.CrXorOut<Md.CrCtrState<X.CmAesKey>>, ~Md.CrCtr.start(~X.CmAesKey, ~16n, ~A.CrAes.key_enc), ~Md.CrCtr.update(~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets), ~St.CrXor.out_data(~Md.CrCtrState<X.CmAesKey>), k, iv, m)

# CTR-DES, in pieces: two updates from one start
def des_ctr_pieces(+k: B.Octets, +iv: B.Octets, +a: B.Octets, +b: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, Md.CrCtrState<D.LcDesKey>, B.Octets, +s => cr.check.two(~Md.CrCtrState<D.LcDesKey>, ~Md.CrCtr.update(~D.LcDesKey, ~L.LcBlock64, ~D.LcDes.encrypt, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets), s, a, b), Md.CrCtr.start(~D.LcDesKey, ~8n, ~LC.CrLc.key(~D.LcDesKey, ~D.LcDes.key), k, iv))

# RC4 through the stream interface: the keystream, and the same in pieces
def rc4(+k: B.Octets, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  St.CrStream.crypt(~R.LcRc4State, ~R.LcRc4Out, ~RC.CrRc4.start, ~R.LcRc4.update, ~R.LcRc4.out_data, k, B.Octets.empty(), B.Octets.zeros(n))

def rc4_pieces(+k: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, R.LcRc4State, B.Octets, +s => cr.check.rc4two(R.LcRc4.update(s, B.Octets.zeros(5n))), RC.CrRc4.start(k, B.Octets.empty()))

def rc4_drop(+k: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  St.CrStream.crypt(~R.LcRc4State, ~R.LcRc4Out, ~RC.CrRc4.start_drop(~1536n), ~R.LcRc4.update, ~R.LcRc4.out_data, k, B.Octets.empty(), B.Octets.zeros(16n))

# CMAC-AES through the MAC interface: the tag, and whether verify accepts it
# and refuses it with its last byte changed
def flip_last(+t: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.take(Nat.sub(B.Octets.len(t), 1n), t), B.Octets.of_list([U32.xor(Maybe.default(&2, U32, B.Octets.at(t, Nat.sub(B.Octets.len(t), 1n)), 0), 1)]))

def cmac(+k: B.Octets, +m: B.Octets) -> String:
  +t = Mc.CrMac.compute_with(~X.CmAesKey, ~A.CrAes.key_enc, ~CMI.CrCmac.mac(~X.CmAesKey, ~X.CmAes.encrypt), k, m)
  cat(show(t), cr.check.verify(Result.map(&2, &2, Cr.CrError, B.Octets, Bool, +tag => Result.default(&2, &2, Cr.CrError, Bool, Result.map(&2, &2, Cr.CrError, X.CmAesKey, Bool, +kk => Bool.and(CMI.CrCmac.verify(~X.CmAesKey, ~X.CmAes.encrypt, kk, m, tag), Bool.not(CMI.CrCmac.verify(~X.CmAesKey, ~X.CmAes.encrypt, kk, m, flip_last(tag)))), A.CrAes.key_enc(k)), False{}), t)))

# CCM-AES through the AEAD interface, an m-byte tag: the sealed message, the
# plaintext opened again, and the result of opening it with the tag's last
# byte changed
def ccm(~tlen: Nat, +k: B.Octets, +n: B.Octets, +a: B.Octets, +p: B.Octets) -> String:
  +c = Ae.CrAead.seal_with(~X.CmAesKey, ~A.CrAes.key_enc, ~CC.CrCcm.seal(~X.CmAesKey, ~X.CmAes.encrypt, ~tlen), k, n, a, p)
  +o = Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Ae.CrAead.open_with(~X.CmAesKey, ~A.CrAes.key_enc, ~CC.CrCcm.open(~X.CmAesKey, ~X.CmAes.encrypt, ~tlen), k, n, a, x))
  +bad = Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Ae.CrAead.open_with(~X.CmAesKey, ~A.CrAes.key_enc, ~CC.CrCcm.open(~X.CmAesKey, ~X.CmAes.encrypt, ~tlen), k, n, a, flip_last(x)))
  cat(show(c), cat(" ", cat(show(o), cat(" ", show(bad)))))

# CRC-32 through the hash interface: one-shot, and in three pieces
def crc32_pieces(+m1: B.Octets, +m2: B.Octets, +m3: B.Octets) -> String:
  cat(B.Octets.hex(CR.CrCrc32.digest(~C.crc32c.spec(), B.Octets.append(m1, B.Octets.append(m2, m3)))), cat(" ", B.Octets.hex(H.CrHash.of_pieces(~U32, ~CR.CrCrc32.init(~C.crc32c.spec()), ~CR.CrCrc32.update(~C.crc32c.spec()), ~CR.CrCrc32.final(~C.crc32c.spec()), [m1, m2, m3]))))

# HMAC over CRC-32: one-shot, in two pieces, and verify
def hmac_crc32(+k: B.Octets, +a: B.Octets, +b: B.Octets) -> String:
  +kk = Hm.CrHmac.key(~64n, ~CR.CrCrc32.digest(~C.crc32.spec()), k)
  +t = Hm.CrHmac.mac(~CR.CrCrc32.digest(~C.crc32.spec()), kk, B.Octets.append(a, b))
  +s = Hm.CrHmac.start(~U32, ~CR.CrCrc32.init(~C.crc32.spec()), ~CR.CrCrc32.update(~C.crc32.spec()), kk)
  +t2 = Hm.CrHmac.finish(~U32, ~CR.CrCrc32.init(~C.crc32.spec()), ~CR.CrCrc32.update(~C.crc32.spec()), ~CR.CrCrc32.final(~C.crc32.spec()), Hm.CrHmac.update(~U32, ~CR.CrCrc32.update(~C.crc32.spec()), Hm.CrHmac.update(~U32, ~CR.CrCrc32.update(~C.crc32.spec()), s, a), b))
  cat(B.Octets.hex(t), cat(" ", cat(B.Octets.hex(t2), cat(" ", yes_no(Hm.CrHmac.verify(~CR.CrCrc32.digest(~C.crc32.spec()), kk, B.Octets.append(a, b), t))))))

# HMAC over CRC-64/XZ, with a key longer than the block size (hashed first)
def hmac_crc64(+k: B.Octets, +m: B.Octets) -> String:
  B.Octets.hex(Hm.CrHmac.mac(~CR.CrCrc64.digest(~C.crc64_xz.spec()), Hm.CrHmac.key(~64n, ~CR.CrCrc64.digest(~C.crc64_xz.spec()), k), m))

def hkdf_crc32(+ikm: B.Octets, +salt: B.Octets, +info: B.Octets, n: Nat) -> String:
  show(Hk.CrHkdf.derive(~64n, ~4n, ~CR.CrCrc32.digest(~C.crc32.spec()), ikm, salt, info, n))

def cr.check.tail8(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Done{+o}:
      cat(Nat.show(B.Octets.len(o)), cat(" ", B.Octets.hex(B.Octets.drop(Nat.sub(B.Octets.len(o), 8n), o))))
    case Fail{e}:
      err(e)

# the longest HKDF output (255 digests): its length and last 8 bytes
def hkdf_crc32_max(+ikm: B.Octets) -> String:
  cr.check.tail8(Hk.CrHkdf.derive(~64n, ~4n, ~CR.CrCrc32.digest(~C.crc32.spec()), ikm, B.Octets.empty(), B.Octets.empty(), 1020n))

# a long message: n pseudo-random bytes
def big.go(n: Nat, +x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      big.go(p, U32.add(U32.mul(x, 1103515245), 12345), Con{B.byte(U32.shrn(x, 16n)), acc})

def big(n: Nat) -> B.Octets:
  B.Octets.of_list(big.go(n, 7, Nil{}))

def sm4_cbc_big(+k: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  +r = LC.CrLc.key(~S.LcSm4Key, ~S.LcSm4.key, k)
  +c = Result.bind(&2, &2, Cr.CrError, S.LcSm4Key, B.Octets, r, kk => Md.CrCbc.encrypt(~S.LcSm4Key, ~M.CmBlock, ~16n, ~S.LcSm4.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, iv, m))
  round(m, c, Result.bind(&2, &2, Cr.CrError, S.LcSm4Key, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Md.CrCbc.decrypt(~S.LcSm4Key, ~M.CmBlock, ~16n, ~S.LcSm4.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, iv, x))))

def aes_ctr_big(+k: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  +c = aes_ctr(k, iv, m)
  round(m, c, Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => aes_ctr(k, iv, x)))

def main() -> IO(Unit):
  +k16 = hx("0123456789abcdeffedcba9876543210")
  +z16 = B.Octets.zeros(16n)
  +nk = hx("2b7e151628aed2a6abf7158809cf4f3c")
  +f4 = hx("6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710")
  +ck = hx("c0c1c2c3c4c5c6c7c8c9cacbcccdcecf")
  do IO<Unit>:
    IO.print(aes(hx("000102030405060708090a0b0c0d0e0f"), hx("00112233445566778899aabbccddeeff")))
    IO.print(aes(hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"), hx("00112233445566778899aabbccddeeff")))
    IO.print(lc64(~D.LcDesKey, ~LC.CrLc.key(~D.LcDesKey, ~D.LcDes.key), ~D.LcDes.encrypt, ~D.LcDes.decrypt, hx("0101010101010101"), hx("8000000000000000")))
    IO.print(lc64(~T.LcTdesKey, ~LC.CrLc.key(~T.LcTdesKey, ~T.LcTdes.key), ~T.LcTdes.encrypt, ~T.LcTdes.decrypt, hx("0123456789abcdef23456789abcdef01456789abcdef0123"), B.Octets.of_string("The qufc")))
    IO.print(lc128(~S.LcSm4Key, ~LC.CrLc.key(~S.LcSm4Key, ~S.LcSm4.key), ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k16, k16))
    IO.print(lc128(~Ca.LcCamelliaKey, ~LC.CrLc.key(~Ca.LcCamelliaKey, ~Ca.LcCamellia.key), ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k16, k16))
    IO.print(lc128(~Sp.LcSerpentKey, ~LC.CrLc.key(~Sp.LcSerpentKey, ~Sp.LcSerpent.key), ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, z16, z16))
    IO.print(lc128(~Tf.LcTwofishKey, ~LC.CrLc.key(~Tf.LcTwofishKey, ~Tf.LcTwofish.key), ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, z16, z16))
    IO.print(aes_ecb(nk, f4))
    IO.print(aes_cbc(nk, hx("000102030405060708090a0b0c0d0e0f"), f4))
    IO.print(show(aes_ctr(nk, hx("f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff"), f4)))
    IO.print(tdes_cbc(hx("0123456789abcdef23456789abcdef01456789abcdef0123"), hx("f69f2445df4f9b17"), B.Octets.of_string("The qufck brown fox jump")))
    IO.print(show(des_ctr_pieces(hx("0123456789abcdef"), hx("fffffffffffffffe"), B.Octets.zeros(5n), B.Octets.zeros(14n))))
    IO.print(show(rc4(hx("0102030405"), 16n)))
    IO.print(show(rc4_pieces(hx("0102030405"))))
    IO.print(show(rc4_drop(hx("0102030405"))))
    IO.print(cmac(nk, B.Octets.empty()))
    IO.print(cmac(nk, B.Octets.take(16n, f4)))
    IO.print(cmac(nk, B.Octets.take(40n, f4)))
    IO.print(cmac(nk, f4))
    IO.print(ccm(~8n, ck, hx("00000003020100a0a1a2a3a4a5"), hx("0001020304050607"), hx("08090a0b0c0d0e0f101112131415161718191a1b1c1d1e")))
    IO.print(ccm(~8n, ck, hx("00000004030201a0a1a2a3a4a5"), hx("0001020304050607"), hx("08090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")))
    IO.print(ccm(~8n, ck, hx("00000005040302a0a1a2a3a4a5"), hx("0001020304050607"), hx("08090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20")))
    IO.print(B.Octets.hex(CR.CrCrc32.digest(~C.crc32.spec(), B.Octets.of_string("123456789"))))
    IO.print(B.Octets.hex(CR.CrCrc64.digest(~C.crc64_xz.spec(), B.Octets.of_string("123456789"))))
    IO.print(crc32_pieces(B.Octets.of_string("1234"), B.Octets.empty(), B.Octets.of_string("56789")))
    IO.print(hmac_crc32(B.Octets.of_string("key"), B.Octets.of_string("The quick"), B.Octets.of_string(" brown fox")))
    IO.print(hmac_crc64(big(100n), B.Octets.of_string("a message")))
    IO.print(hkdf_crc32(B.Octets.of_string("secret"), B.Octets.of_string("salt"), B.Octets.of_string("info"), 10n))
    IO.print(hkdf_crc32_max(B.Octets.of_string("secret")))
    IO.print(sm4_cbc_big(k16, z16, big(32768n)))
    IO.print(aes_ctr_big(nk, hx("f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff"), big(32771n)))
    IO.print(show(Bk.CrBlockCipher.encrypt_with(~X.CmAesKey, ~M.CmBlock, ~A.CrAes.key, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, B.Octets.zeros(24n), z16)))
    IO.print(show(Bk.CrBlockCipher.encrypt_with(~X.CmAesKey, ~M.CmBlock, ~A.CrAes.key, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, z16, B.Octets.zeros(15n))))
    IO.print(show(aes_ctr(nk, B.Octets.zeros(12n), f4)))
    IO.print(aes_cbc(nk, z16, B.Octets.zeros(17n)))
    IO.print(show(rc4(B.Octets.empty(), 4n)))
    IO.print(hkdf_crc32(B.Octets.of_string("secret"), B.Octets.empty(), B.Octets.empty(), 1021n))

#|69c4e0d86a7b0430d8cdb78070b4c55a 00112233445566778899aabbccddeeff
#|8ea2b7ca516745bfeafc49904b496089 00112233445566778899aabbccddeeff
#|95f8a5e5dd31d900 8000000000000000
#|a826fd8ce53b855f 5468652071756663
#|681edf34d206965e86b3e94f536e4246 0123456789abcdeffedcba9876543210
#|67673138549669730857065648eabe43 0123456789abcdeffedcba9876543210
#|3620b17ae6a993d09618b8768266bae9 00000000000000000000000000000000
#|9f589f5cf6122c32b6bfec2f2ae8c35a 00000000000000000000000000000000
#|3ad77bb40d7a3660a89ecaf32466ef97f5d3d58503b9699de785895a96fdbaaf43b1cd7f598ece23881b00e3ed0306887b0c785e27e8ad3f8223207104725dd4 6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710
#|7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b273bed6b8e3c1743b7116e69e222295163ff1caa1681fac09120eca307586e1a7 6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710
#|874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff5ae4df3edbd5d35e5b4f09020db03eab1e031dda2fbe03d1792170a0f3009cee
#|a5c282bad0de3774becd2e04386b589fb5057d8552fc4336 54686520717566636b2062726f776e20666f78206a756d70
#|bc4f694b45d6355359732356f36fde06d5d44f
#|b2396305f03dc027ccc3524a0a1118a8
#|b2396305f03dc027ccc3524a0a1118a8
#|d8729db41882259bee4f825325f5a130
#|bb1d6929e95937287fa37d129b756746 accepted
#|070a16b46b4d4144f79bdd9dd04a287c accepted
#|dfa66747de9ae63030ca32611497c827 accepted
#|51f0bebf7e3b9d92fc49741779363cfe accepted
#|588c979a61c663d2f066d0c2c0f989806d5f6b61dac38417e8d12cfdf926e0 08090a0b0c0d0e0f101112131415161718191a1b1c1d1e tag mismatch
#|72c91a36e135f8cf291ca894085c87e3cc15c439c9e43a3ba091d56e10400916 08090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f tag mismatch
#|51b1e5f44a197d1da46b0f8e2d282ae871e838bb64da8596574adaa76fbd9fb0c5 08090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 tag mismatch
#|cbf43926
#|995dc9bbdf1939fa
#|e3069283 e3069283
#|4534cd57 4534cd57 accepted
#|194e4372ad2f3f4a
#|b397376fd369a94be219
#|1020 c824ab370636d8ad
#|2761bd68ee073229c87a83da87af1b9b ok
#|ee960213d986d3a3c62b718973b132e0 ok
#|bad key length 24
#|bad block size 15
#|bad iv length 12
#|not whole blocks 17 not whole blocks 17
#|bad key length 0
#|bad output length 1021
