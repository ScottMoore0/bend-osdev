# Every instance through its interface, on the specifications' own vectors:
# each block cipher's vector both ways (encryption, then decryption back),
# the modes over the interface (SP 800-38A's ECB, CBC and CTR vectors, and
# 3DES CBC from SP 800-67), RC4 (RFC 6229) whole and in pieces, CMAC
# (RFC 4493), CCM (RFC 3610) with tampered input refused, the CRC check
# values, HMAC and HKDF over CRC-32 (values from Python's hmac, which
# ref/gen.py also checks), long messages both ways, the refusals; then
# SHA-256 and SHA-512 (FIPS 180-4's examples, whole and in pieces),
# HMAC-SHA-256 and HMAC-SHA-512 (RFC 4231 test cases 1 to 7) and
# HKDF-SHA-256 (RFC 5869 A.1 to A.3); then the newer instances (ARIA,
# CAST-256, Blowfish, CAST-128, TEA, XTEA, FCrypt) on their specifications'
# vectors both ways (TEA and XTEA on legacy-ciphers' model values: their
# papers give none), PCBC (the FCrypt specification's PCBC vector), LRW-AES
# (the IEEE P1619 draft's Annex B), CBC-CS3 (RFC 3962's AES vectors, both
# ways, and a refused short message), AES-XCBC-MAC (RFC 3566's seven) and
# VMAC-AES (draft-krovetz-vmac-01's, 64- and 128-bit tags).
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
import ./inst_sha2.bend as SH
import ./pcbc.bend as Pc
import ./lrw.bend as Lw
import ./cts.bend as Ct
import ./xcbc.bend as Xc
import ./vmac.bend as Vm
import ../legacy-ciphers/aria.bend as Ar
import ../legacy-ciphers/cast6.bend as C6
import ../legacy-ciphers/blowfish.bend as Bf
import ../legacy-ciphers/cast5.bend as C5
import ../legacy-ciphers/tea.bend as Te
import ../legacy-ciphers/xtea.bend as Xt
import ../legacy-ciphers/fcrypt.bend as Fc

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

# SHA-256 and SHA-512 through the hash interface: one-shot, and in three
# pieces through the streaming interface
def sha(~digest: B.Octets -> B.Octets, +m: B.Octets) -> String:
  B.Octets.hex(digest(m))

def sha_pieces3(~init: SH.CrSha2State, +a: B.Octets, +b: B.Octets, +c: B.Octets) -> String:
  B.Octets.hex(H.CrHash.of_pieces(~SH.CrSha2State, ~init, ~SH.CrSha2.update, ~SH.CrSha2.final, [a, b, c]))

# HMAC over SHA-256 or SHA-512 (block size bsize)
def hmac_sha(~bsize: Nat, ~digest: B.Octets -> B.Octets, +k: B.Octets, +m: B.Octets) -> B.Octets:
  Hm.CrHmac.mac(~digest, Hm.CrHmac.key(~bsize, ~digest, k), m)

# HMAC-SHA-256 in two pieces, and verify of the tag
def hmac_sha256_pieces(+k: B.Octets, +a: B.Octets, +b: B.Octets) -> String:
  +kk = Hm.CrHmac.key(~64n, ~SH.CrSha2.sha256, k)
  +t = Hm.CrHmac.finish(~SH.CrSha2State, ~SH.CrSha2.init256(), ~SH.CrSha2.update, ~SH.CrSha2.final, Hm.CrHmac.update(~SH.CrSha2State, ~SH.CrSha2.update, Hm.CrHmac.update(~SH.CrSha2State, ~SH.CrSha2.update, Hm.CrHmac.start(~SH.CrSha2State, ~SH.CrSha2.init256(), ~SH.CrSha2.update, kk), a), b))
  cat(B.Octets.hex(t), cat(" ", yes_no(Hm.CrHmac.verify(~SH.CrSha2.sha256, kk, B.Octets.append(a, b), t))))

def hkdf_sha256(+ikm: B.Octets, +salt: B.Octets, +info: B.Octets, n: Nat) -> String:
  show(Hk.CrHkdf.derive(~64n, ~32n, ~SH.CrSha2.sha256, ikm, salt, info, n))

# The newer modes and MACs

def pcbc_fc(+k: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  +r = LC.CrLc.key(~Fc.LcFcryptKey, ~Fc.LcFcrypt.key, k)
  +c = Result.bind(&2, &2, Cr.CrError, Fc.LcFcryptKey, B.Octets, r, kk => Pc.CrPcbc.encrypt(~Fc.LcFcryptKey, ~L.LcBlock64, ~8n, ~Fc.LcFcrypt.encrypt, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, kk, iv, m))
  both(c, Result.bind(&2, &2, Cr.CrError, Fc.LcFcryptKey, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Pc.CrPcbc.decrypt(~Fc.LcFcryptKey, ~L.LcBlock64, ~8n, ~Fc.LcFcrypt.decrypt, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, kk, iv, x))))

def lrw_aes(+k: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  +r = Lw.CrLrw.key(~X.CmAesKey, ~A.CrAes.key, k)
  +c = Result.bind(&2, &2, Cr.CrError, Lw.CrLrwKey<X.CmAesKey>, B.Octets, r, kk => Lw.CrLrw.encrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, iv, m))
  both(c, Result.bind(&2, &2, Cr.CrError, Lw.CrLrwKey<X.CmAesKey>, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Lw.CrLrw.decrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.decrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, iv, x))))

def cts_aes(+k: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  +r = A.CrAes.key(k)
  +c = Result.bind(&2, &2, Cr.CrError, X.CmAesKey, B.Octets, r, kk => Ct.CrCts.encrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, iv, m))
  both(c, Result.bind(&2, &2, Cr.CrError, X.CmAesKey, B.Octets, r, kk => Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, c, x => Ct.CrCts.decrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, iv, x))))

def xcbc_aes(+k: B.Octets, +m: B.Octets) -> String:
  show(Result.map(&2, &2, Cr.CrError, Xc.CrXcbcKey<X.CmAesKey>, B.Octets, kk => Xc.CrXcbc.mac(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, m), Xc.CrXcbc.key(~X.CmAesKey, ~M.CmBlock, ~16n, ~A.CrAes.key, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k)))

def vmac_aes(~words: Nat, +k: B.Octets, +n: B.Octets, +m: B.Octets) -> String:
  show(Result.bind(&2, &2, Cr.CrError, Vm.CrVmacKey<X.CmAesKey>, B.Octets, Vm.CrVmac.key(~X.CmAesKey, ~M.CmBlock, ~16n, ~A.CrAes.key, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~words, k), kk => Vm.CrVmac.tag(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, kk, n, m)))

def rep(n: Nat, +s: String, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep(p, s, cat(acc, s))

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

    IO.print(sha(~SH.CrSha2.sha256, B.Octets.of_string("abc")))
    IO.print(sha(~SH.CrSha2.sha256, B.Octets.of_string("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")))
    IO.print(sha(~SH.CrSha2.sha512, B.Octets.of_string("abc")))
    IO.print(sha_pieces3(~SH.CrSha2.init256(), B.Octets.of_string("abcdbcdecdefdefgefgh"), B.Octets.empty(), B.Octets.of_string("fghighijhijkijkljklmklmnlmnomnopnopq")))
    IO.print(sha_pieces3(~SH.CrSha2.init512(), B.Octets.of_string("a"), B.Octets.of_string("b"), B.Octets.of_string("c")))
    IO.print(B.Octets.hex(hmac_sha(~64n, ~SH.CrSha2.sha256, hx("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"), hx("4869205468657265"))))
    IO.print(B.Octets.hex(hmac_sha(~128n, ~SH.CrSha2.sha512, hx("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"), hx("4869205468657265"))))
    IO.print(B.Octets.hex(hmac_sha(~64n, ~SH.CrSha2.sha256, hx("4a656665"), hx("7768617420646f2079612077616e7420666f72206e6f7468696e673f"))))
    IO.print(B.Octets.hex(hmac_sha(~128n, ~SH.CrSha2.sha512, hx("4a656665"), hx("7768617420646f2079612077616e7420666f72206e6f7468696e673f"))))
    IO.print(B.Octets.hex(hmac_sha(~64n, ~SH.CrSha2.sha256, hx("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), hx("dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"))))
    IO.print(B.Octets.hex(hmac_sha(~128n, ~SH.CrSha2.sha512, hx("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), hx("dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"))))
    IO.print(B.Octets.hex(hmac_sha(~64n, ~SH.CrSha2.sha256, hx("0102030405060708090a0b0c0d0e0f10111213141516171819"), hx("cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"))))
    IO.print(B.Octets.hex(hmac_sha(~128n, ~SH.CrSha2.sha512, hx("0102030405060708090a0b0c0d0e0f10111213141516171819"), hx("cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"))))
    IO.print(B.Octets.hex(B.Octets.take(16n, hmac_sha(~64n, ~SH.CrSha2.sha256, hx("0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c"), hx("546573742057697468205472756e636174696f6e")))))
    IO.print(B.Octets.hex(B.Octets.take(16n, hmac_sha(~128n, ~SH.CrSha2.sha512, hx("0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c"), hx("546573742057697468205472756e636174696f6e")))))
    IO.print(B.Octets.hex(hmac_sha(~64n, ~SH.CrSha2.sha256, hx("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), hx("54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374"))))
    IO.print(B.Octets.hex(hmac_sha(~128n, ~SH.CrSha2.sha512, hx("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), hx("54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374"))))
    IO.print(B.Octets.hex(hmac_sha(~64n, ~SH.CrSha2.sha256, hx("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), hx("5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e"))))
    IO.print(B.Octets.hex(hmac_sha(~128n, ~SH.CrSha2.sha512, hx("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), hx("5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e"))))
    IO.print(hmac_sha256_pieces(hx("4a656665"), B.Octets.of_string("what do ya"), B.Octets.of_string(" want for nothing?")))
    IO.print(hkdf_sha256(hx("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"), hx("000102030405060708090a0b0c"), hx("f0f1f2f3f4f5f6f7f8f9"), 42n))
    IO.print(hkdf_sha256(hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f"), hx("606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeaf"), hx("b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff"), 82n))
    IO.print(hkdf_sha256(hx("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"), hx(""), hx(""), 42n))
    IO.print(lc128(~Ar.LcAriaKey, ~LC.CrLc.key(~Ar.LcAriaKey, ~Ar.LcAria.key), ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, hx("000102030405060708090a0b0c0d0e0f"), hx("00112233445566778899aabbccddeeff")))
    IO.print(lc128(~C6.LcCast6Key, ~LC.CrLc.key(~C6.LcCast6Key, ~C6.LcCast6.key), ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, hx("2342bb9efa38542c0af75647f29f615d"), z16))
    IO.print(lc64(~Bf.LcBlowfishKey, ~LC.CrLc.key(~Bf.LcBlowfishKey, ~Bf.LcBlowfish.key), ~Bf.LcBlowfish.encrypt, ~Bf.LcBlowfish.decrypt, hx("fedcba9876543210"), hx("0123456789abcdef")))
    IO.print(lc64(~C5.LcCast5Key, ~LC.CrLc.key(~C5.LcCast5Key, ~C5.LcCast5.key), ~C5.LcCast5.encrypt, ~C5.LcCast5.decrypt, hx("0123456712345678234567893456789a"), hx("0123456789abcdef")))
    IO.print(lc64(~Te.LcTeaKey, ~LC.CrLc.key(~Te.LcTeaKey, ~Te.LcTea.key), ~Te.LcTea.encrypt, ~Te.LcTea.decrypt, hx("000102030405060708090a0b0c0d0e0f"), hx("0001020304050607")))
    IO.print(lc64(~Xt.LcXteaKey, ~LC.CrLc.key(~Xt.LcXteaKey, ~Xt.LcXtea.key), ~Xt.LcXtea.encrypt, ~Xt.LcXtea.decrypt, hx("000102030405060708090a0b0c0d0e0f"), hx("0001020304050607")))
    IO.print(lc64(~Fc.LcFcryptKey, ~LC.CrLc.key(~Fc.LcFcryptKey, ~Fc.LcFcrypt.key), ~Fc.LcFcrypt.encrypt, ~Fc.LcFcrypt.decrypt, hx("114477aadd003366"), hx("123456789abcdef0")))
    IO.print(pcbc_fc(hx("3141592653589793"), hx("2718281828459045"), hx("74686973206973206120746573740000")))
    IO.print(lrw_aes(hx("4562ac25f828176d4c268414b5680185258e2a05e73e9d03ee5a830ccc094c87"), hx("00000000000000000000000000000001"), hx("30313233343536373839414243444546")))
    IO.print(lrw_aes(hx("59704714f557478cd779e80f548879440d48f0b7b15a53ea1caa6b29c2cafbaf"), hx("00000000000000000000000000000002"), hx("30313233343536373839414243444546")))
    IO.print(lrw_aes(hx("d82a9134b26a565030fe69e2377f9847cdf90b160c648fb6b00d0d1bae85871f"), hx("00000000000000000000000200000000"), hx("30313233343536373839414243444546")))
    IO.print(lrw_aes(hx("f8d476ffd646ee6c2384cb1c77d6195dfef1a9f37bbc8d21a79c21f8cb900289a845348ec8c5b5f126f50e76fefd1b1e"), hx("00000000000000000000000000000001"), hx("30313233343536373839414243444546")))
    IO.print(lrw_aes(hx("fb7615b23d80891dd470980bc79584c8b2fb64ce6097878d17fce45a49e830b76e7817e72d5e12d46064047af12f9e0c"), hx("00000000000000000000000200000000"), hx("30313233343536373839414243444546")))
    IO.print(cts_aes(hx("636869636b656e207465726979616b69"), z16, hx("4920776f756c64206c696b652074686520")))
    IO.print(cts_aes(hx("636869636b656e207465726979616b69"), z16, hx("4920776f756c64206c696b65207468652047656e6572616c20476175277320")))
    IO.print(cts_aes(hx("636869636b656e207465726979616b69"), z16, hx("4920776f756c64206c696b65207468652047656e6572616c2047617527732043")))
    IO.print(cts_aes(hx("636869636b656e207465726979616b69"), z16, hx("4920776f756c64206c696b65207468652047656e6572616c20476175277320436869636b656e2c20706c656173652c20616e6420776f6e746f6e20736f75702e")))
    IO.print(cts_aes(hx("636869636b656e207465726979616b69"), z16, hx("4920776f756c64206c696b6520")))
    IO.print(xcbc_aes(hx("000102030405060708090a0b0c0d0e0f"), B.Octets.empty()))
    IO.print(xcbc_aes(hx("000102030405060708090a0b0c0d0e0f"), hx("000102")))
    IO.print(xcbc_aes(hx("000102030405060708090a0b0c0d0e0f"), hx("000102030405060708090a0b0c0d0e0f")))
    IO.print(xcbc_aes(hx("000102030405060708090a0b0c0d0e0f"), hx("000102030405060708090a0b0c0d0e0f10111213")))
    IO.print(xcbc_aes(hx("000102030405060708090a0b0c0d0e0f"), hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")))
    IO.print(xcbc_aes(hx("000102030405060708090a0b0c0d0e0f"), hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021")))
    IO.print(xcbc_aes(hx("000102030405060708090a0b0c0d0e0f"), B.Octets.zeros(1000n)))
    IO.print(vmac_aes(~1n, B.Octets.of_string("abcdefghijklmnop"), B.Octets.of_string("bcdefghi"), B.Octets.empty()))
    IO.print(vmac_aes(~2n, B.Octets.of_string("abcdefghijklmnop"), B.Octets.of_string("bcdefghi"), B.Octets.empty()))
    IO.print(vmac_aes(~1n, B.Octets.of_string("abcdefghijklmnop"), B.Octets.of_string("bcdefghi"), B.Octets.of_string("abc")))
    IO.print(vmac_aes(~2n, B.Octets.of_string("abcdefghijklmnop"), B.Octets.of_string("bcdefghi"), B.Octets.of_string("abc")))
    IO.print(vmac_aes(~1n, B.Octets.of_string("abcdefghijklmnop"), B.Octets.of_string("bcdefghi"), B.Octets.of_string(rep(16n, "abc", ""))))
    IO.print(vmac_aes(~2n, B.Octets.of_string("abcdefghijklmnop"), B.Octets.of_string("bcdefghi"), B.Octets.of_string(rep(16n, "abc", ""))))
    IO.print(vmac_aes(~1n, B.Octets.of_string("abcdefghijklmnop"), B.Octets.of_string("bcdefghi"), B.Octets.of_string(rep(100n, "abc", ""))))
    IO.print(vmac_aes(~2n, B.Octets.of_string("abcdefghijklmnop"), B.Octets.of_string("bcdefghi"), B.Octets.of_string(rep(100n, "abc", ""))))
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
#|ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
#|248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
#|ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f
#|248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
#|ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f
#|b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7
#|87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854
#|5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843
#|164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737
#|773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe
#|fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb
#|82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b
#|b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3dba91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd
#|a3b6167473100ee06e0c796c2955552b
#|415fad6271580a531d4179bc891d87a6
#|60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54
#|80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598
#|9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2
#|e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58
#|5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843 accepted
#|3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865
#|b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87
#|8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8
#|d718fbd6ab644c739da95f3be6451778 00112233445566778899aabbccddeeff
#|c842a08972b43d20836c91d1b7530f6b 00000000000000000000000000000000
#|0aceab0fc6a0a28d 0123456789abcdef
#|238b4fe5847e44b2 0123456789abcdef
#|6da901760c539dce 0001020304050607
#|256004e1f55bc0c7 0001020304050607
#|d8ed787477ec0680 123456789abcdef0
#|ad5130bd809dc84f08d66ecb10244654 74686973206973206120746573740000
#|f1b273cd65a3df5fe95d489254634eb8 30313233343536373839414243444546
#|00c82bae95bbcde5274f0769b260e136 30313233343536373839414243444546
#|76322183ed8ff182f9596203690e5e01 30313233343536373839414243444546
#|bd06b8e1db98899ec498e491cf1c702b 30313233343536373839414243444546
#|5b908ec1abdd675f3d698a9553c89ce5 30313233343536373839414243444546
#|c6353568f2bf8cb4d8a580362da7ff7f97 4920776f756c64206c696b652074686520
#|fc00783e0efdb2c1d445d4c8eff7ed2297687268d6ecccc0c07b25e25ecfe5 4920776f756c64206c696b65207468652047656e6572616c20476175277320
#|39312523a78662d5be7fcbcc98ebf5a897687268d6ecccc0c07b25e25ecfe584 4920776f756c64206c696b65207468652047656e6572616c2047617527732043
#|97687268d6ecccc0c07b25e25ecfe58439312523a78662d5be7fcbcc98ebf5a84807efe836ee89a526730dbc2f7bc8409dad8bbb96c4cdc03bc103e1a194bbd8 4920776f756c64206c696b65207468652047656e6572616c20476175277320436869636b656e2c20706c656173652c20616e6420776f6e746f6e20736f75702e
#|too short 13 too short 13
#|75f0251d528ac01c4573dfd584d79f29
#|5b376580ae2f19afe7219ceef172756f
#|d2a246fa349b68a79998a4394ff7a263
#|47f51b4564966215b8985c63055ed308
#|f54f0ec8d2b9f3d36807734bd5283fd4
#|becbb3bccdb518a30677d5481fb6b4d8
#|f0dafee895db30253761103b5d84528f
#|2576be1c56d8b81b
#|472766c70f74ed23481d6d7de4e80dac
#|2d376cf5b1813ce5
#|4ee815a06a1d71edd36fc75d51188a42
#|e8421f61d573d298
#|09f2c80c8e1007a0c12fae19fe4504ae
#|4492df6c5cac1bbe
#|66438817154850c61d8a412164803bcb
