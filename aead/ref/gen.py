#!/usr/bin/env python3
"""Differential test cases for bend-osdev-aead, on random inputs.

Writes ref/cases.bend (a Bend program printing each case) and
ref/expected.txt (the same values from Python):
  * Encrypt-then-MAC in the Linux kernel's layout, authenc(hmac(sha256),
    cbc(aes)) through AF_ALG (MAC keys of 0 to 100 bytes, AES-128 and
    AES-256, 16- and 32-byte tags): sealed, opened back, a changed tag
    refused; without AF_ALG, cryptography's AES-CBC and Python's hmac, which
    are first checked against the kernel when it has the algorithm;
  * Encrypt-then-MAC in the McGrew draft's layout (A || IV || C || AL, PKCS
    #7 padding), against cryptography's AES-CBC and padding and Python's
    hmac (the layout first checked on RFC 7518's Appendix B.1);
  * ESSIV over AES-CBC with SHA-256: the kernel's essiv(cbc(aes), sha256),
    or cryptography's AES and hashlib without AF_ALG; both ways;
  * seqiv over AES-CCM: cryptography's AESCCM under the IV this package's
    generator gives (salt XOR the sequence number) and the associated data
    A || IV; sealed, opened, a changed byte (the IV's included) refused;
  * echainiv over authenc(hmac(sha256), cbc(aes)): the IV from
    cryptography's AES, the AEAD the kernel's (or Python's, as above) over
    A || IV; a changed byte, the IV's included, refused;
  * AEGIS-128: sealed, opened back, a changed tag and a changed ciphertext
    byte refused, against ref/model.py. **The model shares this package's
    author** (written from the same specification; no outside AEGIS-128
    implementation is reachable here), so these cases check the Bend code
    against a second reading of the specification, not against an
    independent one; the model itself agrees with the four published
    AEGIS-128 vectors of Wu and Preneel's SAC 2013 paper (Appendix A.1),
    which it checks when imported.
"""
import hashlib, hmac, os, random, socket, struct, sys, warnings

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import model  # noqa: E402

warnings.simplefilter("ignore")
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes  # noqa: E402
from cryptography.hazmat.primitives.ciphers.aead import AESCCM  # noqa: E402
from cryptography.hazmat.primitives import padding  # noqa: E402

h = bytes.fromhex


def o(data):
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


def aes(k, b):
    e = Cipher(algorithms.AES(k), modes.ECB()).encryptor()
    return e.update(b) + e.finalize()


def cbc(k, iv, m):
    e = Cipher(algorithms.AES(k), modes.CBC(iv)).encryptor()
    return e.update(m) + e.finalize()


def cbc_dec(k, iv, c):
    d = Cipher(algorithms.AES(k), modes.CBC(iv)).decryptor()
    return d.update(c) + d.finalize()


def k_authenc(authkey, enckey, iv, aad, p, tlen):
    """the kernel's authenc(hmac(sha256),cbc(aes)) through AF_ALG: C || T
    (None when missing)"""
    try:
        s = socket.socket(socket.AF_ALG, socket.SOCK_SEQPACKET, 0)
        s.bind(("aead", "authenc(hmac(sha256),cbc(aes))"))
        s.setsockopt(socket.SOL_ALG, socket.ALG_SET_KEY, struct.pack("=HH", 8, 1) + struct.pack(">I", len(enckey)) + authkey + enckey)
        s.setsockopt(socket.SOL_ALG, socket.ALG_SET_AEAD_AUTHSIZE, None, tlen)
        op, _ = s.accept()
        op.sendmsg_afalg([aad + p], op=socket.ALG_OP_ENCRYPT, iv=iv, assoclen=len(aad))
        out = op.recv(len(aad) + len(p) + tlen)[len(aad):]
        op.close(); s.close()
        return out
    except Exception:
        return None


def k_essiv(k, iv, p, enc=True):
    """the kernel's essiv(cbc(aes),sha256) through AF_ALG (None when missing)"""
    try:
        s = socket.socket(socket.AF_ALG, socket.SOCK_SEQPACKET, 0)
        s.bind(("skcipher", "essiv(cbc(aes),sha256)"))
        s.setsockopt(socket.SOL_ALG, socket.ALG_SET_KEY, k)
        op, _ = s.accept()
        op.sendmsg_afalg([p], op=socket.ALG_OP_ENCRYPT if enc else socket.ALG_OP_DECRYPT, iv=iv)
        out = op.recv(len(p))
        op.close(); s.close()
        return out
    except Exception:
        return None


def authenc_k(mk, ek, iv, aad, p, tlen):
    """the kernel's layout in Python: A || C authenticated"""
    c = cbc(ek, iv, p)
    return c + hmac.new(mk, aad + c, hashlib.sha256).digest()[:tlen]


def authenc_m(mk, ek, iv, aad, p, tlen):
    """the McGrew draft's layout (RFC 7518 5.2.2.1): A || IV || C || AL"""
    pd = padding.PKCS7(128).padder()
    c = cbc(ek, iv, pd.update(p) + pd.finalize())
    return c + hmac.new(mk, aad + iv + c + (8 * len(aad)).to_bytes(8, "big"), hashlib.sha256).digest()[:tlen]


def essiv(k, iv, p, enc=True):
    iv2 = aes(hashlib.sha256(k).digest(), iv)
    return cbc(k, iv2, p) if enc else cbc_dec(k, iv2, p)


KERNEL = set()


def self_checks(rb):
    # the McGrew layout on RFC 7518 B.1
    k = bytes(range(32))
    t = authenc_m(k[:16], k[16:], h("1af38c2dc2b96ffdd86694092341bc04"), b"The second principle of Auguste Kerckhoffs",
                  b"A cipher system must not be required to be secret, and it must be able to fall into the hands of the enemy without inconvenience", 16)
    assert t[-16:].hex() == "652c3fa36b0a7c5b3219fab3a30bc1c4"
    assert model.aes_round(bytes(range(16)), bytes(range(16, 32))).hex() == "7a7b4e5638782546a8c0477a3b813f43"
    for _ in range(4):
        mk, ek, iv, aad, p = rb(32), rb(16), rb(16), rb(20), rb(32)
        got = k_authenc(mk, ek, iv, aad, p, 32)
        if got is not None:
            KERNEL.add("authenc")
            assert got == authenc_k(mk, ek, iv, aad, p, 32)
        got = k_essiv(mk, iv, p)
        if got is not None:
            KERNEL.add("essiv")
            assert got == essiv(mk, iv, p)


HEADER = '''# Generated by ref/gen.py; do not edit.
import Base
import ../../bytes/bytes.bend as B
import ../../cipher-modes/cipher-modes.bend as M
import ../../cipher-modes/aes.bend as X
import ../../crypto/crypto.bend as Cr
import ../../crypto/inst_cm.bend as CM
import ../../crypto/inst_aes.bend as A
import ../../crypto/inst_ccm.bend as CC
import ../../crypto/inst_sha2.bend as SH
import ../../crypto/hmac.bend as Hm
import ../aegis128.bend as Ae
import ../authenc.bend as Au
import ../ivcipher.bend as Iv
import ../essiv.bend as Es
import ../seqiv.bend as Sq
import ../echainiv.bend as Ec

def res(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      "fail"

def two(a: String, b: String) -> String:
  a ++ " " ++ b

def bind(r: Result<&2, &2, Cr.CrError, B.Octets>, f: B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, r, f)

# sealed, opened back, and two changed ciphertexts opened
def aegis(+k: B.Octets, +n: B.Octets, +a: B.Octets, +p: B.Octets, +c1: B.Octets, +c2: B.Octets) -> String:
  +r = Ae.AdAegis128.key(k)
  +c = Result.bind(&2, &2, Cr.CrError, Ae.AdAegisKey, B.Octets, r, kk => Ae.AdAegis128.seal(kk, n, a, p))
  two(res(c), two(res(Result.bind(&2, &2, Cr.CrError, Ae.AdAegisKey, B.Octets, r, kk => bind(c, x => Ae.AdAegis128.open(kk, n, a, x)))), two(res(Result.bind(&2, &2, Cr.CrError, Ae.AdAegisKey, B.Octets, r, kk => Ae.AdAegis128.open(kk, n, a, c1))), res(Result.bind(&2, &2, Cr.CrError, Ae.AdAegisKey, B.Octets, r, kk => Ae.AdAegis128.open(kk, n, a, c2))))))

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

def au.key(~elen: Nat, o: B.Octets) -> Result<&2, &2, Cr.CrError, Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>>:
  Au.AdAuthenc.key(~X.CmAesKey, ~Hm.CrHmacKey, ~A.CrAes.key, ~au.mkey, ~elen, o)

def au.seal_k(~tlen: Nat, k: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, iv: B.Octets, a: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Au.AdAuthenc.seal(~X.CmAesKey, ~Hm.CrHmacKey, ~au.enc, ~au.mac, ~Au.AdAuthenc.input_kernel, ~tlen, k, iv, a, p)

def au.open_k(~tlen: Nat, k: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, iv: B.Octets, a: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Au.AdAuthenc.open(~X.CmAesKey, ~Hm.CrHmacKey, ~au.dec, ~au.mac, ~Au.AdAuthenc.input_kernel, ~tlen, k, iv, a, c)

def au.seal_m(~tlen: Nat, k: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, iv: B.Octets, a: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Au.AdAuthenc.seal(~X.CmAesKey, ~Hm.CrHmacKey, ~au.encp, ~au.mac, ~Au.AdAuthenc.input_mcgrew, ~tlen, k, iv, a, p)

def au.open_m(~tlen: Nat, k: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, iv: B.Octets, a: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Au.AdAuthenc.open(~X.CmAesKey, ~Hm.CrHmacKey, ~au.decp, ~au.mac, ~Au.AdAuthenc.input_mcgrew, ~tlen, k, iv, a, c)

# sealed, opened back, a changed ciphertext opened
def authenc(~elen: Nat, ~seal: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey> -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~open: Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey> -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: B.Octets, +iv: B.Octets, +a: B.Octets, +p: B.Octets, +c1: B.Octets) -> String:
  +r = au.key(~elen, k)
  +c = Result.bind(&2, &2, Cr.CrError, Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, B.Octets, r, kk => seal(kk, iv, a, p))
  two(res(c), two(res(Result.bind(&2, &2, Cr.CrError, Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, B.Octets, r, kk => bind(c, x => open(kk, iv, a, x)))), res(Result.bind(&2, &2, Cr.CrError, Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, B.Octets, r, kk => open(kk, iv, a, c1)))))

def es.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, Es.AdEssivKey<X.CmAesKey, X.CmAesKey>>:
  Es.AdEssiv.key(~X.CmAesKey, ~X.CmAesKey, ~A.CrAes.key, ~A.CrAes.key, ~SH.CrSha2.sha256, o)

# p encrypted, c decrypted
def essiv(+k: B.Octets, +iv: B.Octets, +p: B.Octets, +c: B.Octets) -> String:
  +r = es.key(k)
  two(res(Result.bind(&2, &2, Cr.CrError, Es.AdEssivKey<X.CmAesKey, X.CmAesKey>, B.Octets, r, kk => Es.AdEssiv.encrypt(~X.CmAesKey, ~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~au.enc, kk, iv, p))), res(Result.bind(&2, &2, Cr.CrError, Es.AdEssivKey<X.CmAesKey, X.CmAesKey>, B.Octets, r, kk => Es.AdEssiv.decrypt(~X.CmAesKey, ~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~au.dec, kk, iv, c))))

def ccm.seal(k: X.CmAesKey, n: B.Octets, a: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CC.CrCcm.seal(~X.CmAesKey, ~X.CmAes.encrypt, ~16n, k, n, a, p)

def ccm.open(k: X.CmAesKey, n: B.Octets, a: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CC.CrCcm.open(~X.CmAesKey, ~X.CmAes.encrypt, ~16n, k, n, a, c)

def seqiv(+k: B.Octets, +seq: B.Octets, +a: B.Octets, +p: B.Octets, +c1: B.Octets) -> String:
  +r = Sq.AdSeqiv.key(~X.CmAesKey, ~A.CrAes.key, ~12n, k)
  +c = Result.bind(&2, &2, Cr.CrError, Sq.AdSeqivKey<X.CmAesKey>, B.Octets, r, kk => Sq.AdSeqiv.seal(~X.CmAesKey, ~ccm.seal, kk, seq, a, p))
  two(res(c), two(res(Result.bind(&2, &2, Cr.CrError, Sq.AdSeqivKey<X.CmAesKey>, B.Octets, r, kk => bind(c, x => Sq.AdSeqiv.open(~X.CmAesKey, ~ccm.open, ~12n, kk, seq, a, x)))), res(Result.bind(&2, &2, Cr.CrError, Sq.AdSeqivKey<X.CmAesKey>, B.Octets, r, kk => Sq.AdSeqiv.open(~X.CmAesKey, ~ccm.open, ~12n, kk, seq, a, c1)))))

def echainiv(~elen: Nat, +ak: B.Octets, +ck: B.Octets, +salt: B.Octets, +seq: B.Octets, +a: B.Octets, +p: B.Octets, +c1: B.Octets) -> String:
  +r = Ec.AdEchainiv.key(~Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, ~X.CmAesKey, ~au.key(~elen), ~A.CrAes.key, ak, ck, salt)
  +c = Result.bind(&2, &2, Cr.CrError, Ec.AdEchainivKey<Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, X.CmAesKey>, B.Octets, r, kk => Ec.AdEchainiv.seal(~Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, ~X.CmAesKey, ~M.CmBlock, ~X.CmAes.encrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~au.seal_k(~32n), kk, seq, a, p))
  two(res(c), two(res(Result.bind(&2, &2, Cr.CrError, Ec.AdEchainivKey<Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, X.CmAesKey>, B.Octets, r, kk => bind(c, x => Ec.AdEchainiv.open(~Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, ~X.CmAesKey, ~au.open_k(~32n), ~16n, kk, seq, a, x)))), res(Result.bind(&2, &2, Cr.CrError, Ec.AdEchainivKey<Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, X.CmAesKey>, B.Octets, r, kk => Ec.AdEchainiv.open(~Au.AdAuthencKey<X.CmAesKey, Hm.CrHmacKey>, ~X.CmAesKey, ~au.open_k(~32n), ~16n, kk, seq, a, c1)))))
'''


def flip(c, i):
    return c[:i] + bytes([c[i] ^ 1]) + c[i + 1:]


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    self_checks(rb)
    lines, expect, counts = [], [], {"kernel": 0, "python": 0, "model": 0}

    def case(name, k, call, want, src):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, k, call))
        expect.append("%s %d %s" % (name, k, want))
        counts[src] += 1

    for i in range(10):  # authenc, the kernel's layout
        el, tl = [16, 32][i % 2], [32, 16][(i // 2) % 2]
        mk, ek, iv = rb([0, 16, 32, 64, 100][i % 5]), rb(el), rb(16)
        aad, p = rb(rng.randrange(0, 40)), rb(16 * rng.randrange(0, 5))
        c, src = k_authenc(mk, ek, iv, aad, p, tl), "kernel"
        if c is None:
            c, src = authenc_k(mk, ek, iv, aad, p, tl), "python"
        case("authenc_kernel", i, "authenc(~%dn, ~au.seal_k(~%dn), ~au.open_k(~%dn), %s, %s, %s, %s, %s)" % (el, tl, tl, o(mk + ek), o(iv), o(aad), o(p), o(flip(c, len(c) - 1))),
             "%s %s fail" % (c.hex(), p.hex()), src)
    for i in range(8):  # authenc, the McGrew draft's layout
        el, tl = [16, 32][i % 2], [16, 32][(i // 2) % 2]
        mk, ek, iv = rb([16, 32][i % 2]), rb(el), rb(16)
        aad, p = rb(rng.randrange(0, 40)), rb(rng.randrange(0, 70))
        c = authenc_m(mk, ek, iv, aad, p, tl)
        case("authenc_mcgrew", i, "authenc(~%dn, ~au.seal_m(~%dn), ~au.open_m(~%dn), %s, %s, %s, %s, %s)" % (el, tl, tl, o(mk + ek), o(iv), o(aad), o(p), o(flip(c, 0))),
             "%s %s fail" % (c.hex(), p.hex()), "python")
    for i in range(6):  # ESSIV
        k, iv = rb([16, 32][i % 2]), rb(16)
        p, c2 = rb(16 * rng.randrange(1, 6)), rb(16 * rng.randrange(1, 6))
        we, wd, src = k_essiv(k, iv, p), k_essiv(k, iv, c2, False), "kernel"
        if we is None:
            we, wd, src = essiv(k, iv, p), essiv(k, iv, c2, False), "python"
        case("essiv", i, "essiv(%s, %s, %s, %s)" % (o(k), o(iv), o(p), o(c2)), "%s %s" % (we.hex(), wd.hex()), src)
    for i in range(6):  # seqiv over AES-CCM
        k, seq = rb(28), rb(rng.randrange(1, 13))
        aad, p = rb(rng.randrange(0, 30)), rb(rng.randrange(0, 50))
        iv = xor(k[16:], bytes(12 - len(seq)) + seq)
        c = iv + AESCCM(k[:16], 16).encrypt(iv, p, aad + iv)
        case("seqiv", i, "seqiv(%s, %s, %s, %s, %s)" % (o(k), o(seq), o(aad), o(p), o(flip(c, rng.randrange(12, len(c))))), "%s %s fail" % (c.hex(), p.hex()), "python")
    for i in range(4):  # echainiv over authenc(hmac(sha256), cbc(aes))
        el = [16, 32][i % 2]
        mk, ek, ck, salt, seq = rb(32), rb(el), rb(16), rb(16), rb(8)
        aad, p = rb(rng.randrange(0, 30)), rb(16 * rng.randrange(0, 4))
        iv = aes(ck, xor(salt, bytes(8) + seq))
        c, src = k_authenc(mk, ek, iv, aad + iv, p, 32), "kernel"
        if c is None:
            c, src = authenc_k(mk, ek, iv, aad + iv, p, 32), "python"
        c = iv + c
        case("echainiv", i, "echainiv(~%dn, %s, %s, %s, %s, %s, %s, %s)" % (el, o(mk + ek), o(ck), o(salt), o(seq), o(aad), o(p), o(flip(c, rng.randrange(0, len(c))))),
             "%s %s fail" % (c.hex(), p.hex()), src)
    for i in range(12):  # AEGIS-128
        k, n = rb(16), rb(16)
        aad, p = rb([0, 0, 16, 5][i % 4] if i < 4 else rng.randrange(0, 70)), rb([0, 16, 0, 33][i % 4] if i < 4 else rng.randrange(0, 100))
        c = model.aegis128_seal(k, n, aad, p)
        assert model.aegis128_open(k, n, aad, c) == p
        case("aegis128", i, "aegis(%s, %s, %s, %s, %s, %s)" % (o(k), o(n), o(aad), o(p), o(flip(c, len(c) - 1)), o(flip(c, rng.randrange(0, len(c))))),
             "%s %s fail fail" % (c.hex(), p.hex()), "model")

    with open(os.path.join(HERE, "cases.bend"), "w", newline="\n") as f:
        f.write(HEADER + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(HERE, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d from the Linux kernel's authenc(hmac(sha256),cbc(aes)) and essiv(cbc(aes),sha256), %d from cryptography, hmac and hashlib, %d from ref/model.py's AEGIS-128, which shares this package's author)"
          % (len(lines), counts["kernel"], counts["python"], counts["model"]))


if __name__ == "__main__":
    main()
