#!/usr/bin/env python3
"""Differential test cases for bend-osdev-crypto: every instance through its
interface, against implementations outside this package.

Writes ref/cases.bend (a Bend program printing each case through the
interfaces) and ref/expected.txt (the same values from Python):
  * block ciphers, one block both ways: AES, DES, 3DES, SM4, Camellia through
    Python's cryptography (OpenSSL; DES as TripleDES with three equal keys);
    Serpent and Twofish through legacy-ciphers' ref/model.py (written from
    the specifications by that package's author: cryptography has neither);
  * the modes over the interface (modes.bend): ECB, CBC and CTR, for those
    ciphers; ECB and CBC through cryptography where it has the cipher, CTR
    through this file's CTR (SP 800-38A) over cryptography's or the model's
    block function, first checked against cryptography's own CTR for AES;
    CTR is fed in two pieces through the stream interface;
  * RC4 through the stream interface, in two pieces: cryptography's ARC4 at
    the key sizes it takes, the model at the others;
  * CMAC through the MAC interface (cryptography's CMAC for AES, SM4 and
    Camellia; this file's RFC 4493 CMAC over the model for Serpent and
    Twofish, first checked against cryptography for AES), with verify
    accepting the tag and refusing it changed;
  * CCM through the AEAD interface (cryptography's AESCCM for AES; this
    file's RFC 3610 CCM, first checked against AESCCM, over cryptography's
    or the model's block function for SM4, Camellia, Serpent and Twofish):
    sealing, opening, and a changed tag, ciphertext byte or associated-data
    byte refused;
  * the CRC hashes, one-shot and in pieces (binascii.crc32 for CRC-32; this
    file's Rocksoft-model CRCs, checked against the catalogue's check
    values, for CRC-32C and CRC-64/XZ);
  * HMAC over CRC-32, CRC-32C and CRC-64/XZ against Python's hmac module
    (with each CRC as its digestmod), one-shot, in pieces, and verify, with
    keys shorter and longer than the block size;
  * SHA-256 and SHA-512 (bend-collections, through inst_sha2.bend), one-shot
    and in pieces, against hashlib; HMAC over them (keys of 0 to 200 bytes,
    across both block sizes) against hmac with hashlib;
  * HKDF over SHA-256 and SHA-512 against cryptography's HKDF, and over
    CRC-32 and CRC-64/XZ against this file's RFC 5869 HKDF on Python's
    hmac, which is first checked against cryptography's HKDF with SHA-256
    on RFC 5869's test case 1;
  * the hashes package's hashes through the hash interface, one-shot and in
    pieces, and HMAC over them: MD5, SHA-1, RIPEMD-160 and SM3 against
    hashlib and hmac; MD4 and Streebog against hashes/ref/model.py (Python
    lacks them here; that model shares an author with the package and is
    checked against the specifications' vectors first) under Python's hmac;
  * Michael through the MAC interface (the tag, verify of it and of it
    changed) against hashes/ref/model.py;
  * PBKDF2 over HMAC over SHA-1, SHA-256, MD5, RIPEMD-160 and SM3 against
    hashlib.pbkdf2_hmac, and over SHA-1 and SHA-256 against cryptography's
    PBKDF2HMAC too, with iteration counts of 1 to 40 and outputs of 1 to
    three blocks and more.
"""
import binascii, hashlib, hmac, os, random, sys, warnings

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(HERE, "..", "..", "legacy-ciphers", "ref"))
import model as lcm  # noqa: E402
import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location("hsmodel", os.path.join(HERE, "..", "..", "hashes", "ref", "model.py"))
hsm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hsm)

warnings.simplefilter("ignore")
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes  # noqa: E402
from cryptography.hazmat.primitives.ciphers.aead import AESCCM  # noqa: E402
from cryptography.hazmat.primitives import cmac as ccmac, hashes  # noqa: E402
from cryptography.hazmat.primitives.kdf.hkdf import HKDF  # noqa: E402
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC  # noqa: E402

h = bytes.fromhex


def o(data):
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


# ---------------------------------------------------------------- block functions

def lib_ecb(alg, key, data, enc=True):
    c = Cipher(alg(key), modes.ECB())
    op = c.encryptor() if enc else c.decryptor()
    return op.update(data) + op.finalize()


def tdes(key):
    return algorithms.TripleDES(key * 3 if len(key) == 8 else key)


CIPHERS = {
    # name: (block size, encrypt one block, Bend template arguments)
    "aes": (16, lambda k, b: lib_ecb(algorithms.AES, k, b),
            "~X.CmAesKey, ~M.CmBlock, ~16n, ~A.CrAes.key, ~X.CmAes.encrypt, ~X.CmAes.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~CM.CrBlk128.xor"),
    "des": (8, lambda k, b: lib_ecb(tdes, k, b),
            "~D.LcDesKey, ~L.LcBlock64, ~8n, ~LC.CrLc.key(~D.LcDesKey, ~D.LcDes.key), ~D.LcDes.encrypt, ~D.LcDes.decrypt, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, ~LC.CrBlk64.xor"),
    "tdes": (8, lambda k, b: lib_ecb(tdes, k, b),
             "~T.LcTdesKey, ~L.LcBlock64, ~8n, ~LC.CrLc.key(~T.LcTdesKey, ~T.LcTdes.key), ~T.LcTdes.encrypt, ~T.LcTdes.decrypt, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, ~LC.CrBlk64.xor"),
    "sm4": (16, lambda k, b: lib_ecb(algorithms.SM4, k, b),
            "~S.LcSm4Key, ~M.CmBlock, ~16n, ~LC.CrLc.key(~S.LcSm4Key, ~S.LcSm4.key), ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~CM.CrBlk128.xor"),
    "camellia": (16, lambda k, b: lib_ecb(algorithms.Camellia, k, b),
                 "~Ca.LcCamelliaKey, ~M.CmBlock, ~16n, ~LC.CrLc.key(~Ca.LcCamelliaKey, ~Ca.LcCamellia.key), ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~CM.CrBlk128.xor"),
    "serpent": (16, lambda k, b: lcm.serpent_encrypt(k, b),
                "~Sp.LcSerpentKey, ~M.CmBlock, ~16n, ~LC.CrLc.key(~Sp.LcSerpentKey, ~Sp.LcSerpent.key), ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~CM.CrBlk128.xor"),
    "twofish": (16, lambda k, b: lcm.twofish_encrypt(k, b),
                "~Tf.LcTwofishKey, ~M.CmBlock, ~16n, ~LC.CrLc.key(~Tf.LcTwofishKey, ~Tf.LcTwofish.key), ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~CM.CrBlk128.xor"),
}
KEYS = {"aes": [16, 32], "des": [8], "tdes": [16, 24], "sm4": [16], "camellia": [16, 24, 32],
        "serpent": [16, 24, 32], "twofish": [16, 24, 32]}
LIB = {"aes", "des", "tdes", "sm4", "camellia"}  # the ciphers cryptography has


def tmpl(name, keep):
    """the template arguments of a cipher that a helper takes: keep is the
    list of positions (0 K, 1 Blk, 2 bsize, 3 key, 4 enc, 5 dec, 6 blk_of,
    7 blk_to, 8 bxor)"""
    parts = [p.strip() for p in split_top(CIPHERS[name][2])]
    return ", ".join(parts[i] for i in keep)


def split_top(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "," and depth == 0:
            out.append(cur); cur = ""
            continue
        depth += ch in "(<"
        depth -= ch in ")>"
        cur += ch
    out.append(cur)
    return out


# ---------------------------------------------------------------- modes, written here

def ecb(enc, key, m, bs):
    return b"".join(enc(key, m[i:i + bs]) for i in range(0, len(m), bs))


def cbc(enc, key, iv, m, bs):
    out, prev = b"", iv
    for i in range(0, len(m), bs):
        prev = enc(key, xor(m[i:i + bs], prev))
        out += prev
    return out


def ctr(enc, key, iv, m, bs):
    n, ks, c = int.from_bytes(iv, "big"), b"", 0
    while len(ks) < len(m):
        ks += enc(key, ((n + c) % (1 << (8 * bs))).to_bytes(bs, "big"))
        c += 1
    return xor(m, ks)


def dbl(b):
    v = (int.from_bytes(b, "big") << 1)
    if v >> 128:
        v = (v & ((1 << 128) - 1)) ^ 0x87
    return v.to_bytes(16, "big")


def cmac(enc, key, m):
    k1 = dbl(enc(key, bytes(16)))
    k2 = dbl(k1)
    n = max(1, (len(m) + 15) // 16)
    last = m[16 * (n - 1):]
    last = xor(last, k1) if len(last) == 16 else xor(last + b"\x80" + bytes(15 - len(last)), k2)
    x = bytes(16)
    for i in range(n - 1):
        x = enc(key, xor(x, m[16 * i:16 * i + 16]))
    return enc(key, xor(x, last))


def ccm(enc, key, nonce, aad, p, tlen):
    L = 15 - len(nonce)
    b0 = bytes([(64 if aad else 0) | (((tlen - 2) // 2) << 3) | (L - 1)]) + nonce + len(p).to_bytes(L, "big")
    a = b""
    if aad:
        a = (len(aad).to_bytes(2, "big") if len(aad) < 0xFF00 else b"\xff\xfe" + len(aad).to_bytes(4, "big")) + aad
        a += bytes(-len(a) % 16)
    data = b0 + a + p + bytes(-len(p) % 16)
    x = bytes(16)
    for i in range(0, len(data), 16):
        x = enc(key, xor(x, data[i:i + 16]))
    ai = lambda i: bytes([L - 1]) + nonce + i.to_bytes(L, "big")
    s = b"".join(enc(key, ai(i)) for i in range(1, (len(p) + 15) // 16 + 1))
    return xor(p, s) + xor(x[:tlen], enc(key, ai(0)))


# ---------------------------------------------------------------- CRCs as hash objects

def crc_model(width, poly, init, xorout):
    """a reflected CRC of the Rocksoft model (every CRC used here is
    reflected)"""
    rpoly = int(bin(poly)[2:].zfill(width)[::-1], 2)
    mask = (1 << width) - 1

    def upd(c, data):
        for b in data:
            c ^= b
            for _ in range(8):
                c = (c >> 1) ^ (rpoly if c & 1 else 0)
        return c

    class Crc:
        digest_size, block_size = width // 8, 64
        name = "crc%d" % width

        def __init__(self, data=b""):
            self.c = upd(int(bin(init)[2:].zfill(width)[::-1], 2), data)

        def update(self, d):
            self.c = upd(self.c, d)

        def digest(self):
            return ((self.c ^ xorout) & mask).to_bytes(width // 8, "big")

        def copy(self):
            n = Crc(); n.c = self.c
            return n
    return Crc


class Crc32:
    """CRC-32/ISO-HDLC through zlib (binascii.crc32)"""
    digest_size, block_size, name = 4, 64, "crc32"

    def __init__(self, data=b""):
        self.c = binascii.crc32(data)

    def update(self, d):
        self.c = binascii.crc32(d, self.c)

    def digest(self):
        return self.c.to_bytes(4, "big")

    def copy(self):
        n = Crc32(); n.c = self.c
        return n


Crc32c = crc_model(32, 0x1EDC6F41, 0xFFFFFFFF, 0xFFFFFFFF)
Crc64xz = crc_model(64, 0x42F0E1EBA9EA3693, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)

HASHES = {
    # name: (Python hash object, Bend template arguments: H, bsize, dsize, init, update, final, digest)
    "crc32": (Crc32, "~U32, ~64n, ~4n, ~CR.CrCrc32.init(~C.crc32.spec()), ~CR.CrCrc32.update(~C.crc32.spec()), ~CR.CrCrc32.final(~C.crc32.spec()), ~CR.CrCrc32.digest(~C.crc32.spec())"),
    "crc32c": (Crc32c, "~U32, ~64n, ~4n, ~CR.CrCrc32.init(~C.crc32c.spec()), ~CR.CrCrc32.update(~C.crc32c.spec()), ~CR.CrCrc32.final(~C.crc32c.spec()), ~CR.CrCrc32.digest(~C.crc32c.spec())"),
    "crc64xz": (Crc64xz, "~W.W64, ~64n, ~8n, ~CR.CrCrc64.init(~C.crc64_xz.spec()), ~CR.CrCrc64.update(~C.crc64_xz.spec()), ~CR.CrCrc64.final(~C.crc64_xz.spec()), ~CR.CrCrc64.digest(~C.crc64_xz.spec())"),
    "sha256": (hashlib.sha256, "~SH.CrSha2State, ~64n, ~32n, ~SH.CrSha2.init256(), ~SH.CrSha2.update, ~SH.CrSha2.final, ~SH.CrSha2.sha256"),
    "sha512": (hashlib.sha512, "~SH.CrSha2State, ~128n, ~64n, ~SH.CrSha2.init512(), ~SH.CrSha2.update, ~SH.CrSha2.final, ~SH.CrSha2.sha512"),
}
SHA = {"sha256": hashes.SHA256, "sha512": hashes.SHA512}


def whole(fn, dsize, name):
    """a hash of hashes/ref/model.py as a Python hash object (for hmac)"""
    class Whole:
        digest_size, block_size = dsize, 64

        def __init__(self, data=b""):
            self.m = bytes(data)

        def update(self, d):
            self.m += d

        def digest(self):
            return fn(self.m)

        def copy(self):
            return Whole(self.m)
    Whole.name = name
    return Whole


def lib(name):
    return lambda data=b"": hashlib.new(name, data)


# the hashes package's hashes: (Python hash object, its source, Bend template
# arguments)
HS = {
    "md4": (whole(hsm.md4, 16, "md4"), "hsmodel", "~Hs.HsMdState<Hs.HsW4>, ~64n, ~16n, ~HM4.HsMd4.init(), ~HM4.HsMd4.update, ~HM4.HsMd4.final, ~HM4.HsMd4.digest"),
    "md5": (hashlib.md5, "python", "~Hs.HsMdState<Hs.HsW4>, ~64n, ~16n, ~HM5.HsMd5.init(), ~HM5.HsMd5.update, ~HM5.HsMd5.final, ~HM5.HsMd5.digest"),
    "sha1": (hashlib.sha1, "python", "~Hs.HsMdState<Hs.HsW5>, ~64n, ~20n, ~HS1.HsSha1.init(), ~HS1.HsSha1.update, ~HS1.HsSha1.final, ~HS1.HsSha1.digest"),
    "ripemd160": (lib("ripemd160"), "python", "~Hs.HsMdState<Hs.HsW5>, ~64n, ~20n, ~HRM.HsRipemd160.init(), ~HRM.HsRipemd160.update, ~HRM.HsRipemd160.final, ~HRM.HsRipemd160.digest"),
    "sm3": (lib("sm3"), "python", "~Hs.HsMdState<Hs.HsW8>, ~64n, ~32n, ~HSM.HsSm3.init(), ~HSM.HsSm3.update, ~HSM.HsSm3.final, ~HSM.HsSm3.digest"),
    "streebog256": (whole(hsm.streebog256, 32, "streebog256"), "hsmodel",
                    "~Hs.HsMdState<HST.HsStbCv>, ~64n, ~32n, ~HST.HsStreebog.init256(), ~HST.HsStreebog.update, ~HST.HsStreebog.final256, ~HST.HsStreebog.digest256"),
    "streebog512": (whole(hsm.streebog512, 64, "streebog512"), "hsmodel",
                    "~Hs.HsMdState<HST.HsStbCv>, ~64n, ~64n, ~HST.HsStreebog.init512(), ~HST.HsStreebog.update, ~HST.HsStreebog.final512, ~HST.HsStreebog.digest512"),
}
for _n in ["ripemd160", "sm3"]:
    if _n not in hashlib.algorithms_available:
        HS[_n] = (whole(getattr(hsm, _n), {"ripemd160": 20, "sm3": 32}[_n], _n), "hsmodel", HS[_n][2])


def hkdf(H, ikm, salt, info, n):
    prk = hmac.new(salt or bytes(H.digest_size), ikm, H).digest()
    t, out, i = b"", b"", 1
    while len(out) < n:
        t = hmac.new(prk, t + info + bytes([i]), H).digest()
        out, i = out + t, i + 1
    return out[:n]


def self_checks():
    """this file's references against outside implementations and published
    values, before they judge the package"""
    hsm.check_vectors()
    assert Crc32(b"123456789").digest().hex() == "cbf43926"
    assert Crc32c(b"123456789").digest().hex() == "e3069283"
    assert Crc64xz(b"123456789").digest().hex() == "995dc9bbdf1939fa"
    # HKDF on hmac against cryptography's HKDF: RFC 5869 A.1 (SHA-256)
    import hashlib
    ikm, salt, info = bytes([0x0b] * 22), h("000102030405060708090a0b0c"), h("f0f1f2f3f4f5f6f7f8f9")
    want = HKDF(hashes.SHA256(), 42, salt, info).derive(ikm)
    assert want.hex().startswith("3cb25f25faacd57a90434f64d0362f2a")
    assert hkdf(hashlib.sha256, ikm, salt, info, 42) == want
    rng = random.Random(1)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    for _ in range(8):
        key, iv, m = rb(16), rb(16), rb(rng.randrange(0, 80))
        c = Cipher(algorithms.AES(key), modes.CTR(iv)).encryptor()
        assert ctr(CIPHERS["aes"][1], key, iv, m, 16) == c.update(m) + c.finalize()
        mac = ccmac.CMAC(algorithms.AES(key)); mac.update(m)
        assert cmac(CIPHERS["aes"][1], key, m) == mac.finalize()
        for tlen, nl in [(4, 7), (8, 11), (16, 13)]:
            nonce, aad = rb(nl), rb(rng.randrange(0, 40))
            assert ccm(CIPHERS["aes"][1], key, nonce, aad, m, tlen) == AESCCM(key, tlen).encrypt(nonce, m, aad)
        assert ecb(CIPHERS["sm4"][1], key, m[:16] * 2, 16) == lib_ecb(algorithms.SM4, key, m[:16] * 2) if len(m) >= 16 else True
    for name, (key, pt, ct) in {"serpent": (bytes(16), bytes(16), "3620b17ae6a993d09618b8768266bae9"),
                                "twofish": (bytes(16), bytes(16), "9f589f5cf6122c32b6bfec2f2ae8c35a")}.items():
        assert CIPHERS[name][1](key, pt).hex() == ct


HEADER = '''# Generated by ref/gen.py; do not edit. Every instance through its interface.
import Base
import ../../bytes/bytes.bend as B
import ../../word64/word64.bend as W
import ../../cipher-modes/cipher-modes.bend as M
import ../../cipher-modes/aes.bend as X
import ../../legacy-ciphers/legacy-ciphers.bend as L
import ../../legacy-ciphers/des.bend as D
import ../../legacy-ciphers/tdes.bend as T
import ../../legacy-ciphers/sm4.bend as S
import ../../legacy-ciphers/camellia.bend as Ca
import ../../legacy-ciphers/serpent.bend as Sp
import ../../legacy-ciphers/twofish.bend as Tf
import ../../legacy-ciphers/rc4.bend as R
import ../../crc/crc.bend as C
import ../crypto.bend as Cr
import ../stream.bend as St
import ../block.bend as Bk
import ../modes.bend as Md
import ../hash.bend as H
import ../mac.bend as Mc
import ../hmac.bend as Hm
import ../hkdf.bend as Hk
import ../aead.bend as Ae
import ../inst_cm.bend as CM
import ../inst_lc.bend as LC
import ../inst_aes.bend as A
import ../inst_rc4.bend as RC
import ../inst_ccm.bend as CC
import ../inst_cmac.bend as CMI
import ../inst_crc.bend as CR
import ../inst_sha2.bend as SH
import ../inst_michael.bend as MIC
import ../pbkdf2.bend as Pb
import ../../hashes/hashes.bend as Hs
import ../../hashes/md4.bend as HM4
import ../../hashes/md5.bend as HM5
import ../../hashes/sha1.bend as HS1
import ../../hashes/ripemd160.bend as HRM
import ../../hashes/sm3.bend as HSM
import ../../hashes/streebog.bend as HST
import ../../hashes/michael.bend as HMI

def res(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      "fail"

def yn(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def two(a: String, b: String) -> String:
  a ++ " " ++ b

# one block both ways
def blk(~K: Data, ~Blk: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: B.Octets, +p: B.Octets, +c: B.Octets) -> String:
  two(res(Bk.CrBlockCipher.encrypt_with(~K, ~Blk, ~key, ~enc, ~blk_of, ~blk_to, k, p)), res(Bk.CrBlockCipher.encrypt_with(~K, ~Blk, ~key, ~dec, ~blk_of, ~blk_to, k, c)))

def ecb(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: B.Octets, +p: B.Octets, +c: B.Octets) -> String:
  +r = key(k)
  two(res(Result.bind(&2, &2, Cr.CrError, K, B.Octets, r, kk => Md.CrEcb.encrypt(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, p))), res(Result.bind(&2, &2, Cr.CrError, K, B.Octets, r, kk => Md.CrEcb.decrypt(~K, ~Blk, ~bsize, ~dec, ~blk_of, ~blk_to, kk, c))))

def cbc(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~bxor: Blk -> Blk -> Blk, +k: B.Octets, +iv: B.Octets, +p: B.Octets, +c: B.Octets) -> String:
  +r = key(k)
  two(res(Result.bind(&2, &2, Cr.CrError, K, B.Octets, r, kk => Md.CrCbc.encrypt(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, kk, iv, p))), res(Result.bind(&2, &2, Cr.CrError, K, B.Octets, r, kk => Md.CrCbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, kk, iv, c))))

def ctr.two(~S: Data, ~update: S -> B.Octets -> St.CrXorOut<S>, o: St.CrXorOut<S>, b: B.Octets) -> B.Octets:
  match o:
    case St.CrXorOut{s, d}:
      B.Octets.append(d, St.CrXor.out_data(~S, update(s, b)))

# CTR as a stream cipher, the message in two pieces
def ctr(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: B.Octets, +iv: B.Octets, +a: B.Octets, +b: B.Octets) -> String:
  res(Result.map(&2, &2, Cr.CrError, Md.CrCtrState<K>, B.Octets, +s => ctr.two(~Md.CrCtrState<K>, ~Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to), Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, a), b), Md.CrCtr.start(~K, ~bsize, ~key, k, iv)))

def rc4.two(+o: R.LcRc4Out, b: B.Octets) -> B.Octets:
  B.Octets.append(R.LcRc4.out_data(o), R.LcRc4.out_data(R.LcRc4.update(R.LcRc4.out_state(o), b)))

# RC4 through the stream interface, the data in two pieces
def rc4(+k: B.Octets, +a: B.Octets, +b: B.Octets) -> String:
  res(Result.map(&2, &2, Cr.CrError, R.LcRc4State, B.Octets, +s => rc4.two(R.LcRc4.update(s, a), b), RC.CrRc4.start(k, B.Octets.empty())))

# a MAC: the tag, whether verify accepts it, and whether verify accepts bad
def mac.go(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~verify: K -> B.Octets -> B.Octets -> Bool, r: Result<&2, &2, Cr.CrError, K>, +m: B.Octets, +bad: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{+k}:
      two(B.Octets.hex(compute(k, m)), two(yn(verify(k, m, compute(k, m))), yn(verify(k, m, bad))))

def mac(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~compute: K -> B.Octets -> B.Octets, ~verify: K -> B.Octets -> B.Octets -> Bool, +k: B.Octets, +m: B.Octets, +bad: B.Octets) -> String:
  mac.go(~K, ~compute, ~verify, key(k), m, bad)

# an AEAD: sealed, opened, and opened with a changed tag, ciphertext byte and
# associated-data byte
def aead(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~seal: K -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~open: K -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: B.Octets, +n: B.Octets, +a: B.Octets, +a2: B.Octets, +p: B.Octets, +c: B.Octets, +c1: B.Octets, +c2: B.Octets) -> String:
  two(res(Ae.CrAead.seal_with(~K, ~key, ~seal, k, n, a, p)), two(res(Ae.CrAead.open_with(~K, ~key, ~open, k, n, a, c)), two(res(Ae.CrAead.open_with(~K, ~key, ~open, k, n, a, c1)), two(res(Ae.CrAead.open_with(~K, ~key, ~open, k, n, a, c2)), res(Ae.CrAead.open_with(~K, ~key, ~open, k, n, a2, c))))))

# a hash: one-shot, and in two pieces
def hash(~H: Data, ~bsize: Nat, ~dsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, +a: B.Octets, +b: B.Octets) -> String:
  two(B.Octets.hex(digest(B.Octets.append(a, b))), B.Octets.hex(final(update(update(init, a), b))))

# HMAC over a hash: one-shot, in two pieces, verify of the tag
def hmac(~H: Data, ~bsize: Nat, ~dsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, +k: B.Octets, +a: B.Octets, +b: B.Octets) -> String:
  +kk = Hm.CrHmac.key(~bsize, ~digest, k)
  +t = Hm.CrHmac.mac(~digest, kk, B.Octets.append(a, b))
  two(B.Octets.hex(t), two(B.Octets.hex(Hm.CrHmac.finish(~H, ~init, ~update, ~final, Hm.CrHmac.update(~H, ~update, Hm.CrHmac.update(~H, ~update, Hm.CrHmac.start(~H, ~init, ~update, kk), a), b))), yn(Hm.CrHmac.verify(~digest, kk, B.Octets.append(a, b), t))))

def hkdf(~H: Data, ~bsize: Nat, ~dsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, +ikm: B.Octets, +salt: B.Octets, +info: B.Octets, n: Nat) -> String:
  res(Hk.CrHkdf.derive(~bsize, ~dsize, ~digest, ikm, salt, info, n))

# PBKDF2 over HMAC over a hash
def pbkdf2(~H: Data, ~bsize: Nat, ~dsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, +p: B.Octets, +salt: B.Octets, c: U32, n: Nat) -> String:
  res(Pb.CrPbkdf2.pbkdf2(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~bsize, ~digest), ~Hm.CrHmac.mac(~digest), ~dsize, p, salt, c, n))
'''


def main():
    self_checks()
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    lines, expect, counts = [], [], {"cryptography": 0, "model": 0, "python": 0, "hsmodel": 0}

    def case(name, k, call, want, src):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, k, call))
        expect.append("%s %d %s" % (name, k, want))
        counts[src] += 1

    for name, (bs, enc, _) in CIPHERS.items():
        src = "cryptography" if name in LIB else "model"
        dec = (lambda kk, cc, n=name: lib_ecb(tdes if n in ("des", "tdes") else {"aes": algorithms.AES, "sm4": algorithms.SM4, "camellia": algorithms.Camellia}[n], kk, cc, False)) if name in LIB else None
        for i, kl in enumerate(KEYS[name] * (2 if len(KEYS[name]) < 3 else 1)):
            key, p, c2 = rb(kl), rb(bs), rb(bs)
            want_p = dec(key, c2).hex() if dec else (lcm.serpent_decrypt if name == "serpent" else lcm.twofish_decrypt)(key, c2).hex()
            case("%s_block" % name, i, "blk(%s, %s, %s, %s)" % (tmpl(name, [0, 1, 3, 4, 5, 6, 7]), o(key), o(p), o(c2)),
                 "%s %s" % (enc(key, p).hex(), want_p), src)
        for i in range(3):  # ECB and CBC, whole blocks (0 to 5, and 20)
            key, iv = rb(KEYS[name][i % len(KEYS[name])]), rb(bs)
            nb = [0, rng.randrange(1, 6), 20][i]
            p, c2 = rb(bs * nb), rb(bs * nb)
            dec_ecb = (lambda kk, cc: ecb(lambda k3, b3: (lcm.serpent_decrypt if name == "serpent" else lcm.twofish_decrypt)(k3, b3), kk, cc, bs)) if name not in LIB else None
            if name in LIB:
                alg = tdes if name in ("des", "tdes") else {"aes": algorithms.AES, "sm4": algorithms.SM4, "camellia": algorithms.Camellia}[name]
                we, wd = lib_ecb(alg, key, p), lib_ecb(alg, key, c2, False)
                cc = Cipher(alg(key), modes.CBC(iv)); e = cc.encryptor(); wce = e.update(p) + e.finalize()
                d = cc.decryptor(); wcd = d.update(c2) + d.finalize()
            else:
                we, wd = ecb(enc, key, p, bs), dec_ecb(key, c2)
                wce = cbc(enc, key, iv, p, bs)
                dfn = lcm.serpent_decrypt if name == "serpent" else lcm.twofish_decrypt
                wcd, prev = b"", iv
                for j in range(0, len(c2), bs):
                    wcd += xor(dfn(key, c2[j:j + bs]), prev); prev = c2[j:j + bs]
            case("%s_ecb" % name, i, "ecb(%s, %s, %s, %s)" % (tmpl(name, [0, 1, 2, 3, 4, 5, 6, 7]), o(key), o(p), o(c2)), "%s %s" % (we.hex(), wd.hex()), src)
            case("%s_cbc" % name, i, "cbc(%s, %s, %s, %s, %s)" % (CIPHERS[name][2], o(key), o(iv), o(p), o(c2)), "%s %s" % (wce.hex(), wcd.hex()), src)
        for i in range(3):  # CTR, any length, in two pieces; a counter near its wrap
            key = rb(KEYS[name][i % len(KEYS[name])])
            iv = rb(bs) if i < 2 else b"\xff" * (bs - 1) + b"\xfe"
            m = rb(rng.randrange(0, 3 * bs + 5))
            cut = rng.randrange(0, len(m) + 1)
            case("%s_ctr" % name, i, "ctr(%s, %s, %s, %s, %s)" % (tmpl(name, [0, 1, 2, 3, 4, 6, 7]), o(key), o(iv), o(m[:cut]), o(m[cut:])),
                 ctr(enc, key, iv, m, bs).hex(), src)

    for i in range(10):  # RC4, keys of 1 to 256 bytes
        kl = [5, 7, 8, 10, 16, 20, 24, 32, 1, 256][i]
        key, m = rb(kl), rb(rng.randrange(0, 90))
        cut = rng.randrange(0, len(m) + 1)
        if kl in (5, 7, 8, 10, 16, 20, 24, 32):
            x = Cipher(algorithms.ARC4(key), mode=None).encryptor()
            want, src = x.update(m) + x.finalize(), "cryptography"
        else:
            want, src = xor(m, lcm.rc4_keystream(key, len(m))), "model"
        case("rc4", i, "rc4(%s, %s, %s)" % (o(key), o(m[:cut]), o(m[cut:])), want.hex(), src)

    for name in ["aes", "sm4", "camellia", "serpent", "twofish"]:  # CMAC
        for i in range(3):
            key = rb(KEYS[name][i % len(KEYS[name])])
            m = rb([0, 16, rng.randrange(1, 70)][i])
            t = None
            if name in LIB:
                try:
                    c = ccmac.CMAC({"aes": algorithms.AES, "sm4": algorithms.SM4, "camellia": algorithms.Camellia}[name](key))
                    c.update(m)
                    t, src = c.finalize(), "cryptography"
                except Exception:
                    t, src = cmac(CIPHERS[name][1], key, m), "python"
            if t is None:
                t, src = cmac(CIPHERS[name][1], key, m), "model"
            bad = t[:-1] + bytes([t[-1] ^ 1])
            K, key_fn, encf = tmpl(name, [0]), tmpl(name, [3]), tmpl(name, [4])
            mt = "%s, %s, ~CMI.CrCmac.mac(%s, %s), ~CMI.CrCmac.verify(%s, %s)" % (K, key_fn, K, encf, K, encf)
            case("%s_cmac" % name, i, "mac(%s, %s, %s, %s)" % (mt, o(key), o(m), o(bad)), "%s yes no" % t.hex(), src)

    for name in ["aes", "sm4", "camellia", "serpent", "twofish"]:  # CCM
        for i in range(6 if name == "aes" else 2):
            key = rb(KEYS[name][i % len(KEYS[name])])
            tlen, nl = [(16, 13), (8, 7), (4, 12), (10, 11), (12, 8), (14, 13)][i]
            nonce, aad, p = rb(nl), rb(rng.randrange(0, 30)), rb(rng.randrange(0, 50))
            if name == "aes":
                c, src = AESCCM(key, tlen).encrypt(nonce, p, aad), "cryptography"
            else:
                c, src = ccm(CIPHERS[name][1], key, nonce, aad, p, tlen), "cryptography" if name in LIB else "model"
            c1 = c[:-1] + bytes([c[-1] ^ 1])  # the tag changed
            c2 = (bytes([c[0] ^ 128]) + c[1:]) if p else c1  # a ciphertext byte changed
            a2 = (aad[:-1] + bytes([aad[-1] ^ 4])) if aad else b"\x00"
            K, key_fn, encf = tmpl(name, [0]), tmpl(name, [3]), tmpl(name, [4])
            at = "%s, %s, ~CC.CrCcm.seal(%s, %s, ~%dn), ~CC.CrCcm.open(%s, %s, ~%dn)" % (K, key_fn, K, encf, tlen, K, encf, tlen)
            case("%s_ccm" % name, i, "aead(%s, %s, %s, %s, %s, %s, %s, %s, %s)" % (at, o(key), o(nonce), o(aad), o(a2), o(p), o(c), o(c1), o(c2)),
                 "%s %s fail fail fail" % (c.hex(), p.hex()), src)

    for name, (Hc, ht) in HASHES.items():  # the hashes, HMAC and HKDF over them
        for i in range(4):
            a, b = rb(rng.randrange(0, 40)), rb(rng.randrange(0, 40))
            d = Hc(a + b).digest().hex()
            case("%s_hash" % name, i, "hash(%s, %s, %s)" % (ht, o(a), o(b)), "%s %s" % (d, d), "python")
        for i in range(6):
            key = rb([0, 3, 32, 64, 65, 200][i])
            a, b = rb(rng.randrange(0, 50)), rb(rng.randrange(0, 50))
            t = hmac.new(key, a + b, Hc).digest().hex()
            case("%s_hmac" % name, i, "hmac(%s, %s, %s, %s)" % (ht, o(key), o(a), o(b)), "%s %s yes" % (t, t), "python")
        for i in range(3):
            ikm, salt, info = rb(rng.randrange(1, 40)), rb([0, 8, 70][i]), rb(rng.randrange(0, 20))
            n = [1, Hc().digest_size * 3 + 1, rng.randrange(1, 60)][i]
            if name in SHA:
                want, src = HKDF(SHA[name](), n, salt or None, info).derive(ikm), "cryptography"
            else:
                want, src = hkdf(Hc, ikm, salt, info, n), "python"
            case("%s_hkdf" % name, i, "hkdf(%s, %s, %s, %s, %dn)" % (ht, o(ikm), o(salt), o(info), n), want.hex(), src)

    for name, (Hc, src, ht) in HS.items():  # the hashes package's hashes, and HMAC over them
        for i in range(4):
            a, b = rb(rng.randrange(0, 90)), rb(rng.randrange(0, 90))
            d = Hc(a + b).digest().hex()
            case("%s_hash" % name, i, "hash(%s, %s, %s)" % (ht, o(a), o(b)), "%s %s" % (d, d), src)
        for i in range(4):
            key = rb([0, 20, 64, 100][i])
            a, b = rb(rng.randrange(0, 70)), rb(rng.randrange(0, 70))
            t = hmac.new(key, a + b, Hc).digest().hex()
            case("%s_hmac" % name, i, "hmac(%s, %s, %s, %s)" % (ht, o(key), o(a), o(b)), "%s %s yes" % (t, t), src)
    mt = "~Hs.HsW2, ~MIC.CrMichael.key, ~HMI.HsMichael.mic, ~MIC.CrMichael.verify"
    for i in range(6):  # Michael
        key, m = rb(8), rb([0, 1, 3, 4, 31, rng.randrange(5, 100)][i])
        t = hsm.michael(key, m)
        bad = bytes([t[0] ^ 1]) + t[1:]
        case("michael_mac", i, "mac(%s, %s, %s, %s)" % (mt, o(key), o(m), o(bad)), "%s yes no" % t.hex(), "hsmodel")
    for name in ["sha1", "sha256", "md5", "ripemd160", "sm3"]:  # PBKDF2
        ht = HASHES["sha256"][1] if name == "sha256" else HS[name][2]
        dsize = hashlib.new(name).digest_size
        for i in range(3):
            pw, salt = rb(rng.randrange(0, 80)), rb(rng.randrange(0, 20))
            c, n = [1, 2, rng.randrange(3, 40)][i], [1, dsize + 1, rng.randrange(2 * dsize, 3 * dsize + 5)][i]
            want = hashlib.pbkdf2_hmac(name, pw, salt, c, n)
            src = "python"
            if name in ("sha1", "sha256"):
                assert PBKDF2HMAC({"sha1": hashes.SHA1, "sha256": hashes.SHA256}[name](), n, salt, c).derive(pw) == want
                src = "cryptography"
            case("%s_pbkdf2" % name, i, "pbkdf2(%s, %s, %s, %d, %dn)" % (ht, o(pw), o(salt), c, n), want.hex(), src)

    with open(os.path.join(HERE, "cases.bend"), "w", newline="\n") as f:
        f.write(HEADER + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(HERE, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d from cryptography or this file's modes over its ciphers, %d from legacy-ciphers' models, %d from Python's hashlib, hmac and binascii and this file's CRCs, %d from hashes' models)"
          % (len(lines), counts["cryptography"], counts["model"], counts["python"], counts["hsmodel"]))


if __name__ == "__main__":
    main()
