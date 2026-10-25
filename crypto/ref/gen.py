#!/usr/bin/env python3
"""Differential test cases for bend-osdev-crypto: every instance through its
interface, against implementations outside this package.

Writes ref/cases00.bend, cases01.bend, ... (Bend programs printing the
cases through the interfaces, CHUNK cases each, so that each one builds or
runs within a check process's memory) and ref/expected.txt (the same values
from Python, in the same order):
  * block ciphers, one block both ways: AES, DES, 3DES, SM4, Camellia through
    Python's cryptography (OpenSSL; DES as TripleDES with three equal keys);
    Serpent and Twofish through their packages' ref/model.py (written from
    the specifications by those packages' author: cryptography has neither);
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
  * SHA-256 and SHA-512 (bend-collections, through inst_sha2.bend) and
    SHA3-256 (bend-collections, through inst_sha3.bend), one-shot and in
    pieces, against hashlib; HMAC over them (keys of 0 to 200 bytes,
    across the block sizes) against hmac with hashlib;
  * HKDF over SHA-256, SHA-512 and SHA3-256 against cryptography's HKDF,
    and over CRC-32 and CRC-64/XZ against this file's RFC 5869 HKDF on
    Python's hmac, which is first checked against cryptography's HKDF with
    SHA-256 on RFC 5869's test case 1;
  * the newer block ciphers, one block both ways and through ECB, CBC and
    CTR: Blowfish and CAST-128 through cryptography, ARIA through the
    openssl command (aria's model when it is missing), CAST-256,
    TEA, XTEA and FCrypt through their packages' models;
  * PCBC over every cipher, through this file's PCBC over the cipher's block
    function (checked first on the FCrypt specification's PCBC vector);
  * LRW over every 16-byte-block cipher: for AES the Linux kernel's
    lrw(aes) through AF_ALG, and this file's LRW (IEEE P1619 draft, checked
    against Annex B's vectors and against the kernel) for the others, or for
    AES when AF_ALG is missing;
  * CBC-CS3 ciphertext stealing over every cipher: for AES the kernel's
    cts(cbc(aes)), this file's CS3 (checked against RFC 3962's vectors and
    the kernel) for the others; a message shorter than a block refused;
  * XCBC-MAC over the 16-byte-key ciphers and VMAC (64- and 128-bit tags,
    nonces of 1 to 15 bytes) over the 128-bit ones, through the MAC
    interface, against this file's XCBC (checked on RFC 3566's vectors) and
    VMAC (checked on draft-krovetz-vmac-01's) over the cipher's block
    function, with verify accepting the tag and refusing it changed.
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
    three blocks and more;
  * SP 800-108 KDFs over HMAC over SHA-1, SHA-256 and SM3: counter mode
    against cryptography's KBKDFHMAC (counter before the fixed input, the
    counter and L fields of 1, 2 and 4 bytes) for SHA-1 and SHA-256, and
    against this file's SP 800-108 (checked first against KBKDFHMAC) for
    SM3; feedback mode, with and without the counter, against this file's
    SP 800-108 (cryptography has no feedback mode), outputs of 1 byte to
    three blocks and more.
This file's PCBC, LRW, CS3, XCBC, VMAC and SP 800-108 were written from the
specifications by the author of this package's: where they are the only
reference (no outside implementation has the mode or the cipher), they
share that author, and the specifications' own vectors are the outside check.
"""
import binascii, hashlib, hmac, os, random, socket, subprocess, sys, warnings

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
import importlib.util  # noqa: E402
import types  # noqa: E402


def _model(pkg):
    """the ref/model.py of a sibling cipher package"""
    spec = importlib.util.spec_from_file_location("model_" + pkg, os.path.join(HERE, "..", "..", pkg, "ref", "model.py"))
    mod = importlib.util.module_from_spec(spec)
    # each model imports its own package's gen/tables.py as "tables"
    sys.modules.pop("tables", None)
    spec.loader.exec_module(mod)
    sys.modules.pop("tables", None)
    return mod


# the ciphers' models, one per cipher package, under one name
lcm = types.SimpleNamespace(**{k: v for p in ("serpent", "twofish", "aria", "cast6", "blowfish", "cast5", "tea", "xtea", "fcrypt", "rc4")
                               for k, v in vars(_model(p)).items() if not k.startswith("__")})
_spec = importlib.util.spec_from_file_location("hsmodel", os.path.join(HERE, "..", "..", "hashes", "ref", "model.py"))
hsm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hsm)

warnings.simplefilter("ignore")
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes  # noqa: E402
from cryptography.hazmat.primitives.ciphers.aead import AESCCM  # noqa: E402
from cryptography.hazmat.primitives import cmac as ccmac, hashes  # noqa: E402
from cryptography.hazmat.primitives.kdf.hkdf import HKDF  # noqa: E402
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC  # noqa: E402
from cryptography.hazmat.primitives.kdf.kbkdf import KBKDFHMAC, Mode, CounterLocation  # noqa: E402

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


def openssl_aria(key, data, enc=True):
    """the openssl command's ARIA in ECB, no padding (None when missing)"""
    cmd = ["openssl", "enc", "-aria-%d-ecb" % (8 * len(key)), "-K", key.hex(), "-nopad"] + ([] if enc else ["-d"])
    try:
        return subprocess.run(cmd, input=data, capture_output=True, check=True).stdout
    except Exception:
        return None


OPENSSL_ARIA = openssl_aria(bytes(range(16)), bytes.fromhex("00112233445566778899aabbccddeeff")) == bytes.fromhex("d718fbd6ab644c739da95f3be6451778")


def lc128(mod, ty):
    return "~%s.Lc%sKey, ~M.CmBlock, ~16n, ~LC.CrLc.key(~%s.Lc%sKey, ~%s.Lc%s.key), ~%s.Lc%s.encrypt, ~%s.Lc%s.decrypt, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~CM.CrBlk128.xor" % ((mod, ty) * 5)


def lc64(mod, ty):
    return "~%s.Lc%sKey, ~L.LcBlock64, ~8n, ~LC.CrLc.key(~%s.Lc%sKey, ~%s.Lc%s.key), ~%s.Lc%s.encrypt, ~%s.Lc%s.decrypt, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, ~LC.CrBlk64.xor" % ((mod, ty) * 5)


CIPHERS.update({
    "aria": (16, (lambda k, b: openssl_aria(k, b)) if OPENSSL_ARIA else lcm.aria_encrypt, lc128("Ar", "Aria")),
    "cast6": (16, lcm.cast6_encrypt, lc128("C6", "Cast6")),
    "blowfish": (8, lcm.blowfish_encrypt, lc64("Bf", "Blowfish")),
    "cast5": (8, lcm.cast5_encrypt, lc64("C5", "Cast5")),
    "tea": (8, lcm.tea_encrypt, lc64("Te", "Tea")),
    "xtea": (8, lcm.xtea_encrypt, lc64("Xt", "Xtea")),
    "fcrypt": (8, lcm.fcrypt_encrypt, lc64("Fc", "Fcrypt")),
})
KEYS = {"aes": [16, 32], "des": [8], "tdes": [16, 24], "sm4": [16], "camellia": [16, 24, 32],
        "serpent": [16, 24, 32], "twofish": [16, 24, 32], "aria": [16, 24, 32], "cast6": [16, 24, 32],
        "blowfish": [16, 4, 56], "cast5": [5, 10, 16], "tea": [16], "xtea": [16], "fcrypt": [8]}
# the ciphers cryptography has, as its algorithms
ALG = {"aes": algorithms.AES, "des": tdes, "tdes": tdes, "sm4": algorithms.SM4, "camellia": algorithms.Camellia}
for _n, _a in [("blowfish", "Blowfish"), ("cast5", "CAST5")]:
    if getattr(algorithms, _a, None) is not None:
        ALG[_n] = getattr(algorithms, _a)
        CIPHERS[_n] = (8, (lambda k, b, a=ALG[_n]: lib_ecb(a, k, b)), CIPHERS[_n][2])
LIB = set(ALG)
SRC = {n: "cryptography" if n in LIB else ("openssl" if n == "aria" and OPENSSL_ARIA else "model") for n in CIPHERS}
DEC = {n: (lambda k, b, a=ALG[n]: lib_ecb(a, k, b, False)) if n in LIB else getattr(lcm, n + "_decrypt") for n in CIPHERS}
if OPENSSL_ARIA:
    DEC["aria"] = lambda k, b: openssl_aria(k, b, False)


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


def cbc_dec(dec, key, iv, c, bs):
    out, prev = b"", iv
    for i in range(0, len(c), bs):
        out += xor(dec(key, c[i:i + bs]), prev)
        prev = c[i:i + bs]
    return out


def pcbc(f, key, iv, m, bs, enc=True):
    """PCBC: C_i = E(P_i xor V), V = P_i xor C_i (decryption with f = D)"""
    out, v = b"", iv
    for i in range(0, len(m), bs):
        x = m[i:i + bs]
        y = f(key, xor(x, v)) if enc else xor(f(key, x), v)
        out += y
        v = xor(x, y)
    return out


def gfmul(a, b):
    """GF(2^128) as IEEE P1619's LRW takes it: big-endian blocks as numbers,
    the coefficient of x^i bit i, modulo x^128 + x^7 + x^2 + x + 1"""
    r = 0
    for i in range(128):
        if (b >> i) & 1:
            r ^= a << i
    for i in range(254, 127, -1):
        if (r >> i) & 1:
            r ^= 0x87 << (i - 128) | 1 << i
    return r


def lrw(f, key, iv, m):
    """LRW (IEEE P1619 draft): the cipher key then a 16-byte tweak key; the IV
    the first block's index; C_j = E(P_j xor T_j) xor T_j, T_j = K2 (I + j)"""
    ck, t, i0 = key[:-16], int.from_bytes(key[-16:], "big"), int.from_bytes(iv, "big")
    out = b""
    for j in range(0, len(m), 16):
        tw = gfmul(t, (i0 + j // 16) % (1 << 128)).to_bytes(16, "big")
        out += xor(f(ck, xor(m[j:j + 16], tw)), tw)
    return out


def cts_enc(enc, key, iv, m, bs):
    """CBC-CS3 (SP 800-38A Addendum)"""
    if len(m) == bs:
        return enc(key, xor(m, iv))
    n = (len(m) + bs - 1) // bs
    d = len(m) - (n - 1) * bs
    cs = cbc(enc, key, iv, m[:(n - 1) * bs], bs)
    cn = enc(key, xor(m[(n - 1) * bs:] + bytes(bs - d), cs[-bs:]))
    return cs[:-bs] + cn + cs[-bs:][:d]


def cts_dec(dec, key, iv, c, bs):
    if len(c) == bs:
        return xor(dec(key, c), iv)
    n = (len(c) + bs - 1) // bs
    d = len(c) - (n - 1) * bs
    head, cn, cstar = c[:(n - 2) * bs], c[(n - 2) * bs:(n - 1) * bs], c[(n - 1) * bs:]
    z = dec(key, cn)
    cn1 = cstar + z[d:]
    prev = head[-bs:] if head else iv
    return cbc_dec(dec, key, iv, head, bs) + xor(dec(key, cn1), prev) + xor(z[:d], cstar)


def xcbc(enc, key, m, bs=16):
    """XCBC-MAC (RFC 3566) over a cipher whose keys are one block"""
    k1, k2, k3 = enc(key, b"\x01" * bs), enc(key, b"\x02" * bs), enc(key, b"\x03" * bs)
    n = max(1, (len(m) + bs - 1) // bs)
    last = m[(n - 1) * bs:]
    last = xor(last, k2) if len(last) == bs else xor(last + b"\x80" + bytes(bs - 1 - len(last)), k3)
    e = bytes(bs)
    for i in range(n - 1):
        e = enc(k1, xor(m[i * bs:(i + 1) * bs], e))
    return enc(k1, xor(last, e))


M64, P127, P64 = (1 << 64) - 1, (1 << 127) - 1, (1 << 64) - 257


def vmac(enc, k, nonce, m, words):
    """VMAC (draft-krovetz-vmac-01) over a 128-bit block cipher, a tag of
    64 words bits"""
    def kdf(index, nbytes):
        out, i = b"", 0
        while len(out) < nbytes:
            out += enc(k, bytes([index]) + i.to_bytes(15, "big"))
            i += 1
        return out[:nbytes]

    def nh(kw, msg):
        y, w = 0, [int.from_bytes(msg[j:j + 8], "little") for j in range(0, len(msg), 8)]
        for i in range(0, len(w), 2):
            y += ((w[i] + kw[i]) & M64) * ((w[i + 1] + kw[i + 1]) & M64)
        return y & ((1 << 126) - 1)

    def word(it):
        nhk = kdf(128, 128 + 16 * it)[16 * it:16 * it + 128]
        kw = [int.from_bytes(nhk[j:j + 8], "big") for j in range(0, 128, 8)]
        pk = int.from_bytes(kdf(192, 16 * (it + 1))[16 * it:], "big") & 0x1FFFFFFF1FFFFFFF1FFFFFFF1FFFFFFF
        segs = [m[i:i + 128] for i in range(0, len(m), 128)]
        y = pk if not segs else 1
        for sg in segs:
            y = (y * pk + nh(kw, sg + bytes(-len(sg) % 16))) % P127
        y = (y + ((len(m) * 8) % 1024) * (1 << 64)) % P127
        i, found = 0, -1
        while found < it:
            c = kdf(224, 16 * (i + 1))[16 * i:]
            k1, k2 = int.from_bytes(c[:8], "big"), int.from_bytes(c[8:], "big")
            i += 1
            if k1 < P64 and k2 < P64:
                found += 1
        m1, m2 = divmod(y, (1 << 64) - (1 << 32))
        return ((m1 + k1) * (m2 + k2)) % P64

    nv = int.from_bytes(nonce, "big")
    t = enc(k, ((nv & ~1) if words == 1 else nv).to_bytes(16, "big"))
    pad = t[8 * (nv & 1):8 * (nv & 1) + 8] if words == 1 else t
    return b"".join(((int.from_bytes(pad[8 * w:8 * w + 8], "big") + word(w)) & M64).to_bytes(8, "big") for w in range(words))


def afalg(name, key, iv, data, enc=True):
    """the Linux kernel's skcipher name through AF_ALG (None when missing)"""
    try:
        sk = socket.socket(socket.AF_ALG, socket.SOCK_SEQPACKET, 0)
        sk.bind(("skcipher", name))
        sk.setsockopt(socket.SOL_ALG, socket.ALG_SET_KEY, key)
        op, _ = sk.accept()
        op.sendmsg_afalg([data], op=socket.ALG_OP_ENCRYPT if enc else socket.ALG_OP_DECRYPT, iv=iv)
        out = op.recv(len(data))
        op.close(); sk.close()
        return out
    except Exception:
        return None


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
    "sha3_256": (hashlib.sha3_256, "~S3.CrSha3State, ~136n, ~32n, ~S3.CrSha3.init(), ~S3.CrSha3.update, ~S3.CrSha3.final, ~S3.CrSha3.sha3_256"),
}
SHA = {"sha256": hashes.SHA256, "sha512": hashes.SHA512, "sha3_256": hashes.SHA3_256}


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


def self_checks(rng, rb):
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
    aes = CIPHERS["aes"][1]
    # PCBC: the FCrypt specification's vector
    assert pcbc(lcm.fcrypt_encrypt, h("3141592653589793"), h("2718281828459045"), b"this is a test\0\0", 8).hex() == "ad5130bd809dc84f08d66ecb10244654"
    # LRW: IEEE P1619 draft Annex B, vectors 1 and 4
    assert lrw(aes, h("4562ac25f828176d4c268414b5680185258e2a05e73e9d03ee5a830ccc094c87"), h("00000000000000000000000000000001"), b"0123456789ABCDEF").hex() == "f1b273cd65a3df5fe95d489254634eb8"
    assert lrw(aes, h("f8d476ffd646ee6c2384cb1c77d6195dfef1a9f37bbc8d21a79c21f8cb900289a845348ec8c5b5f126f50e76fefd1b1e"), h("00000000000000000000000000000001"), b"0123456789ABCDEF").hex() == "bd06b8e1db98899ec498e491cf1c702b"
    # CBC-CS3: RFC 3962 Appendix B (AES-128, IV zero)
    ck, cm = h("636869636b656e207465726979616b69"), b"I would like the General Gau's Chicken, please, and wonton soup."
    for n, want in [(17, "c6353568f2bf8cb4d8a580362da7ff7f97"), (31, "fc00783e0efdb2c1d445d4c8eff7ed2297687268d6ecccc0c07b25e25ecfe5"),
                    (32, "39312523a78662d5be7fcbcc98ebf5a897687268d6ecccc0c07b25e25ecfe584"),
                    (64, "97687268d6ecccc0c07b25e25ecfe58439312523a78662d5be7fcbcc98ebf5a84807efe836ee89a526730dbc2f7bc8409dad8bbb96c4cdc03bc103e1a194bbd8")]:
        assert cts_enc(aes, ck, bytes(16), cm[:n], 16).hex() == want
        assert cts_dec(lambda k, b: lib_ecb(algorithms.AES, k, b, False), ck, bytes(16), h(want), 16) == cm[:n]
    # XCBC: RFC 3566 test cases 1 and 7
    xk = h("000102030405060708090a0b0c0d0e0f")
    assert xcbc(aes, xk, b"").hex() == "75f0251d528ac01c4573dfd584d79f29"
    assert xcbc(aes, xk, bytes(range(34))).hex() == "becbb3bccdb518a30677d5481fb6b4d8"
    assert xcbc(aes, xk, bytes(1000)).hex() == "f0dafee895db30253761103b5d84528f"
    # VMAC: draft-krovetz-vmac-01's vectors
    for m, t64, t128 in [(b"", "2576be1c56d8b81b", "472766c70f74ed23481d6d7de4e80dac"),
                         (b"abc", "2d376cf5b1813ce5", "4ee815a06a1d71edd36fc75d51188a42"),
                         (b"abc" * 16, "e8421f61d573d298", "09f2c80c8e1007a0c12fae19fe4504ae"),
                         (b"abc" * 100, "4492df6c5cac1bbe", "66438817154850c61d8a412164803bcb")]:
        assert vmac(aes, b"abcdefghijklmnop", b"bcdefghi", m, 1).hex() == t64
        assert vmac(aes, b"abcdefghijklmnop", b"bcdefghi", m, 2).hex() == t128
    # this file's LRW and CS3 against the kernel's, when AF_ALG has them
    for _ in range(6):
        key, iv = rb(rng.choice([32, 48])), rb(16)
        m = rb(16 * rng.randrange(1, 6))
        got = afalg("lrw(aes)", key, iv, m)
        if got is not None:
            KERNEL.add("lrw")
            assert got == lrw(aes, key, iv, m)
        m = rb(rng.randrange(16, 90))
        got = afalg("cts(cbc(aes))", key[:16], iv, m)
        if got is not None:
            KERNEL.add("cts")
            assert got == cts_enc(aes, key[:16], iv, m, 16)


KERNEL = set()  # the modes the kernel had (filled by self_checks)

# cases per program: one program of every case outgrows a check process's
# memory (its native build is killed, and the JavaScript lane then runs out
# near 3 GB)
CHUNK = 80

HEADER = '''# Generated by ref/gen.py; do not edit. Every instance through its interface.
import Base
import ../../bytes/bytes.bend as B
import ../../word64/word64.bend as W
import ../../cipher-modes/cipher-modes.bend as M
import ../../cipher-modes/aes.bend as X
import ../../cipher-core/cipher-core.bend as L
import ../../des/des.bend as D
import ../../des/tdes.bend as T
import ../../sm4/sm4.bend as S
import ../../camellia/camellia.bend as Ca
import ../../serpent/serpent.bend as Sp
import ../../twofish/twofish.bend as Tf
import ../../rc4/rc4.bend as R
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
import ../inst_sha3.bend as S3
import ../pcbc.bend as Pc
import ../lrw.bend as Lw
import ../cts.bend as Ct
import ../xcbc.bend as Xc
import ../vmac.bend as Vm
import ../../aria/aria.bend as Ar
import ../../cast6/cast6.bend as C6
import ../../blowfish/blowfish.bend as Bf
import ../../cast5/cast5.bend as C5
import ../../tea/tea.bend as Te
import ../../xtea/xtea.bend as Xt
import ../../fcrypt/fcrypt.bend as Fc
import ../inst_michael.bend as MIC
import ../pbkdf2.bend as Pb
import ../kbkdf.bend as Kb
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

def pcbc(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~bxor: Blk -> Blk -> Blk, +k: B.Octets, +iv: B.Octets, +p: B.Octets, +c: B.Octets) -> String:
  +r = key(k)
  two(res(Result.bind(&2, &2, Cr.CrError, K, B.Octets, r, kk => Pc.CrPcbc.encrypt(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, kk, iv, p))), res(Result.bind(&2, &2, Cr.CrError, K, B.Octets, r, kk => Pc.CrPcbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, kk, iv, c))))

def lrw(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~bxor: Blk -> Blk -> Blk, +k: B.Octets, +iv: B.Octets, +p: B.Octets, +c: B.Octets) -> String:
  +r = Lw.CrLrw.key(~K, ~key, k)
  two(res(Result.bind(&2, &2, Cr.CrError, Lw.CrLrwKey<K>, B.Octets, r, kk => Lw.CrLrw.encrypt(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, kk, iv, p))), res(Result.bind(&2, &2, Cr.CrError, Lw.CrLrwKey<K>, B.Octets, r, kk => Lw.CrLrw.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, kk, iv, c))))

def cts(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: B.Octets, +iv: B.Octets, +p: B.Octets, +c: B.Octets) -> String:
  +r = key(k)
  two(res(Result.bind(&2, &2, Cr.CrError, K, B.Octets, r, kk => Ct.CrCts.encrypt(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, iv, p))), res(Result.bind(&2, &2, Cr.CrError, K, B.Octets, r, kk => Ct.CrCts.decrypt(~K, ~Blk, ~bsize, ~dec, ~blk_of, ~blk_to, kk, iv, c))))

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

def kbc(~H: Data, ~bsize: Nat, ~dsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, ~rlen: Nat, ~llen: Nat, ki: B.Octets, label: B.Octets, context: B.Octets, +n: Nat) -> String:
  res(Kb.CrKbkdf.counter_kdf(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~bsize, ~digest), ~Hm.CrHmac.mac(~digest), ~dsize, ~rlen, ~llen, ki, label, context, n))

def kbf(~H: Data, ~bsize: Nat, ~dsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, ~rlen: Nat, ~llen: Nat, ki: B.Octets, iv: B.Octets, label: B.Octets, context: B.Octets, +n: Nat) -> String:
  res(Kb.CrKbkdf.feedback_kdf(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~bsize, ~digest), ~Hm.CrHmac.mac(~digest), ~dsize, ~rlen, ~llen, ki, iv, label, context, n))
'''


# SP 800-108r1-upd1, sections 4.1 (counter) and 4.2 (feedback): fixed input
# Label || 0x00 || Context || [L]_2, the counter r bits (rlen bytes; 0 in
# feedback mode leaves it out), L in llen bytes
def kbkdf(name, ki, label, context, n, rlen, llen, iv=None):
    fixed = label + b"\0" + context + (8 * n).to_bytes(llen, "big")
    out, prev, i = b"", iv, 1
    while len(out) < n:
        ctr = i.to_bytes(rlen, "big") if rlen else b""
        prev = hmac.new(ki, (ctr + fixed) if iv is None else (prev + ctr + fixed), name).digest()
        out += prev
        i += 1
    return out[:n]


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    self_checks(rng, rb)
    lines, expect, counts = [], [], {"cryptography": 0, "model": 0, "python": 0, "openssl": 0, "kernel": 0, "hsmodel": 0}

    def case(name, k, call, want, src):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, k, call))
        expect.append("%s %d %s" % (name, k, want))
        counts[src] += 1

    for name, (bs, enc, _) in CIPHERS.items():
        src, dec = SRC[name], DEC[name]
        for i, kl in enumerate(KEYS[name] * (2 if len(KEYS[name]) < 3 else 1)):
            key, p, c2 = rb(kl), rb(bs), rb(bs)
            case("%s_block" % name, i, "blk(%s, %s, %s, %s)" % (tmpl(name, [0, 1, 3, 4, 5, 6, 7]), o(key), o(p), o(c2)),
                 "%s %s" % (enc(key, p).hex(), dec(key, c2).hex()), src)
        for i in range(3):  # ECB and CBC, whole blocks (0 to 5, and 20)
            key, iv = rb(KEYS[name][i % len(KEYS[name])]), rb(bs)
            nb = [0, rng.randrange(1, 6), 20][i]
            p, c2 = rb(bs * nb), rb(bs * nb)
            if name in LIB:
                alg = ALG[name]
                we, wd = lib_ecb(alg, key, p), lib_ecb(alg, key, c2, False)
                cc = Cipher(alg(key), modes.CBC(iv)); e = cc.encryptor(); wce = e.update(p) + e.finalize()
                d = cc.decryptor(); wcd = d.update(c2) + d.finalize()
            else:
                we, wd = ecb(enc, key, p, bs), ecb(dec, key, c2, bs)
                wce, wcd = cbc(enc, key, iv, p, bs), cbc_dec(dec, key, iv, c2, bs)
            case("%s_ecb" % name, i, "ecb(%s, %s, %s, %s)" % (tmpl(name, [0, 1, 2, 3, 4, 5, 6, 7]), o(key), o(p), o(c2)), "%s %s" % (we.hex(), wd.hex()), src)
            case("%s_cbc" % name, i, "cbc(%s, %s, %s, %s, %s)" % (CIPHERS[name][2], o(key), o(iv), o(p), o(c2)), "%s %s" % (wce.hex(), wcd.hex()), src)
        for i in range(3):  # CTR, any length, in two pieces; a counter near its wrap
            key = rb(KEYS[name][i % len(KEYS[name])])
            iv = rb(bs) if i < 2 else b"\xff" * (bs - 1) + b"\xfe"
            m = rb(rng.randrange(0, 3 * bs + 5))
            cut = rng.randrange(0, len(m) + 1)
            case("%s_ctr" % name, i, "ctr(%s, %s, %s, %s, %s)" % (tmpl(name, [0, 1, 2, 3, 4, 6, 7]), o(key), o(iv), o(m[:cut]), o(m[cut:])),
                 ctr(enc, key, iv, m, bs).hex(), src)
        for i in range(2):  # PCBC
            key, iv = rb(KEYS[name][i % len(KEYS[name])]), rb(bs)
            nb = [rng.randrange(1, 6), 9][i]
            p, c2 = rb(bs * nb), rb(bs * nb)
            case("%s_pcbc" % name, i, "pcbc(%s, %s, %s, %s, %s)" % (CIPHERS[name][2], o(key), o(iv), o(p), o(c2)),
                 "%s %s" % (pcbc(enc, key, iv, p, bs).hex(), pcbc(dec, key, iv, c2, bs, False).hex()), src)
        for i in range(6 if name == "aes" else 2):  # CBC-CS3, 1 to 5 blocks and a bit
            key, iv = rb(KEYS[name][i % len(KEYS[name])]), rb(bs)
            n = [bs, bs + 1, 2 * bs - 1, 2 * bs, rng.randrange(2 * bs + 1, 5 * bs), 5 * bs][i if name == "aes" else i + 1]
            p, c2 = rb(n), rb(n)
            we, wd, msrc = cts_enc(enc, key, iv, p, bs), cts_dec(dec, key, iv, c2, bs), src
            if name == "aes" and "cts" in KERNEL:
                we, wd, msrc = afalg("cts(cbc(aes))", key, iv, p), afalg("cts(cbc(aes))", key, iv, c2, False), "kernel"
            case("%s_cts" % name, i, "cts(%s, %s, %s, %s, %s)" % (tmpl(name, [0, 1, 2, 3, 4, 5, 6, 7]), o(key), o(iv), o(p), o(c2)),
                 "%s %s" % (we.hex(), wd.hex()), msrc)
        if bs != 16:
            continue
        for i in range(4 if name == "aes" else 2):  # LRW, the cipher key then the tweak key
            key = rb(KEYS[name][i % len(KEYS[name])] + 16)
            iv = rb(16) if i % 2 == 0 else b"\xff" * 15 + b"\xfe"
            nb = rng.randrange(1, 6) if i < 2 else 0 if i == 2 else 7
            p, c2 = rb(16 * nb), rb(16 * nb)
            we, wd, msrc = lrw(enc, key, iv, p), lrw(dec, key, iv, c2), src
            if name == "aes" and "lrw" in KERNEL and nb:
                we, wd, msrc = afalg("lrw(aes)", key, iv, p), afalg("lrw(aes)", key, iv, c2, False), "kernel"
            case("%s_lrw" % name, i, "lrw(%s, %s, %s, %s, %s)" % (CIPHERS[name][2], o(key), o(iv), o(p), o(c2)),
                 "%s %s" % (we.hex(), wd.hex()), msrc)
        K0 = tmpl(name, [0])[1:]
        if 16 in KEYS[name]:
            for i in range(6 if name == "aes" else 2):  # XCBC
                key = rb(16)
                m = rb([0, 16, rng.randrange(1, 16), 17, 48, rng.randrange(49, 120)][i if name == "aes" else 4 * i + 1])
                t = xcbc(enc, key, m)
                bad = t[:-1] + bytes([t[-1] ^ 1])
                mt = "~Xc.CrXcbcKey<%s>, ~Xc.CrXcbc.key(%s), ~Xc.CrXcbc.mac(%s), ~Xc.CrXcbc.verify(%s)" % (
                    K0, tmpl(name, [0, 1, 2, 3, 4, 6, 7]), tmpl(name, [0, 1, 2, 4, 6, 7]), tmpl(name, [0, 1, 2, 4, 6, 7]))
                case("%s_xcbc" % name, i, "mac(%s, %s, %s, %s)" % (mt, o(key), o(m), o(bad)), "%s yes no" % t.hex(), src)
        for i in range(8 if name == "aes" else 2):  # VMAC, the nonce before the message
            key = rb(KEYS[name][i % len(KEYS[name])])
            words, nlen = 1 + i % 2, [8, 15, 1, 8, 12, 15, 3, 8][i]
            nonce = rb(nlen)
            m = rb([0, 3, 127, 128, 129, 256, 300, 1000][i] if name == "aes" else rng.randrange(1, 300))
            t = vmac(enc, key, nonce, m, words)
            bad = bytes([t[0] ^ 128]) + t[1:]
            mt = "~Vm.CrVmacKey<%s>, ~Vm.CrVmac.key(%s, ~%dn), ~Vm.CrVmac.mac(%s, ~%dn), ~Vm.CrVmac.verify(%s, ~%dn)" % (
                K0, tmpl(name, [0, 1, 2, 3, 4, 6, 7]), words, tmpl(name, [0, 1, 2, 4, 6, 7]), nlen, tmpl(name, [0, 1, 2, 4, 6, 7]), nlen)
            case("%s_vmac" % name, i, "mac(%s, %s, %s, %s)" % (mt, o(key), o(nonce + m), o(bad)), "%s yes no" % t.hex(), src)

    for i in range(2):  # CBC-CS3 refuses a message shorter than a block
        key, iv, m = rb(16), rb(16), rb([0, 15][i])
        case("aes_cts_short", i, "cts(%s, %s, %s, %s, %s)" % (tmpl("aes", [0, 1, 2, 3, 4, 5, 6, 7]), o(key), o(iv), o(m), o(m)), "fail fail", "python")

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
    for name in ["sha1", "sha256", "sm3"]:  # SP 800-108
        ht = HASHES["sha256"][1] if name == "sha256" else HS[name][2]
        dsize = 32 if name == "sm3" else hashlib.new(name).digest_size
        hn = HS["sm3"][0] if name == "sm3" else name
        for i in range(4):
            ki, label, context = rb(rng.randrange(1, 70)), rb(rng.randrange(0, 20)), rb(rng.randrange(0, 20))
            n = [1, dsize, dsize + 1, rng.randrange(2 * dsize, 3 * dsize + 5)][i]
            rlen, llen = [(4, 4), (1, 2), (2, 4), (4, 1 if 8 * n < 256 else 2)][i]
            want = kbkdf(hn, ki, label, context, n, rlen, llen)
            src = HS["sm3"][1] if name == "sm3" else "cryptography"
            if name != "sm3":
                h = {"sha1": hashes.SHA1, "sha256": hashes.SHA256}[name]()
                assert KBKDFHMAC(h, Mode.CounterMode, n, rlen, llen, CounterLocation.BeforeFixed, label, context, None).derive(ki) == want
            case("%s_kbkdf_counter" % name, i, "kbc(%s, ~%dn, ~%dn, %s, %s, %s, %dn)" % (ht, rlen, llen, o(ki), o(label), o(context), n), want.hex(), src)
            iv = rb([0, dsize, dsize, 5][i])
            frlen = [4, 0, 1, 4][i]
            want = kbkdf(hn, ki, label, context, n, frlen, llen, iv)
            case("%s_kbkdf_feedback" % name, i, "kbf(%s, ~%dn, ~%dn, %s, %s, %s, %s, %dn)" % (ht, frlen, llen, o(ki), o(iv), o(label), o(context), n), want.hex(), "python" if name != "sm3" else HS["sm3"][1])

    for old in os.listdir(HERE):
        if old.startswith("cases") and old.endswith(".bend"):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        with open(os.path.join(HERE, "cases%02d.bend" % (j // CHUNK)), "w", newline="\n") as f:
            f.write(HEADER + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines[j:j + CHUNK]) + "\n")
    with open(os.path.join(HERE, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d from cryptography or this file's modes over its ciphers, %d from the openssl command's ARIA, %d from the Linux kernel's lrw(aes) and cts(cbc(aes)), %d from the cipher packages' models, %d from Python's hashlib, hmac and binascii and this file's CRCs, %d from hashes' models)"
          % (len(lines), counts["cryptography"], counts["openssl"], counts["kernel"], counts["model"], counts["python"], counts["hsmodel"]))


if __name__ == "__main__":
    main()
