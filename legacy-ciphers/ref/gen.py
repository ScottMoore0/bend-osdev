#!/usr/bin/env python3
"""Differential test cases for bend-osdev-legacy-ciphers.

Writes ref/cases.bend (a Bend program printing each cipher's output on each
case) and ref/expected.txt (the same values from implementations outside the
package):
  * DES, 3DES, SM4, Camellia, Blowfish, CAST-128, RC4: Python's
    cryptography package (OpenSSL), when it is installed and has the cipher
    (DES as TripleDES with K1 = K2 = K3); and always the models in model.py;
  * ARIA: the openssl command (OpenSSL's ARIA), when it is installed; and
    always model.py;
  * Serpent, Twofish, CAST-256, TEA, XTEA, FCrypt: the models in model.py
    only (neither cryptography nor OpenSSL has them). model.py was written
    here from the specifications, by the same author as the package; it is
    first checked against the specifications' published vectors (TEA and
    XTEA have none: their model is checked only against itself, decryption
    against encryption, and against the Bend package).
Each block cipher is run both ways, on single blocks and in CBC through
cipher-modes (128-bit ciphers) or modes64.bend (DES, 3DES).
"""
import os, random, subprocess, sys, warnings

import model as m

try:
    warnings.simplefilter("ignore")
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
except Exception:
    Cipher = None


def lib(name, key, mode, iv, data):
    """cryptography's result (mode "ecb", "cbc" or "stream"), or None when it
    is missing or lacks the cipher."""
    if Cipher is None:
        return None
    try:
        alg = {"tdes": algorithms.TripleDES, "sm4": algorithms.SM4,
               "camellia": algorithms.Camellia, "arc4": algorithms.ARC4,
               "blowfish": algorithms.Blowfish, "cast5": algorithms.CAST5}[name](key)
        md = {"ecb": lambda: modes.ECB(), "cbc": lambda: modes.CBC(iv), "stream": lambda: None}[mode]()
        x = Cipher(alg, md).encryptor()
        return x.update(data) + x.finalize()
    except Exception:
        return None


def openssl_aria(key, mode, iv, data):
    """the openssl command's ARIA (mode "ecb" or "cbc", no padding), or None
    when it is missing"""
    cmd = ["openssl", "enc", "-aria-%d-%s" % (8 * len(key), mode), "-K", key.hex(), "-nopad"]
    if iv is not None:
        cmd += ["-iv", iv.hex()]
    try:
        r = subprocess.run(cmd, input=data, capture_output=True, check=True)
        return r.stdout
    except Exception:
        return None


LIB_CHECKS = []


def agree(model_value, lib_value, what):
    if lib_value is not None:
        assert model_value == lib_value, "model disagrees with cryptography: " + what
        LIB_CHECKS.append(what)
    return model_value


def check_vectors():
    h = bytes.fromhex
    assert m.des_encrypt(h("0101010101010101"), h("8000000000000000")) == h("95F8A5E5DD31D900")
    assert m.tdes_encrypt(h("0123456789ABCDEF23456789ABCDEF01456789ABCDEF0123"), b"The qufc") == h("A826FD8CE53B855F")
    k = h("0123456789abcdeffedcba9876543210")
    assert m.sm4_encrypt(k, k) == h("681EDF34D206965E86B3E94F536E4246")
    assert m.camellia_encrypt(k, k) == h("67673138549669730857065648EABE43")
    assert m.serpent_encrypt(bytes(16), bytes(16)) == h("3620B17AE6A993D09618B8768266BAE9")
    assert m.serpent_encrypt(h("80" + "00" * 15), bytes(16)) == h("264E5481EFF42A4606ABDA06C0BFDA3D")
    assert m.twofish_encrypt(bytes(16), bytes(16)) == h("9F589F5CF6122C32B6BFEC2F2AE8C35A")
    assert m.rc4_keystream(h("0102030405"), 16) == h("B2396305F03DC027CCC3524A0A1118A8")
    # RFC 5794, Appendix A
    p = h("00112233445566778899aabbccddeeff")
    for k, c in [("000102030405060708090a0b0c0d0e0f", "d718fbd6ab644c739da95f3be6451778"),
                 ("000102030405060708090a0b0c0d0e0f1011121314151617", "26449c1805dbe7aa25a468ce263a9e79"),
                 ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", "f92bd7c79fb72e2f2b8f80c1972d24fc")]:
        assert m.aria_encrypt(h(k), p) == h(c) and m.aria_decrypt(h(k), h(c)) == p
    # RFC 2612, Appendix A
    for k, c in [("2342bb9efa38542c0af75647f29f615d", "c842a08972b43d20836c91d1b7530f6b"),
                 ("2342bb9efa38542cbed0ac83940ac298bac77a7717942863", "1b386c0210dcadcbdd0e41aa08a7a7e8"),
                 ("2342bb9efa38542cbed0ac83940ac2988d7c47ce264908461cc1b5137ae6b604", "4f6a2038286897b9c9870136553317fa")]:
        assert m.cast6_encrypt(h(k), bytes(16)) == h(c) and m.cast6_decrypt(h(k), h(c)) == bytes(16)
    # RFC 2144, Appendix B.1
    for k, c in [("0123456712345678234567893456789A", "238B4FE5847E44B2"), ("01234567123456782345", "EB6A711A2C02271B"),
                 ("0123456712", "7AC816D16E9B302E")]:
        assert m.cast5_encrypt(h(k), h("0123456789ABCDEF")) == h(c) and m.cast5_decrypt(h(k), h(c)) == h("0123456789ABCDEF")
    # Schneier's Blowfish vectors (Eric Young's set)
    for k, pt, c in [("0000000000000000", "0000000000000000", "4EF997456198DD78"),
                     ("FFFFFFFFFFFFFFFF", "FFFFFFFFFFFFFFFF", "51866FD5B85ECB8A"),
                     ("3000000000000000", "1000000000000001", "7D856F9A613063F2"),
                     ("FEDCBA9876543210", "0123456789ABCDEF", "0ACEAB0FC6A0A28D"),
                     ("F0E1D2C3B4A5968778695A4B3C2D1E0F0011223344556677", "FEDCBA9876543210", "05044B62FA52D080")]:
        assert m.blowfish_encrypt(h(k), h(pt)) == h(c) and m.blowfish_decrypt(h(k), h(c)) == h(pt)
    # the FCrypt specification's vectors (the third, PCBC, is crypto's)
    assert m.fcrypt_encrypt(bytes(8), bytes(8)) == h("0E0900C73EF7ED41")
    assert m.fcrypt_encrypt(h("114477AADD003366"), h("123456789ABCDEF0")) == h("D8ED787477EC0680")
    # the transcribed CAST-128 S-boxes, every entry, against cryptography:
    # 1500 random keys and blocks make about 450,000 lookups in S5 .. S8 and
    # 96,000 in S1 .. S4, so every entry is reached with overwhelming
    # probability
    if Cipher is not None:
        rng = random.Random(1)
        for _ in range(1500):
            k, b = bytes(rng.randrange(256) for _ in range(16)), bytes(rng.randrange(256) for _ in range(8))
            agree(m.cast5_encrypt(k, b), lib("cast5", k, "ecb", None, b), "cast5 S-boxes")


def cbc(enc, key, iv, data, bs):
    out, prev = b"", iv
    for i in range(0, len(data), bs):
        prev = enc(key, bytes(a ^ b for a, b in zip(data[i:i + bs], prev)))
        out += prev
    return out


def octets(data):
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"


HEADER = """import Base
import ../../bytes/bytes.bend as B
import ../../cipher-modes/cipher-modes.bend as M
import ../../cipher-modes/cbc.bend as CB
import ../legacy-ciphers.bend as L
import ../des.bend as D
import ../tdes.bend as T
import ../sm4.bend as S
import ../camellia.bend as C
import ../serpent.bend as P
import ../twofish.bend as F
import ../aria.bend as A
import ../cast6.bend as C6
import ../blowfish.bend as BF
import ../cast5.bend as C5
import ../tea.bend as TE
import ../xtea.bend as XT
import ../fcrypt.bend as FC
import ../rc4.bend as R
import ../modes64.bend as X

def show(r: Result<&2, &2, L.LcError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{o}:
      B.Octets.hex(o)

def show_cm(r: Result<&2, &2, M.CmError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{o}:
      B.Octets.hex(o)

def b128.of(m: Maybe<&2, M.CmBlock>) -> M.CmBlock:
  match m:
    case None{}:
      M.CmBlock.zero()
    case Some{b}:
      b

def b128(o: B.Octets) -> M.CmBlock:
  b128.of(M.CmBlock.of_octets(o))

def b64.of(m: Maybe<&2, L.LcBlock64>) -> L.LcBlock64:
  match m:
    case None{}:
      L.LcBlock64.zero()
    case Some{b}:
      b

def b64(o: B.Octets) -> L.LcBlock64:
  b64.of(L.LcBlock64.of_octets(o))
"""

# one helper per 128-bit cipher: the block both ways, and CBC both ways
CIPHER128 = """
def NAME.go(r: Result<&2, &2, L.LcError, KEY>, +b: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "badkey"
    case Done{+k}:
      +c = MOD.encrypt(k, b128(b))
      +cm = CB.Cbc.encrypt(~KEY, ~MOD.encrypt, k, iv, m)
      M.CmBlock.hex(c) ++ " " ++ M.CmBlock.hex(MOD.decrypt(k, c)) ++ " " ++ show_cm(cm) ++ " " ++ show_cm(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, cm, x => CB.Cbc.decrypt(~KEY, ~MOD.decrypt, k, iv, x)))

def NAME(key: B.Octets, +b: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  NAME.go(KEYFN(key), b, iv, m)
"""

CIPHER64 = """
def NAME.go(r: Result<&2, &2, L.LcError, KEY>, +b: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "badkey"
    case Done{+k}:
      +c = MOD.encrypt(k, b64(b))
      +cm = X.Lc64.cbc_encrypt(~KEY, ~MOD.encrypt, k, iv, m)
      L.LcBlock64.hex(c) ++ " " ++ L.LcBlock64.hex(MOD.decrypt(k, c)) ++ " " ++ show(cm) ++ " " ++ show(Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, cm, x => X.Lc64.cbc_decrypt(~KEY, ~MOD.decrypt, k, iv, x)))

def NAME(key: B.Octets, +b: B.Octets, +iv: B.Octets, +m: B.Octets) -> String:
  NAME.go(KEYFN(key), b, iv, m)
"""

RC4 = """
def rc4.go(r: Result<&2, &2, L.LcError, R.LcRc4State>, +a: B.Octets, +b: B.Octets) -> String:
  match r:
    case Fail{e}:
      "badkey"
    case Done{+st}:
      +o = R.LcRc4.update(st, a)
      B.Octets.hex(R.LcRc4.out_data(R.LcRc4.update(st, B.Octets.append(a, b)))) ++ " " ++ B.Octets.hex(B.Octets.append(R.LcRc4.out_data(o), R.LcRc4.out_data(R.LcRc4.update(R.LcRc4.out_state(o), b))))

def rc4(key: B.Octets, drop: Nat, +a: B.Octets, +b: B.Octets) -> String:
  rc4.go(R.LcRc4.start_drop(key, drop), a, b)
"""


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    check_vectors()
    defs = [HEADER]
    for name, key, mod, keyfn in [("sm4", "S.LcSm4Key", "S.LcSm4", "S.LcSm4.key"),
                                  ("camellia", "C.LcCamelliaKey", "C.LcCamellia", "C.LcCamellia.key"),
                                  ("serpent", "P.LcSerpentKey", "P.LcSerpent", "P.LcSerpent.key"),
                                  ("twofish", "F.LcTwofishKey", "F.LcTwofish", "F.LcTwofish.key"),
                                  ("twofish_padded", "F.LcTwofishKey", "F.LcTwofish", "F.LcTwofish.key_padded"),
                                  ("aria", "A.LcAriaKey", "A.LcAria", "A.LcAria.key"),
                                  ("cast6", "C6.LcCast6Key", "C6.LcCast6", "C6.LcCast6.key")]:
        defs.append(CIPHER128.replace("NAME", name).replace("KEYFN", keyfn).replace("KEY", key).replace("MOD", mod))
    for name, key, mod, keyfn in [("des", "D.LcDesKey", "D.LcDes", "D.LcDes.key"), ("tdes", "T.LcTdesKey", "T.LcTdes", "T.LcTdes.key"),
                                  ("blowfish", "BF.LcBlowfishKey", "BF.LcBlowfish", "BF.LcBlowfish.key"),
                                  ("cast5", "C5.LcCast5Key", "C5.LcCast5", "C5.LcCast5.key"),
                                  ("tea", "TE.LcTeaKey", "TE.LcTea", "TE.LcTea.key"),
                                  ("tea_be", "TE.LcTeaKey", "TE.LcTea", "TE.LcTea.key_be"),
                                  ("xtea", "XT.LcXteaKey", "XT.LcXtea", "XT.LcXtea.key"),
                                  ("xtea_be", "XT.LcXteaKey", "XT.LcXtea", "XT.LcXtea.key_be"),
                                  ("fcrypt", "FC.LcFcryptKey", "FC.LcFcrypt", "FC.LcFcrypt.key")]:
        defs.append(CIPHER64.replace("NAME", name).replace("KEYFN", keyfn).replace("KEY", key).replace("MOD", mod))
    defs.append(RC4)
    lines, expect = [], []

    def case(label, expr, value):
        lines.append('    IO.print("%s " ++ %s)' % (label, expr))
        expect.append("%s %s" % (label, value))

    def block_case(name, n, key, enc, dec, libname, blocksize, nblocks):
        b = rb(blocksize)
        iv = rb(blocksize)
        msg = rb(blocksize * nblocks)
        c = enc(key, b)
        libkey = key * 3 if name == "des" else key
        if libname == "aria":
            agree(c, openssl_aria(key, "ecb", None, b), name)
        elif libname is not None:
            agree(c, lib(libname, libkey, "ecb", None, b), name)
        assert dec(key, c) == b
        cc = cbc(enc, key, iv, msg, blocksize)
        if libname == "aria":
            agree(cc, openssl_aria(key, "cbc", iv, msg), name + " cbc")
        elif libname is not None:
            agree(cc, lib(libname, libkey, "cbc", iv, msg), name + " cbc")
        case("%s %d" % (name, n), "%s(%s, %s, %s, %s)" % (name, octets(key), octets(b), octets(iv), octets(msg)),
             "%s %s %s %s" % (c.hex(), b.hex(), cc.hex(), msg.hex()))

    for n in range(12):
        block_case("des", n, rb(8), m.des_encrypt, m.des_decrypt, "tdes", 8, rng.randrange(1, 6))
    for n in range(12):
        block_case("tdes", n, rb(24 if n % 3 else 16), m.tdes_encrypt, m.tdes_decrypt, "tdes", 8, rng.randrange(1, 6))
    for n in range(12):
        block_case("sm4", n, rb(16), m.sm4_encrypt, m.sm4_decrypt, "sm4", 16, rng.randrange(1, 4))
    for n in range(12):
        block_case("camellia", n, rb((16, 24, 32)[n % 3]), m.camellia_encrypt, m.camellia_decrypt, "camellia", 16, rng.randrange(1, 4))
    for n in range(12):
        ks = (16, 24, 32, 0, 5, 20, 31)[n % 7]
        block_case("serpent", n, rb(ks), m.serpent_encrypt, m.serpent_decrypt, None, 16, rng.randrange(1, 3))
    for n in range(9):
        block_case("twofish", n, rb((16, 24, 32)[n % 3]), m.twofish_encrypt, m.twofish_decrypt, None, 16, rng.randrange(1, 3))
    for n in range(9):
        block_case("aria", n, rb((16, 24, 32)[n % 3]), m.aria_encrypt, m.aria_decrypt, "aria", 16, rng.randrange(1, 4))
    for n in range(10):
        block_case("cast6", n, rb((16, 20, 24, 28, 32)[n % 5]), m.cast6_encrypt, m.cast6_decrypt, None, 16, rng.randrange(1, 4))
    for n in range(8):
        block_case("blowfish", n, rb((4, 8, 16, 32, 56, 5, 13, 40)[n]), m.blowfish_encrypt, m.blowfish_decrypt, "blowfish", 8, rng.randrange(1, 6))
    for n in range(12):
        block_case("cast5", n, rb(5 + n % 12), m.cast5_encrypt, m.cast5_decrypt, "cast5", 8, rng.randrange(1, 6))
    for name, enc, dec, order in [("tea", m.tea_encrypt, m.tea_decrypt, "little"), ("tea_be", m.tea_encrypt, m.tea_decrypt, "big"),
                                  ("xtea", m.xtea_encrypt, m.xtea_decrypt, "little"), ("xtea_be", m.xtea_encrypt, m.xtea_decrypt, "big")]:
        for n in range(6):
            block_case(name, n, rb(16), lambda k, b, e=enc, o=order: e(k, b, o), lambda k, b, d=dec, o=order: d(k, b, o), None, 8, rng.randrange(1, 6))
    for n in range(10):
        block_case("fcrypt", n, rb(8), m.fcrypt_encrypt, m.fcrypt_decrypt, None, 8, rng.randrange(1, 6))
    for n in range(4):
        ks = (5, 17, 23, 30)[n]
        k = rb(ks)
        full = k + bytes((16 if ks <= 16 else 24 if ks <= 24 else 32) - ks)
        b, iv, msg = rb(16), rb(16), rb(16)
        c = m.twofish_encrypt(full, b)
        cc = cbc(m.twofish_encrypt, full, iv, msg, 16)
        case("twofish_padded %d" % n, "twofish_padded(%s, %s, %s, %s)" % (octets(k), octets(b), octets(iv), octets(msg)),
             "%s %s %s %s" % (c.hex(), b.hex(), cc.hex(), msg.hex()))
    for n in range(16):
        ks = (5, 7, 8, 10, 16, 20, 24, 32, 1, 3, 64, 256)[n % 12]
        k = rb(ks)
        drop = 0 if n < 12 else (1536, 768, 256, 3)[n - 12]
        a, b = rb(rng.randrange(0, 200)), rb(rng.randrange(0, 200))
        stream = m.rc4_keystream(k, len(a) + len(b), drop)
        out = bytes(x ^ y for x, y in zip(a + b, stream))
        if drop == 0:
            agree(out, lib("arc4", k, "stream", None, a + b), "rc4")
        case("rc4 %d" % n, "rc4(%s, %dn, %s, %s)" % (octets(k), drop, octets(a), octets(b)), "%s %s" % (out.hex(), out.hex()))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d results also from cryptography or the openssl command)" % (len(expect), len(LIB_CHECKS)))


main()
