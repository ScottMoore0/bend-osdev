#!/usr/bin/env python3
"""Differential test cases for bend-osdev-legacy-ciphers.

Writes ref/cases.bend (a Bend program printing each cipher's output on each
case) and ref/expected.txt (the same values from implementations outside the
package):
  * DES, 3DES, SM4, Camellia, RC4: Python's cryptography package (OpenSSL),
    when it is installed and has the cipher (DES as TripleDES with K1 = K2 =
    K3); and always the models in model.py;
  * Serpent and Twofish: the models in model.py only (cryptography has
    neither). model.py was written here from the specifications, by the same
    author as the package; it is first checked against the specifications'
    published vectors.
Each block cipher is run both ways, on single blocks and in CBC through
cipher-modes (128-bit ciphers) or modes64.bend (DES, 3DES).
"""
import os, random, sys, warnings

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
               "camellia": algorithms.Camellia, "arc4": algorithms.ARC4}[name](key)
        md = {"ecb": lambda: modes.ECB(), "cbc": lambda: modes.CBC(iv), "stream": lambda: None}[mode]()
        x = Cipher(alg, md).encryptor()
        return x.update(data) + x.finalize()
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
                                  ("twofish_padded", "F.LcTwofishKey", "F.LcTwofish", "F.LcTwofish.key_padded")]:
        defs.append(CIPHER128.replace("NAME", name).replace("KEYFN", keyfn).replace("KEY", key).replace("MOD", mod))
    for name, key, mod, keyfn in [("des", "D.LcDesKey", "D.LcDes", "D.LcDes.key"), ("tdes", "T.LcTdesKey", "T.LcTdes", "T.LcTdes.key")]:
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
        if libname is not None:
            agree(c, lib(libname, libkey, "ecb", None, b), name)
        assert dec(key, c) == b
        cc = cbc(enc, key, iv, msg, blocksize)
        if libname is not None:
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
    print("%d cases (%d results also from cryptography)" % (len(expect), len(LIB_CHECKS)))


main()
