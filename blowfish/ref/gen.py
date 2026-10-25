#!/usr/bin/env python3
"""Differential test cases for bend-osdev-blowfish (Blowfish).

Writes ref/cases.bend (a Bend program printing the cipher's output on each
case) and ref/expected.txt (the same values from implementations outside the
package):
  * Python's cryptography package (OpenSSL), when it is installed and has
    Blowfish; and always the model in model.py.
The cipher is run both ways, on single blocks and in CBC through
modes64.bend (cipher-core).
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
               "camellia": algorithms.Camellia, "arc4": algorithms.ARC4,
               "blowfish": algorithms.Blowfish, "cast5": algorithms.CAST5}[name](key)
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
    # Schneier's Blowfish vectors (Eric Young's set)
    for k, pt, c in [("0000000000000000", "0000000000000000", "4EF997456198DD78"),
                     ("FFFFFFFFFFFFFFFF", "FFFFFFFFFFFFFFFF", "51866FD5B85ECB8A"),
                     ("3000000000000000", "1000000000000001", "7D856F9A613063F2"),
                     ("FEDCBA9876543210", "0123456789ABCDEF", "0ACEAB0FC6A0A28D"),
                     ("F0E1D2C3B4A5968778695A4B3C2D1E0F0011223344556677", "FEDCBA9876543210", "05044B62FA52D080")]:
        assert m.blowfish_encrypt(h(k), h(pt)) == h(c) and m.blowfish_decrypt(h(k), h(c)) == h(pt)


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
import ../../cipher-core/cipher-core.bend as L
import ../../cipher-core/modes64.bend as X
import ../blowfish.bend as BF

def show(r: Result<&2, &2, L.LcError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{o}:
      B.Octets.hex(o)

def b64.of(m: Maybe<&2, L.LcBlock64>) -> L.LcBlock64:
  match m:
    case None{}:
      L.LcBlock64.zero()
    case Some{b}:
      b

def b64(o: B.Octets) -> L.LcBlock64:
  b64.of(L.LcBlock64.of_octets(o))
"""

# the cipher's helper: the block both ways, and CBC both ways
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


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    check_vectors()
    defs = [HEADER]
    for name, key, mod, keyfn in [('blowfish', 'BF.LcBlowfishKey', 'BF.LcBlowfish', 'BF.LcBlowfish.key')]:
        defs.append(CIPHER64.replace("NAME", name).replace("KEYFN", keyfn).replace("KEY", key).replace("MOD", mod))
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

    for n in range(8):
        block_case("blowfish", n, rb((4, 8, 16, 32, 56, 5, 13, 40)[n]), m.blowfish_encrypt, m.blowfish_decrypt, "blowfish", 8, rng.randrange(1, 6))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d results also from cryptography or the openssl command)" % (len(expect), len(LIB_CHECKS)))


main()
