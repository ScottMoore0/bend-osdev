#!/usr/bin/env python3
"""Differential test cases for bend-osdev-rc4 (RC4).

Writes ref/cases.bend (a Bend program printing the cipher's output on each
case) and ref/expected.txt (the same values from implementations outside the
package):
  * Python's cryptography package (ARC4), when it is installed, at the key
    sizes it accepts and with nothing dropped; and always the model in
    model.py.
RC4 is run on random keys of 1 to 256 bytes, on data in two pieces, and
with drop[n].
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
import ../../cipher-core/cipher-core.bend as L
import ../rc4.bend as R


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
