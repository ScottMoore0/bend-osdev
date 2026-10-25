#!/usr/bin/env python3
"""Differential test cases for bend-osdev-aria (ARIA).

Writes ref/cases.bend (a Bend program printing the cipher's output on each
case) and ref/expected.txt (the same values from implementations outside the
package):
  * the openssl command (OpenSSL's ARIA), when it is installed; and always
    model.py.
The cipher is run both ways, on single blocks and in CBC through
the cbc package.
"""
import os, random, subprocess, sys

import model as m

Cipher = None


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
    # RFC 5794, Appendix A
    p = h("00112233445566778899aabbccddeeff")
    for k, c in [("000102030405060708090a0b0c0d0e0f", "d718fbd6ab644c739da95f3be6451778"),
                 ("000102030405060708090a0b0c0d0e0f1011121314151617", "26449c1805dbe7aa25a468ce263a9e79"),
                 ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", "f92bd7c79fb72e2f2b8f80c1972d24fc")]:
        assert m.aria_encrypt(h(k), p) == h(c) and m.aria_decrypt(h(k), h(c)) == p


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
import ../../mode-core/mode-core.bend as M
import ../../cbc/cbc.bend as CB
import ../../cipher-core/cipher-core.bend as L
import ../aria.bend as A

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
"""

# the cipher's helper: the block both ways, and CBC both ways
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


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    check_vectors()
    defs = [HEADER]
    for name, key, mod, keyfn in [('aria', 'A.LcAriaKey', 'A.LcAria', 'A.LcAria.key')]:
        defs.append(CIPHER128.replace("NAME", name).replace("KEYFN", keyfn).replace("KEY", key).replace("MOD", mod))
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

    for n in range(9):
        block_case("aria", n, rb((16, 24, 32)[n % 3]), m.aria_encrypt, m.aria_decrypt, "aria", 16, rng.randrange(1, 4))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d results also from cryptography or the openssl command)" % (len(expect), len(LIB_CHECKS)))


main()
