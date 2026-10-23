#!/usr/bin/env python3
"""Differential test cases for bend-osdev-siphash.

Writes ref/casesNN.bend (Bend programs printing each case's output) and
ref/expected.txt (the same values from outside this package):
  * SipHash-2-4, SipHash-1-3, SipHash-4-8 and SipHash-2-4 with the 128-bit
    output: the openssl command (`openssl mac ... SIPHASH`, with its
    c-rounds and d-rounds parameters), an independent implementation;
  * HalfSipHash-2-4, HalfSipHash-1-3 and HalfSipHash-2-4 with the 64-bit
    output: ref/model.py, written here from halfsiphash.c (no outside
    implementation is installed; the published vectors.h, ref/vectors.py,
    check it first, and check.bend runs all 256 of them).
Random keys and messages of 0 to 300 bytes, each hashed in one piece and in
two pieces at a random split. model.py is checked against openssl and
vectors.h before it is used.
"""
import os, random, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from model import siphash, halfsiphash  # noqa: E402
from vectors import SIP64, SIP128, HSIP32, HSIP64  # noqa: E402

PER_FILE = 60


def openssl(key, data, c, d, size):
    out = subprocess.run(["openssl", "mac", "-macopt", "hexkey:" + key.hex(), "-macopt", "size:%d" % size,
                          "-macopt", "c-rounds:%d" % c, "-macopt", "d-rounds:%d" % d, "SIPHASH"],
                         input=data, capture_output=True, check=True)
    return bytes.fromhex(out.stdout.decode().strip())


def lst(data):
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"


SIP = [  # name, Bend parameter set, c, d, wide
    ("sip24", "S.SipParams.sip24()", 2, 4, False),
    ("sip13", "S.SipParams.sip13()", 1, 3, False),
    ("sip48", "S.SipParams.sip48()", 4, 8, False),
    ("sip24w", "S.SipParams.sip24_wide()", 2, 4, True),
]
HSIP = [
    ("hsip24", "H.HalfSipParams.hsip24()", 2, 4, False),
    ("hsip13", "H.HalfSipParams.hsip13()", 1, 3, False),
    ("hsip24w", "H.HalfSipParams.hsip24_wide()", 2, 4, True),
]

HEAD = """import Base
import ../../word64/word64.bend as W
import ../../bytes/bytes.bend as B
import ../siphash.bend as S
import ../halfsiphash.bend as H

def sk(r: Result<&2, &2, S.SipError, S.SipKey>) -> S.SipKey:
  match r:
    case Done{k}:
      k
    case Fail{e}:
      S.SipKey.of_words(W.W64.zero(), W.W64.zero())

def hk(r: Result<&2, &2, S.SipError, H.HsipKey>) -> H.HsipKey:
  match r:
    case Done{k}:
      k
    case Fail{e}:
      H.HsipKey.of_words(0, 0)

def sip2(+p: S.SipParams, +k: S.SipKey, +n: Nat, +m: B.Octets) -> B.Octets:
  S.SipHash.finish(S.SipHash.update(S.SipHash.update(S.SipHash.start(p, k), B.Octets.take(n, m)), B.Octets.drop(n, m)))

def hsip2(+p: S.SipParams, +k: H.HsipKey, +n: Nat, +m: B.Octets) -> B.Octets:
  H.HalfSipHash.finish(H.HalfSipHash.update(H.HalfSipHash.update(H.HalfSipHash.start(p, k), B.Octets.take(n, m)), B.Octets.drop(n, m)))

"""


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    k = bytes(range(16))
    for i in range(64):
        m = bytes(range(i))
        assert siphash(k, m).hex() == SIP64[i] and siphash(k, m, wide=True).hex() == SIP128[i]
        assert halfsiphash(k, m).hex() == HSIP32[i] and halfsiphash(k, m, wide=True).hex() == HSIP64[i]
    cases = []  # (Bend expression, expected hex)
    for t in range(48):
        n = rng.choice([0, 1, 7, 8, 9, 15, 16, 17, 63, 64, 65]) if t < 12 else rng.randrange(0, 301)
        data = bytes(rng.randrange(256) for _ in range(n))
        cut = rng.randrange(0, n + 1)
        key = bytes(rng.randrange(256) for _ in range(16))
        for name, prm, c, d, wide in SIP:
            want = openssl(key, data, c, d, 16 if wide else 8)
            assert want == siphash(key, data, c, d, wide), "model disagrees with openssl: %s" % name
            kx = "sk(S.SipKey.of_octets(%s))" % lst(key)
            cases.append(("%s %d" % (name, t), "S.SipHash.hash(%s, %s, %s)" % (prm, kx, lst(data)), want.hex()))
            cases.append(("%s %d split" % (name, t), "sip2(%s, %s, %dn, %s)" % (prm, kx, cut, lst(data)), want.hex()))
        hkey = key[:8]
        for name, prm, c, d, wide in HSIP:
            want = halfsiphash(hkey, data, c, d, wide)
            kx = "hk(H.HsipKey.of_octets(%s))" % lst(hkey)
            cases.append(("%s %d" % (name, t), "H.HalfSipHash.hash(%s, %s, %s)" % (prm, kx, lst(data)), want.hex()))
            cases.append(("%s %d split" % (name, t), "hsip2(%s, %s, %dn, %s)" % (prm, kx, cut, lst(data)), want.hex()))
    for f in os.listdir(HERE):
        if f.startswith("cases") and f.endswith(".bend"):
            os.remove(os.path.join(HERE, f))
    expect = []
    for i in range(0, len(cases), PER_FILE):
        part = cases[i:i + PER_FILE]
        body = "".join('    IO.print("%s " ++ B.Octets.hex(%s))\n' % (label, expr) for label, expr, _ in part)
        with open(os.path.join(HERE, "cases%02d.bend" % (i // PER_FILE)), "w", newline="\n") as f:
            f.write(HEAD + "def main() -> IO(Unit):\n  do IO<Unit>:\n" + body)
        expect += ["%s %s" % (label, want) for label, _, want in part]
    with open(os.path.join(HERE, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
