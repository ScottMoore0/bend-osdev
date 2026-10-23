#!/usr/bin/env python3
"""Differential test cases for bend-osdev-kithash: bend-kit-hash through the
adapter, beside bend-osdev's own implementations of the same algorithms.

Writes ref/casesNN.bend (Bend programs printing each case) and
ref/expected.txt (the same values from outside both):
  * CRC-32 (bend-kit-hash's and crc's): Python's zlib.crc32;
  * Adler-32 (bend-kit-hash's and deflate's): Python's zlib.adler32;
  * XXH32 (bend-kit-hash's): the lz4 command's frame content checksum for
    seed 0, ref/model.py for other seeds;
  * XXH64 (bend-kit-hash's and zstd's): ref/model.py, its low 32 bits
    checked against the zstd command's frame content checksum on every
    input (seed 0);
  * FNV-1a 32 and 64 (bend-kit-hash's): ref/model.py, checked first against
    RFC 9923 section 8.3's values;
  * SipHash-1-3 (bend-kit-hash's and siphash's): the openssl command.
Random inputs of 0 to 300 bytes, and lengths at bend-kit-bytes' buffer
boundaries (4 * 2^d bytes and a few either side, where its readers' last
word wraps to word 0), some fed through the hash interface in two pieces.
"""
import os, random, struct, subprocess, sys, zlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from model import xxh32, xxh64, fnv1a32, fnv1a64  # noqa: E402

PER_FILE = 80
RFC9923 = [(b"", 0x811C9DC5, 0xCBF29CE484222325), (b"a", 0xE40C292C, 0xAF63DC4C8601EC8C),
           (b"foobar", 0xBF9CF968, 0x85944171F73967E8), (b"Hello!\x01\xff\xed", 0xFD9D3881, 0xBD51EA7094EE6FA1)]


def lz4_xxh32(d):
    out = subprocess.run(["lz4", "-c", "-q"], input=d, capture_output=True, check=True).stdout
    return struct.unpack("<I", out[-4:])[0]


def zstd_xxh64_lo(d):
    out = subprocess.run(["zstd", "-c", "-q", "--check"], input=d, capture_output=True, check=True).stdout
    return struct.unpack("<I", out[-4:])[0]


def openssl_sip13(key, d):
    out = subprocess.run(["openssl", "mac", "-macopt", "hexkey:" + key.hex(), "-macopt", "size:8", "-macopt",
                          "c-rounds:1", "-macopt", "d-rounds:3", "SIPHASH"], input=d, capture_output=True, check=True)
    return bytes.fromhex(out.stdout.decode().strip())


def lst(data):
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"


def w64(v):
    return "W.W64.from_parts(%d, %d)" % (v >> 32, v & 0xFFFFFFFF)


HEAD = """import Base
import ../../word64/word64.bend as W
import ../../bytes/bytes.bend as B
import ../../crc/crc.bend as C
import ../../deflate/adler32.bend as A
import ../../zstd/xxh64.bend as X
import ../../siphash/siphash.bend as S
import ../kithash.bend as K
import ../inst_hash.bend as IH
import ../inst_mac.bend as IM

def u(v: U32) -> String:
  U32.show(v)

def w(v: W.W64) -> String:
  W.W64.show_hex(v)

# the digest in two pieces, through the hash interface
def two(~digest: B.Octets -> B.Octets, +n: Nat, +m: B.Octets) -> String:
  B.Octets.hex(IH.KhBuf.final(~digest, IH.KhBuf.update(IH.KhBuf.update(IH.KhBuf.init(), B.Octets.take(n, m)), B.Octets.drop(n, m))))

def sip(+k0: W.W64, +k1: W.W64, +m: B.Octets) -> String:
  B.Octets.hex(IM.KhSip13.compute(S.SipKey.of_words(k0, k1), m)) ++ " " ++ B.Octets.hex(IM.KhSip.compute(~S.SipParams.sip13(), S.SipKey.of_words(k0, k1), m))

"""


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    for d, a, b in RFC9923:
        assert fnv1a32(d) == a and fnv1a64(d) == b, "model disagrees with RFC 9923"
    lengths = [0, 1, 2, 3]
    for d in range(1, 9):
        lengths += [4 * 2 ** d + e for e in (-5, -1, 0, 1, 3)]
    lengths += [rng.randrange(0, 301) for _ in range(30)]
    cases = []  # (label, Bend expression, expected)
    for t, n in enumerate(lengths):
        data = bytes(rng.randrange(256) for _ in range(n))
        m = "m%d()" % t
        seed32 = rng.randrange(1 << 32)
        seed64 = rng.randrange(1 << 64)
        key = bytes(rng.randrange(256) for _ in range(16))
        cut = rng.randrange(0, n + 1)
        x32, x64 = lz4_xxh32(data), xxh64(data)
        assert x32 == xxh32(data), "model disagrees with lz4"
        assert x64 & 0xFFFFFFFF == zstd_xxh64_lo(data), "model disagrees with zstd"
        tag = openssl_sip13(key, data)
        k0, k1 = int.from_bytes(key[:8], "little"), int.from_bytes(key[8:], "little")
        c, a = zlib.crc32(data), zlib.adler32(data)
        cases.append((t, data, [
            ("crc32", "u(K.KhCrc32.value(%s)) ++ \" \" ++ u(C.crc32(%s))" % (m, m), "%d %d" % (c, c)),
            ("adler32", "u(K.KhAdler32.value(%s)) ++ \" \" ++ u(A.adler32(%s))" % (m, m), "%d %d" % (a, a)),
            ("xxh32", "u(K.KhXxh32.value(0, %s)) ++ \" \" ++ u(K.KhXxh32.value(%d, %s))" % (m, seed32, m),
             "%d %d" % (x32, xxh32(data, seed32))),
            ("xxh64", "w(K.KhXxh64.value(W.W64.zero(), %s)) ++ \" \" ++ w(X.ZstdXxh64.hash(W.W64.zero(), %s))" % (m, m),
             "%016x %016x" % (x64, x64)),
            ("xxh64 seed", "w(K.KhXxh64.value(%s, %s)) ++ \" \" ++ w(X.ZstdXxh64.hash(%s, %s))" % (w64(seed64), m, w64(seed64), m),
             "%016x %016x" % (xxh64(data, seed64), xxh64(data, seed64))),
            ("fnv1a", "u(K.KhFnv1a32.value(%s)) ++ \" \" ++ w(K.KhFnv1a64.value(%s))" % (m, m),
             "%d %016x" % (fnv1a32(data), fnv1a64(data))),
            ("sip13", "sip(%s, %s, %s)" % (w64(k0), w64(k1), m), "%s %s" % (tag.hex(), tag.hex())),
            ("pieces", "two(~IH.KhCrc32.digest, %dn, %s) ++ \" \" ++ two(~IH.KhXxh64.digest(~W.W64.zero()), %dn, %s)" % (cut, m, cut, m),
             "%08x %016x" % (c, x64)),
        ]))
    for f in os.listdir(HERE):
        if f.startswith("cases") and f.endswith(".bend"):
            os.remove(os.path.join(HERE, f))
    expect, count = [], 0
    for i in range(0, len(cases), PER_FILE // 8):
        part = cases[i:i + PER_FILE // 8]
        defs = "".join("def m%d() -> B.Octets:\n  %s\n\n" % (t, lst(data)) for t, data, _ in part)
        body = ""
        for t, _, lines in part:
            for label, expr, want in lines:
                body += '    IO.print("%s %d " ++ %s)\n' % (label, t, expr)
                expect.append("%s %d %s" % (label, t, want))
                count += 1
        with open(os.path.join(HERE, "cases%02d.bend" % (i // (PER_FILE // 8))), "w", newline="\n") as f:
            f.write(HEAD + defs + "def main() -> IO(Unit):\n  do IO<Unit>:\n" + body)
    with open(os.path.join(HERE, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(count, "cases")


main()
