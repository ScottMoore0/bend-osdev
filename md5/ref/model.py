#!/usr/bin/env python3
"""A Python model of MD5 (RFC 1321), written from the specification (the tables are gen/spec.py's).
The differential test (ref/gen.py) is against Python's hashlib, and
the model is checked against hashlib too.
The model shares an author with the package, so it is checked first against
the specification's own vectors (check_vectors below).

  python3 ref/model.py      checks the model against its vectors
"""
import hashlib, os, struct, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "gen"))
import spec  # noqa: E402

M = 0xFFFFFFFF


def rol(x, n):
    return ((x << n) | (x >> (32 - n))) & M


def md_pad(m, big):
    n = len(m)
    p = m + b"\x80" + b"\x00" * ((55 - n) % 64)
    return p + struct.pack(">Q" if big else "<Q", (8 * n) & (2 ** 64 - 1))


def blocks(p, big):
    fmt = ">16I" if big else "<16I"
    for i in range(0, len(p), 64):
        yield list(struct.unpack(fmt, p[i:i + 64]))


def md5(m):
    h = list(spec.MD5_IV)
    F = [lambda x, y, z: (x & y) | (~x & z), lambda x, y, z: (x & z) | (y & ~z),
         lambda x, y, z: x ^ y ^ z, lambda x, y, z: y ^ (x | (~z & M))]
    for X in blocks(md_pad(m, False), False):
        a, b, c, d = h
        for j in range(64):
            r = j // 16
            t = (a + F[r](b, c, d) + X[spec.MD5_X[r][j % 16]] + spec.MD5_T[j]) & M
            a, b, c, d = d, (b + rol(t, spec.MD5_S[r][j % 4])) & M, b, c
        h = [(u + v) & M for u, v in zip(h, [a, b, c, d])]
    return struct.pack("<4I", *h)


# ------------------------------------------------------------------ vectors

ASCII = [b"", b"a", b"abc", b"message digest", b"abcdefghijklmnopqrstuvwxyz",
         b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789", b"1234567890" * 8]
# RFC 1321, A.5 (the test suite)
MD5_V = ["d41d8cd98f00b204e9800998ecf8427e", "0cc175b9c0f1b6a831c399e269772661", "900150983cd24fb0d6963f7d28e17f72",
         "f96b697d7cb7938d525a2f31aaf161d0", "c3fcd3d76192e4007dfb496cca67e13b", "d174ab98d277d9f5a5611c2c9f419d9f",
         "57edf4a22be3c955ac49da2e2107b67a"]


def check_vectors():
    for m, v in zip(ASCII, MD5_V):
        assert md5(m).hex() == v, ("md5", m)
    # against hashlib, on a few lengths around the block boundaries
    for n in [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, 200]:
        m = bytes((7 * i + 3) & 255 for i in range(n))
        assert md5(m) == hashlib.md5(m).digest()


if __name__ == "__main__":
    check_vectors()
    print("the model matches the specification's vectors")
