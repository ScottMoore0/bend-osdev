#!/usr/bin/env python3
"""A Python model of MD4 (RFC 1320), written from the specification (the tables are gen/spec.py's).
Python's hashlib lacks MD4 here (OpenSSL 3 keeps it in its legacy
provider), so the differential test (ref/gen.py) is against this model.
The model shares an author with the package, so it is checked first against
the specification's own vectors (check_vectors below).

  python3 ref/model.py      checks the model against its vectors
"""
import os, struct, sys

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


def md4(m):
    h = list(spec.MD4_IV)
    F = [lambda x, y, z: (x & y) | (~x & z), lambda x, y, z: (x & y) | (x & z) | (y & z), lambda x, y, z: x ^ y ^ z]
    for X in blocks(md_pad(m, False), False):
        a, b, c, d = h
        for r in range(3):
            for i in range(16):
                k = spec.MD4_X[r][i]
                t = rol((a + F[r](b, c, d) + X[k] + spec.MD4_K[r]) & M, spec.MD4_S[r][i % 4])
                a, b, c, d = d, t, b, c
        h = [(u + v) & M for u, v in zip(h, [a, b, c, d])]
    return struct.pack("<4I", *h)


# ------------------------------------------------------------------ vectors

ASCII = [b"", b"a", b"abc", b"message digest", b"abcdefghijklmnopqrstuvwxyz",
         b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789", b"1234567890" * 8]
# RFC 1320, A.5 (the test suite)
MD4_V = ["31d6cfe0d16ae931b73c59d7e0c089c0", "bde52cb31de33e46245e05fbdbd6fb24", "a448017aaf21d8525fc10ae87aa6729d",
         "d9130a8164549fe818874806e1c7014b", "d79e1c308aa5bbcdeea8ed63df412da9", "043f8582f241db351ce627e153e7f0e4",
         "e33b4ddc9c38f2199c3e7b164fcc0536"]


def check_vectors():
    for m, v in zip(ASCII, MD4_V):
        assert md4(m).hex() == v, ("md4", m)


if __name__ == "__main__":
    check_vectors()
    print("the model matches the specification's vectors")
