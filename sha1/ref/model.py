#!/usr/bin/env python3
"""A Python model of SHA-1 (FIPS 180-4), written from the specification (the tables are gen/spec.py's).
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


def sha1(m):
    h = list(spec.SHA1_IV)
    for W in blocks(md_pad(m, True), True):
        for t in range(16, 80):
            W.append(rol(W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16], 1))
        a, b, c, d, e = h
        for t in range(80):
            if t < 20:
                f = (b & c) | (~b & d)
            elif t < 40 or t >= 60:
                f = b ^ c ^ d
            else:
                f = (b & c) | (b & d) | (c & d)
            a, b, c, d, e = (rol(a, 5) + (f & M) + e + spec.SHA1_K[t // 20] + W[t]) & M, a, rol(b, 30), c, d
        h = [(u + v) & M for u, v in zip(h, [a, b, c, d, e])]
    return struct.pack(">5I", *h)


# ------------------------------------------------------------------ vectors

# FIPS 180-4's examples (NIST's SHA-1 example values): "abc" and the 448-bit message
SHA1_V = [(b"abc", "a9993e364706816aba3e25717850c26c9cd0d89d"),
          (b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "84983e441c3bd26ebaae4aa1f95129e5e54670f1")]


def check_vectors():
    for m, v in SHA1_V:
        assert sha1(m).hex() == v, ("sha1", m)
    # against hashlib, on a few lengths around the block boundaries
    for n in [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, 200]:
        m = bytes((7 * i + 3) & 255 for i in range(n))
        assert sha1(m) == hashlib.sha1(m).digest()


if __name__ == "__main__":
    check_vectors()
    print("the model matches the specification's vectors")
