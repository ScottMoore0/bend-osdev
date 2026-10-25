#!/usr/bin/env python3
"""A Python model of RIPEMD-160, written from the specification (the tables are gen/spec.py's).
The differential test (ref/gen.py) is against Python's hashlib where
OpenSSL provides RIPEMD-160 (the model otherwise), and the model is checked
against hashlib there too.
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


def ripemd160(m):
    f = [lambda x, y, z: x ^ y ^ z, lambda x, y, z: (x & y) | (~x & z), lambda x, y, z: (x | ~y) ^ z,
         lambda x, y, z: (x & z) | (y & ~z), lambda x, y, z: x ^ (y | ~z)]
    h = list(spec.RMD_IV)
    for X in blocks(md_pad(m, False), False):
        a, b, c, d, e = h
        a2, b2, c2, d2, e2 = h
        for j in range(80):
            r = j // 16
            t = (rol((a + (f[r](b, c, d) & M) + X[spec.RMD_R[r][j % 16]] + spec.RMD_K[r]) & M, spec.RMD_S[r][j % 16]) + e) & M
            a, e, d, c, b = e, d, rol(c, 10), b, t
            t = (rol((a2 + (f[4 - r](b2, c2, d2) & M) + X[spec.RMD_RP[r][j % 16]] + spec.RMD_KP[r]) & M, spec.RMD_SP[r][j % 16]) + e2) & M
            a2, e2, d2, c2, b2 = e2, d2, rol(c2, 10), b2, t
        t = (h[1] + c + d2) & M
        h = [t, (h[2] + d + e2) & M, (h[3] + e + a2) & M, (h[4] + a + b2) & M, (h[0] + b + c2) & M]
    return struct.pack("<5I", *h)


# ------------------------------------------------------------------ vectors

ASCII = [b"", b"a", b"abc", b"message digest", b"abcdefghijklmnopqrstuvwxyz",
         b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789", b"1234567890" * 8]
# the RIPEMD-160 page of Bosselaers (the paper's test values)
RMD_V = [(b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31"), (b"a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
         (b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"), (b"message digest", "5d0689ef49d2fae572b881b123a85ffa21595f36"),
         (b"abcdefghijklmnopqrstuvwxyz", "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
         (b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "12a053384a9c0c88e405a06c27dcf49ada62eb2b"),
         (ASCII[5], "b0e20b6e3116640286ed3a87a5713079b21f5189"), (ASCII[6], "9b752e45573d4b39f4dbd3323cab82bf63326bfb")]


def check_vectors():
    for m, v in RMD_V:
        assert ripemd160(m).hex() == v, ("ripemd160", m)
    # against hashlib (where OpenSSL provides RIPEMD-160), on a few lengths around the block boundaries
    for n in [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, 200]:
        m = bytes((7 * i + 3) & 255 for i in range(n))
        if "ripemd160" in hashlib.algorithms_available:
            assert ripemd160(m) == hashlib.new("ripemd160", m).digest(), n


if __name__ == "__main__":
    check_vectors()
    print("the model matches the specification's vectors")
