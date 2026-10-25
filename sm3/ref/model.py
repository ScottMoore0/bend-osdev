#!/usr/bin/env python3
"""A Python model of SM3 (GB/T 32905), written from the specification (the tables are gen/spec.py's).
The differential test (ref/gen.py) is against Python's hashlib where
OpenSSL provides SM3 (the model otherwise), and the model is checked against
hashlib there too.
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


def sm3(m):
    P0 = lambda x: x ^ rol(x, 9) ^ rol(x, 17)
    P1 = lambda x: x ^ rol(x, 15) ^ rol(x, 23)
    v = list(spec.SM3_IV)
    for W in blocks(md_pad(m, True), True):
        for j in range(16, 68):
            W.append(P1(W[j - 16] ^ W[j - 9] ^ rol(W[j - 3], 15)) ^ rol(W[j - 13], 7) ^ W[j - 6])
        A, B, C, D, E, F, G, H = v
        for j in range(64):
            ss1 = rol((rol(A, 12) + E + rol(spec.SM3_T[j], j % 32)) & M, 7)
            ss2 = ss1 ^ rol(A, 12)
            ff = A ^ B ^ C if j < 16 else (A & B) | (A & C) | (B & C)
            gg = E ^ F ^ G if j < 16 else (E & F) | (~E & G)
            tt1 = (ff + D + ss2 + (W[j] ^ W[j + 4])) & M
            tt2 = ((gg & M) + H + ss1 + W[j]) & M
            A, B, C, D = tt1, A, rol(B, 9), C
            E, F, G, H = P0(tt2), E, rol(F, 19), G
        v = [x ^ y for x, y in zip(v, [A, B, C, D, E, F, G, H])]
    return struct.pack(">8I", *v)


# ------------------------------------------------------------------ vectors

# draft-shen-sm3-hash, examples 1 and 2
SM3_V = [(b"abc", "66c7f0f462eeedd9d1f2d46bdc10e4e24167c4875cf2f7a2297da02b8f4ba8e0"),
         (b"abcd" * 16, "debe9ff92275b8a138604889c18e5a4d6fdb70e5387e5765293dcba39c0c5732")]


def check_vectors():
    for m, v in SM3_V:
        assert sm3(m).hex() == v, ("sm3", m)
    # against hashlib (where OpenSSL provides SM3), on a few lengths around the block boundaries
    for n in [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, 200]:
        m = bytes((7 * i + 3) & 255 for i in range(n))
        if "sm3" in hashlib.algorithms_available:
            assert sm3(m) == hashlib.new("sm3", m).digest(), n


if __name__ == "__main__":
    check_vectors()
    print("the model matches the specification's vectors")
