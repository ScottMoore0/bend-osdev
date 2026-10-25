#!/usr/bin/env python3
"""A Python model of Streebog (RFC 6986), written from the specification (the tables are gen/spec.py's).
Python has no Streebog, so the differential test (ref/gen.py) is
against this model.
The model shares an author with the package, so it is checked first against
the specification's own vectors (check_vectors below).

  python3 ref/model.py      checks the model against its vectors
"""
import os, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "gen"))
import spec  # noqa: E402


# Streebog: a 512-bit vector is an integer; byte i (i = 0 the least
# significant) is the i-th byte of the 64-byte string in memory order, as
# RFC 6986 writes its examples a_63 || ... || a_0
def stb_lps(x):
    bs = x.to_bytes(64, "little")
    bs = bytes(spec.STB_PI[b] for b in bs)
    bs = bytes(bs[spec.STB_TAU[i]] for i in range(64))
    out = 0
    for k in range(8):
        v = int.from_bytes(bs[8 * k:8 * k + 8], "little")
        r = 0
        for i in range(64):
            if v >> i & 1:
                r ^= spec.STB_A[63 - i]
        out |= r << (64 * k)
    return out


def stb_g(N, h, m):
    k = stb_lps(h ^ N)
    t = m
    for i in range(12):
        t = stb_lps(t ^ k)
        k = stb_lps(k ^ spec.STB_C[i])
    return t ^ k ^ h ^ m


def streebog(m, bits):
    h = int.from_bytes(b"\x01" * 64, "little") if bits == 256 else 0
    N = S = 0
    mod = 1 << 512
    i = 0
    while len(m) - i >= 64:
        blk = int.from_bytes(m[i:i + 64], "little")
        h = stb_g(N, h, blk)
        N = (N + 512) % mod
        S = (S + blk) % mod
        i += 64
    rest = m[i:]
    blk = int.from_bytes(rest + b"\x01" + b"\x00" * (63 - len(rest)), "little")
    h = stb_g(N, h, blk)
    N = (N + 8 * len(rest)) % mod
    S = (S + blk) % mod
    h = stb_g(0, h, N)
    h = stb_g(0, h, S)
    out = h.to_bytes(64, "little")
    return out[32:] if bits == 256 else out


def streebog256(m):
    return streebog(m, 256)


def streebog512(m):
    return streebog(m, 512)


# ------------------------------------------------------------------ vectors

# RFC 6986, section 10: M1 and M2 and their hash codes, as the RFC writes
# them (most significant byte first: the reverse of memory order)
STB_M1 = b"012345678901234567890123456789012345678901234567890123456789012"
STB_M2 = bytes.fromhex("fbe2e5f0eee3c820fbeafaebef20fffbf0e1e0f0f520e0ed20e8ece0ebe5f0f2f120fff0eeec20f120faf2fee5e2202ce8"
                       "f6f3ede220e8e6eee1e8f0f2d1202ce8f0f2e5e220e5d1")[::-1]
STB_V = [(STB_M1, 512, "486f64c1917879417fef082b3381a4e211c324f074654c38823a7b76f830ad00"
                       "fa1fbae42b1285c0352f227524bc9ab16254288dd6863dccd5b9f54a1ad0541b"),
         (STB_M1, 256, "00557be5e584fd52a449b16b0251d05d27f94ab76cbaa6da890b59d8ef1e159d"),
         (STB_M2, 512, "28fbc9bada033b1460642bdcddb90c3fb3e56c497ccd0f62b8a2ad4935e85f03"
                       "7613966de4ee00531ae60f3b5a47f8dae06915d5f2f194996fcabf2622e6881e"),
         (STB_M2, 256, "508f7e553c06501d749a66fc28c6cac0b005746d97537fa85d9e40904efed29d")]
# RFC 6986, section 10.1 (example 1, the 512-bit hash): K = LPS(0^512),
# the first g_N(h, m), and g_0(h, N) after it, as the RFC prints them
STB_EX1 = ["b383fc2eced4a574" * 8,
           "fd102cf8812ccb1191ea34af21394f3817a86641445aa9a626488adb33738ebd"
           "2754f6908cbbbac5d3ed0f522c50815c954135793fb1f5d905fee4736b3bdae2",
           "5c881fd924695cf196c2e4fec20d14b642026f2a0b1716ebaabb7067d4d59752"
           "3d2db69d6d3794622147a14f19a66e7f9037e1d662d34501a8901a5de7771d7c"]


def check_vectors():
    assert len(STB_M2) == 72
    for m, bits, v in STB_V:
        assert streebog(m, bits)[::-1].hex() == v, ("streebog", bits, m)
    h = stb_g(0, 0, int.from_bytes(STB_M1 + bytes([1]), "little"))
    assert "%0128x" % stb_lps(0) == STB_EX1[0] and "%0128x" % h == STB_EX1[1]
    assert "%0128x" % stb_g(0, h, 504) == STB_EX1[2]


if __name__ == "__main__":
    check_vectors()
    print("the model matches the specification's vectors")
