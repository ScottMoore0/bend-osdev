"""SipHash-c-d and HalfSipHash-c-d in Python, for the differential test.

Written from the SipHash paper (J.-P. Aumasson and D. J. Bernstein,
"SipHash: a fast short-input PRF", 2012-09-18, section 2) and, for
HalfSipHash and the double-width outputs, from the reference implementation's
halfsiphash.c and siphash.c (github.com/veorq/SipHash, CC0). It shares an
author with bend-osdev-siphash; the openssl command (SipHash) and the
published vectors (vectors.h) are the independent references.
"""
M64, M32 = (1 << 64) - 1, (1 << 32) - 1


def _rotl(x, r, w, mask):
    return ((x << r) | (x >> (w - r))) & mask


def _round(v, w, rot):
    mask = (1 << w) - 1
    a, b, c, d, e, f = rot
    v0, v1, v2, v3 = v
    v0 = (v0 + v1) & mask; v1 = _rotl(v1, a, w, mask); v1 ^= v0; v0 = _rotl(v0, b, w, mask)
    v2 = (v2 + v3) & mask; v3 = _rotl(v3, c, w, mask); v3 ^= v2
    v0 = (v0 + v3) & mask; v3 = _rotl(v3, d, w, mask); v3 ^= v0
    v2 = (v2 + v1) & mask; v1 = _rotl(v1, e, w, mask); v1 ^= v2; v2 = _rotl(v2, f, w, mask)
    return [v0, v1, v2, v3]


def _core(v, data, c, d, wide, w, rot, fin):
    nb = w // 8
    def rounds(v, n):
        for _ in range(n):
            v = _round(v, w, rot)
        return v
    if wide:
        v[1] ^= 0xEE
    whole = len(data) - len(data) % nb
    for i in range(0, whole, nb):
        m = int.from_bytes(data[i:i + nb], "little")
        v[3] ^= m; v = rounds(v, c); v[0] ^= m
    b = int.from_bytes(data[whole:], "little") | ((len(data) & 255) << (w - 8))
    v[3] ^= b; v = rounds(v, c); v[0] ^= b
    v[2] ^= 0xEE if wide else 0xFF
    v = rounds(v, d)
    out = fin(v).to_bytes(nb, "little")
    if wide:
        v[1] ^= 0xDD
        v = rounds(v, d)
        out += fin(v).to_bytes(nb, "little")
    return out


def siphash(key, data, c=2, d=4, wide=False):
    k0, k1 = int.from_bytes(key[:8], "little"), int.from_bytes(key[8:16], "little")
    v = [k0 ^ 0x736F6D6570736575, k1 ^ 0x646F72616E646F6D, k0 ^ 0x6C7967656E657261, k1 ^ 0x7465646279746573]
    return _core(v, data, c, d, wide, 64, (13, 32, 16, 21, 17, 32), lambda v: v[0] ^ v[1] ^ v[2] ^ v[3])


def halfsiphash(key, data, c=2, d=4, wide=False):
    k0, k1 = int.from_bytes(key[:4], "little"), int.from_bytes(key[4:8], "little")
    v = [k0, k1, k0 ^ 0x6C796765, k1 ^ 0x74656462]
    return _core(v, data, c, d, wide, 32, (5, 16, 8, 7, 13, 16), lambda v: v[1] ^ v[3])
