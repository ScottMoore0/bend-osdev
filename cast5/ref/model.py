"""An independent Python model of the cast5 package's cipher (CAST-128).

Written here from the specification (not from any implementation), by the
same author as the Bend package, so agreement with it is weaker evidence
than agreement with an outside library. ref/gen.py compares the package
with this model, and also with Python's cryptography, and checks
the model against the specification's published vectors first.
"""

M32 = 0xFFFFFFFF


def rol(x, n):
    n %= 32
    return ((x << n) | (x >> (32 - n))) & M32 if n else x


def ror(x, n):
    return rol(x, 32 - n % 32)


def words_le(b):
    return [int.from_bytes(b[4 * i:4 * i + 4], "little") for i in range(len(b) // 4)]


def bytes_le(ws):
    return b"".join(w.to_bytes(4, "little") for w in ws)


# ---------------------------------------------------------------- tables
# CAST-128's S-boxes are transcribed (or computed) once, in gen/tables.py,
# which both the Bend code's generator and this model use; the published
# vectors, and Python's cryptography (CAST5), check them in ref/gen.py.
import os as _os
import sys as _sys

_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "..", "gen"))
import tables as _t  # noqa: E402


# ---------------------------------------------------------------- CAST-128
# RFC 2144, The CAST-128 Encryption Algorithm (CAST5).

def _cast_f(ty, d, km, kr):
    S1, S2, S3, S4 = _t.CAST_S[:4]
    if ty == 1:
        i = rol((km + d) & M32, kr)
    elif ty == 2:
        i = rol(km ^ d, kr)
    else:
        i = rol((km - d) & M32, kr)
    a, b, c, e = i >> 24, (i >> 16) & 255, (i >> 8) & 255, i & 255
    if ty == 1:
        return ((((S1[a] ^ S2[b]) - S3[c]) & M32) + S4[e]) & M32
    if ty == 2:
        return ((((S1[a] - S2[b]) & M32) + S3[c]) & M32) ^ S4[e]
    return ((((S1[a] + S2[b]) & M32) ^ S3[c]) - S4[e]) & M32


# The key schedule's four sets of subkey formulas (RFC 2144, 2.4.1): each
# subkey is S5[a] ^ S6[b] ^ S7[c] ^ S8[d] ^ Sj[e], on the bytes of z (the
# first and third sets) or of x (the second and fourth)
CAST_KSETS = [
    [(8, 9, 7, 6, 5, 2), (10, 11, 5, 4, 6, 6), (12, 13, 3, 2, 7, 9), (14, 15, 1, 0, 8, 12)],
    [(3, 2, 12, 13, 5, 8), (1, 0, 14, 15, 6, 13), (7, 6, 8, 9, 7, 3), (5, 4, 10, 11, 8, 7)],
    [(3, 2, 12, 13, 5, 9), (1, 0, 14, 15, 6, 12), (7, 6, 8, 9, 7, 2), (5, 4, 10, 11, 8, 6)],
    [(8, 9, 7, 6, 5, 3), (10, 11, 5, 4, 6, 7), (12, 13, 3, 2, 7, 8), (14, 15, 1, 0, 8, 13)],
]


def cast5_subkeys(key):
    """the 32 subkey words K1 .. K32 of a key of 5 to 16 bytes (zero-padded)"""
    S5, S6, S7, S8 = _t.CAST_S[4:]
    S = {5: S5, 6: S6, 7: S7, 8: S8}
    x = list(key + bytes(16 - len(key)))
    z = [0] * 16

    def w(a, i):
        return (a[i] << 24) | (a[i + 1] << 16) | (a[i + 2] << 8) | a[i + 3]

    def put(a, i, v):
        a[i:i + 4] = [(v >> 24) & 255, (v >> 16) & 255, (v >> 8) & 255, v & 255]

    def ks(a, kset):
        return [S5[a[p]] ^ S6[a[q]] ^ S7[a[r]] ^ S8[a[s]] ^ S[j][a[e]] for p, q, r, s, j, e in kset]

    K = []
    for _ in range(2):
        for zset, xset in ((0, 1), (2, 3)):
            put(z, 0, w(x, 0) ^ S5[x[13]] ^ S6[x[15]] ^ S7[x[12]] ^ S8[x[14]] ^ S7[x[8]])
            put(z, 4, w(x, 8) ^ S5[z[0]] ^ S6[z[2]] ^ S7[z[1]] ^ S8[z[3]] ^ S8[x[10]])
            put(z, 8, w(x, 12) ^ S5[z[7]] ^ S6[z[6]] ^ S7[z[5]] ^ S8[z[4]] ^ S5[x[9]])
            put(z, 12, w(x, 4) ^ S5[z[10]] ^ S6[z[9]] ^ S7[z[11]] ^ S8[z[8]] ^ S6[x[11]])
            K += ks(z, CAST_KSETS[zset])
            put(x, 0, w(z, 8) ^ S5[z[5]] ^ S6[z[7]] ^ S7[z[4]] ^ S8[z[6]] ^ S7[z[0]])
            put(x, 4, w(z, 0) ^ S5[x[0]] ^ S6[x[2]] ^ S7[x[1]] ^ S8[x[3]] ^ S8[z[2]])
            put(x, 8, w(z, 4) ^ S5[x[7]] ^ S6[x[6]] ^ S7[x[5]] ^ S8[x[4]] ^ S5[z[1]])
            put(x, 12, w(z, 12) ^ S5[x[10]] ^ S6[x[9]] ^ S7[x[11]] ^ S8[x[8]] ^ S6[z[3]])
            K += ks(x, CAST_KSETS[xset])
    return K


def _cast5_rounds(key):
    K = cast5_subkeys(key)
    n = 12 if len(key) <= 10 else 16
    return [((i % 3) + 1, K[i], K[16 + i] & 31) for i in range(n)]


def cast5_encrypt(key, block):
    L, R = int.from_bytes(block[:4], "big"), int.from_bytes(block[4:], "big")
    for ty, km, kr in _cast5_rounds(key):
        L, R = R, L ^ _cast_f(ty, R, km, kr)
    return R.to_bytes(4, "big") + L.to_bytes(4, "big")


def cast5_decrypt(key, block):
    R, L = int.from_bytes(block[:4], "big"), int.from_bytes(block[4:], "big")
    for ty, km, kr in reversed(_cast5_rounds(key)):
        L, R = R ^ _cast_f(ty, L, km, kr), L
    return L.to_bytes(4, "big") + R.to_bytes(4, "big")
