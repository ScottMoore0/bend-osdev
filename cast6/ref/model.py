"""An independent Python model of the cast6 package's cipher (CAST-256).

Written here from the specification (not from any implementation), by the
same author as the Bend package, so agreement with it is weaker evidence
than agreement with an outside library. ref/gen.py compares the package
with this model (neither Python's cryptography nor OpenSSL has the
cipher), and checks the model against the specification's published
vectors first.
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
# CAST-128's S1 to S4, which CAST-256 shares, are transcribed (or computed) once, in the cast5 package's gen/tables.py,
# which both the Bend code's generator and this model use; the published
# vectors, and Python's cryptography (CAST5), check them in ref/gen.py.
import os as _os
import sys as _sys

_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "..", "..", "cast5", "gen"))
import tables as _t  # noqa: E402


def _words(b, order):
    return [int.from_bytes(b[4 * i:4 * i + 4], order) for i in range(len(b) // 4)]



# CAST-128's round functions f1, f2, f3 (RFC 2144, 2.2), which CAST-256 uses

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



# ---------------------------------------------------------------- CAST-256
# RFC 2612, The CAST-256 Encryption Algorithm (CAST6): CAST-128's f1, f2, f3
# and S1 .. S4, the quad-rounds Q and QBAR, and the key schedule's octaves W.

def cast6_keys(key):
    """the twelve key sets (Km0..Km3, Kr0..Kr3) of a key of 16, 20, 24, 28 or 32 bytes"""
    k = _words(key + bytes(32 - len(key)), "big")
    cm, mm, cr, mr = 0x5A827999, 0x6ED9EBA1, 19, 17
    tm, tr = [], []
    for i in range(24):
        tm.append([])
        tr.append([])
        for _ in range(8):
            tm[i].append(cm)
            cm = (cm + mm) & M32
            tr[i].append(cr)
            cr = (cr + mr) & 31
    A, B, C, D, E, F, G, H = range(8)

    def octave(i):
        def f(ty, d, j):
            return _cast_f(ty, d, tm[i][j], tr[i][j])
        k[G] ^= f(1, k[H], 0)
        k[F] ^= f(2, k[G], 1)
        k[E] ^= f(3, k[F], 2)
        k[D] ^= f(1, k[E], 3)
        k[C] ^= f(2, k[D], 4)
        k[B] ^= f(3, k[C], 5)
        k[A] ^= f(1, k[B], 6)
        k[H] ^= f(2, k[A], 7)

    sets = []
    for i in range(12):
        octave(2 * i)
        octave(2 * i + 1)
        sets.append(([k[H], k[F], k[D], k[B]], [k[A] & 31, k[C] & 31, k[E] & 31, k[G] & 31]))
    return sets


def _cast6_q(s, km, kr):
    a, b, c, d = s
    c ^= _cast_f(1, d, km[0], kr[0])
    b ^= _cast_f(2, c, km[1], kr[1])
    a ^= _cast_f(3, b, km[2], kr[2])
    d ^= _cast_f(1, a, km[3], kr[3])
    return [a, b, c, d]


def _cast6_qbar(s, km, kr):
    a, b, c, d = s
    d ^= _cast_f(1, a, km[3], kr[3])
    a ^= _cast_f(3, b, km[2], kr[2])
    b ^= _cast_f(2, c, km[1], kr[1])
    c ^= _cast_f(1, d, km[0], kr[0])
    return [a, b, c, d]


def cast6_encrypt(key, block):
    s = _words(block, "big")
    for i, (km, kr) in enumerate(cast6_keys(key)):
        s = _cast6_q(s, km, kr) if i < 6 else _cast6_qbar(s, km, kr)
    return b"".join(w.to_bytes(4, "big") for w in s)


def cast6_decrypt(key, block):
    s = _words(block, "big")
    for i, (km, kr) in reversed(list(enumerate(cast6_keys(key)))):
        s = _cast6_qbar(s, km, kr) if i < 6 else _cast6_q(s, km, kr)
    return b"".join(w.to_bytes(4, "big") for w in s)
