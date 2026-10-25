"""An independent Python model of the blowfish package's cipher (Blowfish).

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
# Blowfish's pi words are transcribed (or computed) once, in gen/tables.py,
# which both the Bend code's generator and this model use; the published
# vectors, and Python's cryptography (Blowfish), check them in ref/gen.py.
import os as _os
import sys as _sys

_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "..", "gen"))
import tables as _t  # noqa: E402


# ---------------------------------------------------------------- Blowfish
# B. Schneier, "Description of a New Variable-Length Key, 64-Bit Block
# Cipher (Blowfish)", Fast Software Encryption 1993. Big-endian words.

def _bf_f(S, x):
    return ((((S[0][x >> 24] + S[1][(x >> 16) & 255]) & M32) ^ S[2][(x >> 8) & 255]) + S[3][x & 255]) & M32


def _bf_block(P, S, L, R):
    for i in range(16):
        L ^= P[i]
        R ^= _bf_f(S, L)
        L, R = R, L
    L, R = R, L
    R ^= P[16]
    L ^= P[17]
    return L, R


def bf_keys(key):
    P = list(_t.PI[:18])
    S = [list(_t.PI[18 + 256 * i:18 + 256 * (i + 1)]) for i in range(4)]
    j = 0
    for i in range(18):
        w = 0
        for _ in range(4):
            w = (w << 8) | key[j % len(key)]
            j += 1
        P[i] ^= w
    L = R = 0
    for i in range(0, 18, 2):
        L, R = _bf_block(P, S, L, R)
        P[i], P[i + 1] = L, R
    for s in range(4):
        for i in range(0, 256, 2):
            L, R = _bf_block(P, S, L, R)
            S[s][i], S[s][i + 1] = L, R
    return P, S


def blowfish_encrypt(key, block):
    P, S = bf_keys(key)
    L, R = _bf_block(P, S, int.from_bytes(block[:4], "big"), int.from_bytes(block[4:], "big"))
    return L.to_bytes(4, "big") + R.to_bytes(4, "big")


def blowfish_decrypt(key, block):
    # decryption is encryption with the P-array reversed
    P, S = bf_keys(key)
    L, R = _bf_block(list(reversed(P)), S, int.from_bytes(block[:4], "big"), int.from_bytes(block[4:], "big"))
    return L.to_bytes(4, "big") + R.to_bytes(4, "big")
