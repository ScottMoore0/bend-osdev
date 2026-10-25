"""An independent Python model of the fcrypt package's cipher (FCrypt).

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
# FCrypt's S-boxes are transcribed (or computed) once, in gen/tables.py,
# which both the Bend code's generator and this model use; the published
# vectors check them in ref/gen.py.
import os as _os
import sys as _sys

_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "..", "gen"))
import tables as _t  # noqa: E402


# ---------------------------------------------------------------- FCrypt
# T. Anderson, "Specification of FCrypt: Encryption for AFS Remote Procedure
# Calls" (2000): DES's Feistel structure with its own S-boxes, F and key
# schedule.

def fcrypt_keys(key):
    v = 0
    for b in key:
        v = (v << 7) | (b >> 1)
    ws = []
    for _ in range(16):
        ws.append(v & M32)
        v = ((v >> 11) | (v << 45)) & ((1 << 56) - 1)
    return ws


def _fc_f(r, k):
    S = _t.FCRYPT_S
    t = r ^ k
    u = (S[0][t & 255] << 24) | (S[1][(t >> 8) & 255] << 16) | (S[3][t >> 24] << 8) | S[2][(t >> 16) & 255]
    return ror(u, 5)


def fcrypt_encrypt(key, block):
    L, R = int.from_bytes(block[:4], "big"), int.from_bytes(block[4:], "big")
    for w in fcrypt_keys(key):
        L, R = R, L ^ _fc_f(R, w)
    return L.to_bytes(4, "big") + R.to_bytes(4, "big")


def fcrypt_decrypt(key, block):
    L, R = int.from_bytes(block[:4], "big"), int.from_bytes(block[4:], "big")
    for w in reversed(fcrypt_keys(key)):
        L, R = R ^ _fc_f(L, w), L
    return L.to_bytes(4, "big") + R.to_bytes(4, "big")
