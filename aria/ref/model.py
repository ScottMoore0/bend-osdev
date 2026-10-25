"""An independent Python model of the aria package's cipher (ARIA).

Written here from the specification (not from any implementation), by the
same author as the Bend package, so agreement with it is weaker evidence
than agreement with an outside library. ref/gen.py compares the package
with this model, and also with the openssl command, and checks
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
# ARIA's S-boxes are transcribed (or computed) once, in gen/tables.py,
# which both the Bend code's generator and this model use; the published
# vectors, and OpenSSL (ARIA), check them in ref/gen.py.
import os as _os
import sys as _sys

_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "..", "gen"))
import tables as _t  # noqa: E402


# ---------------------------------------------------------------- ARIA
# RFC 5794, A Description of the ARIA Encryption Algorithm.

ARIA_C = [0x517CC1B727220A94FE13ABE8FA9A6EE0, 0x6DB14ACC9E21C820FF28B1D5EF5DE2B0,
          0xDB92371D2126E9700324977504E8C90E]
ARIA_A = [[3, 4, 6, 8, 9, 13, 14], [2, 5, 7, 8, 9, 12, 15], [1, 4, 6, 10, 11, 12, 15], [0, 5, 7, 10, 11, 13, 14],
          [0, 2, 5, 8, 11, 14, 15], [1, 3, 4, 9, 10, 14, 15], [0, 2, 7, 9, 10, 12, 13], [1, 3, 6, 8, 11, 12, 13],
          [0, 1, 4, 7, 10, 13, 15], [0, 1, 5, 6, 11, 12, 14], [2, 3, 5, 6, 8, 13, 15], [2, 3, 4, 7, 9, 12, 14],
          [1, 2, 6, 7, 9, 11, 12], [0, 3, 6, 7, 8, 10, 13], [0, 3, 4, 5, 9, 11, 14], [1, 2, 4, 5, 8, 10, 15]]
M128 = (1 << 128) - 1


def _aria_sl(x, which):
    sb = [_t.ARIA_SB1, _t.ARIA_SB2, _t.ARIA_SB3, _t.ARIA_SB4]
    order = [0, 1, 2, 3] if which == 1 else [2, 3, 0, 1]
    b = x.to_bytes(16, "big")
    return int.from_bytes(bytes(sb[order[i % 4]][v] for i, v in enumerate(b)), "big")


def aria_diffuse(x):
    b = x.to_bytes(16, "big")
    out = []
    for row in ARIA_A:
        v = 0
        for j in row:
            v ^= b[j]
        out.append(v)
    return int.from_bytes(bytes(out), "big")


def _aria_fo(d, rk):
    return aria_diffuse(_aria_sl(d ^ rk, 1))


def _aria_fe(d, rk):
    return aria_diffuse(_aria_sl(d ^ rk, 2))


def _rot128(x, n):
    """x rotated right by n bits (left for negative n)"""
    n %= 128
    return ((x >> n) | (x << (128 - n))) & M128


def aria_keys(key):
    n = len(key)
    ck = {16: [0, 1, 2], 24: [1, 2, 0], 32: [2, 0, 1]}[n]
    kk = int.from_bytes(key + bytes(32 - n), "big")
    kl, kr = kk >> 128, kk & M128
    w0 = kl
    w1 = _aria_fo(w0, ARIA_C[ck[0]]) ^ kr
    w2 = _aria_fe(w1, ARIA_C[ck[1]]) ^ w0
    w3 = _aria_fo(w2, ARIA_C[ck[2]]) ^ w1
    ek = []
    for r in (19, 31, -61, -31):
        ek += [w0 ^ _rot128(w1, r), w1 ^ _rot128(w2, r), w2 ^ _rot128(w3, r), _rot128(w0, r) ^ w3]
    ek.append(w0 ^ _rot128(w1, -19))
    rounds = {16: 12, 24: 14, 32: 16}[n]
    return ek[:rounds + 1]


def aria_encrypt(key, block):
    ek = aria_keys(key)
    n = len(ek) - 1
    p = int.from_bytes(block, "big")
    for i in range(n - 1):
        p = _aria_fo(p, ek[i]) if i % 2 == 0 else _aria_fe(p, ek[i])
    return (_aria_sl(p ^ ek[n - 1], 2) ^ ek[n]).to_bytes(16, "big")


def aria_decrypt(key, block):
    ek = aria_keys(key)
    n = len(ek) - 1
    dk = [ek[n]] + [aria_diffuse(ek[n - i]) for i in range(1, n)] + [ek[0]]
    p = int.from_bytes(block, "big")
    for i in range(n - 1):
        p = _aria_fo(p, dk[i]) if i % 2 == 0 else _aria_fe(p, dk[i])
    return (_aria_sl(p ^ dk[n - 1], 2) ^ dk[n]).to_bytes(16, "big")
