"""An independent Python model of the xtea package's cipher (XTEA).

Written here from the specification (not from any implementation), by the
same author as the Bend package, so agreement with it is weaker evidence
than agreement with an outside library. ref/gen.py compares the package
with this model (neither Python's cryptography nor OpenSSL has the cipher,
and the paper publishes no vectors).
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


# ---------------------------------------------------------------- XTEA
# D. Wheeler, R. Needham, "TEA, a Tiny Encryption Algorithm" (FSE 1994), and
# R. Needham, D. Wheeler, "Tea extensions" (1997). The papers work on 32-bit
# words; the byte order of a block and a key is a choice ("little" is the
# Linux kernel's).

TEA_DELTA = 0x9E3779B9


def _words(b, order):
    return [int.from_bytes(b[4 * i:4 * i + 4], order) for i in range(len(b) // 4)]


def _xtea_g(x):
    return ((((x << 4) & M32) ^ (x >> 5)) + x) & M32


def xtea_encrypt(key, block, order="little", cycles=32):
    k = _words(key, order)
    y, z = _words(block, order)
    s = 0
    for _ in range(cycles):
        y = (y + (_xtea_g(z) ^ ((s + k[s & 3]) & M32))) & M32
        s = (s + TEA_DELTA) & M32
        z = (z + (_xtea_g(y) ^ ((s + k[(s >> 11) & 3]) & M32))) & M32
    return y.to_bytes(4, order) + z.to_bytes(4, order)


def xtea_decrypt(key, block, order="little", cycles=32):
    k = _words(key, order)
    y, z = _words(block, order)
    s = (TEA_DELTA * cycles) & M32
    for _ in range(cycles):
        z = (z - (_xtea_g(y) ^ ((s + k[(s >> 11) & 3]) & M32))) & M32
        s = (s - TEA_DELTA) & M32
        y = (y - (_xtea_g(z) ^ ((s + k[s & 3]) & M32))) & M32
    return y.to_bytes(4, order) + z.to_bytes(4, order)
