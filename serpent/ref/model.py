"""An independent Python model of the serpent package's cipher (Serpent).

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


# ---------------------------------------------------------------- Serpent
# Anderson, Biham, Knudsen, "Serpent: A Proposal for the Advanced Encryption
# Standard" (1998), the bitslice description. Words are little-endian: byte
# 0 of a block is the low byte of X0, as in the NESSIE vectors.

SERPENT_S = [
    [3, 8, 15, 1, 10, 6, 5, 11, 14, 13, 4, 2, 7, 0, 9, 12],
    [15, 12, 2, 7, 9, 0, 5, 10, 1, 11, 14, 8, 6, 13, 3, 4],
    [8, 6, 7, 9, 3, 12, 10, 15, 13, 1, 14, 4, 0, 11, 5, 2],
    [0, 15, 11, 8, 12, 9, 6, 3, 13, 1, 2, 4, 10, 7, 5, 14],
    [1, 15, 8, 3, 12, 0, 11, 6, 2, 5, 4, 10, 9, 14, 7, 13],
    [15, 5, 2, 11, 4, 10, 9, 12, 0, 3, 14, 8, 13, 6, 7, 1],
    [7, 2, 12, 5, 8, 4, 6, 11, 14, 9, 1, 15, 13, 3, 10, 0],
    [1, 13, 15, 0, 14, 8, 2, 11, 7, 4, 12, 10, 9, 3, 5, 6]]
PHI = 0x9E3779B9


def serpent_apply(table, x):
    out = [0, 0, 0, 0]
    for j in range(32):
        v = sum(((x[i] >> j) & 1) << i for i in range(4))
        w = table[v]
        for i in range(4):
            out[i] |= ((w >> i) & 1) << j
    return out


def serpent_sbox(n, x):
    return serpent_apply(SERPENT_S[n], x)


def serpent_sbox_inv(n, x):
    s = SERPENT_S[n]
    return serpent_apply([s.index(v) for v in range(16)], x)


def serpent_lt(x):
    x0, x1, x2, x3 = x
    x0 = rol(x0, 13)
    x2 = rol(x2, 3)
    x1 = x1 ^ x0 ^ x2
    x3 = x3 ^ x2 ^ ((x0 << 3) & M32)
    x1 = rol(x1, 1)
    x3 = rol(x3, 7)
    x0 = x0 ^ x1 ^ x3
    x2 = x2 ^ x3 ^ ((x1 << 7) & M32)
    x0 = rol(x0, 5)
    x2 = rol(x2, 22)
    return [x0, x1, x2, x3]


def serpent_lt_inv(x):
    x0, x1, x2, x3 = x
    x2 = ror(x2, 22)
    x0 = ror(x0, 5)
    x2 = x2 ^ x3 ^ ((x1 << 7) & M32)
    x0 = x0 ^ x1 ^ x3
    x3 = ror(x3, 7)
    x1 = ror(x1, 1)
    x3 = x3 ^ x2 ^ ((x0 << 3) & M32)
    x1 = x1 ^ x0 ^ x2
    x2 = ror(x2, 3)
    x0 = ror(x0, 13)
    return [x0, x1, x2, x3]


def serpent_keys(key):
    assert len(key) <= 32
    k = bytearray(key)
    if len(k) < 32:
        k += b"\x01" + bytes(31 - len(k))
    w = words_le(bytes(k))
    for i in range(132):
        w.append(rol(w[i] ^ w[i + 3] ^ w[i + 5] ^ w[i + 7] ^ PHI ^ i, 11))
    w = w[8:]
    return [serpent_sbox((3 - i) % 8, w[4 * i:4 * i + 4]) for i in range(33)]


def serpent_encrypt(key, block):
    ks = serpent_keys(key)
    x = words_le(block)
    for i in range(32):
        x = [a ^ b for a, b in zip(x, ks[i])]
        x = serpent_sbox(i % 8, x)
        x = serpent_lt(x) if i < 31 else [a ^ b for a, b in zip(x, ks[32])]
    return bytes_le(x)


def serpent_decrypt(key, block):
    ks = serpent_keys(key)
    x = words_le(block)
    for i in reversed(range(32)):
        x = serpent_lt_inv(x) if i < 31 else [a ^ b for a, b in zip(x, ks[32])]
        x = serpent_sbox_inv(i % 8, x)
        x = [a ^ b for a, b in zip(x, ks[i])]
    return bytes_le(x)
