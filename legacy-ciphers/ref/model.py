"""Independent Python models of the legacy-ciphers package's ciphers.

Written here from the specifications (not from any implementation), by the
same author as the Bend package, so agreement with them is weaker evidence
than agreement with Python's cryptography. ref/gen.py compares the package
with these models for every cipher, and also with cryptography wherever it
has the cipher (DES, 3DES, SM4, Camellia, RC4; not Serpent or Twofish), and
checks the models against the specifications' published vectors first.
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


# ---------------------------------------------------------------- DES
# FIPS 46-3: the tables number bits 1..64, bit 1 the most significant.

IP = [58, 50, 42, 34, 26, 18, 10, 2, 60, 52, 44, 36, 28, 20, 12, 4,
      62, 54, 46, 38, 30, 22, 14, 6, 64, 56, 48, 40, 32, 24, 16, 8,
      57, 49, 41, 33, 25, 17, 9, 1, 59, 51, 43, 35, 27, 19, 11, 3,
      61, 53, 45, 37, 29, 21, 13, 5, 63, 55, 47, 39, 31, 23, 15, 7]
FP = [40, 8, 48, 16, 56, 24, 64, 32, 39, 7, 47, 15, 55, 23, 63, 31,
      38, 6, 46, 14, 54, 22, 62, 30, 37, 5, 45, 13, 53, 21, 61, 29,
      36, 4, 44, 12, 52, 20, 60, 28, 35, 3, 43, 11, 51, 19, 59, 27,
      34, 2, 42, 10, 50, 18, 58, 26, 33, 1, 41, 9, 49, 17, 57, 25]
E = [32, 1, 2, 3, 4, 5, 4, 5, 6, 7, 8, 9, 8, 9, 10, 11, 12, 13,
     12, 13, 14, 15, 16, 17, 16, 17, 18, 19, 20, 21, 20, 21, 22, 23, 24, 25,
     24, 25, 26, 27, 28, 29, 28, 29, 30, 31, 32, 1]
P = [16, 7, 20, 21, 29, 12, 28, 17, 1, 15, 23, 26, 5, 18, 31, 10,
     2, 8, 24, 14, 32, 27, 3, 9, 19, 13, 30, 6, 22, 11, 4, 25]
PC1 = [57, 49, 41, 33, 25, 17, 9, 1, 58, 50, 42, 34, 26, 18,
       10, 2, 59, 51, 43, 35, 27, 19, 11, 3, 60, 52, 44, 36,
       63, 55, 47, 39, 31, 23, 15, 7, 62, 54, 46, 38, 30, 22,
       14, 6, 61, 53, 45, 37, 29, 21, 13, 5, 28, 20, 12, 4]
PC2 = [14, 17, 11, 24, 1, 5, 3, 28, 15, 6, 21, 10,
       23, 19, 12, 4, 26, 8, 16, 7, 27, 20, 13, 2,
       41, 52, 31, 37, 47, 55, 30, 40, 51, 45, 33, 48,
       44, 49, 39, 56, 34, 53, 46, 42, 50, 36, 29, 32]
SHIFTS = [1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1]
SBOX = [
    [[14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7],
     [0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8],
     [4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0],
     [15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13]],
    [[15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10],
     [3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5],
     [0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15],
     [13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9]],
    [[10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8],
     [13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1],
     [13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7],
     [1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12]],
    [[7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15],
     [13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9],
     [10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4],
     [3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14]],
    [[2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9],
     [14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6],
     [4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14],
     [11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3]],
    [[12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11],
     [10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8],
     [9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6],
     [4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13]],
    [[4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1],
     [13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6],
     [1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2],
     [6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12]],
    [[13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7],
     [1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2],
     [7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8],
     [2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11]]]


def permute(x, table, width):
    """The bits of x (width bits, bit 1 the most significant) that table picks."""
    out = 0
    for t in table:
        out = (out << 1) | ((x >> (width - t)) & 1)
    return out


def des_subkeys(key8):
    k = int.from_bytes(key8, "big")
    cd = permute(k, PC1, 64)
    c, d = cd >> 28, cd & 0xFFFFFFF
    out = []
    for s in SHIFTS:
        c = ((c << s) | (c >> (28 - s))) & 0xFFFFFFF
        d = ((d << s) | (d >> (28 - s))) & 0xFFFFFFF
        out.append(permute((c << 28) | d, PC2, 56))
    return out


def des_f(r, k):
    x = permute(r, E, 32) ^ k
    out = 0
    for i in range(8):
        b = (x >> (42 - 6 * i)) & 63
        row = ((b >> 4) & 2) | (b & 1)
        col = (b >> 1) & 15
        out = (out << 4) | SBOX[i][row][col]
    return permute(out, P, 32)


def des_block(block8, subkeys):
    x = permute(int.from_bytes(block8, "big"), IP, 64)
    l, r = x >> 32, x & M32
    for k in subkeys:
        l, r = r, l ^ des_f(r, k)
    return permute((r << 32) | l, FP, 64).to_bytes(8, "big")


def des_encrypt(key8, block8):
    return des_block(block8, des_subkeys(key8))


def des_decrypt(key8, block8):
    return des_block(block8, des_subkeys(key8)[::-1])


def tdes_keys(key):
    k1, k2 = key[0:8], key[8:16]
    k3 = key[16:24] if len(key) == 24 else k1
    return k1, k2, k3


def tdes_encrypt(key, block8):
    k1, k2, k3 = tdes_keys(key)
    return des_encrypt(k3, des_decrypt(k2, des_encrypt(k1, block8)))


def tdes_decrypt(key, block8):
    k1, k2, k3 = tdes_keys(key)
    return des_decrypt(k1, des_encrypt(k2, des_decrypt(k3, block8)))


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


# ---------------------------------------------------------------- Twofish
# Schneier, Kelsey, Whiting, Wagner, Hall, Ferguson, "Twofish: A 128-Bit
# Block Cipher" (1998).

Q_T = [
    [[0x8, 0x1, 0x7, 0xD, 0x6, 0xF, 0x3, 0x2, 0x0, 0xB, 0x5, 0x9, 0xE, 0xC, 0xA, 0x4],
     [0xE, 0xC, 0xB, 0x8, 0x1, 0x2, 0x3, 0x5, 0xF, 0x4, 0xA, 0x6, 0x7, 0x0, 0x9, 0xD],
     [0xB, 0xA, 0x5, 0xE, 0x6, 0xD, 0x9, 0x0, 0xC, 0x8, 0xF, 0x3, 0x2, 0x4, 0x7, 0x1],
     [0xD, 0x7, 0xF, 0x4, 0x1, 0x2, 0x6, 0xE, 0x9, 0xB, 0x3, 0x0, 0x8, 0x5, 0xC, 0xA]],
    [[0x2, 0x8, 0xB, 0xD, 0xF, 0x7, 0x6, 0xE, 0x3, 0x1, 0x9, 0x4, 0x0, 0xA, 0xC, 0x5],
     [0x1, 0xE, 0x2, 0xB, 0x4, 0xC, 0x3, 0x7, 0x6, 0xD, 0xA, 0x5, 0xF, 0x9, 0x0, 0x8],
     [0x4, 0xC, 0x7, 0x5, 0x1, 0x6, 0x9, 0xA, 0x0, 0xE, 0xD, 0x8, 0x2, 0xB, 0x3, 0xF],
     [0xB, 0x9, 0x5, 0x1, 0xC, 0x3, 0xD, 0xE, 0x6, 0x4, 0x7, 0xF, 0x2, 0x0, 0x8, 0xA]]]


def ror4(x, n):
    return ((x >> n) | (x << (4 - n))) & 15


def q(which, x):
    t = Q_T[which]
    a0, b0 = x >> 4, x & 15
    a1 = a0 ^ b0
    b1 = a0 ^ ror4(b0, 1) ^ ((8 * a0) & 15)
    a2, b2 = t[0][a1], t[1][b1]
    a3 = a2 ^ b2
    b3 = a2 ^ ror4(b2, 1) ^ ((8 * a2) & 15)
    a4, b4 = t[2][a3], t[3][b3]
    return 16 * b4 + a4


def gf_mul(a, b, poly):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        if a & 0x100:
            a ^= poly
        b >>= 1
    return r


MDS = [[0x01, 0xEF, 0x5B, 0x5B], [0x5B, 0xEF, 0xEF, 0x01],
       [0xEF, 0x5B, 0x01, 0xEF], [0xEF, 0x01, 0xEF, 0x5B]]
RS = [[0x01, 0xA4, 0x55, 0x87, 0x5A, 0x58, 0xDB, 0x9E],
      [0xA4, 0x56, 0x82, 0xF3, 0x1E, 0xC6, 0x68, 0xE5],
      [0x02, 0xA1, 0xFC, 0xC1, 0x47, 0xAE, 0x3D, 0x19],
      [0xA4, 0x55, 0x87, 0x5A, 0x58, 0xDB, 0x9E, 0x03]]


def tf_h(x, l):
    k = len(l)
    y = [(x >> (8 * i)) & 255 for i in range(4)]
    lb = [[(w >> (8 * i)) & 255 for i in range(4)] for w in l]
    if k == 4:
        y = [q(1, y[0]) ^ lb[3][0], q(0, y[1]) ^ lb[3][1], q(0, y[2]) ^ lb[3][2], q(1, y[3]) ^ lb[3][3]]
    if k >= 3:
        y = [q(1, y[0]) ^ lb[2][0], q(1, y[1]) ^ lb[2][1], q(0, y[2]) ^ lb[2][2], q(0, y[3]) ^ lb[2][3]]
    y = [q(1, q(0, q(0, y[0]) ^ lb[1][0]) ^ lb[0][0]),
         q(0, q(0, q(1, y[1]) ^ lb[1][1]) ^ lb[0][1]),
         q(1, q(1, q(0, y[2]) ^ lb[1][2]) ^ lb[0][2]),
         q(0, q(1, q(1, y[3]) ^ lb[1][3]) ^ lb[0][3])]
    z = 0
    for i in range(4):
        v = 0
        for j in range(4):
            v ^= gf_mul(MDS[i][j], y[j], 0x169)
        z |= v << (8 * i)
    return z


def tf_keys(key):
    assert len(key) in (16, 24, 32)
    k = len(key) // 8
    m = words_le(key)
    me, mo = m[0::2], m[1::2]
    s = []
    for i in range(k):
        v = 0
        for r in range(4):
            acc = 0
            for c in range(8):
                acc ^= gf_mul(RS[r][c], key[8 * i + c], 0x14D)
            v |= acc << (8 * r)
        s.append(v)
    s = s[::-1]
    rho = 0x01010101
    ks = []
    for i in range(20):
        a = tf_h((2 * i * rho) & M32, me)
        b = rol(tf_h(((2 * i + 1) * rho) & M32, mo), 8)
        ks.append((a + b) & M32)
        ks.append(rol((a + 2 * b) & M32, 9))
    return ks, s


def tf_f(r0, r1, r, ks, s):
    t0 = tf_h(r0, s)
    t1 = tf_h(rol(r1, 8), s)
    return (t0 + t1 + ks[2 * r + 8]) & M32, (t0 + 2 * t1 + ks[2 * r + 9]) & M32


def twofish_encrypt(key, block):
    ks, s = tf_keys(key)
    r = [w ^ ks[i] for i, w in enumerate(words_le(block))]
    for rnd in range(16):
        f0, f1 = tf_f(r[0], r[1], rnd, ks, s)
        r = [ror(r[2] ^ f0, 1), rol(r[3], 1) ^ f1, r[0], r[1]]
    return bytes_le([r[(i + 2) % 4] ^ ks[i + 4] for i in range(4)])


def twofish_decrypt(key, block):
    ks, s = tf_keys(key)
    c = words_le(block)
    r = [0, 0, 0, 0]
    for i in range(4):
        r[(i + 2) % 4] = c[i] ^ ks[i + 4]
    for rnd in reversed(range(16)):
        a, b, c0, c1 = r
        f0, f1 = tf_f(c0, c1, rnd, ks, s)
        r = [c0, c1, rol(a, 1) ^ f0, ror(b ^ f1, 1)]
    return bytes_le([w ^ ks[i] for i, w in enumerate(r)])


# ---------------------------------------------------------------- RC4
# The key-scheduling and output algorithms as RFC 6229 describes them.

def rc4_keystream(key, n, drop=0):
    s = list(range(256))
    j = 0
    for i in range(256):
        j = (j + s[i] + key[i % len(key)]) & 255
        s[i], s[j] = s[j], s[i]
    i = j = 0
    out = []
    for _ in range(drop + n):
        i = (i + 1) & 255
        j = (j + s[i]) & 255
        s[i], s[j] = s[j], s[i]
        out.append(s[(s[i] + s[j]) & 255])
    return bytes(out[drop:])


# ---------------------------------------------------------------- SM4
# GB/T 32907-2016 (English description: draft-ribose-cfrg-sm4, RFC 8998).

SM4_S = bytes.fromhex(
    "d690e9fecce13db716b614c228fb2c05" "2b679a762abe04c3aa44132649860699"
    "9c4250f491ef987a33540b43edcfac62" "e4b31ca9c908e89580df94fa758f3fa6"
    "4707a7fcf37317ba83593c19e6854fa8" "686b81b27164da8bf8eb0f4b70569d35"
    "1e240e5e6358d1a225227c3b01217887" "d40046579fd327524c3602e7a0c4c89e"
    "eabf8ad240c738b5a3f7f2cef96115a1" "e0ae5da49b341a55ad933230f58cb1e3"
    "1df6e22e8266ca60c02923ab0d534e6f" "d5db3745defd8e2f03ff6a726d6c5b51"
    "8d1baf92bbddbc7f11d95c411f105ad8" "0ac13188a5cd7bbd2d74d012b8e5b4b0"
    "8969974a0c96777e65b9f109c56ec684" "18f07dec3adc4d2079ee5f3ed7cb3948")
SM4_FK = [0xA3B1BAC6, 0x56AA3350, 0x677D9197, 0xB27022DC]


def sm4_tau(x):
    return int.from_bytes(bytes(SM4_S[b] for b in x.to_bytes(4, "big")), "big")


def sm4_t(x):
    b = sm4_tau(x)
    return b ^ rol(b, 2) ^ rol(b, 10) ^ rol(b, 18) ^ rol(b, 24)


def sm4_t_key(x):
    b = sm4_tau(x)
    return b ^ rol(b, 13) ^ rol(b, 23)


def sm4_keys(key):
    k = [int.from_bytes(key[4 * i:4 * i + 4], "big") ^ SM4_FK[i] for i in range(4)]
    rk = []
    for i in range(32):
        ck = int.from_bytes(bytes(((4 * i + j) * 7) & 255 for j in range(4)), "big")
        k.append(k[i] ^ sm4_t_key(k[i + 1] ^ k[i + 2] ^ k[i + 3] ^ ck))
        rk.append(k[-1])
    return rk


def sm4_block(block, rk):
    x = [int.from_bytes(block[4 * i:4 * i + 4], "big") for i in range(4)]
    for i in range(32):
        x.append(x[i] ^ sm4_t(x[i + 1] ^ x[i + 2] ^ x[i + 3] ^ rk[i]))
    return b"".join(w.to_bytes(4, "big") for w in x[:-5:-1])


def sm4_encrypt(key, block):
    return sm4_block(block, sm4_keys(key))


def sm4_decrypt(key, block):
    return sm4_block(block, sm4_keys(key)[::-1])


# ---------------------------------------------------------------- Camellia
# RFC 3713.

CAM_S1 = [
    112, 130, 44, 236, 179, 39, 192, 229, 228, 133, 87, 53, 234, 12, 174, 65,
    35, 239, 107, 147, 69, 25, 165, 33, 237, 14, 79, 78, 29, 101, 146, 189,
    134, 184, 175, 143, 124, 235, 31, 206, 62, 48, 220, 95, 94, 197, 11, 26,
    166, 225, 57, 202, 213, 71, 93, 61, 217, 1, 90, 214, 81, 86, 108, 77,
    139, 13, 154, 102, 251, 204, 176, 45, 116, 18, 43, 32, 240, 177, 132, 153,
    223, 76, 203, 194, 52, 126, 118, 5, 109, 183, 169, 49, 209, 23, 4, 215,
    20, 88, 58, 97, 222, 27, 17, 28, 50, 15, 156, 22, 83, 24, 242, 34,
    254, 68, 207, 178, 195, 181, 122, 145, 36, 8, 232, 168, 96, 252, 105, 80,
    170, 208, 160, 125, 161, 137, 98, 151, 84, 91, 30, 149, 224, 255, 100, 210,
    16, 196, 0, 72, 163, 247, 117, 219, 138, 3, 230, 218, 9, 63, 221, 148,
    135, 92, 131, 2, 205, 74, 144, 51, 115, 103, 246, 243, 157, 127, 191, 226,
    82, 155, 216, 38, 200, 55, 198, 59, 129, 150, 111, 75, 19, 190, 99, 46,
    233, 121, 167, 140, 159, 110, 188, 142, 41, 245, 249, 182, 47, 253, 180, 89,
    120, 152, 6, 106, 231, 70, 113, 186, 212, 37, 171, 66, 136, 162, 141, 250,
    114, 7, 185, 85, 248, 238, 172, 10, 54, 73, 42, 104, 60, 56, 241, 164,
    64, 40, 211, 123, 187, 201, 67, 193, 21, 227, 173, 244, 119, 199, 128, 158]
CAM_SIGMA = [0xA09E667F3BCC908B, 0xB67AE8584CAA73B2, 0xC6EF372FE94F82BE,
             0x54FF53A5F1D36F1C, 0x10E527FADE682D1D, 0xB05688C2B3E6C1FD]
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1


def rol8(x, n):
    return ((x << n) | (x >> (8 - n))) & 255


def cam_s(n, x):
    if n == 1:
        return CAM_S1[x]
    if n == 2:
        return rol8(CAM_S1[x], 1)
    if n == 3:
        return rol8(CAM_S1[x], 7)
    return CAM_S1[rol8(x, 1)]


def cam_f(x, k):
    x ^= k
    t = [(x >> (56 - 8 * i)) & 255 for i in range(8)]
    t = [cam_s(n, v) for n, v in zip([1, 2, 3, 4, 2, 3, 4, 1], t)]
    t1, t2, t3, t4, t5, t6, t7, t8 = t
    y = [t1 ^ t3 ^ t4 ^ t6 ^ t7 ^ t8, t1 ^ t2 ^ t4 ^ t5 ^ t7 ^ t8,
         t1 ^ t2 ^ t3 ^ t5 ^ t6 ^ t8, t2 ^ t3 ^ t4 ^ t5 ^ t6 ^ t7,
         t1 ^ t2 ^ t6 ^ t7 ^ t8, t2 ^ t3 ^ t5 ^ t7 ^ t8,
         t3 ^ t4 ^ t5 ^ t6 ^ t8, t1 ^ t4 ^ t5 ^ t6 ^ t7]
    out = 0
    for v in y:
        out = (out << 8) | v
    return out


def cam_fl(x, k):
    x1, x2 = x >> 32, x & M32
    k1, k2 = k >> 32, k & M32
    x2 ^= rol(x1 & k1, 1)
    x1 ^= x2 | k2
    return (x1 << 32) | x2


def cam_flinv(y, k):
    y1, y2 = y >> 32, y & M32
    k1, k2 = k >> 32, k & M32
    y1 ^= y2 | k2
    y2 ^= rol(y1 & k1, 1)
    return (y1 << 32) | y2


def rol128(x, n):
    n %= 128
    return ((x << n) | (x >> (128 - n))) & M128 if n else x


def cam_keys(key):
    n = len(key)
    k = int.from_bytes(key, "big")
    if n == 16:
        kl, kr = k, 0
    elif n == 24:
        kl = k >> 64
        r = k & M64
        kr = (r << 64) | (~r & M64)
    else:
        kl, kr = k >> 128, k & M128
    d1 = (kl ^ kr) >> 64
    d2 = (kl ^ kr) & M64
    d2 ^= cam_f(d1, CAM_SIGMA[0])
    d1 ^= cam_f(d2, CAM_SIGMA[1])
    d1 ^= kl >> 64
    d2 ^= kl & M64
    d2 ^= cam_f(d1, CAM_SIGMA[2])
    d1 ^= cam_f(d2, CAM_SIGMA[3])
    ka = (d1 << 64) | d2
    d1 = (ka ^ kr) >> 64
    d2 = (ka ^ kr) & M64
    d2 ^= cam_f(d1, CAM_SIGMA[4])
    d1 ^= cam_f(d2, CAM_SIGMA[5])
    kb = (d1 << 64) | d2

    def hi(v, r):
        return rol128(v, r) >> 64

    def lo(v, r):
        return rol128(v, r) & M64

    if n == 16:
        kw = [hi(kl, 0), lo(kl, 0), hi(ka, 111), lo(ka, 111)]
        ks = [hi(ka, 0), lo(ka, 0), hi(kl, 15), lo(kl, 15), hi(ka, 15), lo(ka, 15),
              hi(kl, 45), lo(kl, 45), hi(ka, 45), lo(kl, 60), hi(ka, 60), lo(ka, 60),
              hi(kl, 94), lo(kl, 94), hi(ka, 94), lo(ka, 94), hi(kl, 111), lo(kl, 111)]
        ke = [hi(ka, 30), lo(ka, 30), hi(kl, 77), lo(kl, 77)]
    else:
        kw = [hi(kl, 0), lo(kl, 0), hi(kb, 111), lo(kb, 111)]
        ks = [hi(kb, 0), lo(kb, 0), hi(kr, 15), lo(kr, 15), hi(ka, 15), lo(ka, 15),
              hi(kb, 30), lo(kb, 30), hi(kl, 45), lo(kl, 45), hi(ka, 45), lo(ka, 45),
              hi(kr, 60), lo(kr, 60), hi(kb, 60), lo(kb, 60), hi(kl, 77), lo(kl, 77),
              hi(kr, 94), lo(kr, 94), hi(ka, 94), lo(ka, 94), hi(kl, 111), lo(kl, 111)]
        ke = [hi(kr, 30), lo(kr, 30), hi(kl, 60), lo(kl, 60), hi(ka, 77), lo(ka, 77)]
    return kw, ks, ke


def camellia_encrypt(key, block):
    kw, ks, ke = cam_keys(key)
    m = int.from_bytes(block, "big")
    d1, d2 = (m >> 64) ^ kw[0], (m & M64) ^ kw[1]
    for i in range(len(ks) // 2):
        if i and i % 3 == 0:
            j = i // 3 - 1
            d1, d2 = cam_fl(d1, ke[2 * j]), cam_flinv(d2, ke[2 * j + 1])
        d2 ^= cam_f(d1, ks[2 * i])
        d1 ^= cam_f(d2, ks[2 * i + 1])
    d2 ^= kw[2]
    d1 ^= kw[3]
    return ((d2 << 64) | d1).to_bytes(16, "big")


def camellia_decrypt(key, block):
    kw, ks, ke = cam_keys(key)
    c = int.from_bytes(block, "big")
    d2, d1 = (c >> 64) ^ kw[2], (c & M64) ^ kw[3]
    for i in reversed(range(len(ks) // 2)):
        d1 ^= cam_f(d2, ks[2 * i + 1])
        d2 ^= cam_f(d1, ks[2 * i])
        if i and i % 3 == 0:
            j = i // 3 - 1
            d1, d2 = cam_flinv(d1, ke[2 * j]), cam_fl(d2, ke[2 * j + 1])
    return (((d1 ^ kw[0]) << 64) | (d2 ^ kw[1])).to_bytes(16, "big")


# ---------------------------------------------------------------- tables
# The newer ciphers' constant tables are transcribed (or computed) once, in
# gen/tables.py, which both the Bend code's generator and these models use;
# the published vectors, and Python's cryptography (CAST5, Blowfish) and
# OpenSSL (ARIA), check them in ref/gen.py.
import os as _os
import sys as _sys

_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "..", "gen"))
import tables as _t  # noqa: E402


# ---------------------------------------------------------------- TEA, XTEA
# D. Wheeler, R. Needham, "TEA, a Tiny Encryption Algorithm" (FSE 1994), and
# R. Needham, D. Wheeler, "Tea extensions" (1997). The papers work on 32-bit
# words; the byte order of a block and a key is a choice ("little" is the
# Linux kernel's).

TEA_DELTA = 0x9E3779B9


def _words(b, order):
    return [int.from_bytes(b[4 * i:4 * i + 4], order) for i in range(len(b) // 4)]


def _tea_g(x, s, a, b):
    return ((((x << 4) & M32) + a) ^ ((x + s) & M32) ^ ((x >> 5) + b)) & M32


def tea_encrypt(key, block, order="little", cycles=32):
    k = _words(key, order)
    y, z = _words(block, order)
    s = 0
    for _ in range(cycles):
        s = (s + TEA_DELTA) & M32
        y = (y + _tea_g(z, s, k[0], k[1])) & M32
        z = (z + _tea_g(y, s, k[2], k[3])) & M32
    return y.to_bytes(4, order) + z.to_bytes(4, order)


def tea_decrypt(key, block, order="little", cycles=32):
    k = _words(key, order)
    y, z = _words(block, order)
    s = (TEA_DELTA * cycles) & M32
    for _ in range(cycles):
        z = (z - _tea_g(y, s, k[2], k[3])) & M32
        y = (y - _tea_g(z, s, k[0], k[1])) & M32
        s = (s - TEA_DELTA) & M32
    return y.to_bytes(4, order) + z.to_bytes(4, order)


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
