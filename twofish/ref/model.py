"""An independent Python model of the twofish package's cipher (Twofish).

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
