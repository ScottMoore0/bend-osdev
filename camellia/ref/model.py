"""An independent Python model of the camellia package's cipher (Camellia).

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
