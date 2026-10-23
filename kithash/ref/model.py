"""XXH32, XXH64 and FNV-1a in Python, for the differential test.

XXH32 and XXH64 are written from the xxHash specification (xxhash_spec.md,
"xxHash fast digest algorithm", Yann Collet, version 0.2.0); FNV-1a from
RFC 9923 ("The FNV Non-Cryptographic Hash Algorithm", 2026), section 2 and
the constants of section 5. These share an author with bend-osdev-kithash's
tests (not with bend-kit-hash); gen.py checks them first against the
outside references: the lz4 command (XXH32, a frame's content checksum), the
zstd command (the low 32 bits of XXH64, likewise) and RFC 9923's section 8.3
values (FNV-1a).
"""
M32, M64 = (1 << 32) - 1, (1 << 64) - 1
P32 = [2654435761, 2246822519, 3266489917, 668265263, 374761393]
P64 = [11400714785074694791, 14029467366897019727, 1609587929392839161, 9650029242287828579, 2870177450012600261]


def _rotl(x, r, w):
    m = (1 << w) - 1
    return ((x << r) | (x >> (w - r))) & m


def xxh32(data, seed=0):
    n, i = len(data), 0
    if n >= 16:
        acc = [(seed + P32[0] + P32[1]) & M32, (seed + P32[1]) & M32, seed & M32, (seed - P32[0]) & M32]
        while i + 16 <= n:
            for j in range(4):
                lane = int.from_bytes(data[i + 4 * j:i + 4 * j + 4], "little")
                acc[j] = (_rotl((acc[j] + lane * P32[1]) & M32, 13, 32) * P32[0]) & M32
            i += 16
        h = (_rotl(acc[0], 1, 32) + _rotl(acc[1], 7, 32) + _rotl(acc[2], 12, 32) + _rotl(acc[3], 18, 32)) & M32
    else:
        h = (seed + P32[4]) & M32
    h = (h + n) & M32
    while i + 4 <= n:
        h = (_rotl((h + int.from_bytes(data[i:i + 4], "little") * P32[2]) & M32, 17, 32) * P32[3]) & M32
        i += 4
    while i < n:
        h = (_rotl((h + data[i] * P32[4]) & M32, 11, 32) * P32[0]) & M32
        i += 1
    h ^= h >> 15; h = (h * P32[1]) & M32; h ^= h >> 13; h = (h * P32[2]) & M32; h ^= h >> 16
    return h


def _round64(acc, lane):
    return (_rotl((acc + lane * P64[1]) & M64, 31, 64) * P64[0]) & M64


def xxh64(data, seed=0):
    n, i = len(data), 0
    if n >= 32:
        acc = [(seed + P64[0] + P64[1]) & M64, (seed + P64[1]) & M64, seed & M64, (seed - P64[0]) & M64]
        while i + 32 <= n:
            for j in range(4):
                acc[j] = _round64(acc[j], int.from_bytes(data[i + 8 * j:i + 8 * j + 8], "little"))
            i += 32
        h = (_rotl(acc[0], 1, 64) + _rotl(acc[1], 7, 64) + _rotl(acc[2], 12, 64) + _rotl(acc[3], 18, 64)) & M64
        for a in acc:
            h = (((h ^ _round64(0, a)) * P64[0]) + P64[3]) & M64
    else:
        h = (seed + P64[4]) & M64
    h = (h + n) & M64
    while i + 8 <= n:
        h ^= _round64(0, int.from_bytes(data[i:i + 8], "little"))
        h = ((_rotl(h, 27, 64) * P64[0]) + P64[3]) & M64
        i += 8
    if i + 4 <= n:
        h ^= (int.from_bytes(data[i:i + 4], "little") * P64[0]) & M64
        h = ((_rotl(h, 23, 64) * P64[1]) + P64[2]) & M64
        i += 4
    while i < n:
        h ^= (data[i] * P64[4]) & M64
        h = (_rotl(h, 11, 64) * P64[0]) & M64
        i += 1
    h ^= h >> 33; h = (h * P64[1]) & M64; h ^= h >> 29; h = (h * P64[2]) & M64; h ^= h >> 32
    return h


def fnv1a32(data):
    h = 0x811C9DC5
    for b in data:
        h = ((h ^ b) * 0x01000193) & M32
    return h


def fnv1a64(data):
    h = 0xCBF29CE484222325
    for b in data:
        h = ((h ^ b) * 0x100000001B3) & M64
    return h
