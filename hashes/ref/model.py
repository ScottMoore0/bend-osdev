#!/usr/bin/env python3
"""Python models of the hashes package's algorithms, written from the
specifications (the tables are gen/spec.py's), for the algorithms Python's
hashlib lacks here: MD4 (RFC 1320; OpenSSL 3 keeps it in its legacy
provider), Streebog (RFC 6986) and Michael (IEEE 802.11i). The models share
an author with the package, so they are checked first against the
specifications' own vectors (check_vectors below), and MD5, SHA-1,
RIPEMD-160 and SM3 are modelled too so that the models themselves are
checked against hashlib.

  python3 ref/model.py      checks every model against its vectors
"""
import hashlib, os, struct, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "gen"))
import spec  # noqa: E402

M = 0xFFFFFFFF


def rol(x, n):
    return ((x << n) | (x >> (32 - n))) & M


def md_pad(m, big):
    n = len(m)
    p = m + b"\x80" + b"\x00" * ((55 - n) % 64)
    return p + struct.pack(">Q" if big else "<Q", (8 * n) & (2 ** 64 - 1))


def blocks(p, big):
    fmt = ">16I" if big else "<16I"
    for i in range(0, len(p), 64):
        yield list(struct.unpack(fmt, p[i:i + 64]))


def md4(m):
    h = list(spec.MD4_IV)
    F = [lambda x, y, z: (x & y) | (~x & z), lambda x, y, z: (x & y) | (x & z) | (y & z), lambda x, y, z: x ^ y ^ z]
    for X in blocks(md_pad(m, False), False):
        a, b, c, d = h
        for r in range(3):
            for i in range(16):
                k = spec.MD4_X[r][i]
                t = rol((a + F[r](b, c, d) + X[k] + spec.MD4_K[r]) & M, spec.MD4_S[r][i % 4])
                a, b, c, d = d, t, b, c
        h = [(u + v) & M for u, v in zip(h, [a, b, c, d])]
    return struct.pack("<4I", *h)


def md5(m):
    h = list(spec.MD5_IV)
    F = [lambda x, y, z: (x & y) | (~x & z), lambda x, y, z: (x & z) | (y & ~z),
         lambda x, y, z: x ^ y ^ z, lambda x, y, z: y ^ (x | (~z & M))]
    for X in blocks(md_pad(m, False), False):
        a, b, c, d = h
        for j in range(64):
            r = j // 16
            t = (a + F[r](b, c, d) + X[spec.MD5_X[r][j % 16]] + spec.MD5_T[j]) & M
            a, b, c, d = d, (b + rol(t, spec.MD5_S[r][j % 4])) & M, b, c
        h = [(u + v) & M for u, v in zip(h, [a, b, c, d])]
    return struct.pack("<4I", *h)


def sha1(m):
    h = list(spec.SHA1_IV)
    for W in blocks(md_pad(m, True), True):
        for t in range(16, 80):
            W.append(rol(W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16], 1))
        a, b, c, d, e = h
        for t in range(80):
            if t < 20:
                f = (b & c) | (~b & d)
            elif t < 40 or t >= 60:
                f = b ^ c ^ d
            else:
                f = (b & c) | (b & d) | (c & d)
            a, b, c, d, e = (rol(a, 5) + (f & M) + e + spec.SHA1_K[t // 20] + W[t]) & M, a, rol(b, 30), c, d
        h = [(u + v) & M for u, v in zip(h, [a, b, c, d, e])]
    return struct.pack(">5I", *h)


def ripemd160(m):
    f = [lambda x, y, z: x ^ y ^ z, lambda x, y, z: (x & y) | (~x & z), lambda x, y, z: (x | ~y) ^ z,
         lambda x, y, z: (x & z) | (y & ~z), lambda x, y, z: x ^ (y | ~z)]
    h = list(spec.RMD_IV)
    for X in blocks(md_pad(m, False), False):
        a, b, c, d, e = h
        a2, b2, c2, d2, e2 = h
        for j in range(80):
            r = j // 16
            t = (rol((a + (f[r](b, c, d) & M) + X[spec.RMD_R[r][j % 16]] + spec.RMD_K[r]) & M, spec.RMD_S[r][j % 16]) + e) & M
            a, e, d, c, b = e, d, rol(c, 10), b, t
            t = (rol((a2 + (f[4 - r](b2, c2, d2) & M) + X[spec.RMD_RP[r][j % 16]] + spec.RMD_KP[r]) & M, spec.RMD_SP[r][j % 16]) + e2) & M
            a2, e2, d2, c2, b2 = e2, d2, rol(c2, 10), b2, t
        t = (h[1] + c + d2) & M
        h = [t, (h[2] + d + e2) & M, (h[3] + e + a2) & M, (h[4] + a + b2) & M, (h[0] + b + c2) & M]
    return struct.pack("<5I", *h)


def sm3(m):
    P0 = lambda x: x ^ rol(x, 9) ^ rol(x, 17)
    P1 = lambda x: x ^ rol(x, 15) ^ rol(x, 23)
    v = list(spec.SM3_IV)
    for W in blocks(md_pad(m, True), True):
        for j in range(16, 68):
            W.append(P1(W[j - 16] ^ W[j - 9] ^ rol(W[j - 3], 15)) ^ rol(W[j - 13], 7) ^ W[j - 6])
        A, B, C, D, E, F, G, H = v
        for j in range(64):
            ss1 = rol((rol(A, 12) + E + rol(spec.SM3_T[j], j % 32)) & M, 7)
            ss2 = ss1 ^ rol(A, 12)
            ff = A ^ B ^ C if j < 16 else (A & B) | (A & C) | (B & C)
            gg = E ^ F ^ G if j < 16 else (E & F) | (~E & G)
            tt1 = (ff + D + ss2 + (W[j] ^ W[j + 4])) & M
            tt2 = ((gg & M) + H + ss1 + W[j]) & M
            A, B, C, D = tt1, A, rol(B, 9), C
            E, F, G, H = P0(tt2), E, rol(F, 19), G
        v = [x ^ y for x, y in zip(v, [A, B, C, D, E, F, G, H])]
    return struct.pack(">8I", *v)


# Streebog: a 512-bit vector is an integer; byte i (i = 0 the least
# significant) is the i-th byte of the 64-byte string in memory order, as
# RFC 6986 writes its examples a_63 || ... || a_0
def stb_lps(x):
    bs = x.to_bytes(64, "little")
    bs = bytes(spec.STB_PI[b] for b in bs)
    bs = bytes(bs[spec.STB_TAU[i]] for i in range(64))
    out = 0
    for k in range(8):
        v = int.from_bytes(bs[8 * k:8 * k + 8], "little")
        r = 0
        for i in range(64):
            if v >> i & 1:
                r ^= spec.STB_A[63 - i]
        out |= r << (64 * k)
    return out


def stb_g(N, h, m):
    k = stb_lps(h ^ N)
    t = m
    for i in range(12):
        t = stb_lps(t ^ k)
        k = stb_lps(k ^ spec.STB_C[i])
    return t ^ k ^ h ^ m


def streebog(m, bits):
    h = int.from_bytes(b"\x01" * 64, "little") if bits == 256 else 0
    N = S = 0
    mod = 1 << 512
    i = 0
    while len(m) - i >= 64:
        blk = int.from_bytes(m[i:i + 64], "little")
        h = stb_g(N, h, blk)
        N = (N + 512) % mod
        S = (S + blk) % mod
        i += 64
    rest = m[i:]
    blk = int.from_bytes(rest + b"\x01" + b"\x00" * (63 - len(rest)), "little")
    h = stb_g(N, h, blk)
    N = (N + 8 * len(rest)) % mod
    S = (S + blk) % mod
    h = stb_g(0, h, N)
    h = stb_g(0, h, S)
    out = h.to_bytes(64, "little")
    return out[32:] if bits == 256 else out


def streebog256(m):
    return streebog(m, 256)


def streebog512(m):
    return streebog(m, 512)


def michael_b(l, r):
    r ^= rol(l, 17); l = (l + r) & M
    r ^= ((l & 0xFF00FF00) >> 8) | ((l & 0x00FF00FF) << 8); l = (l + r) & M
    r ^= rol(l, 3); l = (l + r) & M
    r ^= rol(l, 30); l = (l + r) & M
    return l, r


def michael(key, m):
    l, r = struct.unpack("<2I", key)
    p = m + b"\x5a" + b"\x00" * (4 + (3 - len(m)) % 4)
    assert len(p) % 4 == 0
    for (w,) in struct.iter_unpack("<I", p):
        l ^= w
        r ^= rol(l, 17); l = (l + r) & M
        r ^= ((l & 0xFF00FF00) >> 8) | ((l & 0x00FF00FF) << 8); l = (l + r) & M
        r ^= rol(l, 3); l = (l + r) & M
        r ^= rol(l, 30); l = (l + r) & M
    return struct.pack("<2I", l, r)


# ------------------------------------------------------------------ vectors

ASCII = [b"", b"a", b"abc", b"message digest", b"abcdefghijklmnopqrstuvwxyz",
         b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789", b"1234567890" * 8]
# RFC 1320, A.5 and RFC 1321, A.5 (the same seven messages)
MD4_V = ["31d6cfe0d16ae931b73c59d7e0c089c0", "bde52cb31de33e46245e05fbdbd6fb24", "a448017aaf21d8525fc10ae87aa6729d",
         "d9130a8164549fe818874806e1c7014b", "d79e1c308aa5bbcdeea8ed63df412da9", "043f8582f241db351ce627e153e7f0e4",
         "e33b4ddc9c38f2199c3e7b164fcc0536"]
MD5_V = ["d41d8cd98f00b204e9800998ecf8427e", "0cc175b9c0f1b6a831c399e269772661", "900150983cd24fb0d6963f7d28e17f72",
         "f96b697d7cb7938d525a2f31aaf161d0", "c3fcd3d76192e4007dfb496cca67e13b", "d174ab98d277d9f5a5611c2c9f419d9f",
         "57edf4a22be3c955ac49da2e2107b67a"]
# FIPS 180-4's examples (NIST's SHA-1 example values): "abc" and the 448-bit message
SHA1_V = [(b"abc", "a9993e364706816aba3e25717850c26c9cd0d89d"),
          (b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "84983e441c3bd26ebaae4aa1f95129e5e54670f1")]
# the RIPEMD-160 page of Bosselaers (the paper's test values)
RMD_V = [(b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31"), (b"a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
         (b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"), (b"message digest", "5d0689ef49d2fae572b881b123a85ffa21595f36"),
         (b"abcdefghijklmnopqrstuvwxyz", "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
         (b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "12a053384a9c0c88e405a06c27dcf49ada62eb2b"),
         (ASCII[5], "b0e20b6e3116640286ed3a87a5713079b21f5189"), (ASCII[6], "9b752e45573d4b39f4dbd3323cab82bf63326bfb")]
# draft-shen-sm3-hash, examples 1 and 2
SM3_V = [(b"abc", "66c7f0f462eeedd9d1f2d46bdc10e4e24167c4875cf2f7a2297da02b8f4ba8e0"),
         (b"abcd" * 16, "debe9ff92275b8a138604889c18e5a4d6fdb70e5387e5765293dcba39c0c5732")]
# RFC 6986, section 10: M1 and M2 and their hash codes, as the RFC writes
# them (most significant byte first: the reverse of memory order)
STB_M1 = b"012345678901234567890123456789012345678901234567890123456789012"
STB_M2 = bytes.fromhex("fbe2e5f0eee3c820fbeafaebef20fffbf0e1e0f0f520e0ed20e8ece0ebe5f0f2f120fff0eeec20f120faf2fee5e2202ce8"
                       "f6f3ede220e8e6eee1e8f0f2d1202ce8f0f2e5e220e5d1")[::-1]
STB_V = [(STB_M1, 512, "486f64c1917879417fef082b3381a4e211c324f074654c38823a7b76f830ad00"
                       "fa1fbae42b1285c0352f227524bc9ab16254288dd6863dccd5b9f54a1ad0541b"),
         (STB_M1, 256, "00557be5e584fd52a449b16b0251d05d27f94ab76cbaa6da890b59d8ef1e159d"),
         (STB_M2, 512, "28fbc9bada033b1460642bdcddb90c3fb3e56c497ccd0f62b8a2ad4935e85f03"
                       "7613966de4ee00531ae60f3b5a47f8dae06915d5f2f194996fcabf2622e6881e"),
         (STB_M2, 256, "508f7e553c06501d749a66fc28c6cac0b005746d97537fa85d9e40904efed29d")]
# RFC 6986, section 10.1 (example 1, the 512-bit hash): K = LPS(0^512),
# the first g_N(h, m), and g_0(h, N) after it, as the RFC prints them
STB_EX1 = ["b383fc2eced4a574" * 8,
           "fd102cf8812ccb1191ea34af21394f3817a86641445aa9a626488adb33738ebd"
           "2754f6908cbbbac5d3ed0f522c50815c954135793fb1f5d905fee4736b3bdae2",
           "5c881fd924695cf196c2e4fec20d14b642026f2a0b1716ebaabb7067d4d59752"
           "3d2db69d6d3794622147a14f19a66e7f9037e1d662d34501a8901a5de7771d7c"]
# Michael's test vectors, each key the previous MIC: IEEE Std 802.11-2024,
# Annex J.2.1.3, Table J-2 (README.md, Specifications)
# IEEE Std 802.11-2012, M.6.3 (the TKIP test vector), as hostap's
# BSD-licensed wlantest/test_vectors.c (test_vector_tkip) reproduces its
# data: TK = 12 34 56 78 90 repeated (32 bytes), a FromDS data frame with
# A1 = DA = 02:03:04:05:06:08 and A2 = A3 = SA = 02:03:04:05:06:07, no QoS
# (priority 0), a 92-byte MSDU, and the 8 bytes that follow it in the
# plaintext MPDU (commented out there): its MIC. Michael's input is DA, SA,
# the priority and three zero bytes, then the MSDU; the key is TK bytes 16
# to 23. Read as test data only.
TKIP_M63_KEY = bytes([0x12, 0x34, 0x56, 0x78, 0x90] * 7)[16:24]
TKIP_M63_DA = bytes.fromhex("020304050608")
TKIP_M63_SA = bytes.fromhex("020304050607")
TKIP_M63_MSDU = bytes.fromhex(
    "aaaa030000000800" "4500005400004000" "4001a555c0a80a02" "c0a80a0108003ab0" "00000000cd4c0500" "0000000008090a0b"
    "0c0d0e0f10111213" "1415161718191a1b" "1c1d1e1f20212223" "2425262728292a2b" "2c2d2e2f30313233" "34353637")
TKIP_M63_MIC = "6881a3f3d648d03c"
TKIP_M63_INPUT = TKIP_M63_DA + TKIP_M63_SA + bytes(4) + TKIP_M63_MSDU
assert len(TKIP_M63_MSDU) == 92
MICHAEL_V = [("0000000000000000", b"", "82925c1ca1d130b8"), ("82925c1ca1d130b8", b"M", "434721ca40639b3f"),
             ("434721ca40639b3f", b"Mi", "e8f9becae97e5d29"), ("e8f9becae97e5d29", b"Mic", "90038fc6cf13c1db"),
             ("90038fc6cf13c1db", b"Mich", "d55e100510128986"), ("d55e100510128986", b"Michael", "0a942b124ecaa546")]
# Michael's block function b: IEEE Std 802.11-2024, Annex J.2.1.2, Table J-1,
# ((l, r) in, the number of applications, (l, r) out)
MICHAEL_B = [((0x00000000, 0x00000000), 1, (0x00000000, 0x00000000)), ((0x00000000, 0x00000001), 1, (0xc00015a8, 0xc0000b95)),
             ((0x00000001, 0x00000000), 1, (0x6b519593, 0x572b8b8a)), ((0x01234567, 0x83659326), 1, (0x441492c2, 0x1d8427ed)),
             ((0x00000001, 0x00000000), 1000, (0x9f04c4ad, 0x2ec6c2bf))]


def check_vectors():
    for m, v in zip(ASCII, MD4_V):
        assert md4(m).hex() == v, ("md4", m)
    for m, v in zip(ASCII, MD5_V):
        assert md5(m).hex() == v, ("md5", m)
    for m, v in SHA1_V:
        assert sha1(m).hex() == v, ("sha1", m)
    for m, v in RMD_V:
        assert ripemd160(m).hex() == v, ("ripemd160", m)
    for m, v in SM3_V:
        assert sm3(m).hex() == v, ("sm3", m)
    assert len(STB_M2) == 72
    for m, bits, v in STB_V:
        assert streebog(m, bits)[::-1].hex() == v, ("streebog", bits, m)
    h = stb_g(0, 0, int.from_bytes(STB_M1 + bytes([1]), "little"))
    assert "%0128x" % stb_lps(0) == STB_EX1[0] and "%0128x" % h == STB_EX1[1]
    assert "%0128x" % stb_g(0, h, 504) == STB_EX1[2]
    assert michael(TKIP_M63_KEY, TKIP_M63_INPUT).hex() == TKIP_M63_MIC
    for k, m, v in MICHAEL_V:
        assert michael(bytes.fromhex(k), m).hex() == v, ("michael", m)
    for x, n, v in MICHAEL_B:
        for _ in range(n):
            x = michael_b(*x)
        assert x == v, ("michael_b", n)
    # the models Python can check: against hashlib, on a few lengths around
    # the block boundaries
    for n in [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, 200]:
        m = bytes((7 * i + 3) & 255 for i in range(n))
        assert md5(m) == hashlib.md5(m).digest()
        assert sha1(m) == hashlib.sha1(m).digest()
        for name, f in [("ripemd160", ripemd160), ("sm3", sm3)]:
            if name in hashlib.algorithms_available:
                assert f(m) == hashlib.new(name, m).digest(), (name, n)


if __name__ == "__main__":
    check_vectors()
    print("models match the specifications' vectors")
