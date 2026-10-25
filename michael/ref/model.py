#!/usr/bin/env python3
"""A Python model of Michael (IEEE 802.11i), written from the specification.
Python has no Michael, so the differential test (ref/gen.py) is
against this model.
The model shares an author with the package, so it is checked first against
the specification's own vectors (check_vectors below).

  python3 ref/model.py      checks the model against its vectors
"""
import struct

M = 0xFFFFFFFF


def rol(x, n):
    return ((x << n) | (x >> (32 - n))) & M


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
    assert michael(TKIP_M63_KEY, TKIP_M63_INPUT).hex() == TKIP_M63_MIC
    for k, m, v in MICHAEL_V:
        assert michael(bytes.fromhex(k), m).hex() == v, ("michael", m)
    for x, n, v in MICHAEL_B:
        for _ in range(n):
            x = michael_b(*x)
        assert x == v, ("michael_b", n)


if __name__ == "__main__":
    check_vectors()
    print("the model matches the specification's vectors")
