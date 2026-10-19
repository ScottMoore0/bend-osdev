"""Python models of the aead package's constructions that no
outside implementation reachable here provides.

Written from the specifications (not from any implementation), by the same
author as the Bend package, so agreement with them is weaker evidence than
agreement with an outside implementation:
  * AEGIS-128: H. Wu, B. Preneel, "AEGIS: A Fast Authenticated Encryption
    Algorithm (v1.1)" (CAESAR, 2016), section 2.3; the AES round function
    from FIPS 197 section 5.1, checked against RFC 10032's AESRound test
    vector (Appendix A.1).
The other constructions are compared with outside implementations
(gen.py: the Linux kernel's, cryptography's, hmac's, hashlib's).
"""

M = (1 << 128) - 1


def _mul(a, b):
    r = 0
    for _ in range(8):
        if b & 1:
            r ^= a
        hi = a & 0x80
        a = (a << 1) & 255
        if hi:
            a ^= 0x1B
        b >>= 1
    return r


def _sbox():
    out = []
    for x in range(256):
        b = 0
        if x:
            b = 1
            for _ in range(254):
                b = _mul(b, x)
        s = b
        for i in range(1, 5):
            s ^= ((b << i) | (b >> (8 - i))) & 255
        out.append(s ^ 0x63)
    return out


SBOX = _sbox()


def aes_round(a, k):
    """AESRound(a, k) on 16-byte strings (FIPS 197: byte i is row i % 4,
    column i // 4)"""
    s = [SBOX[x] for x in a]
    t = [s[(i + 4 * (i % 4)) % 16] for i in range(16)]  # ShiftRows
    out = []
    for c in range(4):
        a0, a1, a2, a3 = t[4 * c:4 * c + 4]
        out += [_mul(a0, 2) ^ _mul(a1, 3) ^ a2 ^ a3, a0 ^ _mul(a1, 2) ^ _mul(a2, 3) ^ a3,
                a0 ^ a1 ^ _mul(a2, 2) ^ _mul(a3, 3), _mul(a0, 3) ^ a1 ^ a2 ^ _mul(a3, 2)]
    return bytes(x ^ y for x, y in zip(out, k))


assert aes_round(bytes(range(16)), bytes(range(16, 32))).hex() == "7a7b4e5638782546a8c0477a3b813f43"

C0 = bytes.fromhex("000101020305080d1522375990e97962")
C1 = bytes.fromhex("db3d18556dc22ff12011314273b528dd")


def _x(a, b):
    return bytes(p ^ q for p, q in zip(a, b))


def _and(a, b):
    return bytes(p & q for p, q in zip(a, b))


def _update(s, m):
    return [aes_round(s[4], _x(s[0], m)), aes_round(s[0], s[1]), aes_round(s[1], s[2]),
            aes_round(s[2], s[3]), aes_round(s[3], s[4])]


def _pad(b):
    return b + bytes(16 - len(b))


def _start(key, iv, ad):
    s = [_x(key, iv), C1, C0, _x(key, C0), _x(key, C1)]
    for _ in range(5):
        s = _update(s, key)
        s = _update(s, _x(key, iv))
    for i in range(0, len(ad), 16):
        s = _update(s, _pad(ad[i:i + 16]))
    return s


def _final(s, adlen, msglen):
    tmp = _x(s[3], (8 * adlen).to_bytes(8, "little") + (8 * msglen).to_bytes(8, "little"))
    for _ in range(7):
        s = _update(s, tmp)
    t = s[0]
    for j in range(1, 5):
        t = _x(t, s[j])
    return t


def aegis128_seal(key, iv, ad, p):
    s = _start(key, iv, ad)
    c = b""
    for i in range(0, len(p), 16):
        blk = p[i:i + 16]
        z = _x(_x(s[1], s[4]), _and(s[2], s[3]))
        c += _x(blk, z[:len(blk)])
        s = _update(s, _pad(blk))
    return c + _final(s, len(ad), len(p))


def aegis128_open(key, iv, ad, ct):
    if len(ct) < 16:
        return None
    c, tag = ct[:-16], ct[-16:]
    s = _start(key, iv, ad)
    p = b""
    for i in range(0, len(c), 16):
        blk = c[i:i + 16]
        z = _x(_x(s[1], s[4]), _and(s[2], s[3]))
        pb = _x(blk, z[:len(blk)])
        p += pb
        s = _update(s, _pad(pb))
    return p if _final(s, len(ad), len(c)) == tag else None
