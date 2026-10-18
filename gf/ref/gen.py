#!/usr/bin/env python3
"""Differential test cases for bend-osdev-gf.

Writes ref/cases.bend (a Bend program printing gf's results on each case)
and ref/expected.txt (the same values from implementations outside this
repository):
  * GF(2^8), GF(2^m), and every GF(2^128) bit order: an independent model
    of polynomial arithmetic over GF(2), written here from the definitions
    (carry-less multiplication, then reduction);
  * GHASH: the tags of Python's cryptography package (AES-GCM), from which
    GHASH(H, C || lengths) = tag xor E(K, J0);
  * CMAC's doubling: cryptography's AES-CMAC of one full block M gives
    E(K, M xor K1), so K1 = D(K, tag) xor M;
  * XTS's doubling: the model's T_1 = T_0 * x is checked against
    cryptography's AES-XTS ciphertext before it is used.
"""
import os, random, sys

M128 = (1 << 128) - 1


def clmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def reduce(r, poly):
    d = poly.bit_length() - 1
    while r.bit_length() - 1 >= d:
        r ^= poly << (r.bit_length() - 1 - d)
    return r


def fmul(a, b, poly):
    return reduce(clmul(a, b), poly)


def fpow(a, e, poly):
    r = 1
    while e:
        if e & 1:
            r = fmul(r, a, poly)
        a = fmul(a, a, poly)
        e >>= 1
    return r


def flog(a, g, poly, n):
    x = 1
    for i in range(n):
        if x == a:
            return i
        x = fmul(x, g, poly)
    return 0


P128 = (1 << 128) | 0x87


def rev128(x):
    return int(format(x, "0128b")[::-1], 2)


def gcm_mul(x, y):
    # GCM's order is the bit reversal of the big-endian one
    return rev128(fmul(rev128(x), rev128(y), P128))


def gcm_mul_spec(X, Y):
    # SP 800-38D Algorithm 1, literally
    R = 0xE1 << 120
    Z, V = 0, Y
    for i in range(128):
        if X >> (127 - i) & 1:
            Z ^= V
        V = (V >> 1) ^ R if V & 1 else V >> 1
    return Z


def dbl_be(x):
    return fmul(x, 2, P128)


def dbl_le(x):
    v = int.from_bytes(x.to_bytes(16, "big"), "little")
    return int.from_bytes(fmul(v, 2, P128).to_bytes(16, "little"), "big")


def words(x):
    return ", ".join(str((x >> (96 - 32 * i)) & 0xFFFFFFFF) for i in range(4))


def blk(x):
    return "H.Gf128.of_words(%s)" % words(x)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, call, want):
        lines.append('    IO.print("%s " ++ %s)' % (name, call))
        expect.append("%s %s" % (name, want))

    fields = [("aes", 0x11B, 3), ("rs", 0x11D, 2)]
    for fname, poly, g in fields:
        f = "G.Gf8.%s()" % fname
        for k in range(24):
            a, b = rng.randrange(256), rng.randrange(256)
            ua, ub = a | (rng.randrange(1 << 24) << 8), b  # high bits are ignored
            case("%s_mul_%d" % (fname, k), "U32.show(G.Gf8.mul(%s, %d, %d))" % (f, ua, ub), fmul(a, b, poly))
            case("%s_tab_mul_%d" % (fname, k), "U32.show(tab_mul(%s, %d, %d))" % (f, a, b), fmul(a, b, poly))
            inv = fpow(a, 254, poly)
            case("%s_inv_%d" % (fname, k), "U32.show(G.Gf8.inv(%s, %d))" % (f, a), inv)
            case("%s_tab_inv_%d" % (fname, k), "U32.show(tab_inv(%s, %d))" % (f, a), inv)
            q = fmul(a, fpow(b, 254, poly), poly)
            case("%s_div_%d" % (fname, k), "U32.show(G.Gf8.div(%s, %d, %d))" % (f, a, b), q)
            case("%s_tab_div_%d" % (fname, k), "U32.show(tab_div(%s, %d, %d))" % (f, a, b), q)
            case("%s_xtime_%d" % (fname, k), "U32.show(G.Gf8.xtime(%s, %d))" % (f, a), fmul(a, 2, poly))
            e = rng.randrange(600)
            case("%s_pow_%d" % (fname, k), "U32.show(G.Gf8.pow(%s, %d, %dn))" % (f, a, e), fpow(a, e, poly))
            case("%s_log_%d" % (fname, k), "Nat.show(G.Gf8.log(%s, %d))" % (f, a), flog(a, g, poly, 255))
            case("%s_add_%d" % (fname, k), "U32.show(G.Gf8.add(%d, %d))" % (ua, ub), a ^ b)

    gfm = [("gf16", 4, 19), ("gf32", 5, 37), ("bch13", 13, 0x201B), ("bch14", 14, 0x4443)]
    for fname, m, poly in gfm:
        f = "M.Gfm.%s()" % fname
        for k in range(12):
            a, b = rng.randrange(1, 1 << m), rng.randrange(1 << m)
            case("%s_mul_%d" % (fname, k), "U32.show(M.Gfm.mul(%s, %d, %d))" % (f, a, b), fmul(a, b, poly))
            case("%s_inv_%d" % (fname, k), "U32.show(M.Gfm.inv(%s, %d))" % (f, a), fpow(a, (1 << m) - 2, poly))
            e = rng.randrange(1 << 20)
            case("%s_exp_%d" % (fname, k), "U32.show(M.Gfm.exp(%s, %d))" % (f, e), fpow(2, e, poly))
            if m <= 13:
                case("%s_log_%d" % (fname, k), "U32.show(M.Gfm.log(%s, %d))" % (f, a), flog(a, 2, poly, (1 << m) - 1))

    for k in range(16):
        x, y = rng.getrandbits(128), rng.getrandbits(128)
        assert gcm_mul(x, y) == gcm_mul_spec(x, y)
        case("gcm_mul_%d" % k, "H.Gf128.hex(H.Gf128.mul_gcm(%s, %s))" % (blk(x), blk(y)), "%032x" % gcm_mul(x, y))
        case("gcm_x_%d" % k, "H.Gf128.hex(H.Gf128.mul_x_gcm(%s))" % blk(x), "%032x" % gcm_mul(x, 1 << 126))
        case("be_mul_%d" % k, "H.Gf128.hex(H.Gf128.mul_be(%s, %s))" % (blk(x), blk(y)), "%032x" % fmul(x, y, P128))
        case("be_dbl_%d" % k, "H.Gf128.hex(H.Gf128.double_be(%s))" % blk(x), "%032x" % dbl_be(x))
        case("le_dbl_%d" % k, "H.Gf128.hex(H.Gf128.double_le(%s))" % blk(x), "%032x" % dbl_le(x))

    try:
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM
        from cryptography.hazmat.primitives import cmac
    except ImportError:
        Cipher = None
    if Cipher is not None:
        def ecb(key, block, enc=True):
            c = Cipher(algorithms.AES(key), modes.ECB())
            op = c.encryptor() if enc else c.decryptor()
            return op.update(block) + op.finalize()
        for k in range(8):
            key, iv = rng.randbytes(16), rng.randbytes(12)
            n = rng.randrange(1, 5)
            pt = rng.randbytes(16 * n)
            out = AESGCM(key).encrypt(iv, pt, None)
            ct, tag = out[:-16], out[-16:]
            h = int.from_bytes(ecb(key, bytes(16)), "big")
            ek = int.from_bytes(ecb(key, iv + b"\0\0\0\1"), "big")
            want = int.from_bytes(tag, "big") ^ ek
            blocks = [int.from_bytes(ct[i:i + 16], "big") for i in range(0, len(ct), 16)] + [len(ct) * 8]
            case("ghash_aesgcm_%d" % k, "H.Gf128.hex(H.Gf128.ghash(%s, [%s]))" % (blk(h), ", ".join(blk(b) for b in blocks)), "%032x" % want)
            # CMAC: K1 = D(K, CMAC(K, M)) xor M for one full block M
            msg = rng.randbytes(16)
            c = cmac.CMAC(algorithms.AES(key))
            c.update(msg)
            k1 = int.from_bytes(ecb(key, c.finalize(), False), "big") ^ int.from_bytes(msg, "big")
            el = int.from_bytes(ecb(key, bytes(16)), "big")
            case("cmac_k1_%d" % k, "H.Gf128.hex(H.Gf128.double_be(%s))" % blk(el), "%032x" % k1)
            # XTS: T_1 = T_0 * x, checked against the second block's ciphertext
            k1x, k2x, tw = rng.randbytes(16), rng.randbytes(16), rng.randbytes(16)
            p = rng.randbytes(32)
            enc = Cipher(algorithms.AES(k1x + k2x), modes.XTS(tw)).encryptor()
            ct = enc.update(p) + enc.finalize()
            t0 = int.from_bytes(ecb(k2x, tw), "big")
            t1 = dbl_le(t0)
            tb = t1.to_bytes(16, "big")
            mid = bytes(x ^ y for x, y in zip(p[16:], tb))
            assert bytes(x ^ y for x, y in zip(ecb(k1x, mid), tb)) == ct[16:], "model disagrees with AES-XTS"
            case("xts_t1_%d" % k, "H.Gf128.hex(H.Gf128.double_le(%s))" % blk(t0), "%032x" % t1)

    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../gf.bend as G\nimport ../tables.bend as T\nimport ../gf128.bend as H\nimport ../gfm.bend as M\n\n")
        f.write("def tab_mul(+f: G.Gf8Field, a: U32, b: U32) -> U32:\n  Pair.snd(T.Gf8Tab, U32, T.Gf8Tab.mul(T.Gf8Tab.new(f), a, b))\n\n")
        f.write("def tab_inv(+f: G.Gf8Field, a: U32) -> U32:\n  Pair.snd(T.Gf8Tab, U32, T.Gf8Tab.inv(T.Gf8Tab.new(f), a))\n\n")
        f.write("def tab_div(+f: G.Gf8Field, a: U32, b: U32) -> U32:\n  Pair.snd(T.Gf8Tab, U32, T.Gf8Tab.div(T.Gf8Tab.new(f), a, b))\n\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
