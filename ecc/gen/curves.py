#!/usr/bin/env python3
"""The named curves, from their specifications' tables.

  python3 gen/curves.py           rewrite the generated region of curves.bend
  python3 gen/curves.py --check   only check that it is up to date

Each curve is y^2 = x^3 + a x + b over GF(p), with base point G = (gx, gy) of
prime order n and cofactor h. The values below are transcribed from:
  * P-192: FIPS 186-4 (2013), Appendix D.1.2.1 (SP 800-186 section 3.2.1.1
    keeps it for legacy use only and refers there);
  * P-224, P-256, P-384, P-521: NIST SP 800-186 (2023), sections 3.2.1.2 to
    3.2.1.5;
  * SM2's curve: draft-shen-sm2-ecdsa-02 (2014), Appendix D (the 256-bit
    recommended parameters of GB/T 32918.5);
  * SM2's example curve: draft-shen-sm2-ecdsa-02, Appendix A.2 (the curve
    its signature example uses);
  * GOST R 34.10-2001 CryptoPro A, B and C: RFC 4357 (2006), section 11.4
    (each parameter set is the ASN.1 SEQUENCE {a, b, p, q, x, y}; XchA is
    the same curve as A and XchB as C);
  * the GOST R 34.10-2012 example curve: RFC 7091 (2013), section 7.1.
Before anything is written, every curve is checked: p and n prime (40-round
Miller-Rabin), G on the curve, n G the point at infinity, and |p + 1 - h n|
within Hasse's bound 2 sqrt(p). A digit copied wrongly fails these checks.
ref/run.sh compares the NIST and SM2 curves with the openssl command's.
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.join(HERE, "..")


def H(s):
    return int(s.replace(" ", ""), 16)


CURVES = [
    ("p192", "NIST P-192 (FIPS 186-4, D.1.2.1)", dict(
        p=6277101735386680763835789423207666416083908700390324961279, a=-3,
        b=H("64210519 e59c80e7 0fa7e9ab 72243049 feb8deec c146b9b1"),
        gx=H("188da80e b03090f6 7cbf20eb 43a18800 f4ff0afd 82ff1012"),
        gy=H("07192b95 ffc8da78 631011ed 6b24cdd5 73f977a1 1e794811"),
        n=6277101735386680763835789423176059013767194773182842284081, h=1)),
    ("p224", "NIST P-224 (SP 800-186, 3.2.1.2)", dict(
        p=H("ffffffff ffffffff ffffffff ffffffff 00000000 00000000 00000001"), a=-3,
        b=H("b4050a85 0c04b3ab f5413256 5044b0b7 d7bfd8ba 270b3943 2355ffb4"),
        gx=H("b70e0cbd 6bb4bf7f 321390b9 4a03c1d3 56c21122 343280d6 115c1d21"),
        gy=H("bd376388 b5f723fb 4c22dfe6 cd4375a0 5a074764 44d58199 85007e34"),
        n=H("ffffffff ffffffff ffffffff ffff16a2 e0b8f03e 13dd2945 5c5c2a3d"), h=1)),
    ("p256", "NIST P-256 (SP 800-186, 3.2.1.3)", dict(
        p=H("ffffffff 00000001 00000000 00000000 00000000 ffffffff ffffffff ffffffff"), a=-3,
        b=H("5ac635d8 aa3a93e7 b3ebbd55 769886bc 651d06b0 cc53b0f6 3bce3c3e 27d2604b"),
        gx=H("6b17d1f2 e12c4247 f8bce6e5 63a440f2 77037d81 2deb33a0 f4a13945 d898c296"),
        gy=H("4fe342e2 fe1a7f9b 8ee7eb4a 7c0f9e16 2bce3357 6b315ece cbb64068 37bf51f5"),
        n=H("ffffffff 00000000 ffffffff ffffffff bce6faad a7179e84 f3b9cac2 fc632551"), h=1)),
    ("p384", "NIST P-384 (SP 800-186, 3.2.1.4)", dict(
        p=H("ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff fffffffe ffffffff 00000000 00000000 ffffffff"), a=-3,
        b=H("b3312fa7 e23ee7e4 988e056b e3f82d19 181d9c6e fe814112 0314088f 5013875a c656398d 8a2ed19d 2a85c8ed d3ec2aef"),
        gx=H("aa87ca22 be8b0537 8eb1c71e f320ad74 6e1d3b62 8ba79b98 59f741e0 82542a38 5502f25d bf55296c 3a545e38 72760ab7"),
        gy=H("3617de4a 96262c6f 5d9e98bf 9292dc29 f8f41dbd 289a147c e9da3113 b5f0b8c0 0a60b1ce 1d7e819d 7a431d7c 90ea0e5f"),
        n=H("ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff c7634d81 f4372ddf 581a0db2 48b0a77a ecec196a ccc52973"), h=1)),
    ("p521", "NIST P-521 (SP 800-186, 3.2.1.5)", dict(
        p=2 ** 521 - 1, a=-3,
        b=H("051 953eb961 8e1c9a1f 929a21a0 b68540ee a2da725b 99b315f3 b8b48991 8ef109e1 56193951 ec7e937b 1652c0bd"
            " 3bb1bf07 3573df88 3d2c34f1 ef451fd4 6b503f00"),
        gx=H("c6 858e06b7 0404e9cd 9e3ecb66 2395b442 9c648139 053fb521 f828af60 6b4d3dba a14b5e77 efe75928 fe1dc127"
             " a2ffa8de 3348b3c1 856a429b f97e7e31 c2e5bd66"),
        gy=H("118 39296a78 9a3bc004 5c8a5fb4 2c7d1bd9 98f54449 579b4468 17afbd17 273e662c 97ee7299 5ef42640 c550b901"
             " 3fad0761 353c7086 a272c240 88be9476 9fd16650"),
        n=H("1ff ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff fffffffa 51868783 bf2f966b 7fcc0148"
            " f709a5d0 3bb5c9b8 899c47ae bb6fb71e 91386409"), h=1)),
    ("sm2", "SM2's recommended curve (draft-shen-sm2-ecdsa-02, Appendix D)", dict(
        p=H("FFFFFFFE FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF 00000000 FFFFFFFF FFFFFFFF"),
        a=H("FFFFFFFE FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF 00000000 FFFFFFFF FFFFFFFC"),
        b=H("28E9FA9E 9D9F5E34 4D5A9E4B CF6509A7 F39789F5 15AB8F92 DDBCBD41 4D940E93"),
        gx=H("32C4AE2C 1F198119 5F990446 6A39C994 8FE30BBF F2660BE1 715A4589 334C74C7"),
        gy=H("BC3736A2 F4F6779C 59BDCEE3 6B692153 D0A9877C C62A4740 02DF32E5 2139F0A0"),
        n=H("FFFFFFFE FFFFFFFF FFFFFFFF FFFFFFFF 7203DF6B 21C6052B 53BBF409 39D54123"), h=1)),
    ("sm2_example", "the curve of SM2's signature example (draft-shen-sm2-ecdsa-02, Appendix A.2)", dict(
        p=H("8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3"),
        a=H("787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498"),
        b=H("63E4C6D3 B23B0C84 9CF84241 484BFE48 F61D59A5 B16BA06E 6E12D1DA 27C5249A"),
        gx=H("421DEBD6 1B62EAB6 746434EB C3CC315E 32220B3B ADD50BDC 4C4E6C14 7FEDD43D"),
        gy=H("0680512B CBB42C07 D47349D2 153B70C4 E5D7FDFC BFA36EA1 A85841B9 E46E09A2"),
        n=H("8542D69E 4C044F18 E8B92435 BF6FF7DD 29772063 0485628D 5AE74EE7 C32E79B7"), h=1)),
    ("gost_cp_a", "GOST R 34.10-2001 CryptoPro-A (RFC 4357, 11.4; also XchA)", dict(
        a=H("00 FF FF FF FF FF FF FF FF FF FF FF FF FF FF FF" "FF FF FF FF FF FF FF FF FF FF FF FF FF FF FF FD" "94"), b=166,
        p=H("00 FF FF FF FF FF FF FF FF FF FF FF FF FF FF FF" "FF FF FF FF FF FF FF FF FF FF FF FF FF FF FF FD" "97"),
        n=H("00 FF FF FF FF FF FF FF FF FF FF FF FF FF FF FF FF 6C 61 10 70 99 5A D1 00 45 84 1B 09 B7 61 B8 93"),
        gx=1, gy=H("00 8D 91 E4 71 E0 98 9C DA 27 DF 50 5A 45 3F 2B 76 35 29 4F 2D DF 23 E3 B1 22 AC C9 9C 9E 9F 1E 14"), h=1)),
    ("gost_cp_b", "GOST R 34.10-2001 CryptoPro-B (RFC 4357, 11.4)", dict(
        a=H("00 80 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 0C 96"),
        b=H("3E 1A F4 19 A2 69 A5 F8 66 A7 D3 C2 5C 3D F8 0A E9 79 25 93 73 FF 2B 18 2F 49 D4 CE 7E 1B BC 8B"),
        p=H("00 80 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 0C 99"),
        n=H("00 80 00 00 00 00 00 00 00 00 00 00 00 00 00 00 01 5F 70 0C FF F1 A6 24 E5 E4 97 16 1B CC 8A 19 8F"),
        gx=1, gy=H("3F A8 12 43 59 F9 66 80 B8 3D 1C 3E B2 C0 70 E5 C5 45 C9 85 8D 03 EC FB 74 4B F8 D7 17 71 7E FC"), h=1)),
    ("gost_cp_c", "GOST R 34.10-2001 CryptoPro-C (RFC 4357, 11.4; also XchB)", dict(
        a=H("00 9B 9F 60 5F 5A 85 81 07 AB 1E C8 5E 6B 41 C8 AA CF 84 6E 86 78 90 51 D3 79 98 F7 B9 02 2D 75 98"), b=32858,
        p=H("00 9B 9F 60 5F 5A 85 81 07 AB 1E C8 5E 6B 41 C8 AA CF 84 6E 86 78 90 51 D3 79 98 F7 B9 02 2D 75 9B"),
        n=H("00 9B 9F 60 5F 5A 85 81 07 AB 1E C8 5E 6B 41 C8 AA 58 2C A3 51 1E DD FB 74 F0 2F 3A 65 98 98 0B B9"),
        gx=0, gy=H("41 EC E5 57 43 71 1A 8C 3C BF 37 83 CD 08 C0 EE 4D 4D C4 40 D4 64 1A 8F 36 6E 55 0D FD B3 BB 67"), h=1)),
    ("gost_example", "the curve of GOST R 34.10-2012's example (RFC 7091, 7.1)", dict(
        p=57896044618658097711785492504343953926634992332820282019728792003956564821041, a=7,
        b=43308876546767276905765904595650931995942111794451039583252968842033849580414,
        gx=2, gy=4018974056539037503335449422937059775635739389905545080690979365213431566280,
        n=57896044618658097711785492504343953927082934583725450622380973592137631069619, h=1)),
]

CURVES_BY_NAME = [(name, c) for name, _, c in CURVES]


def is_prime(n):
    if n < 2:
        return False
    for q in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    import random
    r = random.Random(n)
    for _ in range(40):
        a = r.randrange(2, n - 1)
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def add(P, Q, a, p):
    if P is None:
        return Q
    if Q is None:
        return P
    if P[0] == Q[0]:
        if (P[1] + Q[1]) % p == 0:
            return None
        lam = (3 * P[0] * P[0] + a) * pow(2 * P[1], -1, p) % p
    else:
        lam = (Q[1] - P[1]) * pow(Q[0] - P[0], -1, p) % p
    x = (lam * lam - P[0] - Q[0]) % p
    return (x, (lam * (P[0] - x) - P[1]) % p)


def mul(k, P, a, p):
    R = None
    while k:
        if k & 1:
            R = add(R, P, a, p)
        P = add(P, P, a, p)
        k >>= 1
    return R


def isqrt(v):
    x = int(v ** 0.5) if v < 2 ** 52 else 1 << ((v.bit_length() + 1) // 2)
    while True:
        y = (x + v // x) // 2
        if y >= x:
            return x
        x = y


def check(name, c):
    p, a, b, gx, gy, n, h = c["p"], c["a"] % c["p"], c["b"], c["gx"], c["gy"], c["n"], c["h"]
    assert is_prime(p) and is_prime(n), name + ": p or n not prime"
    assert (gy * gy - (gx ** 3 + a * gx + b)) % p == 0, name + ": G not on the curve"
    assert (4 * a ** 3 + 27 * b * b) % p != 0, name + ": singular"
    assert mul(n, (gx, gy), a, p) is None, name + ": n G is not infinity"
    assert abs(p + 1 - h * n) <= 2 * isqrt(p) + 2, name + ": order outside Hasse's bound"


def limbs(v):
    out = []
    while v:
        out.append(v & 65535)
        v >>= 16
    return out or [0]


def lit(v):
    return "N.BnNat.of_limbs([%s])" % ", ".join(map(str, limbs(v)))


def region():
    out = []
    for name, title, c in CURVES:
        check(name, c)
        p = c["p"]
        out.append("# %s\ndef EcCurves.%s() -> E.EcParams:\n  E.EcParams{%s, %s, %s, %s, %s, %s, %s}\n"
                   % (title, name, lit(p), lit(c["a"] % p), lit(c["b"]), lit(c["gx"]), lit(c["gy"]), lit(c["n"]), lit(c["h"])))
    return "\n".join(out)


def main():
    check_only = "--check" in sys.argv[1:]
    path = os.path.join(PKG, "curves.bend")
    with open(path) as f:
        text = f.read()
    begin = "# BEGIN GENERATED by gen/curves.py: curves\n"
    end = "# END GENERATED: curves\n"
    i, j = text.index(begin) + len(begin), text.index(end)
    new = text[:i] + region() + text[j:]
    if check_only:
        if new != text:
            print("out of date (run gen/curves.py): curves.bend")
            sys.exit(1)
        print("generated region up to date")
    elif new != text:
        with open(path, "w", newline="\n") as f:
            f.write(new)


if __name__ == "__main__":
    main()
