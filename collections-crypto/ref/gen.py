#!/usr/bin/env python3
"""Differential test of collections-crypto's instances, through crypto's
interfaces, against Python's cryptography and hashlib, and against this
file's models where Python has no implementation.

  python3 gen.py [seed]   writes cases00.bend, ... and expected.txt

Every key, nonce and message travels as bytes, and every call goes through
crypto's interface helpers (CrAead.seal_with / open_with, CrStream.crypt,
CrMac.compute_with, CrHash.of_pieces, CrKex.agree, CrSign.keypair /
verify_bytes). The cases:
  * AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305: Bend's ciphertext and tag
    equal cryptography's (AESGCM, ChaCha20Poly1305), Bend opens it, and a
    changed tag, ciphertext or associated data is refused;
  * XChaCha20-Poly1305: the same against this file's XChaCha20-Poly1305
    (HChaCha20 below, then cryptography's ChaCha20Poly1305 under the subkey,
    draft-irtf-cfrg-xchacha-03 section 2.3), checked first on the draft's
    A.3.1 vector;
  * ChaCha20 in two pieces against cryptography's ChaCha20 (whose 16-byte
    nonce is the counter, little-endian, then the RFC 8439 nonce), random
    initial counters; XChaCha20, ChaCha12 and ChaCha8 against this file's
    ChaCha (checked first against cryptography's ChaCha20 and the draft's
    HChaCha20 and XChaCha20 vectors);
  * Poly1305 against cryptography's Poly1305; GMAC against AESGCM sealing
    nothing (the tag of the associated data), verify accepting it and
    refusing it changed;
  * BLAKE2b-512, BLAKE2s-256 and BLAKE2b with 1 to 64-byte digests, in two
    pieces, against hashlib; Keccak-256 against this file's Keccak (FIPS
    202's Keccak-f[1600] and sponge with Keccak's pad10*1 padding, checked
    first against hashlib's SHA3-224/256/384/512 and SHAKE128/256 by giving
    it their padding);
  * X25519: Bend's public key and shared secret (each party from the other's
    bytes) equal cryptography's; edge cases of RFC 7748: a u-coordinate with
    its top bit set (section 5: masked) and one at or above p
    (non-canonical, section 5: accepted), and a small-order peer key whose
    shared secret is all zero (section 6.1: refused here);
  * Ed25519: Bend's public key and signature equal cryptography's, Bend
    accepts cryptography's signature, and refuses it for a changed message
    and with S + L in place of S (RFC 8032 section 5.1.7); and five edge
    cases checked against RFC 8032's own rules rather than cryptography's
    answers (it accepts two encodings that section 5.1.3 rejects).
BLAKE3 has no implementation in Python here: check.bend tests it on the
BLAKE3 team's published vectors.
"""
import hashlib, os, random, struct, sys
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms
from cryptography.hazmat.primitives.ciphers.aead import AESGCM, ChaCha20Poly1305
from cryptography.hazmat.primitives.poly1305 import Poly1305
from cryptography.hazmat.primitives.asymmetric import x25519, ed25519
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat, PrivateFormat, NoEncryption

HERE = os.path.dirname(os.path.abspath(__file__))
CHUNK = 60

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../../crypto/crypto.bend as Cr
import ../../crypto/stream.bend as St
import ../../crypto/hash.bend as H
import ../../crypto/mac.bend as Mc
import ../../crypto/aead.bend as Ae
import ../../crypto/sign.bend as Sg
import ../../crypto/kex.bend as Kx
import ../collections-crypto.bend as C
import ../aead.bend as Ad
import ../gmac.bend as Gm
import ../poly1305.bend as Po
import ../chacha.bend as Ch
import ../blake.bend as Bl
import ../keccak.bend as Kc
import ../x25519.bend as Xx
import ../ed25519.bend as Ed

def ob(xs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(xs)

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def ro(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "refused"
    case Done{o}:
      B.Octets.hex(o)

def seal(~key: B.Octets -> Result<&2, &2, Cr.CrError, Ad.CcAeadKey>, k: B.Octets, n: B.Octets, a: B.Octets, p: B.Octets) -> String:
  ro(Ae.CrAead.seal_with(~Ad.CcAeadKey, ~key, ~Ad.CcAead.seal, k, n, a, p))

def open(~key: B.Octets -> Result<&2, &2, Cr.CrError, Ad.CcAeadKey>, k: B.Octets, n: B.Octets, a: B.Octets, c: B.Octets) -> String:
  ro(Ae.CrAead.open_with(~Ad.CcAeadKey, ~key, ~Ad.CcAead.open, k, n, a, c))

def two.go(~r: Nat, o: St.CrXorOut<Ch.CcChaState>, b: B.Octets) -> B.Octets:
  match o:
    case St.CrXorOut{s, d}:
      B.Octets.append(d, Ch.CcChacha.out_data(Ch.CcChacha.update(~r, s, b)))

def two.st(~r: Nat, r0: Result<&2, &2, Cr.CrError, Ch.CcChaState>, a: B.Octets, b: B.Octets) -> String:
  match r0:
    case Fail{e}:
      "refused"
    case Done{s}:
      B.Octets.hex(two.go(~r, Ch.CcChacha.update(~r, s, a), b))

def chacha(~r: Nat, k: B.Octets, iv: B.Octets, a: B.Octets, b: B.Octets) -> String:
  two.st(~r, Ch.CcChacha.start(k, iv), a, b)

def xchacha(~r: Nat, k: B.Octets, iv: B.Octets, a: B.Octets, b: B.Octets) -> String:
  two.st(~r, Ch.CcChacha.start_x(~r, k, iv), a, b)

def poly(k: B.Octets, m: B.Octets) -> String:
  ro(Mc.CrMac.compute_with(~Po.CcPolyKey, ~Po.CcPoly1305.key, ~Po.CcPoly1305.mac, k, m))

def gmac.v(r: Result<&2, &2, Cr.CrError, Gm.CcGmacKey>, m: B.Octets, t: B.Octets) -> String:
  match r:
    case Fail{e}:
      "refused"
    case Done{k}:
      bs(Gm.CcGmac.verify(k, m, t))

def gmac(~key: B.Octets -> Result<&2, &2, Cr.CrError, Gm.CcGmacKey>, k: B.Octets, m: B.Octets) -> String:
  ro(Mc.CrMac.compute_with(~Gm.CcGmacKey, ~key, ~Gm.CcGmac.mac, k, m))

def gmac_verify(~key: B.Octets -> Result<&2, &2, Cr.CrError, Gm.CcGmacKey>, k: B.Octets, m: B.Octets, t: B.Octets) -> String:
  gmac.v(key(k), m, t)

def pieces(~digest: B.Octets -> B.Octets, a: B.Octets, b: B.Octets) -> String:
  B.Octets.hex(H.CrHash.of_pieces(~C.CcBuf, ~C.CcBuf.init(), ~C.CcBuf.update, ~C.CcBuf.final(~digest), [a, b]))

def x.pub(r: Result<&2, &2, Cr.CrError, Xx.CcX25519Sk>) -> String:
  match r:
    case Fail{e}:
      "refused"
    case Done{k}:
      B.Octets.hex(Xx.CcX25519.pk_to(Xx.CcX25519.public(k)))

def x25519_pub(k: B.Octets) -> String:
  x.pub(Xx.CcX25519.secret(k))

def x25519(k: B.Octets, peer: B.Octets) -> String:
  ro(Kx.CrKex.agree(~Xx.CcX25519Sk, ~Xx.CcX25519Pk, ~Xx.CcX25519.secret, ~Xx.CcX25519.pk_of, ~Xx.CcX25519.shared, k, peer))

def ed.go(r: Result<&2, &2, Cr.CrError, Sg.CrKeypair<Ed.CcEdSk, Ed.CcEdPk>>, m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "refused"
    case Done{kp}:
      match kp:
        case Sg.CrKeypair{sk, pk}:
          B.Octets.hex(Ed.CcEd25519.pk_to(pk)) ++ " " ++ B.Octets.hex(Ed.CcEd25519.sign(sk, m))

def ed25519(k: B.Octets, m: B.Octets) -> String:
  ed.go(Sg.CrSign.keypair(~Ed.CcEdSk, ~Ed.CcEdPk, ~Ed.CcEd25519.secret, ~Ed.CcEd25519.public, k), m)

def ed25519_verify(pk: B.Octets, m: B.Octets, s: B.Octets) -> String:
  bs(Sg.CrSign.verify_bytes(~Ed.CcEdPk, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.verify, pk, m, s))
'''

# ---------------------------------------------------------------- models

M32 = 0xffffffff


def rotl(x, n):
    return ((x << n) | (x >> (32 - n))) & M32


def qr(s, a, b, c, d):
    s[a] = (s[a] + s[b]) & M32; s[d] = rotl(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & M32; s[b] = rotl(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b]) & M32; s[d] = rotl(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & M32; s[b] = rotl(s[b] ^ s[c], 7)


CONST = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]


def rounds(s, r):
    s = list(s)
    for _ in range(r):
        qr(s, 0, 4, 8, 12); qr(s, 1, 5, 9, 13); qr(s, 2, 6, 10, 14); qr(s, 3, 7, 11, 15)
        qr(s, 0, 5, 10, 15); qr(s, 1, 6, 11, 12); qr(s, 2, 7, 8, 13); qr(s, 3, 4, 9, 14)
    return s


# RFC 8439 2.3: the block function with r double rounds and a 32-bit counter
def block(key, ctr, nonce, r):
    s = CONST + list(struct.unpack('<8I', key)) + [ctr & M32] + list(struct.unpack('<3I', nonce))
    w = rounds(s, r)
    return struct.pack('<16I', *[(x + y) & M32 for x, y in zip(w, s)])


def chacha(key, ctr, nonce, m, r):
    out = bytearray()
    for i in range(0, len(m), 64):
        ks = block(key, ctr + i // 64, nonce, r)
        out += bytes(x ^ y for x, y in zip(m[i:i + 64], ks))
    return bytes(out)


# draft-irtf-cfrg-xchacha-03 2.2: HChaCha (words 0..3 and 12..15, no feed-forward)
def hchacha(key, n16, r):
    s = CONST + list(struct.unpack('<8I', key)) + list(struct.unpack('<4I', n16))
    w = rounds(s, r)
    return struct.pack('<8I', *(w[0:4] + w[12:16]))


def xchacha(key, n24, m, r, ctr=0):
    return chacha(hchacha(key, n24[:16], r), ctr, b'\0' * 4 + n24[16:], m, r)


def xchapoly_seal(key, n24, aad, p):
    return ChaCha20Poly1305(hchacha(key, n24[:16], 10)).encrypt(b'\0' * 4 + n24[16:], p, aad)


# FIPS 202: Keccak-f[1600] (section 3.3, rounds 3.2.1 to 3.2.5) and the
# sponge (Algorithm 8) over bytes, with the padding given as its first byte
# (the domain bits and the first 1 of pad10*1: 0x06 for SHA-3, 0x1f for
# SHAKE, 0x01 for Keccak) and 0x80 for the last 1
RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
      0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
      0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
      0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
      0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
M64 = (1 << 64) - 1


def rot64(x, n):
    n %= 64
    return ((x << n) | (x >> (64 - n))) & M64 if n else x


# rho's offsets: (t + 1)(t + 2)/2 along (x, y) -> (y, 2x + 3y), from (1, 0)
RHO = [0] * 25
_x, _y = 1, 0
for _t in range(24):
    RHO[_x + 5 * _y] = ((_t + 1) * (_t + 2) // 2) % 64
    _x, _y = _y, (2 * _x + 3 * _y) % 5


def keccak_f(a):
    for rc in RC:
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ rot64(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rot64(a[x + 5 * y], RHO[x + 5 * y])
        a = [b[i] ^ ((~b[(i % 5 + 1) % 5 + 5 * (i // 5)]) & b[(i % 5 + 2) % 5 + 5 * (i // 5)]) for i in range(25)]
        a[0] ^= rc
    return a


def sponge(rate, pad, m, n):
    m = bytearray(m) + bytes([pad]) + bytes((-len(m) - 1) % rate)
    m[-1] |= 0x80
    a = [0] * 25
    for i in range(0, len(m), rate):
        blk = m[i:i + rate] + bytes(200 - rate)
        a = keccak_f([x ^ y for x, y in zip(a, struct.unpack('<25Q', blk))])
    out = b''
    while len(out) < n:
        out += struct.pack('<25Q', *a)[:rate]
        a = keccak_f(a)
    return out[:n]


def keccak256(m):
    return sponge(136, 0x01, m, 32)


def check_models():
    # ChaCha20 against cryptography, HChaCha20 and XChaCha20 against the draft
    k, n = bytes(range(32)), bytes(range(12))
    m = bytes(range(200))
    enc = Cipher(algorithms.ChaCha20(k, struct.pack('<I', 7) + n), mode=None).encryptor()
    assert enc.update(m) == chacha(k, 7, n, m, 10)
    assert hchacha(bytes(range(32)), bytes.fromhex('000000090000004a0000000031415927'), 10).hex() == \
        '82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc'
    ks = xchacha(bytes(range(128, 160)), bytes.fromhex('404142434445464748494a4b4c4d4e4f5051525354555658'), bytes(32), 10)
    assert ks.hex() == '1131ce9a2a20ae0d67c8935c7789fa1025c9e5bb720fb96f11354fb97af0bd9a'
    p = (b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, "
         b"sunscreen would be it.")
    c = xchapoly_seal(bytes(range(128, 160)), bytes.fromhex('404142434445464748494a4b4c4d4e4f5051525354555657'),
                      bytes.fromhex('50515253c0c1c2c3c4c5c6c7'), p)
    assert c[-16:].hex() == 'c0875924c1c7987947deafd8780acf49'
    # the sponge against hashlib's SHA-3 and SHAKE
    for t in [b'', b'abc', bytes(range(256)) * 3]:
        assert sponge(144, 0x06, t, 28) == hashlib.sha3_224(t).digest()
        assert sponge(136, 0x06, t, 32) == hashlib.sha3_256(t).digest()
        assert sponge(104, 0x06, t, 48) == hashlib.sha3_384(t).digest()
        assert sponge(72, 0x06, t, 64) == hashlib.sha3_512(t).digest()
        assert sponge(168, 0x1f, t, 300) == hashlib.shake_128(t).digest(300)
        assert sponge(136, 0x1f, t, 300) == hashlib.shake_256(t).digest(300)


# ---------------------------------------------------------------- cases

def o(b):
    return 'ob([%s])' % ', '.join(map(str, b))


def flip(b, i):
    b = bytearray(b)
    b[i] ^= 1
    return bytes(b)


P25519 = 2 ** 255 - 19
L25519 = 2 ** 252 + 27742317777372353535851937790883648493


def main():
    check_models()
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, expr, want):
        lines.append(('c%d' % len(lines), name, expr))
        expect.append('%s %s' % (name, want))

    def rb(n):
        return bytes(rnd.randrange(256) for _ in range(n))

    def msg(hi=70):
        return rb(rnd.randrange(0, hi))

    # AEADs
    aeads = [('gcm128', '~Ad.CcGcm.key128', 16, 12, lambda k, n, a, p: AESGCM(k).encrypt(n, p, a)),
             ('gcm256', '~Ad.CcGcm.key256', 32, 12, lambda k, n, a, p: AESGCM(k).encrypt(n, p, a)),
             ('chapoly', '~Ad.CcChaPoly.key', 32, 12, lambda k, n, a, p: ChaCha20Poly1305(k).encrypt(n, p, a)),
             ('xchapoly', '~Ad.CcXChaPoly.key', 32, 24, xchapoly_seal)]
    for name, tp, kl, nl, ref in aeads:
        for i in range(6):
            k, n, a, p = rb(kl), rb(nl), msg(40), msg()
            c = ref(k, n, a, p)
            args = '%s, %s, %s' % (o(k), o(n), o(a))
            case('%s-%d' % (name, i), 'seal(%s, %s, %s)' % (tp, args, o(p)), c.hex())
            case('%s-%d-open' % (name, i), 'open(%s, %s, %s)' % (tp, args, o(c)), p.hex())
            case('%s-%d-tag' % (name, i), 'open(%s, %s, %s)' % (tp, args, o(flip(c, len(c) - 1))), 'refused')
            if p:
                case('%s-%d-ct' % (name, i), 'open(%s, %s, %s)' % (tp, args, o(flip(c, 0))), 'refused')
            case('%s-%d-aad' % (name, i), 'open(%s, %s, %s, %s, %s)' % (tp, o(k), o(n), o(a + b'x'), o(c)), 'refused')
        case('%s-short-nonce' % name, 'seal(%s, %s, %s, %s, %s)' % (tp, o(rb(kl)), o(rb(nl - 1)), o(b''), o(b'p')), 'refused')
        case('%s-short-key' % name, 'seal(%s, %s, %s, %s, %s)' % (tp, o(rb(kl - 1)), o(rb(nl)), o(b''), o(b'p')), 'refused')
    # ChaCha20 against cryptography, in two pieces, random counters
    for i in range(8):
        k, n, m = rb(32), rb(12), msg(200)
        ctr = rnd.randrange(0, 1 << 32) if i % 2 else rnd.randrange(0, 4)
        iv = struct.pack('<I', ctr) + n
        c = Cipher(algorithms.ChaCha20(k, iv), mode=None).encryptor().update(m)
        cut = rnd.randrange(0, len(m) + 1)
        case('chacha20-%d' % i, 'chacha(~10n, %s, %s, %s, %s)' % (o(k), o(iv), o(m[:cut]), o(m[cut:])), c.hex())
    # the counter at its last value: RFC 8439's 32-bit counter wraps to 0
    k, n, m = rb(32), rb(12), rb(100)
    iv = struct.pack('<I', M32) + n
    case('chacha20-wrap', 'chacha(~10n, %s, %s, %s, %s)' % (o(k), o(iv), o(m[:30]), o(m[30:])), chacha(k, M32, n, m[:64], 10).hex() + chacha(k, 0, n, m[64:], 10).hex())
    for name, r in [('xchacha20', 10), ('xchacha12', 6)]:
        for i in range(4):
            k, n, m = rb(32), rb(24), msg(150)
            cut = rnd.randrange(0, len(m) + 1)
            case('%s-%d' % (name, i), 'xchacha(~%dn, %s, %s, %s, %s)' % (r, o(k), o(n), o(m[:cut]), o(m[cut:])), xchacha(k, n, m, r).hex())
    for name, r in [('chacha12', 6), ('chacha8', 4)]:
        for i in range(3):
            k, n, m = rb(32), rb(12), msg(150)
            ctr = rnd.randrange(0, 1 << 32)
            cut = rnd.randrange(0, len(m) + 1)
            case('%s-%d' % (name, i), 'chacha(~%dn, %s, %s, %s, %s)' % (r, o(k), o(struct.pack('<I', ctr) + n), o(m[:cut]), o(m[cut:])), chacha(k, ctr, n, m, r).hex())
    # Poly1305
    for i in range(8):
        k, m = rb(32), msg(120)
        case('poly1305-%d' % i, 'poly(%s, %s)' % (o(k), o(m)), Poly1305.generate_tag(k, m).hex())
    case('poly1305-short-key', 'poly(%s, %s)' % (o(rb(31)), o(b'm')), 'refused')
    # GMAC
    for name, key, kl in [('gmac128', 'Gm.CcGmac.key128', 16), ('gmac256', 'Gm.CcGmac.key256', 32)]:
        for i in range(4):
            k, n, a = rb(kl), rb(12), msg(80)
            t = AESGCM(k).encrypt(n, b'', a)
            case('%s-%d' % (name, i), 'gmac(~%s, %s, %s)' % (key, o(k), o(n + a)), t.hex())
            case('%s-%d-verify' % (name, i), 'gmac_verify(~%s, %s, %s, %s)' % (key, o(k), o(n + a), o(t)), 'yes')
            case('%s-%d-changed' % (name, i), 'gmac_verify(~%s, %s, %s, %s)' % (key, o(k), o(n + a + b'!'), o(t)), 'no')
    # Hashes in two pieces
    for i in range(6):
        m = msg(300)
        cut = rnd.randrange(0, len(m) + 1)
        a, b = o(m[:cut]), o(m[cut:])
        case('blake2b-%d' % i, 'pieces(~Bl.CcBlake.blake2b, %s, %s)' % (a, b), hashlib.blake2b(m).hexdigest())
        case('blake2s-%d' % i, 'pieces(~Bl.CcBlake.blake2s, %s, %s)' % (a, b), hashlib.blake2s(m).hexdigest())
        case('keccak256-%d' % i, 'pieces(~Kc.CcKeccak.keccak256, %s, %s)' % (a, b), keccak256(m).hex())
    for nn in [1, 20, 32, 48, 63, 64]:
        m = msg(300)
        cut = rnd.randrange(0, len(m) + 1)
        case('blake2b-n%d' % nn, 'pieces(~Bl.CcBlake.blake2b_n(~%dn), %s, %s)' % (nn, o(m[:cut]), o(m[cut:])), hashlib.blake2b(m, digest_size=nn).hexdigest())
    for n in [127, 128, 129, 255, 256, 257, 1000]:
        m = rb(n)
        case('blake2b-len%d' % n, 'pieces(~Bl.CcBlake.blake2b, %s, %s)' % (o(m[:n // 3]), o(m[n // 3:])), hashlib.blake2b(m).hexdigest())
        case('blake2s-len%d' % n, 'pieces(~Bl.CcBlake.blake2s, %s, %s)' % (o(m[:n // 3]), o(m[n // 3:])), hashlib.blake2s(m).hexdigest())
    for n in [135, 136, 137, 271, 272, 273]:
        m = rb(n)
        case('keccak256-len%d' % n, 'pieces(~Kc.CcKeccak.keccak256, %s, %s)' % (o(m[:n // 2]), o(m[n // 2:])), keccak256(m).hex())
    # X25519
    raw = dict(encoding=Encoding.Raw, format=PublicFormat.Raw)
    for i in range(6):
        a = x25519.X25519PrivateKey.generate()
        b = x25519.X25519PrivateKey.generate()
        ab = a.private_bytes(Encoding.Raw, PrivateFormat.Raw, NoEncryption())
        bb = b.private_bytes(Encoding.Raw, PrivateFormat.Raw, NoEncryption())
        pa = a.public_key().public_bytes(**raw)
        pb = b.public_key().public_bytes(**raw)
        z = a.exchange(b.public_key())
        case('x25519-%d-pub' % i, 'x25519_pub(%s)' % o(ab), pa.hex())
        case('x25519-%d' % i, 'x25519(%s, %s)' % (o(ab), o(pb)), z.hex())
        case('x25519-%d-peer' % i, 'x25519(%s, %s)' % (o(bb), o(pa)), z.hex())
        # the peer's key with the top bit set: masked (RFC 7748 section 5)
        hi = pb[:31] + bytes([pb[31] | 0x80])
        case('x25519-%d-topbit' % i, 'x25519(%s, %s)' % (o(ab), o(hi)),
             a.exchange(x25519.X25519PublicKey.from_public_bytes(hi)).hex())
    # non-canonical u-coordinates (u >= p, accepted as u mod p, section 5)
    for i, u in enumerate([P25519 + 9, P25519 + 2 ** 20, 2 ** 255 - 1]):
        a = x25519.X25519PrivateKey.generate()
        ab = a.private_bytes(Encoding.Raw, PrivateFormat.Raw, NoEncryption())
        ub = u.to_bytes(32, 'little')
        case('x25519-noncanonical-%d' % i, 'x25519(%s, %s)' % (o(ab), o(ub)),
             a.exchange(x25519.X25519PublicKey.from_public_bytes(ub)).hex())
    # small-order peer keys: the shared secret is all zero, refused (6.1)
    for i, u in enumerate([0, 1, P25519 - 1, P25519, P25519 + 1]):
        a = x25519.X25519PrivateKey.generate()
        ab = a.private_bytes(Encoding.Raw, PrivateFormat.Raw, NoEncryption())
        ub = u.to_bytes(32, 'little')
        try:
            a.exchange(x25519.X25519PublicKey.from_public_bytes(ub))
            want = 'not refused by cryptography'
        except ValueError:
            want = 'refused'
        case('x25519-zero-%d' % i, 'x25519(%s, %s)' % (o(ab), o(ub)), want)
    case('x25519-short-key', 'x25519(%s, %s)' % (o(rb(31)), o(rb(32))), 'refused')
    case('x25519-short-peer', 'x25519(%s, %s)' % (o(rb(32)), o(rb(33))), 'refused')
    # Ed25519
    for i in range(6):
        k = ed25519.Ed25519PrivateKey.generate()
        kb = k.private_bytes(Encoding.Raw, PrivateFormat.Raw, NoEncryption())
        pk = k.public_key().public_bytes(**raw)
        m = msg(100)
        s = k.sign(m)
        case('ed25519-%d' % i, 'ed25519(%s, %s)' % (o(kb), o(m)), pk.hex() + ' ' + s.hex())
        case('ed25519-%d-verify' % i, 'ed25519_verify(%s, %s, %s)' % (o(pk), o(m), o(s)), 'yes')
        case('ed25519-%d-changed' % i, 'ed25519_verify(%s, %s, %s)' % (o(pk), o(m + b'.'), o(s)), 'no')
        s2 = s[:32] + (int.from_bytes(s[32:], 'little') + L25519).to_bytes(32, 'little')
        try:
            k.public_key().verify(s2, m)
            want = 'yes'
        except Exception:
            want = 'no'
        case('ed25519-%d-s-plus-l' % i, 'ed25519_verify(%s, %s, %s)' % (o(pk), o(m), o(s2)), want)
    # Ed25519 edge cases, against RFC 8032 itself (section 5.1.3's decoding
    # and 5.1.7's cofactorless check): Python's cryptography (OpenSSL)
    # accepts the non-canonical public key (y = p + 1) and the key with x = 0
    # and its sign bit set, both of which 5.1.3 says fail to decode
    ident = (1).to_bytes(32, 'little')
    edge = [('ed25519-identity', ident, b'x', ident + bytes(32), 'yes'),
            ('ed25519-noncanonical-a', (P25519 + 1).to_bytes(32, 'little'), b'x', ident + bytes(32), 'no'),
            ('ed25519-noncanonical-r', ident, b'x', (P25519 + 1).to_bytes(32, 'little') + bytes(32), 'no'),
            ('ed25519-x0-sign-bit', (1 | (1 << 255)).to_bytes(32, 'little'), b'x', ident + bytes(32), 'no'),
            ('ed25519-s-equals-l', ident, b'x', ident + L25519.to_bytes(32, 'little'), 'no')]
    for name, pk, m, s, want in edge:
        case(name, 'ed25519_verify(%s, %s, %s)' % (o(pk), o(m), o(s)), want)
    return lines, expect


def write(lines, expect):
    for old in os.listdir(HERE):
        if old.startswith('cases') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        part = lines[j:j + CHUNK]
        defs = ''.join('\ndef %s() -> String:\n  "%s " ++ %s\n' % (d, name, expr) for d, name, expr in part)
        body = '\n'.join('    IO.print(%s())' % d for d, name, expr in part)
        with open(os.path.join(HERE, 'cases%02d.bend' % (j // CHUNK)), 'w', newline='\n') as fh:
            fh.write(HEADER + defs + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + body + '\n')
    with open(os.path.join(HERE, 'expected.txt'), 'w', newline='\n') as fh:
        fh.write('\n'.join(expect) + '\n')


if __name__ == '__main__':
    lines, expect = main()
    write(lines, expect)
    print('%d cases' % len(lines))
