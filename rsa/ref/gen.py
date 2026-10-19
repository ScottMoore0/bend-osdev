#!/usr/bin/env python3
"""Differential test of rsa against Python's cryptography package.

  python3 gen.py [seed]   writes cases00.bend, ... and expected.txt

Keys come from cryptography's RSA key generation (512 to 2048 bits, e = 3
and 65537). The cases:
  * RSASSA-PKCS1-v1_5 over SHA-256 and SHA-512: Bend's signature equals
    cryptography's (the scheme is deterministic), and Bend verifies
    cryptography's signature, and refuses it changed;
  * RSASSA-PSS (MGF1 over the same hash): Bend verifies cryptography's
    signatures (random salts of several lengths), and Bend's own signature
    with a given salt equals this file's RFC 8017 encoding signed with the
    raw private key, which cryptography first verifies;
  * RSAES-OAEP and RSAES-PKCS1-v1_5: Bend decrypts cryptography's
    ciphertexts (random seeds and padding), and Bend's ciphertext with a
    given seed or padding equals this file's encoding, which cryptography
    first decrypts back to the message;
  * the raw primitives: RSADP by the CRT equals the first form (n, d) and
    Python's pow;
  * key generation from seeds: the key Bend finds is checked by this file
    (p and q prime by cryptography's own key check, through
    RSAPrivateNumbers), and the refusals of bad keys and ciphertexts.
"""
import hashlib, os, random, sys
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import rsa, padding
from cryptography.exceptions import InvalidSignature

HERE = os.path.dirname(os.path.abspath(__file__))
CHUNK = 40

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../../bignum/bignum.bend as N
import ../rsa.bend as R
import ../mgf1.bend as M
import ../pkcs1.bend as P
import ../pss.bend as S
import ../oaep.bend as O
import ../es15.bend as E
import ../keys.bend as K
import ../keygen.bend as G
import bend-collections-laws-crypto@1.0.0.0/src/crypto/hash.bend as Hc

def sha256(o: B.Octets) -> B.Octets:
  B.Octets.of_list(Hc.sha256(B.Octets.to_list(o)))

def sha512(o: B.Octets) -> B.Octets:
  B.Octets.of_list(Hc.sha512(B.Octets.to_list(o)))

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

def ob(xs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(xs)

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def err(e: R.RsaError) -> String:
  match e:
    case R.RsaMessageTooLong{}:
      "too-long"
    case R.RsaDecryptionError{}:
      "decryption-error"
    case R.RsaEncodingError{}:
      "encoding-error"
    case R.RsaOutOfRange{}:
      "out-of-range"
    case R.RsaIntegerTooLarge{}:
      "too-large"
    case R.RsaBadKey{}:
      "bad-key"
    case R.RsaBadFormat{}:
      "bad-format"
    case R.RsaNoPrime{}:
      "no-prime"

def ro(r: Result<&2, &2, R.RsaError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{o}:
      B.Octets.hex(o) ++ "."

def rn(r: Result<&2, &2, R.RsaError, N.BnNat>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{x}:
      N.BnNat.hex(x)

def priv.go(r: Result<&2, &2, R.RsaError, R.RsaPrivate>) -> R.RsaPrivate:
  match r:
    case Fail{x}:
      R.RsaPrivate{N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero()}
    case Done{k}:
      k

def priv(n: N.BnNat, e: N.BnNat, d: N.BnNat, p: N.BnNat, q: N.BnNat) -> R.RsaPrivate:
  priv.go(R.Rsa.private_of(n, e, d, p, q))

def kshow(r: Result<&2, &2, R.RsaError, R.RsaPrivate>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{R.RsaPrivate{n, e, d, p, q, dp, dq, qinv}}:
      N.BnNat.hex(p) ++ " " ++ N.BnNat.hex(q) ++ " " ++ N.BnNat.hex(d)

def pshow(r: Result<&2, &2, R.RsaError, R.RsaPublic>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{R.RsaPublic{n, e}}:
      N.BnNat.hex(n) ++ " " ++ N.BnNat.hex(e)

def sshow(r: Result<&2, &2, R.RsaError, R.RsaPrivate>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{k}:
      B.Octets.hex(K.RsaKeys.private_to(k))
'''

HASHES = {'sha256': (hashes.SHA256, hashlib.sha256), 'sha512': (hashes.SHA512, hashlib.sha512)}
PREFIX = {'sha256': 'P.RsaDigestInfo.sha256()', 'sha512': 'P.RsaDigestInfo.sha512()'}


def hx(v):
    return '%x' % v


def o(b):
    return 'ob([%s])' % ', '.join(map(str, b))


def mgf1(H, seed, n):
    out = b''
    c = 0
    while len(out) < n:
        out += H(seed + c.to_bytes(4, 'big')).digest()
        c += 1
    return out[:n]


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


def pss_encode(H, m, salt, embits):
    emlen = (embits + 7) // 8
    mh = H(m).digest()
    hh = H(b'\0' * 8 + mh + salt).digest()
    db = b'\0' * (emlen - len(salt) - len(mh) - 2) + b'\1' + salt
    masked = bytearray(xor(db, mgf1(H, hh, emlen - len(mh) - 1)))
    masked[0] &= 0xff >> (8 * emlen - embits)
    return bytes(masked) + hh + b'\xbc'


def oaep_encode(H, m, label, seed, k):
    lh = H(label).digest()
    db = lh + b'\0' * (k - len(m) - 2 * len(lh) - 2) + b'\1' + m
    masked = xor(db, mgf1(H, seed, k - len(lh) - 1))
    return b'\0' + xor(seed, mgf1(H, masked, len(lh))) + masked


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    lines, expect = [], []

    def case(name, i, expr, want):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, i, expr))
        expect.append('%s %d %s' % (name, i, want))

    keys = []
    for bits, e in [(512, 65537), (1024, 3), (1024, 65537), (2048, 65537), (1032, 65537)]:
        keys.append(rsa.generate_private_key(e, bits))
    for ki, key in enumerate(keys):
        pn = key.private_numbers()
        n, e, d, p, q = pn.public_numbers.n, pn.public_numbers.e, pn.d, pn.p, pn.q
        k = (n.bit_length() + 7) // 8
        sk = 'priv(h("%s"), h("%s"), h("%s"), h("%s"), h("%s"))' % (hx(n), hx(e), hx(d), hx(p), hx(q))
        pk = 'R.Rsa.public(%s)' % sk
        pub = key.public_key()
        for hn, (Hc, Hl) in HASHES.items():
            if hn == 'sha512' and k < 64 + 19 + 11:
                continue
            m = rb(rng.randrange(0, 100))
            sig = key.sign(m, padding.PKCS1v15(), Hc())
            case('pkcs1_sign', ki, 'ro(P.RsaPkcs1.sign(~%s, %s, %s, %s))' % (hn, PREFIX[hn], sk, o(m)), sig.hex() + '.')
            case('pkcs1_verify', ki, 'bs(P.RsaPkcs1.verify(~%s, %s, %s, %s, %s))' % (hn, PREFIX[hn], pk, o(m), o(sig)), 'yes')
            bad = bytearray(sig)
            bad[rng.randrange(k)] ^= 1 << rng.randrange(8)
            case('pkcs1_verify_bad', ki, 'bs(P.RsaPkcs1.verify(~%s, %s, %s, %s, %s))' % (hn, PREFIX[hn], pk, o(m), o(bytes(bad))), 'no')
            case('pkcs1_verify_badmsg', ki, 'bs(P.RsaPkcs1.verify(~%s, %s, %s, %s, %s))' % (hn, PREFIX[hn], pk, o(m + b'x'), o(sig)), 'no')
            mg = '~M.RsaMgf1.mask(~%s)' % hn
            hl = Hl().digest_size
            embits = n.bit_length() - 1
            for slen in [0, hl, rng.randrange(1, 20)]:
                if (embits + 7) // 8 < hl + slen + 2:
                    continue
                m = rb(rng.randrange(0, 100))
                sig = key.sign(m, padding.PSS(padding.MGF1(Hc()), slen), Hc())
                case('pss_verify', ki, 'bs(S.RsaPss.verify(~%s, %s, %s, %s, %s, %dn))' % (hn, mg, pk, o(m), o(sig), slen), 'yes')
                case('pss_verify_wrongslen', ki, 'bs(S.RsaPss.verify(~%s, %s, %s, %s, %s, %dn))' % (hn, mg, pk, o(m), o(sig), slen + 1), 'no')
                salt = rb(slen)
                em = pss_encode(Hl, m, salt, embits)
                mine = pow(int.from_bytes(em, 'big'), d, n).to_bytes(k, 'big')
                pub.verify(mine, m, padding.PSS(padding.MGF1(Hc()), slen), Hc())
                case('pss_sign', ki, 'ro(S.RsaPss.sign(~%s, %s, %s, %s, %s))' % (hn, mg, sk, o(m), o(salt)), mine.hex() + '.')
            # OAEP
            label = rb(rng.randrange(0, 20))
            if k >= 2 * hl + 2:
                m = rb(rng.randrange(0, k - 2 * hl - 1))
                c = pub.encrypt(m, padding.OAEP(padding.MGF1(Hc()), Hc(), label or None))
                case('oaep_decrypt', ki, 'ro(O.RsaOaep.decrypt(~%s, %s, %s, %s, %s))' % (hn, mg, sk, o(label), o(c)), m.hex() + '.')
                seed = rb(hl)
                em = oaep_encode(Hl, m, label, seed, k)
                mine = pow(int.from_bytes(em, 'big'), e, n).to_bytes(k, 'big')
                assert key.decrypt(mine, padding.OAEP(padding.MGF1(Hc()), Hc(), label or None)) == m
                case('oaep_encrypt', ki, 'ro(O.RsaOaep.encrypt(~%s, %s, %s, %s, %s, %s))' % (hn, mg, pk, o(label), o(m), o(seed)), mine.hex() + '.')
                case('oaep_decrypt_badlabel', ki, 'ro(O.RsaOaep.decrypt(~%s, %s, %s, %s, %s))' % (hn, mg, sk, o(label + b'z'), o(c)), 'decryption-error')
                case('oaep_too_long', ki, 'ro(O.RsaOaep.encrypt(~%s, %s, %s, %s, %s, %s))' % (hn, mg, pk, o(label), o(rb(k - 2 * hl - 1)), o(seed)), 'too-long')
        # PKCS #1 v1.5 encryption
        m = rb(rng.randrange(0, k - 10))
        c = pub.encrypt(m, padding.PKCS1v15())
        case('es15_decrypt', ki, 'ro(E.RsaEs15.decrypt(%s, %s))' % (sk, o(c)), m.hex() + '.')
        ps = bytes(rng.randrange(1, 256) for _ in range(k - len(m) - 3))
        mine = pow(int.from_bytes(b'\0\2' + ps + b'\0' + m, 'big'), e, n).to_bytes(k, 'big')
        assert key.decrypt(mine, padding.PKCS1v15()) == m
        case('es15_encrypt', ki, 'ro(E.RsaEs15.encrypt(%s, %s, %s))' % (pk, o(m), o(ps)), mine.hex() + '.')
        case('es15_badps', ki, 'ro(E.RsaEs15.encrypt(%s, %s, %s))' % (pk, o(m), o(b'\0' + ps[1:])), 'encoding-error')
        case('es15_too_long', ki, 'ro(E.RsaEs15.encrypt(%s, %s, %s))' % (pk, o(rb(k - 10)), o(b'')), 'too-long')
        case('es15_wrong_len', ki, 'ro(E.RsaEs15.decrypt(%s, %s))' % (sk, o(c[1:])), 'decryption-error')
        # primitives
        x = rng.randrange(n)
        case('rsadp', ki, 'rn(R.Rsa.dp(%s, h("%s")))' % (sk, hx(x)), hx(pow(x, d, n)))
        case('rsadp_plain', ki, 'rn(R.Rsa.dp_plain(%s, h("%s")))' % (sk, hx(x)), hx(pow(x, d, n)))
        case('rsaep', ki, 'rn(R.Rsa.ep(%s, h("%s")))' % (pk, hx(x)), hx(pow(x, e, n)))
        case('rsaep_range', ki, 'rn(R.Rsa.ep(%s, h("%s")))' % (pk, hx(n)), 'out-of-range')
        # key forms
        case('keys', ki, 'pshow(K.RsaKeys.public_of(K.RsaKeys.public_to(%s)))' % pk, '%s %s' % (hx(n), hx(e)))
        f = lambda v: len(v.to_bytes((v.bit_length() + 7) // 8, 'big')).to_bytes(4, 'big') + v.to_bytes((v.bit_length() + 7) // 8, 'big')
        form = f(n) + f(e) + f(d) + f(p) + f(q)
        case('keys_private', ki, 'sshow(K.RsaKeys.private_of(%s))' % o(form), form.hex())
        case('keys_private_bad', ki, 'sshow(K.RsaKeys.private_of(%s))' % o(form[:-1]), 'bad-format')
        case('private_of_primes', ki, 'kshow(R.Rsa.private_of_primes(h("%s"), h("%s"), h("%s")))' % (hx(p), hx(q), hx(e)),
             '%s %s %s' % (hx(p), hx(q), hx(pow(e, -1, (p - 1) * (q - 1) // __import__('math').gcd(p - 1, q - 1)))))
    case('bad_key', 0, 'pshow(R.Rsa.public_of(h("%s"), h("2")))' % hx(3233), 'bad-key')
    case('bad_key', 1, 'kshow(R.Rsa.private_of(h("%s"), h("11"), h("3"), h("3d"), h("35")))' % hx(3233), 'bad-key')
    # key generation from seeds
    import math
    bases = ', '.join('h("%x")' % b for b in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41])
    for i, nlen in enumerate([256, 512, 768]):
        sp, sq = rb(nlen // 16), rb(nlen // 16)

        def find(seed):
            b = nlen // 2
            x = (int.from_bytes(seed, 'big') % (1 << (b - 2))) + (1 << (b - 1)) + (1 << (b - 2))
            x |= 1
            while True:
                if math.gcd(x - 1, 65537) == 1 and all(pow(a, x - 1, x) == 1 for a in [2, 3, 5, 7, 11, 13]) and all(x % s for s in range(3, 256, 2) if s < x):
                    return x
                x += 2
        p, q = find(sp), find(sq)
        d = pow(65537, -1, (p - 1) * (q - 1) // math.gcd(p - 1, q - 1))
        rsa.RSAPrivateNumbers(p, q, d, d % (p - 1), d % (q - 1), pow(q, -1, p), rsa.RSAPublicNumbers(65537, p * q)).private_key()
        case('keygen', i, 'kshow(G.RsaKeygen.generate(h("10001"), %dn, %s, %s, [%s], 2000n))' % (nlen, o(sp), o(sq), bases),
             '%s %s %s' % (hx(p), hx(q), hx(d)))

    for old in os.listdir(HERE):
        if old.startswith('cases') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        with open(os.path.join(HERE, 'cases%02d.bend' % (j // CHUNK)), 'w', newline='\n') as fh:
            fh.write(HEADER + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(lines[j:j + CHUNK]) + '\n')
    with open(os.path.join(HERE, 'expected.txt'), 'w', newline='\n') as fh:
        fh.write('\n'.join(expect) + '\n')
    print('%d cases against cryptography' % len(lines))


if __name__ == '__main__':
    main()
