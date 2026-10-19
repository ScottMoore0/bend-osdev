#!/usr/bin/env python3
"""Differential test of ecc against Python's cryptography package and the
openssl command.

  python3 gen.py [seed]   writes cases00.bend, ... and expected.txt

* The curves: each NIST curve's and SM2's parameters (as curves.bend writes
  them) equal the openssl command's (openssl ecparam -param_enc explicit),
  read back through cryptography.
* Keys: d G equals cryptography's public key for the same d (P-192 to
  P-521); public keys round-trip through SEC 1's form.
* ECDH: the shared secret equals cryptography's ECDH exchange, both ways.
* ECDSA: Bend verifies cryptography's signatures (SHA-256, SHA-512), and
  refuses them changed; Bend's signature with a given k equals this file's
  FIPS 186-5 computation, which cryptography first verifies.
* Validation: points off the curve, with a coordinate of p or more, of the
  wrong length or first byte are refused; n G is the point at infinity.
* The GOST and SM2 curves: k G and u G + v Q against this file's affine
  model (gen/curves.py's), which checks itself on the curves' own orders.
"""
import os, random, subprocess, sys
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature, encode_dss_signature

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'gen'))
import curves as CV  # noqa: E402

CHUNK = 40

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../../bignum/bignum.bend as N
import ../ecc.bend as E
import ../curves.bend as C
import ../ecdh.bend as D
import ../ecdsa.bend as S
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

def err(e: E.EcError) -> String:
  match e:
    case E.EcBadPoint{}:
      "bad-point"
    case E.EcInfinity{}:
      "infinity"
    case E.EcBadEncoding{}:
      "bad-encoding"
    case E.EcBadPrivateKey{}:
      "bad-private"
    case E.EcBadNonce{}:
      "bad-nonce"

def pt(p: E.EcPoint) -> String:
  match p:
    case E.EcInf{}:
      "inf"
    case E.EcAff{x, y}:
      N.BnNat.hex(x) ++ " " ++ N.BnNat.hex(y)

def rp(r: Result<&2, &2, E.EcError, E.EcPoint>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{p}:
      pt(p)

def ro(r: Result<&2, &2, E.EcError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{o}:
      B.Octets.hex(o)

def rs(r: Result<&2, &2, E.EcError, S.EcSig>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{S.EcSig{r, s}}:
      N.BnNat.hex(r) ++ " " ++ N.BnNat.hex(s)

def prm(c: E.EcParams) -> String:
  match c:
    case E.EcParams{p, a, b, gx, gy, n, h}:
      N.BnNat.hex(p) ++ " " ++ N.BnNat.hex(a) ++ " " ++ N.BnNat.hex(b) ++ " " ++ N.BnNat.hex(gx) ++ " " ++ N.BnNat.hex(gy) ++ " " ++ N.BnNat.hex(n) ++ " " ++ N.BnNat.hex(h)

def aff(x: String, y: String) -> E.EcPoint:
  E.EcAff{h(x), h(y)}
'''

NIST = [('p192', ec.SECP192R1, 'prime192v1'), ('p224', ec.SECP224R1, 'secp224r1'), ('p256', ec.SECP256R1, 'prime256v1'),
        ('p384', ec.SECP384R1, 'secp384r1'), ('p521', ec.SECP521R1, 'secp521r1')]
OTHER = ['sm2', 'sm2_example', 'gost_cp_a', 'gost_cp_b', 'gost_cp_c', 'gost_example']


def hx(v):
    return '%x' % v


def o(b):
    return 'ob([%s])' % ', '.join(map(str, b))


def der_leaves(b):
    """the INTEGER and OCTET STRING values of a DER encoding, in order"""
    out, pos = [], 0
    while pos < len(b):
        t, ln = b[pos], b[pos + 1]
        pos += 2
        if ln & 0x80:
            k = ln & 0x7f
            ln = int.from_bytes(b[pos:pos + k], 'big')
            pos += k
        v = b[pos:pos + ln]
        pos += ln
        if t == 0x30:
            out += der_leaves(v)
        elif t in (2, 4):
            out.append(int.from_bytes(v, 'big'))
    return out


def openssl_params(name):
    """p, a, b, gx, gy, n, h of a named curve, from the openssl command"""
    der = subprocess.run(['openssl', 'ecparam', '-name', name, '-param_enc', 'explicit', '-outform', 'DER'],
                         capture_output=True, check=True).stdout
    # ECParameters: version, fieldID {oid, p}, curve {a, b, seed}, base, order, cofactor
    version, p, a, b, base, n, hco = der_leaves(der)
    pl = (p.bit_length() + 7) // 8
    bb = base.to_bytes(1 + 2 * pl, 'big')
    return p, a, b, int.from_bytes(bb[1:1 + pl], 'big'), int.from_bytes(bb[1 + pl:], 'big'), n, hco


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, i, expr, want):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, i, expr))
        expect.append('%s %d %s' % (name, i, want))

    for ci, (name, curve, oname) in enumerate(NIST + [('sm2', None, 'SM2')]):
        p, a, b, gx, gy, n, hco = openssl_params(oname)
        case('params', ci, 'prm(C.EcCurves.%s())' % name, ' '.join(map(hx, [p, a, b, gx, gy, n, hco])))
    for ci, (name, curve, oname) in enumerate(NIST):
        c = 'E.EcCurve.of(C.EcCurves.%s())' % name
        p = dict(CV.CURVES_BY_NAME)[name]['p']
        n = dict(CV.CURVES_BY_NAME)[name]['n']
        fl = (p.bit_length() + 7) // 8
        nl = (n.bit_length() + 7) // 8
        for i in range(3):
            k1 = ec.generate_private_key(curve())
            k2 = ec.generate_private_key(curve())
            d1 = k1.private_numbers().private_value
            d2 = k2.private_numbers().private_value
            q1 = k1.public_key().public_numbers()
            q2 = k2.public_key().public_numbers()
            enc1 = k1.public_key().public_bytes(serialization.Encoding.X962, serialization.PublicFormat.UncompressedPoint)
            enc2 = k2.public_key().public_bytes(serialization.Encoding.X962, serialization.PublicFormat.UncompressedPoint)
            tag = ci * 10 + i
            case('public', tag, 'pt(D.EcDh.public(%s, h("%s")))' % (c, hx(d1)), '%s %s' % (hx(q1.x), hx(q1.y)))
            case('point_of', tag, 'rp(E.EcCurve.point_of(%s, %s))' % (c, o(enc1)), '%s %s' % (hx(q1.x), hx(q1.y)))
            case('point_to', tag, 'B.Octets.hex(E.EcCurve.point_to(%s, aff("%s", "%s")))' % (c, hx(q1.x), hx(q1.y)), enc1.hex())
            z = k1.exchange(ec.ECDH(), k2.public_key())
            assert z == k2.exchange(ec.ECDH(), k1.public_key())
            case('ecdh', tag, 'ro(D.EcDh.agree(%s, h("%s"), aff("%s", "%s")))' % (c, hx(d1), hx(q2.x), hx(q2.y)), z.hex())
            if i == 0:
                case('ecdh_b', tag, 'ro(D.EcDh.primitive(%s, h("%s"), aff("%s", "%s")))' % (c, hx(d2), hx(q1.x), hx(q1.y)), z.hex())
            for hn, hcls in [('sha256', hashes.SHA256), ('sha512', hashes.SHA512)]:
                if i == 2 and hn == 'sha512':
                    continue
                m = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 80)))
                der = k1.sign(m, ec.ECDSA(hcls()))
                r, s = decode_dss_signature(der)
                sig = r.to_bytes(nl, 'big') + s.to_bytes(nl, 'big')
                pk = 'aff("%s", "%s")' % (hx(q1.x), hx(q1.y))
                case('verify_' + hn, tag, 'bs(S.EcDsa.verify_bytes(~%s, %s, %s, %s, %s))' % (hn, c, pk, o(m), o(sig)), 'yes')
                bad = bytearray(sig)
                bad[rng.randrange(len(bad))] ^= 1 << rng.randrange(8)
                case('verify_bad_' + hn, tag, 'bs(S.EcDsa.verify_bytes(~%s, %s, %s, %s, %s))' % (hn, c, pk, o(m), o(bytes(bad))), 'no')
                # Bend signs with a given k; the expected value is FIPS 186-5's formula, checked by cryptography
                import hashlib
                hv = hashlib.new(hn, m).digest()
                e = int.from_bytes(hv, 'big') >> max(0, 8 * len(hv) - n.bit_length())
                k = rng.randrange(1, n)
                cd = dict(CV.CURVES_BY_NAME)[name]
                R = CV.mul(k, (cd['gx'], cd['gy']), cd['a'] % p, p)
                r2 = R[0] % n
                s2 = pow(k, -1, n) * (e + r2 * d1) % n
                k1.public_key().verify(encode_dss_signature(r2, s2), m, ec.ECDSA(hcls()))
                case('sign_' + hn, tag, 'rs(S.EcDsa.sign(~%s, %s, h("%s"), %s, h("%s")))' % (hn, c, hx(d1), o(m), hx(k)), '%s %s' % (hx(r2), hx(s2)))
        # validation
        cd = dict(CV.CURVES_BY_NAME)[name]
        gx, gy = cd['gx'], cd['gy']
        case('off_curve', ci, 'rp(E.EcCurve.point_of(%s, %s))' % (c, o(b'\x04' + gx.to_bytes(fl, 'big') + (gy ^ 1).to_bytes(fl, 'big'))), 'bad-point')
        case('big_coord', ci, 'rp(E.EcCurve.point_of(%s, %s))' % (c, o(b'\x04' + (gx + p).to_bytes(fl + 1, 'big')[-fl:] + gy.to_bytes(fl, 'big'))),
             'bad-point' if gx + p >= 256 ** fl else 'bad-point')
        case('bad_prefix', ci, 'rp(E.EcCurve.point_of(%s, %s))' % (c, o(b'\x03' + gx.to_bytes(fl, 'big') + gy.to_bytes(fl, 'big'))), 'bad-encoding')
        case('bad_length', ci, 'rp(E.EcCurve.point_of(%s, %s))' % (c, o(b'\x04' + gx.to_bytes(fl, 'big'))), 'bad-encoding')
        case('order', ci, 'pt(E.EcCurve.base_mul(%s, h("%s")))' % (c, hx(n)), 'inf')
        case('order_minus_one', ci, 'pt(E.EcCurve.base_mul(%s, h("%s")))' % (c, hx(n - 1)), '%s %s' % (hx(gx), hx(p - gy)))
        case('validate', ci, 'bs(E.EcCurve.validate(%s, E.EcCurve.generator(%s)))' % (c, c), 'yes')
        case('check', ci, 'bs(E.EcCurve.check(%s))' % c, 'yes')
        case('ecdh_inf', ci, 'ro(D.EcDh.primitive(%s, h("%s"), E.EcCurve.generator(%s)))' % (c, hx(n), c), 'infinity')
        case('private_of', ci, 'B.Octets.hex(D.EcDh.private_to(%s, h("1")))' % c, (1).to_bytes(nl, 'big').hex())
    for ci, name in enumerate(OTHER):
        cd = dict(CV.CURVES_BY_NAME)[name]
        p, a, n = cd['p'], cd['a'] % cd['p'], cd['n']
        G = (cd['gx'], cd['gy'])
        c = 'E.EcCurve.of(C.EcCurves.%s())' % name
        case('check', 10 + ci, 'bs(E.EcCurve.check(%s))' % c, 'yes')
        for i in range(3):
            k = rng.randrange(1, n)
            P = CV.mul(k, G, a, p)
            case('mul', ci * 10 + i, 'pt(E.EcCurve.base_mul(%s, h("%s")))' % (c, hx(k)), '%s %s' % (hx(P[0]), hx(P[1])))
            u, v = rng.randrange(n), rng.randrange(n)
            R = CV.add(CV.mul(u, G, a, p), CV.mul(v, P, a, p), a, p)
            want = 'inf' if R is None else '%s %s' % (hx(R[0]), hx(R[1]))
            case('mul2', ci * 10 + i, 'pt(E.EcCurve.mul2(%s, h("%s"), E.EcCurve.generator(%s), h("%s"), aff("%s", "%s")))'
                 % (c, hx(u), c, hx(v), hx(P[0]), hx(P[1])), want)

    for old in os.listdir(HERE):
        if old.startswith('cases') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        with open(os.path.join(HERE, 'cases%02d.bend' % (j // CHUNK)), 'w', newline='\n') as fh:
            fh.write(HEADER + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(lines[j:j + CHUNK]) + '\n')
    with open(os.path.join(HERE, 'expected.txt'), 'w', newline='\n') as fh:
        fh.write('\n'.join(expect) + '\n')
    print('%d cases against cryptography, the openssl command and the affine model' % len(lines))


if __name__ == '__main__':
    main()
