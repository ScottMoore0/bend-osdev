#!/usr/bin/env python3
"""Differential test of sm2 against the openssl command's SM2 (OpenSSL 3).

  python3 gen.py [seed]   writes cases00.bend, ... and expected.txt

For keys the openssl command generates on SM2's curve, with SM3 and several
identities:
  * Bend verifies openssl's signatures (openssl pkeyutl -sign -rawin
    -digest sm3 -pkeyopt distid:<ID>), and refuses them changed, under
    another identity, or for another message;
  * Bend's signature with a given k equals this file's computation of
    draft-shen-sm2-ecdsa-02's algorithm (Z_A and e through Python's hashlib
    SM3), which openssl pkeyutl -verify first accepts;
  * Bend's Z_A equals this file's.
The draft's own example (Appendix A.2) is in check.bend.
"""
import hashlib, os, random, re, subprocess, sys, tempfile
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature, encode_dss_signature

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'ecc', 'gen'))
import curves as CV  # noqa: E402

CHUNK = 40

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../../bignum/bignum.bend as N
import ../../ecc/ecc.bend as E
import ../../ecc/curves.bend as C
import ../../ecc/ecdsa.bend as S
import ../sm2.bend as M

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

def rs(r: Result<&2, &2, M.Sm2Error, S.EcSig>) -> String:
  match r:
    case Fail{M.Sm2BadNonce{}}:
      "bad-nonce"
    case Fail{M.Sm2BadPrivateKey{}}:
      "bad-private"
    case Fail{M.Sm2IdTooLong{}}:
      "id-too-long"
    case Done{S.EcSig{r, s}}:
      N.BnNat.hex(r) ++ " " ++ N.BnNat.hex(s)

def curve() -> E.EcCurve:
  E.EcCurve.of(C.EcCurves.sm2())

def pk(x: String, y: String) -> E.EcPoint:
  E.EcAff{h(x), h(y)}

def sig(r: String, s: String) -> S.EcSig:
  S.EcSig{h(r), h(s)}
'''


def hx(v):
    return '%x' % v


def o(b):
    return 'ob([%s])' % ', '.join(map(str, b))


def sm3(b):
    return hashlib.new('sm3', b).digest()


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    cd = dict(CV.CURVES_BY_NAME)['sm2']
    p, a, b, n, G = cd['p'], cd['a'], cd['b'], cd['n'], (cd['gx'], cd['gy'])
    lines, expect = [], []

    def case(name, i, expr, want):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, i, expr))
        expect.append('%s %d %s' % (name, i, want))

    def za(ident, P):
        f = lambda v: v.to_bytes(32, 'big')
        return sm3((8 * len(ident)).to_bytes(2, 'big') + ident + f(a) + f(b) + f(G[0]) + f(G[1]) + f(P[0]) + f(P[1]))

    tmp = tempfile.mkdtemp()

    def run(*args, data=None):
        return subprocess.run(args, capture_output=True, input=data, cwd=tmp)

    for i in range(10):
        run('openssl', 'genpkey', '-algorithm', 'EC', '-pkeyopt', 'ec_paramgen_curve:SM2', '-out', 'k.pem')
        text = run('openssl', 'pkey', '-in', 'k.pem', '-text', '-noout').stdout.decode()
        priv = int(re.sub(r'[\s:]', '', text.split('priv:')[1].split('pub:')[0]), 16)
        pub = bytes.fromhex(re.sub(r'[\s:]', '', text.split('pub:')[1].split('ASN1')[0]))
        P = (int.from_bytes(pub[1:33], 'big'), int.from_bytes(pub[33:65], 'big'))
        assert CV.mul(priv, G, a, p) == P
        ident = [b'ALICE123@YAHOO.COM', b'1234567812345678', bytes(rng.choice(b'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789@.') for _ in range(rng.randrange(1, 40)))][i % 3]
        m = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 100)))
        with open(os.path.join(tmp, 'm'), 'wb') as fh:
            fh.write(m)
        distid = 'distid:' + ident.decode()
        der = run('openssl', 'pkeyutl', '-sign', '-inkey', 'k.pem', '-in', 'm', '-rawin', '-digest', 'sm3', '-pkeyopt', distid).stdout
        r, s = decode_dss_signature(der)
        args = (o(ident), o(m))
        P_ = 'pk("%s", "%s")' % (hx(P[0]), hx(P[1]))
        case('verify', i, 'bs(M.Sm2.verify(~M.Sm2.sm3, curve(), %s, %s, %s, sig("%s", "%s")))' % ((P_,) + args + (hx(r), hx(s))), 'yes')
        case('verify_bad_s', i, 'bs(M.Sm2.verify(~M.Sm2.sm3, curve(), %s, %s, %s, sig("%s", "%s")))' % ((P_,) + args + (hx(r), hx(s ^ 1))), 'no')
        case('verify_other_id', i, 'bs(M.Sm2.verify(~M.Sm2.sm3, curve(), %s, %s, %s, sig("%s", "%s")))' % (P_, o(ident + b'x'), o(m), hx(r), hx(s)), 'no')
        case('verify_other_msg', i, 'bs(M.Sm2.verify(~M.Sm2.sm3, curve(), %s, %s, %s, sig("%s", "%s")))' % (P_, o(ident), o(m + b'x'), hx(r), hx(s)), 'no')
        z = za(ident, P)
        case('za', i, 'B.Octets.hex(M.Sm2.za(~M.Sm2.sm3, curve(), %s, %s))' % (o(ident), P_), z.hex())
        e = int.from_bytes(sm3(z + m), 'big')
        while True:
            k = rng.randrange(1, n)
            x1 = CV.mul(k, G, a, p)[0]
            r2 = (e + x1) % n
            s2 = pow(1 + priv, -1, n) * (k - r2 * priv) % n
            if r2 and r2 + k != n and s2:
                break
        with open(os.path.join(tmp, 's.der'), 'wb') as fh:
            fh.write(encode_dss_signature(r2, s2))
        res = run('openssl', 'pkeyutl', '-verify', '-inkey', 'k.pem', '-in', 'm', '-rawin', '-digest', 'sm3', '-pkeyopt', distid, '-sigfile', 's.der')
        assert b'Verified Successfully' in res.stdout, res
        case('sign', i, 'rs(M.Sm2.sign(~M.Sm2.sm3, curve(), h("%s"), %s, %s, h("%s")))' % (hx(priv), o(ident), o(m), hx(k)), '%s %s' % (hx(r2), hx(s2)))
    case('bad_nonce', 0, 'rs(M.Sm2.sign(~M.Sm2.sm3, curve(), h("5"), %s, %s, h("0")))' % (o(b'A'), o(b'm')), 'bad-nonce')
    case('id_too_long', 0, 'rs(M.Sm2.sign(~M.Sm2.sm3, curve(), h("5"), B.Octets.zeros(8192n), %s, h("7")))' % o(b'm'), 'id-too-long')

    for old in os.listdir(HERE):
        if old.startswith('cases') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        with open(os.path.join(HERE, 'cases%02d.bend' % (j // CHUNK)), 'w', newline='\n') as fh:
            fh.write(HEADER + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(lines[j:j + CHUNK]) + '\n')
    with open(os.path.join(HERE, 'expected.txt'), 'w', newline='\n') as fh:
        fh.write('\n'.join(expect) + '\n')
    print('%d cases against the openssl command' % len(lines))


if __name__ == '__main__':
    main()
