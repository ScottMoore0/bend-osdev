#!/usr/bin/env python3
"""Differential test of ecrdsa against a model of RFC 7091's algorithm.

  python3 gen.py [seed]   writes cases00.bend, ... and expected.txt

No implementation of GOST R 34.10-2012 outside this repository is installed
here (Python's cryptography and the openssl command have none without the
GOST engine), so the reference is this file's model of RFC 7091 sections 6.1
and 6.2, on ecc's affine model (gen/curves.py), with Streebog from the
streebog package's model (streebog/ref/model.py). Both share an author with
this package; the model checks itself first on RFC 7091's example (section
7: Q = d P, and the signature r, s from e and k), which check.bend also
runs through this package.
For RFC 4357's CryptoPro A, B and C curves and RFC 7091's example curve:
  * Bend's signature with a given k equals the model's, for e given and for
    messages through Streebog-256;
  * Bend verifies the model's signatures, and refuses them changed;
  * RFC 4491's forms of keys and signatures round-trip.
"""
import os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'ecc', 'gen'))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'streebog', 'ref'))
import curves as CV  # noqa: E402
import model as HM  # noqa: E402

CHUNK = 40

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../../bignum/bignum.bend as N
import ../../ecc/ecc.bend as E
import ../../ecc/curves.bend as C
import ../../ecc/ecdsa.bend as S
import ../ecrdsa.bend as G

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

def rs(r: Result<&2, &2, G.EcrdsaError, S.EcSig>) -> String:
  match r:
    case Fail{G.EcrdsaBadNonce{}}:
      "bad-nonce"
    case Fail{G.EcrdsaBadPrivateKey{}}:
      "bad-private"
    case Fail{G.EcrdsaBadPublicKey{}}:
      "bad-public"
    case Done{S.EcSig{r, s}}:
      N.BnNat.hex(r) ++ " " ++ N.BnNat.hex(s)

def rp(r: Result<&2, &2, G.EcrdsaError, E.EcPoint>) -> String:
  match r:
    case Fail{e}:
      "bad-public"
    case Done{E.EcAff{x, y}}:
      N.BnNat.hex(x) ++ " " ++ N.BnNat.hex(y)
    case Done{E.EcInf{}}:
      "inf"

def sb(c: E.EcCurve, r: Result<&2, &2, G.EcrdsaError, S.EcSig>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{x}:
      B.Octets.hex(G.Ecrdsa.sig_to(c, x))

def pk(x: String, y: String) -> E.EcPoint:
  E.EcAff{h(x), h(y)}

def sig(r: String, s: String) -> S.EcSig:
  S.EcSig{h(r), h(s)}
'''

CURVES = ['gost_cp_a', 'gost_cp_b', 'gost_cp_c', 'gost_example']


def hx(v):
    return '%x' % v


def o(b):
    return 'ob([%s])' % ', '.join(map(str, b))


def model_sign(cd, d, e, k):
    p, a, n = cd['p'], cd['a'] % cd['p'], cd['n']
    C = CV.mul(k, (cd['gx'], cd['gy']), a, p)
    r = C[0] % n
    return r, (r * d + k * e) % n


def model_verify(cd, Q, e, r, s):
    p, a, n = cd['p'], cd['a'] % cd['p'], cd['n']
    if not (0 < r < n and 0 < s < n):
        return False
    v = pow(e, -1, n)
    z1, z2 = s * v % n, (-r * v) % n
    C = CV.add(CV.mul(z1, (cd['gx'], cd['gy']), a, p), CV.mul(z2, Q, a, p), a, p)
    return C is not None and C[0] % n == r


def e_of(cd, hv):
    e = int.from_bytes(hv, 'little') % cd['n']
    return e or 1


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, i, expr, want):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, i, expr))
        expect.append('%s %d %s' % (name, i, want))

    # the model against RFC 7091's example first
    ex = dict(CV.CURVES_BY_NAME)['gost_example']
    d = 55441196065363246126355624130324183196576709222340016572108097750006097525544
    Q = CV.mul(d, (ex['gx'], ex['gy']), ex['a'], ex['p'])
    assert Q == (57520216126176808443631405023338071176630104906313632182896741342206604859403,
                 17614944419213781543809391949654080031942662045363639260709847859438286763994)
    e = 20798893674476452017134061561508270130637142515379653289952617252661468872421
    k = 53854137677348463731403841147996619241504003434302020712960838528893196233395
    assert model_sign(ex, d, e, k) == (29700980915817952874371204983938256990422752107994319651632687982059210933395,
                                       574973400270084654178925310019147038455227042649098563933718999175515839552)
    assert model_verify(ex, Q, e, *model_sign(ex, d, e, k))

    for ci, name in enumerate(CURVES):
        cd = dict(CV.CURVES_BY_NAME)[name]
        p, a, n = cd['p'], cd['a'] % cd['p'], cd['n']
        c = 'E.EcCurve.of(C.EcCurves.%s())' % name
        fl = (p.bit_length() + 7) // 8
        nl = (n.bit_length() + 7) // 8
        for i in range(4):
            d = rng.randrange(1, n)
            Q = CV.mul(d, (cd['gx'], cd['gy']), a, p)
            P_ = 'pk("%s", "%s")' % (hx(Q[0]), hx(Q[1]))
            tag = ci * 10 + i
            e = rng.randrange(0, n)
            k = rng.randrange(1, n)
            r, s = model_sign(cd, d, e or 1, k)
            case('sign_e', tag, 'rs(G.Ecrdsa.sign_e(%s, h("%s"), h("%s"), h("%s")))' % (c, hx(d), hx(e or 1), hx(k)), '%s %s' % (hx(r), hx(s)))
            case('verify_e', tag, 'bs(G.Ecrdsa.verify_e(%s, %s, h("%s"), sig("%s", "%s")))' % (c, P_, hx(e or 1), hx(r), hx(s)), 'yes')
            case('verify_e_bad', tag, 'bs(G.Ecrdsa.verify_e(%s, %s, h("%s"), sig("%s", "%s")))' % (c, P_, hx(e or 1), hx(r), hx((s + 1) % n)), 'no')
            m = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 90)))
            em = e_of(cd, HM.streebog256(m))
            r2, s2 = model_sign(cd, d, em, k)
            sigb = s2.to_bytes(nl, 'big') + r2.to_bytes(nl, 'big')
            case('sign', tag, 'sb(%s, G.Ecrdsa.sign(~G.Ecrdsa.streebog256, %s, h("%s"), %s, h("%s")))'
                 % (c, c, hx(d), o(m), hx(k)), sigb.hex())
            case('verify', tag, 'bs(G.Ecrdsa.verify_bytes(~G.Ecrdsa.streebog256, %s, %s, %s, %s))' % (c, P_, o(m), o(sigb)), 'yes')
            case('verify_other', tag, 'bs(G.Ecrdsa.verify_bytes(~G.Ecrdsa.streebog256, %s, %s, %s, %s))' % (c, P_, o(m + b'!'), o(sigb)), 'no')
            pkb = Q[0].to_bytes(fl, 'little') + Q[1].to_bytes(fl, 'little')
            case('public_to', tag, 'B.Octets.hex(G.Ecrdsa.public_to(%s, %s))' % (c, P_), pkb.hex())
            case('public_of', tag, 'rp(G.Ecrdsa.public_of(%s, %s))' % (c, o(pkb)), '%s %s' % (hx(Q[0]), hx(Q[1])))
        case('public_off', ci, 'rp(G.Ecrdsa.public_of(%s, %s))' % (c, o(b'\x01' * (2 * fl))), 'bad-public')
        case('bad_nonce', ci, 'rs(G.Ecrdsa.sign_e(%s, h("5"), h("7"), h("%s")))' % (c, hx(n)), 'bad-nonce')

    for old in os.listdir(HERE):
        if old.startswith('cases') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        with open(os.path.join(HERE, 'cases%02d.bend' % (j // CHUNK)), 'w', newline='\n') as fh:
            fh.write(HEADER + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(lines[j:j + CHUNK]) + '\n')
    with open(os.path.join(HERE, 'expected.txt'), 'w', newline='\n') as fh:
        fh.write('\n'.join(expect) + '\n')
    print('%d cases against the RFC 7091 model' % len(lines))


if __name__ == '__main__':
    main()
