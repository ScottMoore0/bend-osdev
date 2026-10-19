#!/usr/bin/env python3
"""Differential test of dh against the openssl command and Python's
cryptography package.

  python3 gen.py [seed]   writes cases00.bend, ... and expected.txt

* The named groups: each p (as groups.bend writes it) equals the prime of
  the openssl command's group of that name (openssl genpkey -genparam
  -pkeyopt group:ffdhe2048 and so on, read back with cryptography).
* Agreement: for keys made by cryptography's DH over each group (private
  keys of 256 to 2048 bits), Bend's public key equals cryptography's, and
  Bend's shared secret from one side's private key and the other's public
  key equals cryptography's exchange, both ways.
* Validation: full (y^q = 1) and by the Legendre symbol agree on valid keys
  and on non-residues; the range checks refuse 0, 1, p - 1 and p; a public
  key of the wrong length is refused.
"""
import os, random, subprocess, sys
from cryptography.hazmat.primitives.asymmetric import dh
from cryptography.hazmat.primitives.serialization import load_pem_parameters

HERE = os.path.dirname(os.path.abspath(__file__))
CHUNK = 40

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../../bignum/bignum.bend as N
import ../dh.bend as D
import ../groups.bend as G

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

def err(e: D.DhError) -> String:
  match e:
    case D.DhBadPrivateKey{}:
      "bad-private"
    case D.DhBadPublicKey{}:
      "bad-public"
    case D.DhBadSharedSecret{}:
      "bad-shared"
    case D.DhBadLength{}:
      "bad-length"

def ro(r: Result<&2, &2, D.DhError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{o}:
      B.Octets.hex(o)

def rn(r: Result<&2, &2, D.DhError, N.BnNat>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{x}:
      N.BnNat.hex(x)

def gp(gr: D.DhGroup) -> String:
  match gr:
    case D.DhGroup{p, g, q}:
      N.BnNat.hex(p) ++ " " ++ N.BnNat.hex(g) ++ " " ++ N.BnNat.hex(q)
'''

GROUPS = [('ffdhe2048', 'ffdhe2048'), ('ffdhe3072', 'ffdhe3072'), ('ffdhe4096', 'ffdhe4096'), ('ffdhe6144', 'ffdhe6144'),
          ('ffdhe8192', 'ffdhe8192'), ('modp1536', 'modp_1536'), ('modp2048', 'modp_2048'), ('modp3072', 'modp_3072'),
          ('modp4096', 'modp_4096'), ('modp6144', 'modp_6144'), ('modp8192', 'modp_8192')]


def hx(v):
    return '%x' % v


def o(b):
    return 'ob([%s])' % ', '.join(map(str, b))


def openssl_p(name):
    pem = subprocess.run(['openssl', 'genpkey', '-genparam', '-algorithm', 'DH', '-pkeyopt', 'group:' + name],
                         capture_output=True, check=True).stdout
    return load_pem_parameters(pem).parameter_numbers().p


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, i, expr, want):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, i, expr))
        expect.append('%s %d %s' % (name, i, want))

    for gi, (name, oname) in enumerate(GROUPS):
        p = openssl_p(oname)
        case('group', gi, 'gp(G.DhGroups.%s())' % name, '%s 2 %s' % (hx(p), hx((p - 1) // 2)))
        g = 'G.DhGroups.%s()' % name
        plen = (p.bit_length() + 7) // 8
        params = dh.DHParameterNumbers(p, 2).parameters()
        for i in range(2 if p.bit_length() <= 3072 else 1):
            nbits = [256, 2047][i] if p.bit_length() == 2048 else 256
            xa, xb = rng.getrandbits(nbits) | 1, rng.getrandbits(nbits) | 1
            ka = dh.DHPrivateNumbers(xa, dh.DHPublicNumbers(pow(2, xa, p), params.parameter_numbers())).private_key()
            kb = dh.DHPrivateNumbers(xb, dh.DHPublicNumbers(pow(2, xb, p), params.parameter_numbers())).private_key()
            ya, yb = ka.public_key().public_numbers().y, kb.public_key().public_numbers().y
            z = int.from_bytes(ka.exchange(kb.public_key()), 'big')
            assert z == int.from_bytes(kb.exchange(ka.public_key()), 'big')
            case('public', gi * 10 + i, 'N.BnNat.hex(D.Dh.public(%s, h("%s")))' % (g, hx(xa)), hx(ya))
            agree = 'D.Dh.agree' if p.bit_length() <= 2048 else 'D.Dh.agree_safe'
            zb = z.to_bytes(plen, 'big').hex()
            case('shared_a', gi * 10 + i, 'ro(%s(%s, h("%s"), h("%s")))' % (agree, g, hx(xa), hx(yb)), zb)
            case('shared_b', gi * 10 + i, 'ro(D.Dh.agree_safe(%s, h("%s"), h("%s")))' % (g, hx(xb), hx(ya)), zb)
            yab = ya.to_bytes(plen, 'big')
            case('public_of', gi * 10 + i, 'rn(D.Dh.public_of(%s, %s))' % (g, o(yab)), hx(ya))
            case('public_to', gi * 10 + i, 'B.Octets.hex(D.Dh.public_to(%s, h("%s")))' % (g, hx(ya)), yab.hex())
        if p.bit_length() <= 2048:
            q = (p - 1) // 2
            for i in range(4):  # validation: residues pass, non-residues fail, both ways
                y = rng.randrange(2, p - 1)
                res = pow(y, q, p) == 1
                case('check_full', gi * 10 + i, 'bs(D.Dh.check_full(%s, h("%s")))' % (g, hx(y)), 'yes' if res else 'no')
                case('check_safe', gi * 10 + i, 'bs(D.Dh.check_safe(%s, h("%s")))' % (g, hx(y)), 'yes' if res else 'no')
            for i, y in enumerate([0, 1, p - 1, p]):
                case('bad_public', gi * 10 + i, 'ro(D.Dh.agree_safe(%s, h("5"), h("%s")))' % (g, hx(y)), 'bad-public')
            case('bad_length', gi, 'rn(D.Dh.public_of(%s, %s))' % (g, o(b'\x05')), 'bad-length')
            case('private_of', gi, 'rn(D.Dh.private_of(%s, %s))' % (g, o(q.to_bytes(plen, 'big'))), 'bad-private')
            c = rng.getrandbits(256 + 64)
            m = min(2 ** 256, q)
            case('private_from_bits', gi, 'N.BnNat.hex(D.Dh.private_from_bits(%s, %s, 256n))' % (g, o(c.to_bytes(40, 'big'))),
                 hx(c % (m - 1) + 1))

    for old in os.listdir(HERE):
        if old.startswith('cases') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        with open(os.path.join(HERE, 'cases%02d.bend' % (j // CHUNK)), 'w', newline='\n') as fh:
            fh.write(HEADER + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(lines[j:j + CHUNK]) + '\n')
    with open(os.path.join(HERE, 'expected.txt'), 'w', newline='\n') as fh:
        fh.write('\n'.join(expect) + '\n')
    print('%d cases against the openssl command and cryptography' % len(lines))


if __name__ == '__main__':
    main()
