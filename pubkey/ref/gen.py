#!/usr/bin/env python3
"""Differential test of pubkey's instances, through crypto's interfaces,
against Python's cryptography package.

  python3 gen.py [seed]   writes cases00.bend, ... and expected.txt

Keys and signatures come from cryptography; every key travels as bytes
(the instance's forms) and every check goes through CrSign.verify_bytes or
CrKex.agree. The cases:
  * ECDSA over P-256 with SHA-256: Bend accepts cryptography's signatures
    (random k; DER turned into r || s here) under the public key's SEC 1
    bytes, and refuses them for a changed message;
  * ECDH over P-256: Bend's shared secret from its private key's bytes and
    the peer's public-key bytes equals cryptography's exchange;
  * DH over FFDHE-2048 (the group's p from the openssl command, genpkey
    -pkeyopt group:ffdhe2048, read back with cryptography): Bend's shared
    secret equals cryptography's exchange, padded to p's length, and a peer
    key of p - 1 is refused;
  * RSASSA-PKCS1-v1_5 over SHA-256 (keys of 1024 to 2048 bits, in rsa's raw
    form): Bend's signature equals cryptography's (the scheme is
    deterministic), and Bend accepts it; RSASSA-PSS over SHA-256 with 32-byte
    salts: Bend accepts cryptography's signatures and refuses them for a
    changed message; Bend's own signature (its salt derived as PkRsa.pss_salt
    derives it) equals this file's RFC 8017 encoding signed with the raw
    private key, which cryptography first verifies.
"""
import hashlib, os, random, subprocess, sys
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, rsa, padding, dh
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat, load_pem_parameters

HERE = os.path.dirname(os.path.abspath(__file__))
CHUNK = 20

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../../bignum/bignum.bend as N
import ../../ecc/ecc.bend as E
import ../../ecc/curves.bend as EC
import ../../dh/groups.bend as DG
import ../../rsa/rsa.bend as R
import ../../crypto/crypto.bend as Cr
import ../../crypto/sign.bend as Sg
import ../../crypto/kex.bend as Kx
import ../rsa.bend as PR
import ../dh.bend as PD
import ../ecc.bend as PE

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

def rsa.go(r: Result<&2, &2, Cr.CrError, R.RsaPrivate>, m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "refused"
    case Done{sk}:
      B.Octets.hex(PR.PkRsa.pkcs1_sha256_sign(sk, m))

def rsa_sign(k: B.Octets, m: B.Octets) -> String:
  rsa.go(PR.PkRsa.secret(k), m)

def pss.go(r: Result<&2, &2, Cr.CrError, R.RsaPrivate>, m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "refused"
    case Done{sk}:
      B.Octets.hex(PR.PkRsa.pss_sha256_sign(sk, m))

def pss_sign(k: B.Octets, m: B.Octets) -> String:
  pss.go(PR.PkRsa.secret(k), m)

def ecdsa(pk: B.Octets, m: B.Octets, s: B.Octets) -> String:
  bs(Sg.CrSign.verify_bytes(~E.EcPoint, ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdsa.p256_sha256_verify, pk, m, s))

def ecdh(a: B.Octets, pb: B.Octets) -> String:
  ro(Kx.CrKex.agree(~N.BnNat, ~E.EcPoint, ~PE.PkEcdh.secret(~EC.EcCurves.p256()), ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdh.shared(~EC.EcCurves.p256()), a, pb))

def ffdhe(a: B.Octets, pb: B.Octets) -> String:
  ro(Kx.CrKex.agree(~N.BnNat, ~N.BnNat, ~PD.PkDh.secret(~DG.DhGroups.ffdhe2048()), ~PD.PkDh.pk_of(~DG.DhGroups.ffdhe2048()), ~PD.PkDh.shared(~DG.DhGroups.ffdhe2048()), a, pb))

def rsa_verify(pk: B.Octets, m: B.Octets, s: B.Octets) -> String:
  bs(Sg.CrSign.verify_bytes(~R.RsaPublic, ~PR.PkRsa.pk_of, ~PR.PkRsa.pkcs1_sha256_verify, pk, m, s))

def pss_verify(pk: B.Octets, m: B.Octets, s: B.Octets) -> String:
  bs(Sg.CrSign.verify_bytes(~R.RsaPublic, ~PR.PkRsa.pk_of, ~PR.PkRsa.pss_sha256_verify, pk, m, s))
'''

def openssl_p(name):
    pem = subprocess.run(['openssl', 'genpkey', '-genparam', '-algorithm', 'DH', '-pkeyopt', 'group:' + name],
                         capture_output=True, check=True).stdout
    return load_pem_parameters(pem).parameter_numbers().p


def mgf1(seed, n):
    out, c = b'', 0
    while len(out) < n:
        out += hashlib.sha256(seed + c.to_bytes(4, 'big')).digest()
        c += 1
    return out[:n]


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


# RFC 8017, 9.1.1: EMSA-PSS-ENCODE over SHA-256 with MGF1-SHA-256
def pss_encode(m, salt, embits):
    emlen = (embits + 7) // 8
    mh = hashlib.sha256(m).digest()
    hh = hashlib.sha256(b'\0' * 8 + mh + salt).digest()
    db = b'\0' * (emlen - len(salt) - len(mh) - 2) + b'\1' + salt
    masked = bytearray(xor(db, mgf1(hh, emlen - len(mh) - 1)))
    masked[0] &= 0xff >> (8 * emlen - embits)
    return bytes(masked) + hh + b'\xbc'


def o(b):
    return 'ob([%s])' % ', '.join(map(str, b))


def be(x, n):
    return x.to_bytes(n, 'big')


def field(x):
    b = x.to_bytes(max(1, (x.bit_length() + 7) // 8), 'big') if x else b''
    return len(b).to_bytes(4, 'big') + b


def main():
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, expr, want):
        lines.append('    IO.print("%s " ++ %s)' % (name, expr))
        expect.append('%s %s' % (name, want))

    def msg():
        return bytes(rnd.randrange(256) for _ in range(rnd.randrange(0, 80)))

    # ECDSA P-256 / SHA-256
    for i in range(12):
        k = ec.generate_private_key(ec.SECP256R1())
        pk = k.public_key().public_bytes(Encoding.X962, PublicFormat.UncompressedPoint)
        m = msg()
        r, s = decode_dss_signature(k.sign(m, ec.ECDSA(hashes.SHA256())))
        sig = be(r, 32) + be(s, 32)
        case('ecdsa%d' % i, 'ecdsa(%s, %s, %s)' % (o(pk), o(m), o(sig)), 'yes')
        case('ecdsa%d-changed' % i, 'ecdsa(%s, %s, %s)' % (o(pk), o(m + b'!'), o(sig)), 'no')
    # ECDH P-256
    for i in range(12):
        a = ec.generate_private_key(ec.SECP256R1())
        b = ec.generate_private_key(ec.SECP256R1())
        pb = b.public_key().public_bytes(Encoding.X962, PublicFormat.UncompressedPoint)
        z = a.exchange(ec.ECDH(), b.public_key())
        case('ecdh%d' % i, 'ecdh(%s, %s)' % (o(be(a.private_numbers().private_value, 32)), o(pb)), z.hex())
    # FFDHE-2048
    p = openssl_p('ffdhe2048')
    params = dh.DHParameterNumbers(p, 2).parameters()
    q = (p - 1) // 2
    for i in range(6):
        x = rnd.randrange(1, q)
        y = rnd.randrange(1, q)
        a = dh.DHPrivateNumbers(x, dh.DHPublicNumbers(pow(2, x, p), params.parameter_numbers())).private_key()
        b = dh.DHPrivateNumbers(y, dh.DHPublicNumbers(pow(2, y, p), params.parameter_numbers())).private_key()
        z = a.exchange(b.public_key())
        z = z.rjust(256, b'\0')
        assert z == be(pow(pow(2, y, p), x, p), 256)
        case('ffdhe%d' % i, 'ffdhe(%s, %s)' % (o(be(x, 256)), o(be(pow(2, y, p), 256))), z.hex())
    case('ffdhe-refused', 'ffdhe(%s, %s)' % (o(be(5, 256)), o(be(p - 1, 256))), 'refused')
    # RSA
    for i, bits in enumerate([1024, 1536, 2048, 1024]):
        k = rsa.generate_private_key(public_exponent=65537, key_size=bits)
        nums = k.private_numbers()
        n, e = nums.public_numbers.n, nums.public_numbers.e
        skb = field(n) + field(e) + field(nums.d) + field(nums.p) + field(nums.q)
        pkb = field(n) + field(e)
        m = msg()
        s1 = k.sign(m, padding.PKCS1v15(), hashes.SHA256())
        case('rsa%d-pkcs1-sign' % i, 'rsa_sign(%s, %s)' % (o(skb), o(m)), s1.hex())
        case('rsa%d-pkcs1-verify' % i, 'rsa_verify(%s, %s, %s)' % (o(pkb), o(m), o(s1)), 'yes')
        pss = padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32)
        s2 = k.sign(m, pss, hashes.SHA256())
        case('rsa%d-pss-verify' % i, 'pss_verify(%s, %s, %s)' % (o(pkb), o(m), o(s2)), 'yes')
        case('rsa%d-pss-changed' % i, 'pss_verify(%s, %s, %s)' % (o(pkb), o(m + b'?'), o(s2)), 'no')
        salt = mgf1(hashlib.sha256(skb + m).digest(), 32)
        em = pss_encode(m, salt, n.bit_length() - 1)
        s3 = be(pow(int.from_bytes(em, 'big'), nums.d, n), (n.bit_length() + 7) // 8)
        k.public_key().verify(s3, m, pss, hashes.SHA256())
        case('rsa%d-pss-own' % i, 'pss_sign(%s, %s)' % (o(skb), o(m)), s3.hex())
    return lines, expect


def write(lines, expect):
    for old in os.listdir(HERE):
        if old.startswith('cases') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        with open(os.path.join(HERE, 'cases%02d.bend' % (j // CHUNK)), 'w', newline='\n') as fh:
            fh.write(HEADER + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(lines[j:j + CHUNK]) + '\n')
    with open(os.path.join(HERE, 'expected.txt'), 'w', newline='\n') as fh:
        fh.write('\n'.join(expect) + '\n')


if __name__ == '__main__':
    lines, expect = main()
    write(lines, expect)
    print('%d cases against cryptography' % len(lines))
