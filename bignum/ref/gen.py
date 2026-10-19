#!/usr/bin/env python3
"""Differential test of bignum against Python's integers (and, for
primality, primes made by the cryptography package's RSA key generation).

  python3 gen.py [seed]   writes cases00.bend, cases01.bend, ... and expected.txt

Each case prints one line, "<name> <i> <result>"; the expected line is
Python's. Values travel as hex text (BnNat.of_hex, BnNat.hex)."""
import math, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
CHUNK = 80

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../bignum.bend as N
import ../modular.bend as Md
import ../mont.bend as Mt
import ../prime.bend as Pr
import ../jacobi.bend as J

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

def x(n: N.BnNat) -> String:
  N.BnNat.hex(n)

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def cs(c: Cmp) -> String:
  match c:
    case LT{}:
      "lt"
    case EQ{}:
      "eq"
    case GT{}:
      "gt"

def dm(m: Maybe<&2, N.BnDivMod>) -> String:
  match m:
    case None{}:
      "none"
    case Some{N.BnDivMod{q, r}}:
      x(q) ++ " " ++ x(r)

def mo(m: Maybe<&2, B.Octets>) -> String:
  match m:
    case None{}:
      "none"
    case Some{o}:
      B.Octets.hex(o) ++ "."

def mn(m: Maybe<&2, N.BnNat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      x(v)

def js(m: Maybe<&2, J.BnJacobi>) -> String:
  match m:
    case None{}:
      "none"
    case Some{J.BnJacZero{}}:
      "0"
    case Some{J.BnJacPlus{}}:
      "1"
    case Some{J.BnJacMinus{}}:
      "-1"

def ob(xs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(xs)

def mexp(c: Maybe<&2, Mt.BnMont>, a: N.BnNat, b: N.BnNat) -> String:
  match c:
    case None{}:
      "none"
    case Some{k}:
      x(Mt.BnMont.modexp(k, a, b))
'''


def hx(v):
    return '%x' % v


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, i, expr, want):
        lines.append('    IO.print("%s %d " ++ %s)' % (name, i, expr))
        expect.append('%s %d %s' % (name, i, want))

    def H(v):
        return 'h("%s")' % hx(v)

    def rnd(bits):
        return rng.getrandbits(bits) if bits else 0

    sizes = [0, 1, 8, 15, 16, 17, 31, 32, 33, 64, 100, 128, 255, 256, 257, 521, 1024, 2048]
    for i in range(24):
        a, b = rnd(rng.choice(sizes)), rnd(rng.choice(sizes))
        case('add', i, 'x(N.BnNat.add(%s, %s))' % (H(a), H(b)), hx(a + b))
        case('sub', i, 'x(N.BnNat.sub(%s, %s))' % (H(max(a, b)), H(min(a, b))), hx(max(a, b) - min(a, b)))
        case('mul', i, 'x(N.BnNat.mul(%s, %s))' % (H(a), H(b)), hx(a * b))
        c = (a > b) - (a < b)
        case('cmp', i, 'cs(N.BnNat.cmp(%s, %s))' % (H(a), H(b)), ['lt', 'eq', 'gt'][c + 1])
    case('sub', 99, 'x(N.BnNat.sub(h("5"), h("7")))', '0')
    case('cmp', 99, 'cs(N.BnNat.cmp(N.BnNat.of_limbs([5, 0, 0]), h("5")))', 'eq')
    for i in range(24):
        a = rnd(rng.choice(sizes[3:]))
        b = rnd(rng.choice(sizes[1:]))
        if i % 5 == 0:
            b = rnd(rng.randrange(1, 40)) + 1
        if b == 0:
            b = 3
        case('divmod', i, 'dm(N.BnNat.divmod(%s, %s))' % (H(a), H(b)), '%s %s' % (hx(a // b), hx(a % b)))
    case('divmod', 99, 'dm(N.BnNat.divmod(h("5"), h("0")))', 'none')
    for i in range(16):
        a, n = rnd(rng.choice(sizes)), rng.randrange(0, 70)
        case('shl', i, 'x(N.BnNat.shl(%s, %dn))' % (H(a), n), hx(a << n))
        case('shr', i, 'x(N.BnNat.shr(%s, %dn))' % (H(a), n), hx(a >> n))
        case('bitlen', i, 'Nat.show(N.BnNat.bit_len(%s))' % H(a), str(a.bit_length()))
        k = rng.randrange(0, max(1, a.bit_length() + 3))
        case('bit', i, 'bs(N.BnNat.bit(%s, %dn))' % (H(a), k), 'yes' if (a >> k) & 1 else 'no')
    for i in range(16):  # OS2IP and I2OSP
        n = rng.randrange(0, 70)
        o = bytes(rng.randrange(256) for _ in range(n))
        lst = '[%s]' % ', '.join(map(str, o))
        v = int.from_bytes(o, 'big')
        case('os2ip', i, 'x(N.BnNat.of_octets(ob(%s)))' % lst, hx(v))
        L = rng.randrange(0, n + 3)
        want = (v.to_bytes(L, 'big').hex() + '.') if v < 256 ** L else 'none'
        case('i2osp', i, 'mo(N.BnNat.to_octets(%s, %dn))' % (H(v), L), want)
    for i in range(20):  # modular exponentiation, odd and even moduli
        bits = rng.choice([2, 16, 17, 64, 255, 256, 512, 1024])
        m = rnd(bits) | (1 << (bits - 1))
        if i % 3 == 0:
            m &= ~1
        m = max(m, 2)
        xv, e = rnd(bits + 8), rnd(rng.choice([0, 1, 5, 17, bits]))
        case('modexp', i, 'x(Md.BnMod.exp(%s, %s, %s))' % (H(xv), H(e), H(m)), hx(pow(xv, e, m)))
        case('modexp_plain', i, 'x(Md.BnMod.exp_plain(%s, %s, %s))' % (H(xv), H(e), H(m)), hx(pow(xv, e, m)))
        mm = m | 1
        case('mont', i, 'mexp(Mt.BnMont.ctx(%s), %s, %s)' % (H(mm), H(xv), H(e)), hx(pow(xv, e, mm)) if mm > 1 else 'none')
    case('mont', 99, 'mexp(Mt.BnMont.ctx(h("1")), h("5"), h("3"))', 'none')
    case('mont', 98, 'mexp(Mt.BnMont.ctx(h("10")), h("5"), h("3"))', 'none')
    for i in range(20):  # inverse and gcd
        bits = rng.choice([8, 64, 256, 1024])
        m = rnd(bits) + 2
        a = rnd(bits + 4)
        try:
            want = hx(pow(a, -1, m))
        except ValueError:
            want = 'none'
        case('inv', i, 'mn(Md.BnMod.inv(%s, %s))' % (H(a), H(m)), want)
        g = rng.choice([1, 2, 6, rnd(40) + 1])
        a2, b2 = a * g, m * g
        case('gcd', i, 'x(Md.BnMod.gcd(%s, %s))' % (H(a2), H(b2)), hx(math.gcd(a2, b2)))
    case('inv', 99, 'mn(Md.BnMod.inv(h("3"), h("1")))', 'none')
    case('inv', 98, 'mn(Md.BnMod.inv(h("4"), h("6")))', 'none')

    # primes: from cryptography's RSA key generation (an outside source)
    from cryptography.hazmat.primitives.asymmetric import rsa
    primes = []
    for bits in [512, 1024]:
        k = rsa.generate_private_key(65537, bits).private_numbers()
        primes += [k.p, k.q]
    primes += [2 ** 127 - 1, 2 ** 89 - 1, 65537, 251, 257]
    carmichael = [561, 1105, 1729, 2465, 2821, 6601, 8911, 41041, 825265]
    bases = ', '.join('h("%x")' % b for b in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41])
    for i, p in enumerate(primes):
        case('prime', i, 'bs(Pr.BnPrime.is_probable(%s, [%s]))' % (H(p), bases), 'yes')
    for i, c in enumerate(carmichael + [primes[0] * primes[1], primes[4] * primes[5], 2 ** 128 + 1, 3 * 5 * 7, 1, 0, 4, 2, 3]):
        want = 'yes' if c in (2, 3) else 'no'
        case('composite', i, 'bs(Pr.BnPrime.is_probable(%s, [%s]))' % (H(c), bases), want)

    def isprime(v):
        return v > 1 and all(v % q for q in range(2, int(v ** 0.5) + 1))
    for i in range(6):
        s = rng.randrange(2, 10 ** 9)
        want = s if s % 2 else s + 1
        while not isprime(want):
            want += 2
        case('next', i, 'mn(Pr.BnPrime.next(%s, [%s], 1000n))' % (H(s), bases), hx(want))
    for i in range(10):
        xv, d = rnd(rng.choice([16, 100, 1000])), rng.randrange(1, 65536)
        case('mod_u16', i, 'U32.show(Pr.BnNat.mod_u16(%s, %d))' % (H(xv), d), str(xv % d))

    def jacobi(a, n):
        a %= n
        t = 1
        while a:
            while a % 2 == 0:
                a //= 2
                if n % 8 in (3, 5):
                    t = -t
            a, n = n, a
            if a % 4 == 3 and n % 4 == 3:
                t = -t
            a %= n
        return t if n == 1 else 0
    for i in range(20):  # Jacobi: against Euler's criterion for primes, and the textbook algorithm
        if i < 10:
            p = primes[i % len(primes)]
            a = rnd(p.bit_length() + 3)
            if i == 9:
                a = p * 3
            e = pow(a, (p - 1) // 2, p)
            want = '0' if e == 0 else ('1' if e == 1 else '-1')
            assert int(want) == jacobi(a, p)
        else:
            p = rnd(rng.choice([8, 64, 300])) | 1
            a = rnd(300)
            want = str(jacobi(a, p))
        case('jacobi', i, 'js(J.BnNat.jacobi(%s, %s))' % (H(a), H(p)), want)
    case('jacobi', 99, 'js(J.BnNat.jacobi(h("3"), h("8")))', 'none')
    for i in range(10):
        v = rnd(rng.choice(sizes))
        case('hex', i, 'x(h("%s"))' % ('0' * rng.randrange(3) + hx(v).upper()), hx(v))
    case('hex', 99, 'mn(N.BnNat.of_hex("12g4"))', 'none')

    for old in os.listdir(HERE):
        if old.startswith('cases') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    for j in range(0, len(lines), CHUNK):
        with open(os.path.join(HERE, 'cases%02d.bend' % (j // CHUNK)), 'w', newline='\n') as f:
            f.write(HEADER + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(lines[j:j + CHUNK]) + '\n')
    with open(os.path.join(HERE, 'expected.txt'), 'w', newline='\n') as f:
        f.write('\n'.join(expect) + '\n')
    print('%d cases against Python integers, primes from cryptography' % len(lines))


if __name__ == '__main__':
    main()
