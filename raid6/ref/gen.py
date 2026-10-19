#!/usr/bin/env python3
"""Differential test cases for bend-osdev-raid6.

Writes ref/cases.bend (a Bend program printing raid6's results) and
ref/expected.txt (the same from an independent model written here from H.
Peter Anvin, "The mathematics of RAID-6": GF(2^8) multiplication as
carry-less multiplication reduced by 0x11D, P as XOR, Q as the sum of
g^i D_i computed term by term, not by Horner's rule, and recovery by the
paper's equations 5 and 16 to 20, checked against the original blocks
before they are used as expectations).

For random stripes of 1 to 12 data blocks of equal length: P and Q, and
the stripe recovered after each kind of loss (one data block, P, Q, both,
data and P, data and Q, two data blocks), with the lost blocks overwritten
with junk first.
"""
import os, random, sys


def gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        if a & 0x100:
            a ^= 0x11D
        b >>= 1
    return r


def gpow(a, n):
    r = 1
    for _ in range(n):
        r = gmul(r, a)
    return r


def ginv(a):
    return gpow(a, 254)


def syndromes(ds):
    n = len(ds[0]) if ds else 0
    p, q = bytearray(n), bytearray(n)
    for i, d in enumerate(ds):
        g = gpow(2, i)
        for j, b in enumerate(d):
            p[j] ^= b
            q[j] ^= gmul(g, b)
    return bytes(p), bytes(q)


def recover_dd(ds, p, q, x, y):
    # the paper's equations 16 to 20, with the missing blocks set to zero
    zs = [d if i not in (x, y) else bytes(len(p)) for i, d in enumerate(ds)]
    pxy, qxy = syndromes(zs)
    gyx = gmul(gpow(2, y), ginv(gpow(2, x)))
    den = ginv(gyx ^ 1)
    a, b = gmul(gyx, den), gmul(ginv(gpow(2, x)), den)
    dx = bytes(gmul(a, p[j] ^ pxy[j]) ^ gmul(b, q[j] ^ qxy[j]) for j in range(len(p)))
    dy = bytes(p[j] ^ pxy[j] ^ dx[j] for j in range(len(p)))
    return dx, dy


def recover_dq(ds, q, x):
    # equation 5
    zs = [d if i != x else bytes(len(q)) for i, d in enumerate(ds)]
    _, qx = syndromes(zs)
    ix = ginv(gpow(2, x))
    return bytes(gmul(ix, q[j] ^ qx[j]) for j in range(len(q)))


def lit(b):
    return "B.Octets.of_list([%s])" % ", ".join(str(x) for x in b)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, lines, expect = [], [], []
    k = [0]

    def case(name, expr, want):
        k[0] += 1
        defs.append("def c%d() -> String:\n  %s\n" % (k[0], expr))
        lines.append('    IO.print("%s " ++ c%d())' % (name, k[0]))
        expect.append("%s %s" % (name, want))

    for s in range(24):
        n = rng.randrange(1, 13)
        w = rng.choice([1, 3, 8, rng.randrange(1, 40)])
        ds = [rng.randbytes(w) for _ in range(n)]
        p, q = syndromes(ds)
        dsl = "[%s]" % ", ".join(lit(d) for d in ds)
        whole = "".join(d.hex() for d in ds) + "/" + p.hex() + "/" + q.hex()
        case("pq_%d" % s, "show(R.Raid6.encode(R.Raid6.spec(), %s))" % dsl, whole)
        x = rng.randrange(n)
        losses = [("data", "V.Raid6LostData{%dn}" % x), ("p", "V.Raid6LostP{}"), ("q", "V.Raid6LostQ{}"),
                  ("pq", "V.Raid6LostPQ{}"), ("dp", "V.Raid6LostDataP{%dn}" % x), ("dq", "V.Raid6LostDataQ{%dn}" % x)]
        assert recover_dq(ds, q, x) == ds[x], "equation 5 disagrees"
        if n >= 2:
            x, y = rng.sample(range(n), 2)
            assert recover_dd(ds, p, q, x, y) == (ds[x], ds[y]), "equations 16-20 disagree"
            losses.append(("dd", "V.Raid6LostDataData{%dn, %dn}" % (x, y)))
        for lname, lost in losses:
            case("rec_%s_%d" % (lname, s), "rec(R.Raid6.encode(R.Raid6.spec(), %s), %s)" % (dsl, lost), whole)

    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../../bytes/bytes.bend as B\nimport ../raid6.bend as R\nimport ../recover.bend as V\n\n")
        f.write("def cat(ds: List<&2, B.Octets>) -> String:\n  match ds:\n    case Nil{}:\n      \"\"\n    case Con{d, r}:\n      B.Octets.hex(d) ++ cat(r)\n\n")
        f.write("def show(st: R.Raid6Stripe) -> String:\n  match st:\n    case R.Raid6Stripe{ds, p, q}:\n      cat(ds) ++ \"/\" ++ B.Octets.hex(p) ++ \"/\" ++ B.Octets.hex(q)\n\n")
        # the lost blocks overwritten with junk (all-ones blocks of other lengths)
        f.write("""def ones(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{255, ones(k)}

def bad(n: Nat) -> B.Octets:
  B.Octets.of_list(ones(n))

def damage(st: R.Raid6Stripe, lost: V.Raid6Lost) -> R.Raid6Stripe:
  match st:
    case R.Raid6Stripe{ds, p, q}:
      match lost:
        case V.Raid6LostNone{}:
          R.Raid6Stripe{ds, p, q}
        case V.Raid6LostData{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, bad(5n)), p, q}
        case V.Raid6LostP{}:
          R.Raid6Stripe{ds, bad(2n), q}
        case V.Raid6LostQ{}:
          R.Raid6Stripe{ds, p, bad(7n)}
        case V.Raid6LostDataData{x, y}:
          R.Raid6Stripe{R.Raid6.set_block(R.Raid6.set_block(ds, x, bad(3n)), y, bad(9n)), p, q}
        case V.Raid6LostDataP{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, bad(4n)), bad(1n), q}
        case V.Raid6LostDataQ{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, bad(6n)), p, bad(8n)}
        case V.Raid6LostPQ{}:
          R.Raid6Stripe{ds, bad(1n), bad(1n)}

def res(r: Result<&2, &2, V.Raid6Error, R.Raid6Stripe>) -> String:
  match r:
    case Done{s}:
      show(s)
    case Fail{e}:
      "fail"

def rec(st: R.Raid6Stripe, +lost: V.Raid6Lost) -> String:
  res(V.Raid6.recover(R.Raid6.spec(), damage(st, lost), lost))

""")
        f.write("\n".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
