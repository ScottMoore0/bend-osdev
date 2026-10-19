# Modular arithmetic on BnNat: sums, differences and products modulo m,
# powers (Montgomery's method for an odd modulus, square and multiply with
# division for any other), the greatest common divisor (Euclid) and the
# inverse modulo m (the extended Euclidean algorithm, with the coefficients
# kept modulo m; no book was read for it: the inverse is checked against
# its definition, a x = 1 mod m, by LAWS.bend and ref/run.sh).
#
# A modulus of 0 is refused where a result needs one: the defs answering a
# BnNat take m > 0 (and give 0 for m = 1); inv answers None when there is no
# inverse.
import Base
import ./bignum.bend as N
import ./mont.bend as Mt

# a + b mod m
def BnMod.add(a: N.BnNat, b: N.BnNat, m: N.BnNat) -> N.BnNat:
  N.BnNat.mod(N.BnNat.add(a, b), m)

# a - b mod m
def BnMod.sub(a: N.BnNat, b: N.BnNat, +m: N.BnNat) -> N.BnNat:
  N.BnNat.mod(N.BnNat.sub(N.BnNat.add(N.BnNat.mod(a, m), m), N.BnNat.mod(b, m)), m)

# a b mod m
def BnMod.mul(a: N.BnNat, b: N.BnNat, m: N.BnNat) -> N.BnNat:
  N.BnNat.mod(N.BnNat.mul(a, b), m)

def bn.pexp.pick(set: Bool, +acc: N.BnNat, x: N.BnNat, m: N.BnNat) -> N.BnNat:
  match set:
    case True{}:
      BnMod.mul(acc, x, m)
    case False{}:
      acc

# from bit i - 1 of e down to bit 0
def bn.pexp.go(+i: Nat, +x: N.BnNat, +e: N.BnNat, +m: N.BnNat, +acc: N.BnNat) -> N.BnNat:
  match i:
    case 0n:
      acc
    case 1n+p:
      bn.pexp.go(p, x, e, m, bn.pexp.pick(N.BnNat.bit(e, p), BnMod.mul(acc, acc, m), x, m))

# x^e mod m by square and multiply, each step reduced by division: the
# reference form, for every m > 0
def BnMod.exp_plain(x: N.BnNat, +e: N.BnNat, +m: N.BnNat) -> N.BnNat:
  bn.pexp.go(N.BnNat.bit_len(e), N.BnNat.mod(x, m), e, m, N.BnNat.mod(N.BnNat.one(), m))

def bn.exp.with(c: Maybe<&2, Mt.BnMont>, x: N.BnNat, +e: N.BnNat, +m: N.BnNat) -> N.BnNat:
  match c:
    case Some{ctx}:
      Mt.BnMont.modexp(ctx, x, e)
    case None{}:
      BnMod.exp_plain(x, e, m)

# x^e mod m, for m > 0: Montgomery's method when m is odd and above 1
def BnMod.exp(x: N.BnNat, +e: N.BnNat, +m: N.BnNat) -> N.BnNat:
  bn.exp.with(Mt.BnMont.ctx(m), x, e, m)

# the number of Euclid's steps never exceeds this (Lame: fewer than 1.45
# times the bits of the smaller, plus 2)
def bn.euclid.fuel(+a: N.BnNat, +b: N.BnNat) -> Nat:
  Nat.add(Nat.mul(2n, Nat.add(N.BnNat.bit_len(a), N.BnNat.bit_len(b))), 4n)

# Euclid: z says b is 0
def bn.gcd.go(f: Nat, z: Bool, +a: N.BnNat, +b: N.BnNat) -> N.BnNat:
  match f:
    case 0n:
      a
    case 1n+p:
      match z:
        case True{}:
          a
        case False{}:
          +r = N.BnNat.mod(a, b)
          bn.gcd.go(p, N.BnNat.is_zero(r), b, r)

# gcd(a, b); gcd(0, 0) is 0
def BnMod.gcd(+a: N.BnNat, +b: N.BnNat) -> N.BnNat:
  bn.gcd.go(bn.euclid.fuel(a, b), N.BnNat.is_zero(b), a, b)

# lcm(a, b) = a b / gcd(a, b); lcm with 0 is 0
def BnMod.lcm(+a: N.BnNat, +b: N.BnNat) -> N.BnNat:
  N.BnNat.mul(N.BnNat.div(a, BnMod.gcd(a, b)), b)

def bn.inv.end(one: Bool, t: N.BnNat) -> Maybe<&2, N.BnNat>:
  match one:
    case True{}:
      Some{t}
    case False{}:
      None{}

# The extended Euclidean algorithm on (r0, r1), with t0 and t1 the
# coefficients of a modulo m (r_i = t_i a mod m): z says r1 is 0, and then
# r0 is gcd(a, m), with t0 its coefficient
def bn.inv.go(f: Nat, z: Bool, +r0: N.BnNat, +r1: N.BnNat, +t0: N.BnNat, +t1: N.BnNat, +m: N.BnNat) -> Maybe<&2, N.BnNat>:
  match f:
    case 0n:
      None{}
    case 1n+p:
      match z:
        case True{}:
          bn.inv.end(N.BnNat.is_eq(r0, N.BnNat.one()), t0)
        case False{}:
          +d = Maybe.default(&2, N.BnDivMod, N.BnNat.divmod(r0, r1), N.BnDivMod{N.BnNat.zero(), r0})
          +r = N.BnDivMod.r(d)
          bn.inv.go(p, N.BnNat.is_zero(r), r1, r, t1, BnMod.sub(t0, BnMod.mul(N.BnDivMod.q(d), t1, m), m), m)

def bn.inv.run(+a: N.BnNat, +m: N.BnNat) -> Maybe<&2, N.BnNat>:
  +r1 = N.BnNat.mod(a, m)
  bn.inv.go(bn.euclid.fuel(m, m), N.BnNat.is_zero(r1), m, r1, N.BnNat.zero(), N.BnNat.mod(N.BnNat.one(), m), m)

def bn.inv.pick(big: Bool, +a: N.BnNat, +m: N.BnNat) -> Maybe<&2, N.BnNat>:
  match big:
    case True{}:
      bn.inv.run(a, m)
    case False{}:
      None{}

# a^-1 mod m: the x in [0, m) with a x mod m = 1, or None when gcd(a, m) is
# not 1 or m is 0 or 1
def BnMod.inv(+a: N.BnNat, +m: N.BnNat) -> Maybe<&2, N.BnNat>:
  bn.inv.pick(N.BnNat.is_lt(N.BnNat.one(), m), a, m)
