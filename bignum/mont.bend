# Montgomery multiplication (named after P. L. Montgomery's 1985 paper,
# which was not read for this package: the method is written from its
# defining identity below, and checked by LAWS.bend and ref/run.sh), modulo
# an odd n > 1 of k limbs, with R = 2^(16 k):
#   mul(a, b) = a b R^-1 mod n,
# computed a limb of a at a time (t = (t + a_i b + m n) / 2^16, m chosen to
# make the division exact: m = t_0 n' mod 2^16, n' = -n^-1 mod 2^16).
#
# A residue in Montgomery form is x R mod n: to() takes a number there,
# of() brings it back, and add, sub, mul, sqr and exp work on the forms. A
# context (BnMont) holds n, n', k, R^2 mod n and R mod n (the form of 1),
# built once per modulus and used for every operation under it: RSA's,
# DH's, and the field and scalar arithmetic of the ecc package.
import Base
import ./bignum.bend as N

# A Montgomery context (opaque): n, n' = -n^-1 mod 2^16, k (n's limbs),
# R^2 mod n, R mod n
type BnMont is Data:
  BnMont{n: List<&2, U32>, np: U32, k: Nat, r2: List<&2, U32>, one: List<&2, U32>}

# t + a_i b, then t + m n with m making the low limb zero, then that limb
# dropped: k times, a limb of a each (a missing limb is 0)
def bn.mm.go(i: Nat, +a: List<&2, U32>, +b: List<&2, U32>, +n: List<&2, U32>, +np: U32, t: List<&2, U32>) -> List<&2, U32>:
  match i:
    case 0n:
      t
    case 1n+p:
      +t1 = N.bn.mac(b, N.bn.hd(a), t, 0)
      +m = U32.and(65535, (N.bn.hd(t1) * np : U32))
      bn.mm.go(p, N.bn.tl(a), b, n, np, N.bn.tl(N.bn.mac(n, m, t1, 0)))

def bn.csub.go(ge: Bool, t: List<&2, U32>, n: List<&2, U32>) -> List<&2, U32>:
  match ge:
    case True{}:
      N.bn.sub(t, n, 0)
    case False{}:
      t

# t - n if t >= n
def bn.csub(+t: List<&2, U32>, +n: List<&2, U32>) -> List<&2, U32>:
  bn.csub.go(N.bn.ge(N.bn.cmp(t, n, EQ{})), t, n)

def bn.trim(+k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, xs, k)

# a b R^-1 mod n, for a, b < n
def bn.mm(a: List<&2, U32>, +b: List<&2, U32>, +n: List<&2, U32>, +np: U32, +k: Nat) -> List<&2, U32>:
  bn.trim(k, bn.csub(bn.mm.go(k, a, b, n, np, N.bn.zeros(k)), n))

# R^2 mod n: 1 doubled 32 k times, reduced at each step
def bn.mont.r2(f: Nat, +x: List<&2, U32>, +n: List<&2, U32>, +k: Nat) -> List<&2, U32>:
  match f:
    case 0n:
      x
    case 1n+p:
      bn.mont.r2(p, bn.trim(k, bn.csub(N.bn.shl1(x, 0), n)), n, k)

# i (2 - x i) mod 2^16: Newton's step for x^-1, doubling the correct bits
def bn.inv16(+x: U32, +i: U32) -> U32:
  U32.and(65535, (i * (2 - x * i) : U32))

# -n0^-1 mod 2^16 for odd n0 (n0 is its own inverse mod 8: 3, 6, 12, 24 bits)
def bn.np(+n0: U32) -> U32:
  +i = bn.inv16(n0, bn.inv16(n0, bn.inv16(n0, bn.inv16(n0, n0))))
  U32.and(65535, (65536 - i : U32))

def bn.mont.mk(+n: List<&2, U32>) -> BnMont:
  +k = N.bn.len(n)
  +np = bn.np(N.bn.hd(n))
  +r2 = bn.mont.r2(Nat.mul(32n, k), Con{1, Nil{}}, n, k)
  BnMont{n, np, k, r2, bn.mm(r2, Con{1, Nil{}}, n, np, k)}

def bn.mont.ok(ok: Bool, +n: List<&2, U32>) -> Maybe<&2, BnMont>:
  match ok:
    case True{}:
      Some{bn.mont.mk(n)}
    case False{}:
      None{}

# The context of an odd modulus n > 1, or None
def BnMont.ctx(m: N.BnNat) -> Maybe<&2, BnMont>:
  match m:
    case N.BnNat{ls}:
      +n = N.bn.norm(ls)
      bn.mont.ok(Bool.and(U32.is_eq(U32.and(1, N.bn.hd(n)), 1), Cmp.is_gt(N.bn.cmp(n, Con{1, Nil{}}, EQ{}))), n)

# The context of n without the check: for an odd n > 1 (built from any
# other n, its results are meaningless). For moduli known to be odd primes,
# such as a curve's p and n
def BnMont.of_odd(m: N.BnNat) -> BnMont:
  match m:
    case N.BnNat{ls}:
      bn.mont.mk(N.bn.norm(ls))

# the modulus
def BnMont.modulus(c: BnMont) -> N.BnNat:
  match c:
    case BnMont{n, np, k, r2, one}:
      N.BnNat{n}

# n's size in limbs of 16 bits
def BnMont.limbs(c: BnMont) -> Nat:
  match c:
    case BnMont{n, np, k, r2, one}:
      k

def bn.mont.to(x: N.BnNat, r2: List<&2, U32>, +n: List<&2, U32>, +np: U32, +k: Nat) -> N.BnNat:
  match x:
    case N.BnNat{ls}:
      N.BnNat{bn.mm(ls, r2, n, np, k)}

# x R mod n, the Montgomery form of x (any x: it is reduced first)
def BnMont.to(c: BnMont, x: N.BnNat) -> N.BnNat:
  match c:
    case BnMont{+n, np, +k, r2, one}:
      bn.mont.to(N.BnNat.mod(x, N.BnNat{n}), r2, n, np, k)

# x R^-1 mod n: a Montgomery form brought back
def BnMont.of(c: BnMont, x: N.BnNat) -> N.BnNat:
  match c x:
    case BnMont{n, np, +k, r2, one} N.BnNat{ls}:
      N.BnNat{N.bn.norm(bn.mm(ls, Con{1, Nil{}}, n, np, k))}

# the form of 1 (R mod n)
def BnMont.one(c: BnMont) -> N.BnNat:
  match c:
    case BnMont{n, np, k, r2, one}:
      N.BnNat{one}

# a b R^-1 mod n: the form of the product, of the forms of a and b
def BnMont.mul(c: BnMont, a: N.BnNat, b: N.BnNat) -> N.BnNat:
  match c a b:
    case BnMont{n, np, +k, r2, one} N.BnNat{x} N.BnNat{y}:
      N.BnNat{bn.mm(x, y, n, np, k)}

def BnMont.sqr(c: BnMont, a: N.BnNat) -> N.BnNat:
  match c a:
    case BnMont{n, np, +k, r2, one} N.BnNat{+x}:
      N.BnNat{bn.mm(x, x, n, np, k)}

# a + b mod n, for a, b < n (in either form)
def BnMont.add(c: BnMont, a: N.BnNat, b: N.BnNat) -> N.BnNat:
  match c a b:
    case BnMont{+n, np, +k, r2, one} N.BnNat{x} N.BnNat{y}:
      N.BnNat{bn.trim(k, bn.csub(N.bn.add(x, y, 0), n))}

def bn.msub.go(ge: Bool, +x: List<&2, U32>, y: List<&2, U32>, n: List<&2, U32>, +k: Nat) -> List<&2, U32>:
  match ge:
    case True{}:
      bn.trim(k, N.bn.sub(x, y, 0))
    case False{}:
      bn.trim(k, N.bn.sub(N.bn.add(x, n, 0), y, 0))

# a - b mod n, for a, b < n (in either form)
def BnMont.sub(c: BnMont, a: N.BnNat, b: N.BnNat) -> N.BnNat:
  match c a b:
    case BnMont{n, np, k, r2, one} N.BnNat{+x} N.BnNat{+y}:
      N.BnNat{bn.msub.go(N.bn.ge(N.bn.cmp(x, y, EQ{})), x, y, n, k)}

# -a mod n
def BnMont.neg(+c: BnMont, a: N.BnNat) -> N.BnNat:
  BnMont.sub(c, N.BnNat.zero(), a)

def bn.mexp.pick(z: Bool, +sq: List<&2, U32>, +x: List<&2, U32>, +n: List<&2, U32>, +np: U32, +k: Nat) -> List<&2, U32>:
  match z:
    case True{}:
      sq
    case False{}:
      bn.mm(sq, x, n, np, k)

# the bits of one exponent limb w, from bit b - 1 down: square, and multiply
# by x where the bit is set
def bn.mexp.bits(+b: Nat, +w: U32, +acc: List<&2, U32>, +x: List<&2, U32>, +n: List<&2, U32>, +np: U32, +k: Nat) -> List<&2, U32>:
  match b:
    case 0n:
      acc
    case 1n+p:
      bn.mexp.bits(p, w, bn.mexp.pick(U32.is_zero(U32.and(1, U32.shrn(w, p))), bn.mm(acc, acc, n, np, k), x, n, np, k), x, n, np, k)

# the exponent's limbs, most significant first
def bn.mexp.go(es: List<&2, U32>, +acc: List<&2, U32>, +x: List<&2, U32>, +n: List<&2, U32>, +np: U32, +k: Nat) -> List<&2, U32>:
  match es:
    case Nil{}:
      acc
    case Con{e, t}:
      bn.mexp.go(t, bn.mexp.bits(16n, e, acc, x, n, np, k), x, n, np, k)

# x^e in Montgomery form, of x's form: left-to-right square and multiply
def BnMont.exp(c: BnMont, x: N.BnNat, e: N.BnNat) -> N.BnNat:
  match c x e:
    case BnMont{n, np, k, r2, one} N.BnNat{xs} N.BnNat{es}:
      N.BnNat{bn.mexp.go(List.reverse(&2, U32, N.bn.norm(es)), one, xs, n, np, k)}

# x^e mod n, from and to ordinary numbers
def BnMont.modexp(+c: BnMont, x: N.BnNat, e: N.BnNat) -> N.BnNat:
  BnMont.of(c, BnMont.exp(c, BnMont.to(c, x), e))
