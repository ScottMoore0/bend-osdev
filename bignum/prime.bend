# Primality: trial division by the odd primes below 256, then the
# Miller-Rabin probabilistic test (FIPS 186-5, Digital Signature Standard,
# 2023, Appendix B.3.1) with the bases the caller gives; and the search
# for the first probable prime at or above a start, as RSA key generation
# and test parameters use.
#
# The bases are a parameter: random ones (FIPS 186-5 B.3.1 draws each
# uniformly from [2, n - 2], and its Appendix C.1 gives how many rounds a size
# needs), or fixed ones for a deterministic test of small numbers. A base
# outside [2, n - 2] is skipped.
import Base
import ./bignum.bend as N
import ./mont.bend as Mt

def bn.small_primes() -> List<&2, U32>:
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

# r = (r 2^16 + limb) mod d over the limbs, most significant first (d below
# 2^16, so every step fits in a U32)
def bn.rem1(xs: List<&2, U32>, +d: U32, +r: U32) -> U32:
  match xs:
    case Nil{}:
      r
    case Con{x, t}:
      bn.rem1(t, d, ((U32.shln(r, 16n) + x) % d : U32))

# x mod d, for 0 < d < 2^16
def BnNat.mod_u16(x: N.BnNat, +d: U32) -> U32:
  bn.rem1(List.reverse(&2, U32, N.BnNat.to_limbs(x)), d, 0)

# trial division: True when some prime p of the list with p < x divides x
def bn.trial(ps: List<&2, U32>, +x: N.BnNat) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{+p, t}:
      Bool.or(Bool.and(U32.is_zero(BnNat.mod_u16(x, p)), N.BnNat.is_lt(N.BnNat.of_u32(p), x)), bn.trial(t, x))

def bn.ctz16.pick(z: Bool, +i: Nat, rest: Nat) -> Nat:
  match z:
    case True{}:
      rest
    case False{}:
      Nat.sub(16n, i)

# the number of trailing zero bits (16 for each zero limb)
def bn.ctz16(+i: Nat, +x: U32) -> Nat:
  match i:
    case 0n:
      16n
    case 1n+p:
      bn.ctz16.pick(U32.is_zero(U32.and(1, U32.shrn(x, Nat.sub(16n, i)))), i, bn.ctz16(p, x))

def bn.ctz.pick(z: Bool, +x: U32, rest: Nat) -> Nat:
  match z:
    case True{}:
      Nat.add(16n, rest)
    case False{}:
      bn.ctz16(16n, x)

def bn.ctz(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, t}:
      bn.ctz.pick(U32.is_zero(x), x, bn.ctz(t))

# the number of trailing zero bits of x (0 for zero)
def BnNat.trailing_zeros(x: N.BnNat) -> Nat:
  bn.ctz(N.BnNat.to_limbs(x))

# s - 1 more squarings of y: a pass if one is n - 1 (m1, in form)
def bn.mr.sq(i: Nat, +c: Mt.BnMont, +y: N.BnNat, +m1: N.BnNat) -> Bool:
  match i:
    case 0n:
      False{}
    case 1n+p:
      +y2 = Mt.BnMont.sqr(c, y)
      Bool.or(N.BnNat.is_eq(y2, m1), bn.mr.sq(p, c, y2, m1))

# one round with base b (FIPS 186-5 B.3.1 steps 4.1 to 4.7)
def bn.mr.round(+c: Mt.BnMont, +n: N.BnNat, +d: N.BnNat, +s: Nat, b: N.BnNat) -> Bool:
  +b2 = N.BnNat.mod(b, n)
  +skip = Bool.or(N.BnNat.is_lt(b2, N.BnNat.of_u32(2)), N.BnNat.is_le(N.BnNat.sub(n, N.BnNat.one()), b2))
  +y = Mt.BnMont.exp(c, Mt.BnMont.to(c, b2), d)
  +m1 = Mt.BnMont.to(c, N.BnNat.sub(n, N.BnNat.one()))
  Bool.or(skip, Bool.or(Bool.or(N.BnNat.is_eq(y, Mt.BnMont.one(c)), N.BnNat.is_eq(y, m1)), bn.mr.sq(Nat.sub(s, 1n), c, y, m1)))

def bn.mr.all(bs: List<&2, N.BnNat>, +c: Mt.BnMont, +n: N.BnNat, +d: N.BnNat, +s: Nat) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, t}:
      Bool.and(bn.mr.round(c, n, d, s, b), bn.mr.all(t, c, n, d, s))

def bn.mr.with(m: Maybe<&2, Mt.BnMont>, bs: List<&2, N.BnNat>, +n: N.BnNat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      +n1 = N.BnNat.sub(n, N.BnNat.one())
      +s = BnNat.trailing_zeros(n1)
      bn.mr.all(bs, c, n, N.BnNat.shr(n1, s), s)

# Miller-Rabin with the given bases, for an odd n > 3: False means n is
# composite; True means n passed a round for every base
def BnPrime.miller_rabin(+n: N.BnNat, bs: List<&2, N.BnNat>) -> Bool:
  bn.mr.with(Mt.BnMont.ctx(n), bs, n)

def bn.prime.pick(small: Bool, two3: Bool, even: Bool, +n: N.BnNat, bs: List<&2, N.BnNat>) -> Bool:
  match small two3 even:
    case True{} _ _:
      False{}
    case False{} True{} _:
      True{}
    case False{} False{} True{}:
      False{}
    case False{} False{} False{}:
      Bool.and(Bool.not(bn.trial(bn.small_primes(), n)), BnPrime.miller_rabin(n, bs))

# whether n is a probable prime: 2 and 3 are; 0, 1 and even numbers are
# not; otherwise no small prime below n divides it and every base passes
def BnPrime.is_probable(+n: N.BnNat, bs: List<&2, N.BnNat>) -> Bool:
  bn.prime.pick(N.BnNat.is_lt(n, N.BnNat.of_u32(2)), N.BnNat.is_lt(n, N.BnNat.of_u32(4)), Bool.not(N.BnNat.is_odd(n)), n, bs)

def bn.next.end(hit: Bool, +x: N.BnNat) -> Maybe<&2, N.BnNat>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      None{}

def bn.next.go(f: Nat, hit: Bool, +x: N.BnNat, +bs: List<&2, N.BnNat>) -> Maybe<&2, N.BnNat>:
  match f:
    case 0n:
      bn.next.end(hit, x)
    case 1n+p:
      match hit:
        case True{}:
          Some{x}
        case False{}:
          +y = N.BnNat.add(x, N.BnNat.of_u32(2))
          bn.next.go(p, BnPrime.is_probable(y, bs), y, bs)

def bn.next.odd(odd: Bool, +x: N.BnNat) -> N.BnNat:
  match odd:
    case True{}:
      x
    case False{}:
      N.BnNat.add(x, N.BnNat.one())

# the first probable prime among the odd numbers from start (start + 1 if it
# is even), trying at most f + 1 of them, or None
def BnPrime.next(+start: N.BnNat, +bs: List<&2, N.BnNat>, f: Nat) -> Maybe<&2, N.BnNat>:
  +x = bn.next.odd(N.BnNat.is_odd(start), start)
  bn.next.go(f, BnPrime.is_probable(x, bs), x, bs)
