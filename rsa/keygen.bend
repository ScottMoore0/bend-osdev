# RSA key generation from random bytes (FIPS 186-5, Appendix A.1.3,
# "Generation of Random Primes that are Probably Prime", in the shape of its
# steps): each prime is searched for upwards from a candidate made of the
# caller's random bytes, with its top two bits set (so that p q has nlen
# bits and p >= sqrt(2) 2^(nlen/2 - 1)) and made odd; a candidate is taken
# when it passes trial division and Miller-Rabin with the given bases and
# gcd(p - 1, e) = 1. |p - q| must exceed 2^(nlen/2 - 100).
#
# The randomness (the seeds and the Miller-Rabin bases) is the caller's:
# this package has no random source. FIPS 186-5 B.3.1 asks for random bases,
# as many as its Appendix C.1 gives for the size.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ../bignum/prime.bend as Pr
import ./rsa.bend as R

def rsa.kg.odd(odd: Bool, +x: N.BnNat) -> N.BnNat:
  match odd:
    case True{}:
      x
    case False{}:
      N.BnNat.add(x, N.BnNat.one())

# the candidate of b bits: the seed's low b bits, the top two set, odd
def rsa.kg.start(seed: B.Octets, +b: Nat) -> N.BnNat:
  +top = N.BnNat.add(N.BnNat.shl(N.BnNat.one(), Nat.sub(b, 1n)), N.BnNat.shl(N.BnNat.one(), Nat.sub(b, 2n)))
  +x = N.BnNat.mod(N.BnNat.of_octets(seed), N.BnNat.shl(N.BnNat.one(), Nat.sub(b, 2n)))
  +y = N.BnNat.add(top, x)
  rsa.kg.odd(N.BnNat.is_odd(y), y)

def rsa.kg.ok(+x: N.BnNat, +e: N.BnNat, bs: List<&2, N.BnNat>) -> Bool:
  Bool.and(N.BnNat.is_eq(Md.BnMod.gcd(N.BnNat.sub(x, N.BnNat.one()), e), N.BnNat.one()), Pr.BnPrime.is_probable(x, bs))

def rsa.kg.end(hit: Bool, +x: N.BnNat) -> Result<&2, &2, R.RsaError, N.BnNat>:
  match hit:
    case True{}:
      Done{x}
    case False{}:
      Fail{R.RsaNoPrime{}}

# up to f more candidates after x (hit: x is taken)
def rsa.kg.search(f: Nat, hit: Bool, +x: N.BnNat, +e: N.BnNat, +bs: List<&2, N.BnNat>) -> Result<&2, &2, R.RsaError, N.BnNat>:
  match f:
    case 0n:
      rsa.kg.end(hit, x)
    case 1n+p:
      match hit:
        case True{}:
          Done{x}
        case False{}:
          +y = N.BnNat.add(x, N.BnNat.of_u32(2))
          rsa.kg.search(p, rsa.kg.ok(y, e, bs), y, e, bs)

# A prime of b bits for the exponent e, searched from the seed's candidate
# through at most f + 1 odd numbers (RsaNoPrime when none passes)
def RsaKeygen.prime(seed: B.Octets, +b: Nat, +e: N.BnNat, +bs: List<&2, N.BnNat>, f: Nat) -> Result<&2, &2, R.RsaError, N.BnNat>:
  +x = rsa.kg.start(seed, b)
  rsa.kg.search(f, rsa.kg.ok(x, e, bs), x, e, bs)

def rsa.kg.apart(+p: N.BnNat, +q: N.BnNat, +nlen: Nat) -> Bool:
  +d = N.BnNat.add(N.BnNat.sub(p, q), N.BnNat.sub(q, p))
  N.BnNat.is_lt(N.BnNat.shl(N.BnNat.one(), Nat.sub(Nat.div(nlen, 2n), 100n)), d)

# A key of nlen bits (even, at least 16) for the odd exponent e, from two
# seeds of random bytes and the Miller-Rabin bases, each prime searched
# through at most f + 1 candidates
def RsaKeygen.generate(+e: N.BnNat, +nlen: Nat, sp: B.Octets, sq: B.Octets, +bs: List<&2, N.BnNat>, +f: Nat) -> Result<&2, &2, R.RsaError, R.RsaPrivate>:
  +b = Nat.div(nlen, 2n)
  Result.bind(&2, &2, R.RsaError, N.BnNat, R.RsaPrivate, RsaKeygen.prime(sp, b, e, bs, f), +p => Result.bind(&2, &2, R.RsaError, N.BnNat, R.RsaPrivate, RsaKeygen.prime(sq, b, e, bs, f), +q => Result.bind(&2, &2, R.RsaError, Unit, R.RsaPrivate, R.RsaError.check(rsa.kg.apart(p, q, nlen), R.RsaBadKey{}), u => R.Rsa.private_of_primes(p, q, e))))
