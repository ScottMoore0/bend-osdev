# bend-osdev-bignum's RSA laws, on Nat, for every input: Fermat's little
# theorem generalised (a^(1 + k (p - 1)) = a mod p for a prime p), the
# uniqueness half of the Chinese remainder theorem for two distinct primes
# (x = y mod p and mod q give x = y mod p q), RSA's correctness on the
# integers ((m^e)^d = (m^d)^e = m mod p q when d e = 1 modulo p - 1 and
# modulo q - 1, the check rsa's Rsa.private_of makes), the private
# exponentiation by the Chinese remainder theorem (RFC 8017 section 5.1.2,
# step 2.b: Garner's recombination of c^dP mod p and c^dQ mod q, with
# dP = d mod (p - 1), dQ = d mod (q - 1) and q qInv = 1 mod p, is c^d mod
# p q), and that a congruence modulo lcm(p - 1, q - 1) (FIPS 186-5's d)
# gives the congruences modulo p - 1 and q - 1; with the Nat facts on mod and
# pow the RSA laws of other packages are stated through, and the oddness of
# a number (BnNat.is_odd) as its value's. Primality is LAWS_fermat.bend's
# bnlaw.prime. Proved in PROOF_rsa.bend.
import Base
import ../kmath/kmath.bend as K
import ./bignum.bend as N
import ./LAWS_limbs.bend as LL
import ./LAWS_fermat.bend as LF

# Fermat's theorem generalised: for a prime p, a^(1 + k (p - 1)) = a mod p,
# for every a and k
law fermat_gen:
  for +p: Nat
  for +a: Nat
  for +k: Nat
  for hp: {LF.bnlaw.prime(p) == True{} : Bool}
  {Nat.mod(Nat.pow(a, Nat.add(1n, Nat.mul(k, Nat.sub(p, 1n)))), p) == Nat.mod(a, p) : Nat}

# the Chinese remainder theorem's uniqueness: for distinct primes p and q,
# x = y mod p and x = y mod q give x = y mod p q
law crt_unique:
  for +p: Nat
  for +q: Nat
  for +x: Nat
  for +y: Nat
  for hp: {LF.bnlaw.prime(p) == True{} : Bool}
  for hq: {LF.bnlaw.prime(q) == True{} : Bool}
  for hpq: {Nat.is_eq(p, q) == False{} : Bool}
  for ex: {Nat.mod(x, p) == Nat.mod(y, p) : Nat}
  for ey: {Nat.mod(x, q) == Nat.mod(y, q) : Nat}
  {Nat.mod(x, Nat.mul(p, q)) == Nat.mod(y, Nat.mul(p, q)) : Nat}

# RSA on the integers: for distinct primes p and q, n = p q, and d e = 1
# modulo p - 1 and modulo q - 1, (m^e)^d = m and (m^d)^e = m modulo n, for
# every m (and every e and d with the hypotheses)
law rsa_nat:
  for +p: Nat
  for +q: Nat
  for +e: Nat
  for +d: Nat
  for +m: Nat
  for hp: {LF.bnlaw.prime(p) == True{} : Bool}
  for hq: {LF.bnlaw.prime(q) == True{} : Bool}
  for hpq: {Nat.is_eq(p, q) == False{} : Bool}
  for hdp: {Nat.mod(Nat.mul(d, e), Nat.sub(p, 1n)) == Nat.mod(1n, Nat.sub(p, 1n)) : Nat}
  for hdq: {Nat.mod(Nat.mul(d, e), Nat.sub(q, 1n)) == Nat.mod(1n, Nat.sub(q, 1n)) : Nat}
  {Nat.mod(Nat.pow(Nat.pow(m, e), d), Nat.mul(p, q)) == Nat.mod(m, Nat.mul(p, q)) : Nat}

law rsa_nat_rev:
  for +p: Nat
  for +q: Nat
  for +e: Nat
  for +d: Nat
  for +m: Nat
  for hp: {LF.bnlaw.prime(p) == True{} : Bool}
  for hq: {LF.bnlaw.prime(q) == True{} : Bool}
  for hpq: {Nat.is_eq(p, q) == False{} : Bool}
  for hdp: {Nat.mod(Nat.mul(d, e), Nat.sub(p, 1n)) == Nat.mod(1n, Nat.sub(p, 1n)) : Nat}
  for hdq: {Nat.mod(Nat.mul(d, e), Nat.sub(q, 1n)) == Nat.mod(1n, Nat.sub(q, 1n)) : Nat}
  {Nat.mod(Nat.pow(Nat.pow(m, d), e), Nat.mul(p, q)) == Nat.mod(m, Nat.mul(p, q)) : Nat}

# The private exponentiation by the CRT (RFC 8017, 5.1.2 step 2.b), on the
# values: with m1 = c^dP mod p, m2 = c^dQ mod q (dP = d mod (p - 1), dQ = d
# mod (q - 1)), h = (m1 - m2) qInv mod p (the difference as BnMod.sub takes
# it: (m1 mod p + p - m2 mod p) mod p) and q qInv = 1 mod p, m2 + q h is
# c^d mod p q, for distinct primes p and q with p q odd and d e = 1 modulo
# p - 1 and modulo q - 1 (an even prime would give dP or dQ = 0)
law crt_exp_nat:
  for +p: Nat
  for +q: Nat
  for +e: Nat
  for +d: Nat
  for +t: Nat
  for +c: Nat
  for hp: {LF.bnlaw.prime(p) == True{} : Bool}
  for hq: {LF.bnlaw.prime(q) == True{} : Bool}
  for hpq: {Nat.is_eq(p, q) == False{} : Bool}
  for hodd: {Nat.mod(Nat.mul(p, q), 2n) == 1n : Nat}
  for hdp: {Nat.mod(Nat.mul(d, e), Nat.sub(p, 1n)) == Nat.mod(1n, Nat.sub(p, 1n)) : Nat}
  for hdq: {Nat.mod(Nat.mul(d, e), Nat.sub(q, 1n)) == Nat.mod(1n, Nat.sub(q, 1n)) : Nat}
  for ht: {Nat.mod(Nat.mul(q, t), p) == 1n : Nat}
  {Nat.add(Nat.mod(Nat.pow(c, Nat.mod(d, Nat.sub(q, 1n))), q), Nat.mul(q, Nat.mod(Nat.mul(Nat.mod(Nat.sub(Nat.add(Nat.mod(Nat.mod(Nat.pow(c, Nat.mod(d, Nat.sub(p, 1n))), p), p), p), Nat.mod(Nat.mod(Nat.pow(c, Nat.mod(d, Nat.sub(q, 1n))), q), p)), p), t), p))) == Nat.mod(Nat.pow(c, d), Nat.mul(p, q)) : Nat}

# A congruence modulo lcm(a, b) is one modulo a and modulo b (so a d with
# d e = 1 mod lcm(p - 1, q - 1), FIPS 186-5's, meets rsa_nat's hypotheses)
law mod_lcm_l:
  for +a: Nat
  for +b: Nat
  for +x: Nat
  for +y: Nat
  for h: {Nat.mod(x, K.KMath.lcm(a, b)) == Nat.mod(y, K.KMath.lcm(a, b)) : Nat}
  {Nat.mod(x, a) == Nat.mod(y, a) : Nat}

law mod_lcm_r:
  for +a: Nat
  for +b: Nat
  for +x: Nat
  for +y: Nat
  for h: {Nat.mod(x, K.KMath.lcm(a, b)) == Nat.mod(y, K.KMath.lcm(a, b)) : Nat}
  {Nat.mod(x, b) == Nat.mod(y, b) : Nat}

# Nat facts on mod and pow: powers of powers, a base reduced first, a
# number below the modulus, and a remainder below it

law nat_pow_pow:
  for +x: Nat
  for +a: Nat
  for +b: Nat
  {Nat.pow(Nat.pow(x, a), b) == Nat.pow(x, Nat.mul(a, b)) : Nat}

law nat_pow_mod:
  for +x: Nat
  for +e: Nat
  for +m: Nat
  for hm: {Nat.is_lt(0n, m) == True{} : Bool}
  {Nat.mod(Nat.pow(Nat.mod(x, m), e), m) == Nat.mod(Nat.pow(x, e), m) : Nat}

law nat_mod_small:
  for +a: Nat
  for +m: Nat
  for h: {Nat.is_lt(a, m) == True{} : Bool}
  {Nat.mod(a, m) == a : Nat}

law nat_mod_lt:
  for +a: Nat
  for +m: Nat
  for hm: {Nat.is_lt(0n, m) == True{} : Bool}
  {Nat.is_lt(Nat.mod(a, m), m) == True{} : Bool}

# BnNat.is_odd is whether the value is odd, for a valid number
law is_odd_value:
  for +x: N.BnNat
  for hx: {LL.bnlaw.valid(x) == True{} : Bool}
  {N.BnNat.is_odd(x) == Nat.is_eq(Nat.mod(LL.bnlaw.value(x), 2n), 1n) : Bool}
