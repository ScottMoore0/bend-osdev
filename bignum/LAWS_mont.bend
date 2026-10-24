# bend-osdev-bignum's Montgomery and exponentiation laws, for every input:
# Montgomery multiplication modulo an odd m > 1 is a b R^-1 mod m, with
# R = 2^(16 k) for m's k limbs, stated without an inverse as
# (mul(a, b) R) mod m = (a b) mod m; the conversions into and out of
# Montgomery form; Montgomery exponentiation and BnMod.exp are x^e mod m;
# and so the two Diffie-Hellman exponentiations commute. Proved in
# PROOF_mont.bend.
import Base
import ../u32/u32.bend as U
import ./bignum.bend as N
import ./modular.bend as Md
import ./mont.bend as Mt
import ./LAWS_limbs.bend as LL

# The context: for a valid odd m above 1, BnMont.ctx(m) is the context of
# BnMont.of_odd(m) (the limbs' -m^-1 mod 2^16, by bn.np's Newton steps, R^2
# mod m and R mod m)
law ctx_of_odd:
  for +m: N.BnNat
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  {Mt.BnMont.ctx(m) == Some{Mt.BnMont.of_odd(m)} : Maybe<&2, Mt.BnMont>}

# Montgomery multiplication (REDC), for valid a, b below m: the product
# times R is a b modulo m, and it is below m; it is valid for every input
law mont_mul_value:
  for +m: N.BnNat
  for +a: N.BnNat
  for +b: N.BnNat
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +hal: {Nat.is_lt(LL.bnlaw.value(a), LL.bnlaw.value(m)) == True{} : Bool}
  for +hbl: {Nat.is_lt(LL.bnlaw.value(b), LL.bnlaw.value(m)) == True{} : Bool}
  {Nat.mod(U.U32Nat.dbl(Nat.mul(Mt.BnMont.limbs(Mt.BnMont.of_odd(m)), 16n), LL.bnlaw.value(Mt.BnMont.mul(Mt.BnMont.of_odd(m), a, b))), LL.bnlaw.value(m)) == Nat.mod(Nat.mul(LL.bnlaw.value(a), LL.bnlaw.value(b)), LL.bnlaw.value(m)) : Nat}

law mont_mul_lt:
  for +m: N.BnNat
  for +a: N.BnNat
  for +b: N.BnNat
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +hal: {Nat.is_lt(LL.bnlaw.value(a), LL.bnlaw.value(m)) == True{} : Bool}
  for +hbl: {Nat.is_lt(LL.bnlaw.value(b), LL.bnlaw.value(m)) == True{} : Bool}
  {Nat.is_lt(LL.bnlaw.value(Mt.BnMont.mul(Mt.BnMont.of_odd(m), a, b)), LL.bnlaw.value(m)) == True{} : Bool}

law mont_mul_valid:
  for +m: N.BnNat
  for +a: N.BnNat
  for +b: N.BnNat
  {LL.bnlaw.valid(Mt.BnMont.mul(Mt.BnMont.of_odd(m), a, b)) == True{} : Bool}

# Into Montgomery form (by R^2 mod m): x R mod m, for every valid x; the
# form of 1 is R mod m; and out of it: the result times R is y modulo m,
# for a valid y below m, so out of the form of x is x mod m
law mont_to_value:
  for +m: N.BnNat
  for +x: N.BnNat
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  {LL.bnlaw.value(Mt.BnMont.to(Mt.BnMont.of_odd(m), x)) == Nat.mod(U.U32Nat.dbl(Nat.mul(Mt.BnMont.limbs(Mt.BnMont.of_odd(m)), 16n), LL.bnlaw.value(x)), LL.bnlaw.value(m)) : Nat}

law mont_one_value:
  for +m: N.BnNat
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  {LL.bnlaw.value(Mt.BnMont.one(Mt.BnMont.of_odd(m))) == Nat.mod(U.U32Nat.dbl(Nat.mul(Mt.BnMont.limbs(Mt.BnMont.of_odd(m)), 16n), 1n), LL.bnlaw.value(m)) : Nat}

law mont_of_value:
  for +m: N.BnNat
  for +y: N.BnNat
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  for +hy: {LL.bnlaw.valid(y) == True{} : Bool}
  for +hyl: {Nat.is_lt(LL.bnlaw.value(y), LL.bnlaw.value(m)) == True{} : Bool}
  {Nat.mod(U.U32Nat.dbl(Nat.mul(Mt.BnMont.limbs(Mt.BnMont.of_odd(m)), 16n), LL.bnlaw.value(Mt.BnMont.of(Mt.BnMont.of_odd(m), y))), LL.bnlaw.value(m)) == Nat.mod(LL.bnlaw.value(y), LL.bnlaw.value(m)) : Nat}

law mont_of_to:
  for +m: N.BnNat
  for +x: N.BnNat
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  {LL.bnlaw.value(Mt.BnMont.of(Mt.BnMont.of_odd(m), Mt.BnMont.to(Mt.BnMont.of_odd(m), x))) == Nat.mod(LL.bnlaw.value(x), LL.bnlaw.value(m)) : Nat}

# Montgomery exponentiation (left to right over e's limbs and bits):
# x^e mod m, for valid x and e
law modexp_value:
  for +m: N.BnNat
  for +x: N.BnNat
  for +e: N.BnNat
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  {LL.bnlaw.value(Mt.BnMont.modexp(Mt.BnMont.of_odd(m), x, e)) == Nat.mod(Nat.pow(LL.bnlaw.value(x), LL.bnlaw.value(e)), LL.bnlaw.value(m)) : Nat}

# BnMod.exp (Montgomery for odd m > 1, exp_plain otherwise) is x^e mod m
# for valid x, e and m with m above 0, so it equals the reference; its
# result is valid for every input
law exp_value:
  for +x: N.BnNat
  for +e: N.BnNat
  for +m: N.BnNat
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hm0: {Nat.is_lt(0n, LL.bnlaw.value(m)) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.exp(x, e, m)) == Nat.mod(Nat.pow(LL.bnlaw.value(x), LL.bnlaw.value(e)), LL.bnlaw.value(m)) : Nat}

law exp_eq_plain:
  for +x: N.BnNat
  for +e: N.BnNat
  for +m: N.BnNat
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hm0: {Nat.is_lt(0n, LL.bnlaw.value(m)) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.exp(x, e, m)) == LL.bnlaw.value(Md.BnMod.exp_plain(x, e, m)) : Nat}

law exp_valid:
  for +x: N.BnNat
  for +e: N.BnNat
  for +m: N.BnNat
  {LL.bnlaw.valid(Md.BnMod.exp(x, e, m)) == True{} : Bool}

# Powers of powers: (x^a mod m)^b mod m = x^(a b) mod m, for m above 0; and
# for an odd m above 1 the two orders give the same number (the Montgomery
# result has no zero limbs on top), which is Diffie-Hellman's agreement
law exp_exp_value:
  for +x: N.BnNat
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hm0: {Nat.is_lt(0n, LL.bnlaw.value(m)) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.exp(Md.BnMod.exp(x, a, m), b, m)) == Nat.mod(Nat.pow(LL.bnlaw.value(x), Nat.mul(LL.bnlaw.value(a), LL.bnlaw.value(b))), LL.bnlaw.value(m)) : Nat}

law exp_exp_comm:
  for +x: N.BnNat
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hmo: {N.BnNat.is_odd(m) == True{} : Bool}
  for +hm1: {Nat.is_lt(1n, LL.bnlaw.value(m)) == True{} : Bool}
  {Md.BnMod.exp(Md.BnMod.exp(x, a, m), b, m) == Md.BnMod.exp(Md.BnMod.exp(x, b, m), a, m) : N.BnNat}
