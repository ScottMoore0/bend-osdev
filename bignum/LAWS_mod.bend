# bend-osdev-bignum's modular laws, for every input: BnMod.add, sub and
# mul are the sum, difference and product of the numbers' values modulo m,
# and BnMod.exp_plain (square and multiply over the exponent's bits from the
# top, each step reduced by division) is x^e mod m. Proved in PROOF_mod.bend.
import Base
import ./bignum.bend as N
import ./modular.bend as Md
import ./LAWS_limbs.bend as LL

# a + b mod m, a b mod m, and a - b mod m as the code defines it,
# ((a mod m) + m - (b mod m)) mod m, which for m > 0 is the x below m with
# x + b = a mod m (mod_sub_add); for valid a, b and m (by 0 too, where Base's
# Nat.mod gives its first argument back)

law mod_add_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.add(a, b, m)) == Nat.mod(Nat.add(LL.bnlaw.value(a), LL.bnlaw.value(b)), LL.bnlaw.value(m)) : Nat}

law mod_add_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  {LL.bnlaw.valid(Md.BnMod.add(a, b, m)) == True{} : Bool}

law mod_sub_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.sub(a, b, m)) == Nat.mod(Nat.sub(Nat.add(Nat.mod(LL.bnlaw.value(a), LL.bnlaw.value(m)), LL.bnlaw.value(m)), Nat.mod(LL.bnlaw.value(b), LL.bnlaw.value(m))), LL.bnlaw.value(m)) : Nat}

law mod_sub_add:
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hm0: {Nat.is_lt(0n, LL.bnlaw.value(m)) == True{} : Bool}
  {Nat.mod(Nat.add(LL.bnlaw.value(Md.BnMod.sub(a, b, m)), LL.bnlaw.value(b)), LL.bnlaw.value(m)) == Nat.mod(LL.bnlaw.value(a), LL.bnlaw.value(m)) : Nat}

law mod_sub_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  {LL.bnlaw.valid(Md.BnMod.sub(a, b, m)) == True{} : Bool}

law mod_mul_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.mul(a, b, m)) == Nat.mod(Nat.mul(LL.bnlaw.value(a), LL.bnlaw.value(b)), LL.bnlaw.value(m)) : Nat}

law mod_mul_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  for +m: N.BnNat
  {LL.bnlaw.valid(Md.BnMod.mul(a, b, m)) == True{} : Bool}

# The reference exponentiation: for valid x, e and m with m above 0,
# exp_plain(x, e, m) is x^value(e) mod m (Base's Nat.pow); its result is
# valid for every input

law exp_plain_value:
  for +x: N.BnNat
  for +e: N.BnNat
  for +m: N.BnNat
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hm0: {Nat.is_lt(0n, LL.bnlaw.value(m)) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.exp_plain(x, e, m)) == Nat.mod(Nat.pow(LL.bnlaw.value(x), LL.bnlaw.value(e)), LL.bnlaw.value(m)) : Nat}

law exp_plain_valid:
  for +x: N.BnNat
  for +e: N.BnNat
  for +m: N.BnNat
  {LL.bnlaw.valid(Md.BnMod.exp_plain(x, e, m)) == True{} : Bool}
