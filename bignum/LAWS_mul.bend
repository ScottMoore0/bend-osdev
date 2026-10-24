# bend-osdev-bignum's multiplication laws, for every input: BnNat.mul is
# the product of the numbers the limbs stand for, and its limbs are 16-bit.
# Proved in PROOF_mul.bend.
import Base
import ./bignum.bend as N
import ./LAWS_limbs.bend as LL

# The schoolbook product (bn.mul, a row bn.mac at a time): for valid a and
# b, the value of a b is the product of the values; and a b is valid for
# every a and b

law mul_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for hb: {LL.bnlaw.valid(b) == True{} : Bool}
  {LL.bnlaw.value(N.BnNat.mul(a, b)) == Nat.mul(LL.bnlaw.value(a), LL.bnlaw.value(b)) : Nat}

law mul_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  {LL.bnlaw.valid(N.BnNat.mul(a, b)) == True{} : Bool}
