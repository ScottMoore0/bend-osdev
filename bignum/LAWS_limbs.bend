# bend-osdev-bignum's limb laws, for every input: the number a list of
# 16-bit limbs stands for, and add, sub and cmp computing on those numbers.
# Proved in PROOF_limbs.bend.
import Base
import ../u32/u32.bend as U
import ./bignum.bend as N

# The number a list of limbs stands for (least significant first, base
# 2^16), and whether every limb is a 16-bit one (its bits from 16 up are 0);
# bnlaw.value and bnlaw.valid are those of a BnNat's limbs. Every number the
# public defs build is valid (of_limbs, and add and sub of valid numbers).
def bnlaw.val(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(U32.to_nat(x), U.U32Nat.dbl(16n, bnlaw.val(t)))

def bnlaw.ok(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(U32.is_zero(U32.shrn(x, 16n)), bnlaw.ok(t))

def bnlaw.value(x: N.BnNat) -> Nat:
  match x:
    case N.BnNat{ls}:
      bnlaw.val(ls)

def bnlaw.valid(x: N.BnNat) -> Bool:
  match x:
    case N.BnNat{ls}:
      bnlaw.ok(ls)

# The limbs (bignum's first arithmetic laws, for every input): of_limbs
# makes a valid number; for valid numbers, add is the sum of the values (and
# valid), cmp is the order of the values, and sub is the difference, 0 when
# b > a (and valid)

law of_limbs_valid:
  for +xs: List<&2, U32>
  {bnlaw.valid(N.BnNat.of_limbs(xs)) == True{} : Bool}

law add_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {bnlaw.valid(a) == True{} : Bool}
  for hb: {bnlaw.valid(b) == True{} : Bool}
  {bnlaw.value(N.BnNat.add(a, b)) == Nat.add(bnlaw.value(a), bnlaw.value(b)) : Nat}

law add_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {bnlaw.valid(a) == True{} : Bool}
  for hb: {bnlaw.valid(b) == True{} : Bool}
  {bnlaw.valid(N.BnNat.add(a, b)) == True{} : Bool}

law cmp_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {bnlaw.valid(a) == True{} : Bool}
  for hb: {bnlaw.valid(b) == True{} : Bool}
  {N.BnNat.cmp(a, b) == Nat.cmp(bnlaw.value(a), bnlaw.value(b)) : Cmp}

law sub_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {bnlaw.valid(a) == True{} : Bool}
  for hb: {bnlaw.valid(b) == True{} : Bool}
  {bnlaw.value(N.BnNat.sub(a, b)) == Nat.sub(bnlaw.value(a), bnlaw.value(b)) : Nat}

law sub_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  {bnlaw.valid(N.BnNat.sub(a, b)) == True{} : Bool}
