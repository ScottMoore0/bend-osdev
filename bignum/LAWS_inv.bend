# bend-osdev-bignum's modular inverse laws, for every input: for valid a
# and m, BnMod.inv(a, m) (the extended Euclidean algorithm) gives an inverse
# exactly when m > 1 and gcd(a, m) = 1, and the t it gives is valid, below
# m, and has a t mod m = 1. Proved in PROOF_inv.bend.
import Base
import ./bignum.bend as N
import ./modular.bend as Md
import ./LAWS_limbs.bend as LL

# whether a Maybe holds a number
def bnlaw.is_some(r: Maybe<&2, N.BnNat>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{x}:
      True{}

# inv(a, m) is Some exactly when m > 1 and gcd(a, m) = 1 (so None for m = 0
# and m = 1, and for a = 0 with m > 1)
law inv_some:
  for +a: N.BnNat
  for +m: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  {bnlaw.is_some(Md.BnMod.inv(a, m)) == Bool.and(Nat.is_lt(1n, LL.bnlaw.value(m)), Nat.is_eq(LL.bnlaw.value(Md.BnMod.gcd(a, m)), 1n)) : Bool}

# the inverse it gives: a t mod m = 1, t < m, and t is valid
law inv_value:
  for +a: N.BnNat
  for +m: N.BnNat
  for +t: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for e: {Md.BnMod.inv(a, m) == Some{t} : Maybe<&2, N.BnNat>}
  {Nat.mod(Nat.mul(LL.bnlaw.value(a), LL.bnlaw.value(t)), LL.bnlaw.value(m)) == 1n : Nat}

law inv_lt:
  for +a: N.BnNat
  for +m: N.BnNat
  for +t: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for e: {Md.BnMod.inv(a, m) == Some{t} : Maybe<&2, N.BnNat>}
  {Nat.is_lt(LL.bnlaw.value(t), LL.bnlaw.value(m)) == True{} : Bool}

law inv_valid:
  for +a: N.BnNat
  for +m: N.BnNat
  for +t: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for e: {Md.BnMod.inv(a, m) == Some{t} : Maybe<&2, N.BnNat>}
  {LL.bnlaw.valid(t) == True{} : Bool}
