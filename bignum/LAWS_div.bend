# bend-osdev-bignum's division laws, for every input: BnNat.divmod, mod
# and div are long division of the numbers the limbs stand for. Proved in
# PROOF_div.bend.
import Base
import ./bignum.bend as N
import ./LAWS_limbs.bend as LL

# divmod is None exactly when the divisor is 0; otherwise its quotient and
# remainder are div and mod
law divmod_none:
  for +a: N.BnNat
  for +b: N.BnNat
  for h: {LL.bnlaw.value(b) == 0n : Nat}
  {N.BnNat.divmod(a, b) == None{} : Maybe<&2, N.BnDivMod>}

law divmod_q:
  for +a: N.BnNat
  for +b: N.BnNat
  for h: {Nat.is_lt(0n, LL.bnlaw.value(b)) == True{} : Bool}
  {Maybe.map(&2, N.BnDivMod, N.BnNat, d => N.BnDivMod.q(d), N.BnNat.divmod(a, b)) == Some{N.BnNat.div(a, b)} : Maybe<&2, N.BnNat>}

law divmod_r:
  for +a: N.BnNat
  for +b: N.BnNat
  for h: {Nat.is_lt(0n, LL.bnlaw.value(b)) == True{} : Bool}
  {Maybe.map(&2, N.BnDivMod, N.BnNat, d => N.BnDivMod.r(d), N.BnNat.divmod(a, b)) == Some{N.BnNat.mod(a, b)} : Maybe<&2, N.BnNat>}

# Long division (shift and subtract): for valid a and b with b above 0,
# a = q b + r with r < b, q = div(a, b) and r = mod(a, b)
law divmod_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for h: {Nat.is_lt(0n, LL.bnlaw.value(b)) == True{} : Bool}
  {Nat.add(Nat.mul(LL.bnlaw.value(N.BnNat.div(a, b)), LL.bnlaw.value(b)), LL.bnlaw.value(N.BnNat.mod(a, b))) == LL.bnlaw.value(a) : Nat}

law mod_lt:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for h: {Nat.is_lt(0n, LL.bnlaw.value(b)) == True{} : Bool}
  {Nat.is_lt(LL.bnlaw.value(N.BnNat.mod(a, b)), LL.bnlaw.value(b)) == True{} : Bool}

# so mod and div are Base's Nat.mod and Nat.div of the values, for every
# valid a and b (by 0 too: a mod 0 is a, a / 0 is 0, as in Base)
law mod_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for hb: {LL.bnlaw.valid(b) == True{} : Bool}
  {LL.bnlaw.value(N.BnNat.mod(a, b)) == Nat.mod(LL.bnlaw.value(a), LL.bnlaw.value(b)) : Nat}

law div_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for hb: {LL.bnlaw.valid(b) == True{} : Bool}
  {LL.bnlaw.value(N.BnNat.div(a, b)) == Nat.div(LL.bnlaw.value(a), LL.bnlaw.value(b)) : Nat}

# the quotient is valid for every input, the remainder for a valid a
law div_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  {LL.bnlaw.valid(N.BnNat.div(a, b)) == True{} : Bool}

law mod_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  for ha: {LL.bnlaw.valid(a) == True{} : Bool}
  {LL.bnlaw.valid(N.BnNat.mod(a, b)) == True{} : Bool}
