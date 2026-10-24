# bend-osdev-bignum's gcd and lcm laws, for every input: for valid a and b,
# BnMod.gcd(a, b) and BnMod.lcm(a, b) are bend-osdev-kmath's KMath.gcd and
# KMath.lcm of the numbers' values. So gcd(a, b) divides a and b and every
# common divisor of a and b divides it, lcm(a, b) is a common multiple of a
# and b and divides every common multiple, gcd(a, 0) = a and gcd(0, b) = b
# (so gcd(0, 0) = 0), and lcm(a, b) is 0 when a or b is. Proved in
# PROOF_gcd.bend.
import Base
import ../kmath/kmath.bend as K
import ./bignum.bend as N
import ./modular.bend as Md
import ./LAWS_limbs.bend as LL

# Euclid's algorithm computes the greatest common divisor of the values,
# and its result is valid
law gcd_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.gcd(a, b)) == K.KMath.gcd(LL.bnlaw.value(a), LL.bnlaw.value(b)) : Nat}

law gcd_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  {LL.bnlaw.valid(Md.BnMod.gcd(a, b)) == True{} : Bool}

# gcd(a, b) divides a and b (with witnesses: k gcd(a, b) = a), and every
# common divisor d of a and b divides it
law gcd_divides_l:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  exs k: Nat
  {Nat.mul(k, LL.bnlaw.value(Md.BnMod.gcd(a, b))) == LL.bnlaw.value(a) : Nat}

law gcd_divides_r:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  exs k: Nat
  {Nat.mul(k, LL.bnlaw.value(Md.BnMod.gcd(a, b))) == LL.bnlaw.value(b) : Nat}

law gcd_greatest:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +d: Nat
  for +u: Nat
  for +v: Nat
  for eu: {Nat.mul(u, d) == LL.bnlaw.value(a) : Nat}
  for ev: {Nat.mul(v, d) == LL.bnlaw.value(b) : Nat}
  exs k: Nat
  {Nat.mul(k, d) == LL.bnlaw.value(Md.BnMod.gcd(a, b)) : Nat}

# with 0: gcd(a, 0) = a and gcd(0, b) = b
law gcd_zero_r:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for hz: {LL.bnlaw.value(b) == 0n : Nat}
  {LL.bnlaw.value(Md.BnMod.gcd(a, b)) == LL.bnlaw.value(a) : Nat}

law gcd_zero_l:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for hz: {LL.bnlaw.value(a) == 0n : Nat}
  {LL.bnlaw.value(Md.BnMod.gcd(a, b)) == LL.bnlaw.value(b) : Nat}

# lcm(a, b) = (a / gcd(a, b)) b is kmath's lcm of the values, and valid for
# every input
law lcm_value:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  {LL.bnlaw.value(Md.BnMod.lcm(a, b)) == K.KMath.lcm(LL.bnlaw.value(a), LL.bnlaw.value(b)) : Nat}

law lcm_valid:
  for +a: N.BnNat
  for +b: N.BnNat
  {LL.bnlaw.valid(Md.BnMod.lcm(a, b)) == True{} : Bool}

# lcm(a, b) is a multiple of a and of b, and divides every common multiple m
law lcm_multiple_l:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  exs k: Nat
  {Nat.mul(k, LL.bnlaw.value(a)) == LL.bnlaw.value(Md.BnMod.lcm(a, b)) : Nat}

law lcm_multiple_r:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  exs k: Nat
  {Nat.mul(k, LL.bnlaw.value(b)) == LL.bnlaw.value(Md.BnMod.lcm(a, b)) : Nat}

law lcm_least:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for +m: Nat
  for +u: Nat
  for +v: Nat
  for eu: {Nat.mul(u, LL.bnlaw.value(a)) == m : Nat}
  for ev: {Nat.mul(v, LL.bnlaw.value(b)) == m : Nat}
  exs k: Nat
  {Nat.mul(k, LL.bnlaw.value(Md.BnMod.lcm(a, b))) == m : Nat}

# lcm with 0 is 0
law lcm_zero_r:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for hz: {LL.bnlaw.value(b) == 0n : Nat}
  {LL.bnlaw.value(Md.BnMod.lcm(a, b)) == 0n : Nat}

law lcm_zero_l:
  for +a: N.BnNat
  for +b: N.BnNat
  for +ha: {LL.bnlaw.valid(a) == True{} : Bool}
  for +hb: {LL.bnlaw.valid(b) == True{} : Bool}
  for hz: {LL.bnlaw.value(a) == 0n : Nat}
  {LL.bnlaw.value(Md.BnMod.lcm(a, b)) == 0n : Nat}
