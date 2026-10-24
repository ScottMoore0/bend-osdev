# Base's Nat division by a divisor 1 + bp (every positive divisor), as the
# packages' proofs use it: quotient and remainder recompose the dividend,
# the remainder is below the divisor, a dividend g (1 + bp) + i with i below
# the divisor has quotient g and remainder i, and rounding a up to a
# multiple of the divisor adds the slack (1 + bp - 1) - (a + bp) mod (1 + bp).
import Base

law nat_div_mod:
  for +a: Nat
  for +bp: Nat
  {Nat.add(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)) == a : Nat}

law nat_mod_lt:
  for +a: Nat
  for +bp: Nat
  {Nat.is_lt(Nat.mod(a, 1n+bp), 1n+bp) == True{} : Bool}

law nat_divmod_exact:
  for +g: Nat
  for +i: Nat
  for +bp: Nat
  for h: {Nat.is_lt(i, 1n+bp) == True{} : Bool}
  {Nat.divmod(Nat.add(Nat.mul(g, 1n+bp), i), 1n+bp) == (g, i) : Nat & Nat}

law nat_round_up:
  for +bp: Nat
  for +a: Nat
  {Nat.mul(Nat.div(Nat.add(a, Nat.sub(1n+bp, 1n)), 1n+bp), 1n+bp) == Nat.add(a, Nat.sub(Nat.sub(1n+bp, 1n), Nat.mod(Nat.add(a, Nat.sub(1n+bp, 1n)), 1n+bp))) : Nat}
