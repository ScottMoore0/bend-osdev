# bend-osdev-word64's laws of division, for every input: W64.div and
# W64.mod are the Nat quotient and remainder, and division by 0 gives 0 and
# the dividend. Proved in PROOF_div.bend.
import Base
import ../u32/u32.bend as U
import ./word64.bend as W

# Division (shift and subtract, 64 steps): for b not 0, the quotient and the
# remainder are the Nat ones, a = q b + r with r < b; by 0, the quotient is 0
# and the remainder a.
law divmod_value:
  for +a: W.W64
  for +b: W.W64
  for h: {W.W64.is_zero(b) == False{} : Bool}
  {Nat.add(Nat.mul(W.W64.to_nat(W.W64.div(a, b)), W.W64.to_nat(b)), W.W64.to_nat(W.W64.mod(a, b))) == W.W64.to_nat(a) : Nat}

law mod_lt:
  for +a: W.W64
  for +b: W.W64
  for h: {W.W64.is_zero(b) == False{} : Bool}
  {Nat.is_lt(W.W64.to_nat(W.W64.mod(a, b)), W.W64.to_nat(b)) == True{} : Bool}

law div_zero:
  for +a: W.W64
  {W.W64.div(a, W.W64.zero()) == W.W64.zero() : W.W64}

law mod_zero:
  for +a: W.W64
  {W.W64.mod(a, W.W64.zero()) == a : W.W64}
