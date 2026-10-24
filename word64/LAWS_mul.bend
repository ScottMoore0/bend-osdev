# bend-osdev-word64's laws of multiplication, for every input: the high
# half of a 32-bit product (W64.mulhi), and W64.mul as the low 64 bits of the
# product of the values. Proved in PROOF_mul.bend.
import Base
import ../u32/u32.bend as U
import ./word64.bend as W

# Multiplication. W64.mulhi(a, b) is the high 32 bits of the product of two
# 32-bit words: with the low 32 bits (U32.mul), the whole product. W64.mul
# is the product modulo 2^64: its value is the low 64 bits of the product of
# the values (U32Nat.low, from bend-osdev-u32), what wraps is 2^64 times the
# rest, and with the product no more than a word's value nothing wraps.
law mulhi_value:
  for +a: U32
  for +b: U32
  {Nat.add(U32.to_nat(U32.mul(a, b)), U.U32Nat.dbl(32n, U32.to_nat(W.W64.mulhi(a, b)))) == Nat.mul(U32.to_nat(a), U32.to_nat(b)) : Nat}

law mul_wrap:
  for +a: W.W64
  for +b: W.W64
  {Nat.add(W.W64.to_nat(W.W64.mul(a, b)), U.U32Nat.dbl(64n, U.U32Nat.high(64n, Nat.mul(W.W64.to_nat(a), W.W64.to_nat(b))))) == Nat.mul(W.W64.to_nat(a), W.W64.to_nat(b)) : Nat}

law mul_low:
  for +a: W.W64
  for +b: W.W64
  {W.W64.to_nat(W.W64.mul(a, b)) == U.U32Nat.low(64n, Nat.mul(W.W64.to_nat(a), W.W64.to_nat(b))) : Nat}

law mul_value:
  for +a: W.W64
  for +b: W.W64
  for +c: W.W64
  for h: {Nat.is_le(Nat.mul(W.W64.to_nat(a), W.W64.to_nat(b)), W.W64.to_nat(c)) == True{} : Bool}
  {W.W64.to_nat(W.W64.mul(a, b)) == Nat.mul(W.W64.to_nat(a), W.W64.to_nat(b)) : Nat}
