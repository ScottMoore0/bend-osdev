# bend-osdev-word64's laws of the bitwise operations and of the one-bit
# shift, for every input. Proved in PROOF_bits.bend.
import Base
import ../u32/u32.bend as U
import ./word64.bend as W

# The bits: and, or and xor commute; and + or is the sum of the values, and
# so is xor + 2 and; with no bit in common (and is 0), or is the sum; not is
# the subtraction from 2^64 - 1.
law and_comm:
  for +a: W.W64
  for +b: W.W64
  {W.W64.and(a, b) == W.W64.and(b, a) : W.W64}

law or_comm:
  for +a: W.W64
  for +b: W.W64
  {W.W64.or(a, b) == W.W64.or(b, a) : W.W64}

law xor_comm:
  for +a: W.W64
  for +b: W.W64
  {W.W64.xor(a, b) == W.W64.xor(b, a) : W.W64}

law and_or:
  for +a: W.W64
  for +b: W.W64
  {Nat.add(W.W64.to_nat(W.W64.and(a, b)), W.W64.to_nat(W.W64.or(a, b))) == Nat.add(W.W64.to_nat(a), W.W64.to_nat(b)) : Nat}

law xor_and:
  for +a: W.W64
  for +b: W.W64
  {Nat.add(W.W64.to_nat(W.W64.xor(a, b)), Nat.double(W.W64.to_nat(W.W64.and(a, b)))) == Nat.add(W.W64.to_nat(a), W.W64.to_nat(b)) : Nat}

law or_disjoint:
  for +a: W.W64
  for +b: W.W64
  for h: {W.W64.and(a, b) == W.W64.zero() : W.W64}
  {W.W64.to_nat(W.W64.or(a, b)) == Nat.add(W.W64.to_nat(a), W.W64.to_nat(b)) : Nat}

law not_sub:
  for +a: W.W64
  {W.W64.not(a) == W.W64.sub(W.W64.max(), a) : W.W64}

# A shift left by one bit: twice the value, less 2^64 for the top bit (bit
# 31 of the high half) going out.
law shl_one_wrap:
  for +a: W.W64
  {Nat.add(W.W64.to_nat(W.W64.shl(a, 1n)), U.U32Nat.dbl(64n, U32.to_nat(U32.shrn(W.W64.hi(a), 31n)))) == Nat.double(W.W64.to_nat(a)) : Nat}
