# The edge cases of 64-bit arithmetic, as vectors: wrapping at 2^64, the two
# 32-bit halves, shifts across the halves, a multiply that overflows, and the
# text forms. 0xDEADBEEF = 3735928559, 0xCAFEBABE = 3405691582.
import Base
import ../u32/u32.bend as U
import ./word64.bend as W

law add_wraps:
  {W.W64.add(W.W64.max(), W.W64.one()) == W.W64.zero() : W.W64}

law sub_wraps:
  {W.W64.sub(W.W64.zero(), W.W64.one()) == W.W64.max() : W.W64}

law hi_of_parts:
  {W.W64.hi(W.W64.from_parts(3735928559, 3405691582)) == 3735928559 : U32}

law lo_of_parts:
  {W.W64.lo(W.W64.from_parts(3735928559, 3405691582)) == 3405691582 : U32}

law shl_crosses_halves:
  {W.W64.shl(W.W64.one(), 32n) == W.W64.from_parts(1, 0) : W.W64}

law shr_crosses_halves:
  {W.W64.shr(W.W64.from_parts(1, 0), 1n) == W.W64.from_parts(0, 2147483648) : W.W64}

# (2^32 - 1)^2 = 2^64 - 2^33 + 1
law mul_of_max_halves:
  {W.W64.mul(W.W64.from_u32(4294967295), W.W64.from_u32(4294967295)) == W.W64.from_parts(4294967294, 1) : W.W64}

law show_max:
  {W.W64.show(W.W64.max()) == "18446744073709551615" : String}

law show_hex_parts:
  {W.W64.show_hex(W.W64.from_parts(3735928559, 3405691582)) == "deadbeefcafebabe" : String}

law show_hex_zero:
  {W.W64.show_hex(W.W64.zero()) == "0000000000000000" : String}

# For every 32-bit a: from_u32 then lo gives a back.
law lo_from_u32:
  for a: U32
  {W.W64.lo(W.W64.from_u32(a)) == a : U32}

# For every pair of halves: splitting the joined word gives them back.
law hi_from_parts:
  for h: U32
  for l: U32
  {W.W64.hi(W.W64.from_parts(h, l)) == h : U32}

law lo_from_parts:
  for h: U32
  for l: U32
  {W.W64.lo(W.W64.from_parts(h, l)) == l : U32}

# Interface laws: a word whose high half is 0 is the word of its low half,
# and the word of halves 0 and 0 is zero.
law from_parts_zero_hi:
  for a: U32
  {W.W64.from_parts(0, a) == W.W64.from_u32(a) : W.W64}

law from_parts_zero:
  {W.W64.from_parts(0, 0) == W.W64.zero() : W.W64}

# Interface law: a word is its two halves joined (for every word). Other
# packages' proofs use this instead of looking inside W64.
law parts_of:
  for v: W.W64
  {W.W64.from_parts(W.W64.hi(v), W.W64.lo(v)) == v : W.W64}

# The value of a word (for every word): lo + hi * 2^32, the weight 2^32 being
# 32 doublings (U32Nat.dbl, from bend-osdev-u32).
law to_nat_parts:
  for +h: U32
  for +l: U32
  {W.W64.to_nat(W.W64.from_parts(h, l)) == Nat.add(U32.to_nat(l), U.U32Nat.dbl(32n, U32.to_nat(h))) : Nat}

# Two words with the same value are the same word.
law value_eq:
  for +a: W.W64
  for +b: W.W64
  for e: {W.W64.to_nat(a) == W.W64.to_nat(b) : Nat}
  {a == b : W.W64}

# Comparison is the order of the values (for every pair of words).
law cmp_value:
  for +a: W.W64
  for +b: W.W64
  {W.W64.cmp(a, b) == Nat.cmp(W.W64.to_nat(a), W.W64.to_nat(b)) : Cmp}

law lt_value:
  for +a: W.W64
  for +b: W.W64
  {W.W64.is_lt(a, b) == Nat.is_lt(W.W64.to_nat(a), W.W64.to_nat(b)) : Bool}

law le_value:
  for +a: W.W64
  for +b: W.W64
  {W.W64.is_le(a, b) == Nat.is_le(W.W64.to_nat(a), W.W64.to_nat(b)) : Bool}

law eq_value:
  for +a: W.W64
  for +b: W.W64
  {W.W64.is_eq(a, b) == Nat.is_eq(W.W64.to_nat(a), W.W64.to_nat(b)) : Bool}

# Comparison is by the high halves, then the low halves (for dependents
# that order words through W64.hi and W64.lo).
law cmp_hi_lt:
  for +a: W.W64
  for +b: W.W64
  for h: {U32.cmp(W.W64.hi(a), W.W64.hi(b)) == LT{} : Cmp}
  {W.W64.cmp(a, b) == LT{} : Cmp}

law cmp_hi_gt:
  for +a: W.W64
  for +b: W.W64
  for h: {U32.cmp(W.W64.hi(a), W.W64.hi(b)) == GT{} : Cmp}
  {W.W64.cmp(a, b) == GT{} : Cmp}

law cmp_hi_eq:
  for +a: W.W64
  for +b: W.W64
  for h: {U32.cmp(W.W64.hi(a), W.W64.hi(b)) == EQ{} : Cmp}
  {W.W64.cmp(a, b) == U32.cmp(W.W64.lo(a), W.W64.lo(b)) : Cmp}

# Addition, for every pair of words: the sum of the values, less 2^64 when
# it wraps, which is exactly when the result is below the first operand;
# and with the sum no more than a word's value, it does not wrap.
law add_wrap:
  for +a: W.W64
  for +b: W.W64
  {Nat.add(W.W64.to_nat(W.W64.add(a, b)), U.U32Nat.dbl(64n, U.U32Nat.bit(W.W64.is_lt(W.W64.add(a, b), a)))) == Nat.add(W.W64.to_nat(a), W.W64.to_nat(b)) : Nat}

law add_value:
  for +a: W.W64
  for +b: W.W64
  for +c: W.W64
  for h: {Nat.is_le(Nat.add(W.W64.to_nat(a), W.W64.to_nat(b)), W.W64.to_nat(c)) == True{} : Bool}
  {W.W64.to_nat(W.W64.add(a, b)) == Nat.add(W.W64.to_nat(a), W.W64.to_nat(b)) : Nat}

# Subtraction, for every pair of words: the difference plus the subtrahend
# is the minuend, plus 2^64 when the subtrahend is the larger; when it is
# not, the difference is the Nat difference.
law sub_wrap:
  for +a: W.W64
  for +b: W.W64
  {Nat.add(W.W64.to_nat(W.W64.sub(a, b)), W.W64.to_nat(b)) == Nat.add(W.W64.to_nat(a), U.U32Nat.dbl(64n, U.U32Nat.bit(W.W64.is_lt(a, b)))) : Nat}

law sub_value:
  for +a: W.W64
  for +b: W.W64
  for h: {Nat.is_le(W.W64.to_nat(b), W.W64.to_nat(a)) == True{} : Bool}
  {W.W64.to_nat(W.W64.sub(a, b)) == Nat.sub(W.W64.to_nat(a), W.W64.to_nat(b)) : Nat}

# Shifts, as Nat facts. A shift left by k < 64 multiplies the value by 2^k
# when the result is no more than a word's value; a shift right by k < 64
# is the floor of the value divided by 2^k (2^k times it is at most the
# value, and 2^k times one more is above it); by 64 or more, both give 0.
law shl_value:
  for +a: W.W64
  for +k: Nat
  for +c: W.W64
  for hk: {Nat.is_lt(k, 64n) == True{} : Bool}
  for +h: {Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(a)), W.W64.to_nat(c)) == True{} : Bool}
  {W.W64.to_nat(W.W64.shl(a, k)) == U.U32Nat.dbl(k, W.W64.to_nat(a)) : Nat}

law shr_value_le:
  for +a: W.W64
  for +k: Nat
  for hk: {Nat.is_lt(k, 64n) == True{} : Bool}
  {Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(W.W64.shr(a, k))), W.W64.to_nat(a)) == True{} : Bool}

law shr_value_lt:
  for +a: W.W64
  for +k: Nat
  for hk: {Nat.is_lt(k, 64n) == True{} : Bool}
  {Nat.is_lt(W.W64.to_nat(a), U.U32Nat.dbl(k, 1n+W.W64.to_nat(W.W64.shr(a, k)))) == True{} : Bool}

law shl_big:
  for +a: W.W64
  for +k: Nat
  for +h: {Nat.is_le(64n, k) == True{} : Bool}
  {W.W64.shl(a, k) == W.W64.zero() : W.W64}

law shr_big:
  for +a: W.W64
  for +k: Nat
  for +h: {Nat.is_le(64n, k) == True{} : Bool}
  {W.W64.shr(a, k) == W.W64.zero() : W.W64}
