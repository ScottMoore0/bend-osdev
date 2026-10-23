# The arithmetic of Base's Word(n) and U32 as Nat arithmetic, for every
# width n and every word:
#
# * a word's value (Word.to_nat) is below 2^n, and two words with the same
#   value are the same word;
# * Word.cmp and U32.cmp are the order of the values (so are U32.is_lt,
#   is_le, is_eq);
# * addition is the sum of the values, less 2^n when it wraps, and it wraps
#   exactly when the result is below the first operand; with a bound on the
#   sum (no more than another word's value), it does not wrap;
# * subtraction plus the subtrahend is the minuend, plus 2^n when the
#   subtrahend is the larger; when it is not, it is the Nat difference;
# * increment, and a shift left by one bit (or by k bits, for U32), are the
#   successor and the doubling when the result is bounded by a word's value;
#   a shift right by one bit halves, rounding down;
# * the complement of w is 2^n - 1 - w.
#
# And laws of the Nat functions they are stated with (u32.bend): 2^n is
# U32Nat.dbl(n, 1n), and dbl(n, x) = x * 2^n is additive, composes, and
# keeps the order.
#
# A bound is stated as "no more than a word's value" (Nat.is_le(x,
# U32.to_nat(c))) rather than "below 2^32", because a closed 2^32 is a unary
# Nat in the checkers (see README.md).
import Base
import ./u32.bend as U

# The Nat functions

law dbl_zero:
  for +n: Nat
  {U.U32Nat.dbl(n, 0n) == 0n : Nat}

law dbl_add:
  for +n: Nat
  for +x: Nat
  for +y: Nat
  {U.U32Nat.dbl(n, Nat.add(x, y)) == Nat.add(U.U32Nat.dbl(n, x), U.U32Nat.dbl(n, y)) : Nat}

law dbl_dbl:
  for +m: Nat
  for +k: Nat
  for +x: Nat
  {U.U32Nat.dbl(m, U.U32Nat.dbl(k, x)) == U.U32Nat.dbl(Nat.add(m, k), x) : Nat}

law dbl_lt:
  for +n: Nat
  for +x: Nat
  for +y: Nat
  {Nat.is_lt(U.U32Nat.dbl(n, x), U.U32Nat.dbl(n, y)) == Nat.is_lt(x, y) : Bool}

law dbl_le:
  for +n: Nat
  for +x: Nat
  for +y: Nat
  {Nat.is_le(U.U32Nat.dbl(n, x), U.U32Nat.dbl(n, y)) == Nat.is_le(x, y) : Bool}

law half_double:
  for +x: Nat
  {U.U32Nat.half(Nat.double(x)) == x : Nat}

law half_double_one:
  for +x: Nat
  {U.U32Nat.half(1n+Nat.double(x)) == x : Nat}

# Words of any width n

law word_zero_value:
  for +n: Nat
  {Word.to_nat(n, Word.zero(n)) == 0n : Nat}

law word_value_lt:
  for +n: Nat
  for +w: Word(n)
  {Nat.is_lt(Word.to_nat(n, w), U.U32Nat.dbl(n, 1n)) == True{} : Bool}

law word_value_eq:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}

law word_cmp_value:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

law word_not_value:
  for +n: Nat
  for +w: Word(n)
  {1n+Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)) == U.U32Nat.dbl(n, 1n) : Nat}

law word_add_wrap:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Nat.add(Word.to_nat(n, Word.add(n, a, b)), U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, a, b), a))))) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law word_add_value:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +z: Word(n)
  for h: {Nat.is_le(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Word.to_nat(n, z)) == True{} : Bool}
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law word_sub_wrap:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Nat.add(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b)) == Nat.add(Word.to_nat(n, a), U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, a, b))))) : Nat}

law word_sub_value:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for h: {Nat.is_le(Word.to_nat(n, b), Word.to_nat(n, a)) == True{} : Bool}
  {Word.to_nat(n, Word.sub(n, a, b)) == Nat.sub(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law word_inc_value:
  for +n: Nat
  for +w: Word(n)
  for +z: Word(n)
  for h: {Nat.is_le(1n+Word.to_nat(n, w), Word.to_nat(n, z)) == True{} : Bool}
  {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}

law word_shl_value:
  for +n: Nat
  for +w: Word(n)
  for +z: Word(n)
  for h: {Nat.is_le(Nat.double(Word.to_nat(n, w)), Word.to_nat(n, z)) == True{} : Bool}
  {Word.to_nat(n, Word.shl(n, w)) == Nat.double(Word.to_nat(n, w)) : Nat}

law word_shr_value:
  for +n: Nat
  for +w: Word(n)
  {Word.to_nat(n, Word.shr(n, w)) == U.U32Nat.half(Word.to_nat(n, w)) : Nat}

# U32

law u32_cmp_value:
  for +a: U32
  for +b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

law u32_lt_value:
  for +a: U32
  for +b: U32
  {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}

law u32_le_value:
  for +a: U32
  for +b: U32
  {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}

law u32_eq_value:
  for +a: U32
  for +b: U32
  {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}

law u32_value_eq:
  for +a: U32
  for +b: U32
  for e: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}

law u32_add_wrap:
  for +a: U32
  for +b: U32
  {Nat.add(U32.to_nat(U32.add(a, b)), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32.add(a, b), a)))) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

law u32_add_value:
  for +a: U32
  for +b: U32
  for +c: U32
  for h: {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)) == True{} : Bool}
  {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

law u32_sub_wrap:
  for +a: U32
  for +b: U32
  {Nat.add(U32.to_nat(U32.sub(a, b)), U32.to_nat(b)) == Nat.add(U32.to_nat(a), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(a, b)))) : Nat}

law u32_sub_value:
  for +a: U32
  for +b: U32
  for h: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}
  {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

law u32_inc_value:
  for +a: U32
  for +c: U32
  for h: {Nat.is_le(1n+U32.to_nat(a), U32.to_nat(c)) == True{} : Bool}
  {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}

law u32_shl_value:
  for +a: U32
  for +c: U32
  for h: {Nat.is_le(Nat.double(U32.to_nat(a)), U32.to_nat(c)) == True{} : Bool}
  {U32.to_nat(U32.shl(a)) == Nat.double(U32.to_nat(a)) : Nat}

law u32_shln_value:
  for +a: U32
  for +k: Nat
  for +c: U32
  for +h: {Nat.is_le(U.U32Nat.dbl(k, U32.to_nat(a)), U32.to_nat(c)) == True{} : Bool}
  {U32.to_nat(U32.shln(a, k)) == U.U32Nat.dbl(k, U32.to_nat(a)) : Nat}

law u32_shr_value:
  for +a: U32
  {U32.to_nat(U32.shr(a)) == U.U32Nat.half(U32.to_nat(a)) : Nat}

# Witnesses and vectors

# the bounds can hold, and the wrapping cases happen: 2^32 - 1 + 1 wraps to
# 0, below the first operand; 0 - 1 borrows
law u32_wit:
  {(Nat.is_le(Nat.add(U32.to_nat(3), U32.to_nat(4)), U32.to_nat(7)), U32.is_lt(U32.add(4294967295, 1), 4294967295), U32.is_lt(0, 1), U32.add(4294967295, 1), U32.sub(0, 1)) == (True{}, True{}, True{}, 0, 4294967295) : Bool & Bool & Bool & U32 & U32}

law dbl_vec:
  {(U.U32Nat.dbl(3n, 5n), U.U32Nat.bit(True{}), U.U32Nat.half(7n)) == (40n, 1n, 3n) : Nat & Nat & Nat}
