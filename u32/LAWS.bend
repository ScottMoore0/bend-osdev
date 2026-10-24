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

# Nat arithmetic: the semiring laws, the order as witnesses, the uniqueness
# of a quotient and remainder, and a sum that cannot wrap. They are what the
# word laws below are proved from, and what other packages' proofs use for
# their own Nat arithmetic (scripts/natproof.py writes ring identities from
# them).

law nat_add_zero:
  for +x: Nat
  {Nat.add(x, 0n) == x : Nat}

law nat_add_succ:
  for +x: Nat
  for +y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

law nat_add_comm:
  for +x: Nat
  for +y: Nat
  {Nat.add(x, y) == Nat.add(y, x) : Nat}

law nat_add_assoc:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Nat.add(Nat.add(x, y), z) == Nat.add(x, Nat.add(y, z)) : Nat}

law nat_add_left_comm:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}

law nat_add_cancel:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  for e: {Nat.add(k, x) == Nat.add(k, y) : Nat}
  {x == y : Nat}

law nat_mul_zero:
  for +x: Nat
  {Nat.mul(x, 0n) == 0n : Nat}

law nat_mul_one:
  for +x: Nat
  {Nat.mul(x, 1n) == x : Nat}

law nat_one_mul:
  for +x: Nat
  {Nat.mul(1n, x) == x : Nat}

law nat_mul_succ:
  for +x: Nat
  for +y: Nat
  {Nat.mul(x, 1n+y) == Nat.add(x, Nat.mul(x, y)) : Nat}

law nat_mul_comm:
  for +x: Nat
  for +y: Nat
  {Nat.mul(x, y) == Nat.mul(y, x) : Nat}

law nat_mul_assoc:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Nat.mul(Nat.mul(x, y), z) == Nat.mul(x, Nat.mul(y, z)) : Nat}

law nat_mul_left_comm:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Nat.mul(x, Nat.mul(y, z)) == Nat.mul(y, Nat.mul(x, z)) : Nat}

law nat_mul_add:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Nat.mul(x, Nat.add(y, z)) == Nat.add(Nat.mul(x, y), Nat.mul(x, z)) : Nat}

law nat_add_mul:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Nat.mul(Nat.add(x, y), z) == Nat.add(Nat.mul(x, z), Nat.mul(y, z)) : Nat}

law nat_double:
  for +x: Nat
  {Nat.double(x) == Nat.add(x, x) : Nat}

law dbl_comm:
  for +j: Nat
  for +k: Nat
  for +x: Nat
  {U.U32Nat.dbl(j, U.U32Nat.dbl(k, x)) == U.U32Nat.dbl(k, U.U32Nat.dbl(j, x)) : Nat}

law dbl_mul_l:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {Nat.mul(U.U32Nat.dbl(k, x), y) == U.U32Nat.dbl(k, Nat.mul(x, y)) : Nat}

law dbl_mul_r:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {Nat.mul(x, U.U32Nat.dbl(k, y)) == U.U32Nat.dbl(k, Nat.mul(x, y)) : Nat}

# the order: x <= y exactly when (y - x) + x = y, and x < y when
# (y - (1 + x)) + 1 + x = y; and w + 1 + x is never x

law nat_le_refl:
  for +x: Nat
  {Nat.is_le(x, x) == True{} : Bool}

law nat_le_add:
  for +x: Nat
  for +w: Nat
  {Nat.is_le(x, Nat.add(w, x)) == True{} : Bool}

law nat_lt_add:
  for +x: Nat
  for +w: Nat
  {Nat.is_lt(x, Nat.add(w, 1n+x)) == True{} : Bool}

law nat_le_witness:
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_le(x, y) == True{} : Bool}
  {Nat.add(Nat.sub(y, x), x) == y : Nat}

law nat_lt_witness:
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.add(Nat.sub(y, 1n+x), 1n+x) == y : Nat}

law nat_succ_add_absurd:
  for +w: Nat
  for +x: Nat
  for e: {Nat.add(w, 1n+x) == x : Nat}
  Empty

# a quotient and remainder are unique: q b + r with r < b determines q and r

law nat_div_unique:
  for +b: Nat
  for +q1: Nat
  for +r1: Nat
  for +q2: Nat
  for +r2: Nat
  for e: {Nat.add(Nat.mul(q1, b), r1) == Nat.add(Nat.mul(q2, b), r2) : Nat}
  for h1: {Nat.is_lt(r1, b) == True{} : Bool}
  for h2: {Nat.is_lt(r2, b) == True{} : Bool}
  {q1 == q2 : Nat}

law nat_mod_unique:
  for +b: Nat
  for +q1: Nat
  for +r1: Nat
  for +q2: Nat
  for +r2: Nat
  for e: {Nat.add(Nat.mul(q1, b), r1) == Nat.add(Nat.mul(q2, b), r2) : Nat}
  for h1: {Nat.is_lt(r1, b) == True{} : Bool}
  for h2: {Nat.is_lt(r2, b) == True{} : Bool}
  {r1 == r2 : Nat}

# r + 2^n k = p, with p no more than z and z below 2^n: k is 0, and r = p
# (a sum below 2^n did not wrap)

law dbl_nowrap:
  for +n: Nat
  for +k: Nat
  for +r: Nat
  for +p: Nat
  for +z: Nat
  for e: {Nat.add(r, U.U32Nat.dbl(n, k)) == p : Nat}
  for h: {Nat.is_le(p, z) == True{} : Bool}
  for hz: {Nat.is_lt(z, U.U32Nat.dbl(n, 1n)) == True{} : Bool}
  {r == p : Nat}

# The low k bits of x and the rest (u32.bend): x = low(k, x) + 2^k high(k, x)
# with low(k, x) below 2^k, and these are the only such pair

law nat_odd_half:
  for +x: Nat
  {Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.half(x))) == x : Nat}

law nat_odd_le:
  for +x: Nat
  {Nat.is_le(U.U32Nat.odd(x), 1n) == True{} : Bool}

law low_high:
  for +k: Nat
  for +x: Nat
  {Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))) == x : Nat}

law low_lt:
  for +k: Nat
  for +x: Nat
  {Nat.is_lt(U.U32Nat.low(k, x), U.U32Nat.dbl(k, 1n)) == True{} : Bool}

law low_unique:
  for +k: Nat
  for +x: Nat
  for +r: Nat
  for +q: Nat
  for e: {Nat.add(r, U.U32Nat.dbl(k, q)) == x : Nat}
  for h: {Nat.is_lt(r, U.U32Nat.dbl(k, 1n)) == True{} : Bool}
  {r == U.U32Nat.low(k, x) : Nat}

law high_unique:
  for +k: Nat
  for +x: Nat
  for +r: Nat
  for +q: Nat
  for e: {Nat.add(r, U.U32Nat.dbl(k, q)) == x : Nat}
  for h: {Nat.is_lt(r, U.U32Nat.dbl(k, 1n)) == True{} : Bool}
  {q == U.U32Nat.high(k, x) : Nat}

law low_add_dbl:
  for +k: Nat
  for +x: Nat
  for +q: Nat
  {U.U32Nat.low(k, Nat.add(x, U.U32Nat.dbl(k, q))) == U.U32Nat.low(k, x) : Nat}

law low_small:
  for +k: Nat
  for +x: Nat
  for h: {Nat.is_lt(x, U.U32Nat.dbl(k, 1n)) == True{} : Bool}
  {U.U32Nat.low(k, x) == x : Nat}

# Multiplication: the product's value is the low n bits of the product of
# the values; what wraps is 2^n times the rest; with the product no more
# than a word's value, nothing wraps

law word_mul_wrap:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Nat.add(Word.to_nat(n, Word.mul(n, a, b)), U.U32Nat.dbl(n, U.U32Nat.high(n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))))) == Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law word_mul_low:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.to_nat(n, Word.mul(n, a, b)) == U.U32Nat.low(n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))) : Nat}

law word_mul_value:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +z: Word(n)
  for h: {Nat.is_le(Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)), Word.to_nat(n, z)) == True{} : Bool}
  {Word.to_nat(n, Word.mul(n, a, b)) == Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law u32_mul_wrap:
  for +a: U32
  for +b: U32
  {Nat.add(U32.to_nat(U32.mul(a, b)), U.U32Nat.dbl(32n, U.U32Nat.high(32n, Nat.mul(U32.to_nat(a), U32.to_nat(b))))) == Nat.mul(U32.to_nat(a), U32.to_nat(b)) : Nat}

law u32_mul_low:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.mul(a, b)) == U.U32Nat.low(32n, Nat.mul(U32.to_nat(a), U32.to_nat(b))) : Nat}

law u32_mul_value:
  for +a: U32
  for +b: U32
  for +c: U32
  for h: {Nat.is_le(Nat.mul(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)) == True{} : Bool}
  {U32.to_nat(U32.mul(a, b)) == Nat.mul(U32.to_nat(a), U32.to_nat(b)) : Nat}

# Division: for b not 0, the quotient and remainder are the Nat ones,
# a = q b + r with r < b; by 0, the quotient is 0 and the remainder a

law u32_divmod:
  for +a: U32
  for +b: U32
  for h: {U32.is_zero(b) == False{} : Bool}
  {Nat.add(Nat.mul(U32.to_nat(U32.div(a, b)), U32.to_nat(b)), U32.to_nat(U32.mod(a, b))) == U32.to_nat(a) : Nat}

law u32_mod_lt:
  for +a: U32
  for +b: U32
  for h: {U32.is_zero(b) == False{} : Bool}
  {Nat.is_lt(U32.to_nat(U32.mod(a, b)), U32.to_nat(b)) == True{} : Bool}

law u32_div_zero:
  for +a: U32
  {U32.div(a, 0) == 0 : U32}

law u32_mod_zero:
  for +a: U32
  {U32.mod(a, 0) == a : U32}

# The bitwise operations: and, or and xor commute; and + or is the sum of
# the values, and so is xor + 2 and; an or of a multiple of 2^k and a value
# below 2^k is their sum; an and with the mask of the low k bits is the low
# k bits; not is the subtraction from the mask of all n bits

law word_and_comm:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.and(n, a, b) == Word.and(n, b, a) : Word(n)}

law word_or_comm:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.or(n, a, b) == Word.or(n, b, a) : Word(n)}

law word_xor_comm:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.xor(n, a, b) == Word.xor(n, b, a) : Word(n)}

law word_and_or:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Nat.add(Word.to_nat(n, Word.and(n, a, b)), Word.to_nat(n, Word.or(n, a, b))) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law word_xor_and:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Nat.add(Word.to_nat(n, Word.xor(n, a, b)), Nat.double(Word.to_nat(n, Word.and(n, a, b)))) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law word_or_split:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Nat
  for +q: Nat
  for e: {Word.to_nat(n, a) == U.U32Nat.dbl(k, q) : Nat}
  for h: {Nat.is_lt(Word.to_nat(n, b), U.U32Nat.dbl(k, 1n)) == True{} : Bool}
  {Word.to_nat(n, Word.or(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law word_mask_value:
  for +n: Nat
  for +k: Nat
  for h: {Nat.is_le(k, n) == True{} : Bool}
  {1n+Word.to_nat(n, U.U32Word.mask(n, k)) == U.U32Nat.dbl(k, 1n) : Nat}

law word_and_mask:
  for +n: Nat
  for +w: Word(n)
  for +m: Word(n)
  for +k: Nat
  for h: {1n+Word.to_nat(n, m) == U.U32Nat.dbl(k, 1n) : Nat}
  {Word.to_nat(n, Word.and(n, w, m)) == U.U32Nat.low(k, Word.to_nat(n, w)) : Nat}

law word_not_sub:
  for +n: Nat
  for +w: Word(n)
  {Word.not(n, w) == Word.sub(n, U.U32Word.mask(n, n), w) : Word(n)}

law u32_and_comm:
  for +a: U32
  for +b: U32
  {U32.and(a, b) == U32.and(b, a) : U32}

law u32_or_comm:
  for +a: U32
  for +b: U32
  {U32.or(a, b) == U32.or(b, a) : U32}

law u32_xor_comm:
  for +a: U32
  for +b: U32
  {U32.xor(a, b) == U32.xor(b, a) : U32}

law u32_and_or:
  for +a: U32
  for +b: U32
  {Nat.add(U32.to_nat(U32.and(a, b)), U32.to_nat(U32.or(a, b))) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

law u32_xor_and:
  for +a: U32
  for +b: U32
  {Nat.add(U32.to_nat(U32.xor(a, b)), Nat.double(U32.to_nat(U32.and(a, b)))) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

law u32_or_split:
  for +a: U32
  for +b: U32
  for +k: Nat
  for +q: Nat
  for e: {U32.to_nat(a) == U.U32Nat.dbl(k, q) : Nat}
  for h: {Nat.is_lt(U32.to_nat(b), U.U32Nat.dbl(k, 1n)) == True{} : Bool}
  {U32.to_nat(U32.or(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

law u32_and_mask:
  for +a: U32
  for +m: U32
  for +k: Nat
  for h: {1n+U32.to_nat(m) == U.U32Nat.dbl(k, 1n) : Nat}
  {U32.to_nat(U32.and(a, m)) == U.U32Nat.low(k, U32.to_nat(a)) : Nat}

# the 16-bit mask, written as Base reads it (65535 = U32Word.mask(32, 16))
law u32_and_65535:
  for +a: U32
  {U32.to_nat(U32.and(a, 65535)) == U.U32Nat.low(16n, U32.to_nat(a)) : Nat}

law u32_not_sub:
  for +a: U32
  {U32.not(a) == U32.sub(4294967295, a) : U32}

# Shifts by k bits: right, the rest of the value past its low k bits; left,
# the low 32 bits of the value times 2^k

law u32_shrn_value:
  for +a: U32
  for +k: Nat
  {U32.to_nat(U32.shrn(a, k)) == U.U32Nat.high(k, U32.to_nat(a)) : Nat}

law u32_shln_low:
  for +a: U32
  for +k: Nat
  {U32.to_nat(U32.shln(a, k)) == U.U32Nat.low(32n, U.U32Nat.dbl(k, U32.to_nat(a))) : Nat}

# More of the Nat library: doubling and the low bits, a bound on the rest,
# order of products and of powers of two

law low_double:
  for +k: Nat
  for +x: Nat
  {U.U32Nat.low(1n+k, Nat.double(x)) == Nat.double(U.U32Nat.low(k, x)) : Nat}

law high_double:
  for +k: Nat
  for +x: Nat
  {U.U32Nat.high(1n+k, Nat.double(x)) == U.U32Nat.high(k, x) : Nat}

# x below 2^(k + j): high(k, x) below 2^j
law high_lt:
  for +k: Nat
  for +j: Nat
  for +m: Nat
  for +x: Nat
  for e: {Nat.add(k, j) == m : Nat}
  for h: {Nat.is_lt(x, U.U32Nat.dbl(m, 1n)) == True{} : Bool}
  {Nat.is_lt(U.U32Nat.high(k, x), U.U32Nat.dbl(j, 1n)) == True{} : Bool}

law nat_mul_lt:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for h1: {Nat.is_lt(a, c) == True{} : Bool}
  for h2: {Nat.is_lt(b, d) == True{} : Bool}
  {Nat.is_lt(Nat.mul(a, b), Nat.mul(c, d)) == True{} : Bool}

law nat_le_dbl:
  for +k: Nat
  for +x: Nat
  {Nat.is_le(x, U.U32Nat.dbl(k, x)) == True{} : Bool}

law dbl_le_exp:
  for +j: Nat
  for +k: Nat
  for +x: Nat
  for h: {Nat.is_le(j, k) == True{} : Bool}
  {Nat.is_le(U.U32Nat.dbl(j, x), U.U32Nat.dbl(k, x)) == True{} : Bool}

# One step of restoring division on n-bit registers (as Base's U32.divmod
# and bend-osdev-word64's W64.div do it): the remainder r below b < 2^n is
# shifted left with a bit a coming in, s keeping the low n bits and t the bit
# going out; if t, or if s is not below b (l false), b is subtracted (g),
# giving r1 (er: r1 + b = s + 2^n [s < b] when g, r1 = s when not). Then
# r1 + g b = 2 r + a, and r1 is below b.

law divstep_value:
  for +n: Nat
  for +s: Nat
  for +b: Nat
  for +r: Nat
  for +a: Nat
  for +r1: Nat
  for +t: Bool
  for +l: Bool
  for +g: Bool
  for e: {Nat.add(s, U.U32Nat.dbl(n, U.U32Nat.bit(t))) == Nat.add(a, Nat.double(r)) : Nat}
  for el: {Nat.is_lt(s, b) == l : Bool}
  for eg: {Bool.or(t, Bool.not(l)) == g : Bool}
  for er: {Nat.add(r1, Nat.mul(U.U32Nat.bit(g), b)) == Nat.add(s, U.U32Nat.dbl(n, Nat.mul(U.U32Nat.bit(g), U.U32Nat.bit(l)))) : Nat}
  for ha: {Nat.is_le(a, 1n) == True{} : Bool}
  for hr: {Nat.is_lt(r, b) == True{} : Bool}
  for hb: {Nat.is_lt(b, U.U32Nat.dbl(n, 1n)) == True{} : Bool}
  {Nat.add(r1, Nat.mul(U.U32Nat.bit(g), b)) == Nat.add(a, Nat.double(r)) : Nat}

law divstep_lt:
  for +n: Nat
  for +s: Nat
  for +b: Nat
  for +r: Nat
  for +a: Nat
  for +r1: Nat
  for +t: Bool
  for +l: Bool
  for +g: Bool
  for e: {Nat.add(s, U.U32Nat.dbl(n, U.U32Nat.bit(t))) == Nat.add(a, Nat.double(r)) : Nat}
  for el: {Nat.is_lt(s, b) == l : Bool}
  for eg: {Bool.or(t, Bool.not(l)) == g : Bool}
  for er: {Nat.add(r1, Nat.mul(U.U32Nat.bit(g), b)) == Nat.add(s, U.U32Nat.dbl(n, Nat.mul(U.U32Nat.bit(g), U.U32Nat.bit(l)))) : Nat}
  for ha: {Nat.is_le(a, 1n) == True{} : Bool}
  for hr: {Nat.is_lt(r, b) == True{} : Bool}
  for hb: {Nat.is_lt(b, U.U32Nat.dbl(n, 1n)) == True{} : Bool}
  {Nat.is_lt(r1, b) == True{} : Bool}
