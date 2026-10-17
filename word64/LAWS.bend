# DRAFT: not yet reviewed by the maintainer
#
# The edge cases of 64-bit arithmetic, as vectors: wrapping at 2^64, the two
# 32-bit halves, shifts across the halves, a multiply that overflows, and the
# text forms. 0xDEADBEEF = 3735928559, 0xCAFEBABE = 3405691582.
import Base
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

# Interface law: a word is its two halves joined (for every word). Other
# packages' proofs use this instead of looking inside W64.
law parts_of:
  for v: W.W64
  {W.W64.from_parts(W.W64.hi(v), W.W64.lo(v)) == v : W.W64}
