# bend-osdev-kmath's laws of 64-bit division (div64.bend), for every input:
# the quotient and remainder are the Nat ones, by 0 they are 0 and the
# dividend, and rounding up gives the least multiple count. Proved in
# PROOF_div.bend.
import Base
import ../word64/word64.bend as W
import ./div64.bend as D

# the parts of a KDiv64 and of a pair (for the laws below)
def kmlaw.q(x: D.KDiv64) -> W.W64:
  match x:
    case D.KDiv64{q, r}:
      q

def kmlaw.r(x: D.KDiv64) -> U32:
  match x:
    case D.KDiv64{q, r}:
      r

def kmlaw.fst(p: W.W64 & W.W64) -> W.W64:
  (q, r) = p
  q

def kmlaw.snd(p: W.W64 & W.W64) -> W.W64:
  (q, r) = p
  r

# 64-bit division, for every input (unsigned): for a divisor d not 0, the
# quotient q and remainder r are the Nat ones, n = q d + r with r < d; the
# quotient alone is the q of the pair; rounding up gives the least multiple
# count, n <= q' d < n + d; by 0, the quotient is 0 and the remainder n (as
# word64's division)

law div_u64_rem_value:
  for +n: W.W64
  for +d: U32
  for h: {U32.is_zero(d) == False{} : Bool}
  {Nat.add(Nat.mul(W.W64.to_nat(kmlaw.q(D.KMath.div_u64_rem(n, d))), U32.to_nat(d)), U32.to_nat(kmlaw.r(D.KMath.div_u64_rem(n, d)))) == W.W64.to_nat(n) : Nat}

law div_u64_rem_lt:
  for +n: W.W64
  for +d: U32
  for h: {U32.is_zero(d) == False{} : Bool}
  {Nat.is_lt(U32.to_nat(kmlaw.r(D.KMath.div_u64_rem(n, d))), U32.to_nat(d)) == True{} : Bool}

law div_u64_q:
  for +n: W.W64
  for +d: U32
  {D.KMath.div_u64(n, d) == kmlaw.q(D.KMath.div_u64_rem(n, d)) : W.W64}

law div_u64_rem_zero:
  for +n: W.W64
  {D.KMath.div_u64_rem(n, 0) == D.KDiv64{W.W64.zero(), W.W64.lo(n)} : D.KDiv64}

law div64_u64_rem_value:
  for +n: W.W64
  for +d: W.W64
  for h: {W.W64.is_zero(d) == False{} : Bool}
  {Nat.add(Nat.mul(W.W64.to_nat(kmlaw.fst(D.KMath.div64_u64_rem(n, d))), W.W64.to_nat(d)), W.W64.to_nat(kmlaw.snd(D.KMath.div64_u64_rem(n, d)))) == W.W64.to_nat(n) : Nat}

law div64_u64_rem_lt:
  for +n: W.W64
  for +d: W.W64
  for h: {W.W64.is_zero(d) == False{} : Bool}
  {Nat.is_lt(W.W64.to_nat(kmlaw.snd(D.KMath.div64_u64_rem(n, d))), W.W64.to_nat(d)) == True{} : Bool}

law div64_u64_q:
  for +n: W.W64
  for +d: W.W64
  {D.KMath.div64_u64(n, d) == kmlaw.fst(D.KMath.div64_u64_rem(n, d)) : W.W64}

law div64_u64_rem_zero:
  for +n: W.W64
  {D.KMath.div64_u64_rem(n, W.W64.zero()) == (W.W64.zero(), n) : W.W64 & W.W64}

law div64_round_up_le:
  for +n: W.W64
  for +d: W.W64
  for h: {W.W64.is_zero(d) == False{} : Bool}
  {Nat.is_le(W.W64.to_nat(n), Nat.mul(W.W64.to_nat(D.KMath.div64_u64_round_up(n, d)), W.W64.to_nat(d))) == True{} : Bool}

law div64_round_up_lt:
  for +n: W.W64
  for +d: W.W64
  for h: {W.W64.is_zero(d) == False{} : Bool}
  {Nat.is_lt(Nat.mul(W.W64.to_nat(D.KMath.div64_u64_round_up(n, d)), W.W64.to_nat(d)), Nat.add(W.W64.to_nat(n), W.W64.to_nat(d))) == True{} : Bool}
