# bend-osdev-kmath's laws of the number of bits (KMath.fls, reciprocal.bend),
# for every input. Proved in PROOF_fls.bend.
import Base
import ../u32/u32.bend as U
import ./reciprocal.bend as R

# The number of bits (fls): every x is below 2^fls(x), a nonzero x is at
# least 2^(fls(x) - 1), and fls(x) is at most 32

law fls_lt:
  for +x: U32
  {Nat.is_lt(U32.to_nat(x), U.U32Nat.dbl(R.KMath.fls(x), 1n)) == True{} : Bool}

law fls_le:
  for +x: U32
  for h: {U32.is_zero(x) == False{} : Bool}
  {Nat.is_le(U.U32Nat.dbl(R.KMath.fls(x), 1n), Nat.double(U32.to_nat(x))) == True{} : Bool}

law fls_bound:
  for +x: U32
  {Nat.is_le(R.KMath.fls(x), 32n) == True{} : Bool}
