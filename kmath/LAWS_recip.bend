# bend-osdev-kmath's law of reciprocal division (reciprocal.bend), for every
# input. Proved in PROOF_recip.bend.
import Base
import ./reciprocal.bend as R

# Reciprocal division is exact (Granlund and Montgomery, Theorem 4.2): for
# every a and every d not 0, the multiply and shifts give a / d
law recip_exact:
  for +a: U32
  for +d: U32
  for h: {U32.is_zero(d) == False{} : Bool}
  {R.KRecip.divide(a, R.KRecip.of(d)) == U32.div(a, d) : U32}
