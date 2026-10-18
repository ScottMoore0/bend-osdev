# A sample of the noise source: one time delta, a W64. The health tests and
# the stuck test compare samples; two samples are equal when both of their
# 32-bit halves are (word64's public halves), so that the laws can use the
# equality of a U32 with itself rather than anything inside W64.
import Base
import ../word64/word64.bend as W

def JitSample.eq(+a: W.W64, +b: W.W64) -> Bool:
  Bool.and(U32.is_eq(W.W64.lo(a), W.W64.lo(b)), U32.is_eq(W.W64.hi(a), W.W64.hi(b)))
