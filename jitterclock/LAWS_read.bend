# The pure part of JClock.read (jitterclock.bend): the deltas of the
# stamps read, given to jitter's generator. A stopped clock, one that
# reads the same stamp every time, gives deltas that are all the same, so
# a read of 32 bytes under the default parameters fails with JitRctFailure
# rather than running out of deltas (JitNeedMore): the read's budget, 3916
# deltas (budget_default), is at least the RCT's cutoff of 91 (jitter's
# constant_fails_default).
import Base
import ../word64/word64.bend as W
import ../crypto/inst_sha3.bend as S3
import ../jitter/jitter.bend as J
import ../jitter/sha3.bend as JS
import ./time.bend as T

law stopped_clock:
  for +t: W.W64
  {JS.JitSha3.generate(J.JitParams.default(), T.JClock.time.deltas(List.replicate(W.W64, 1n+T.JClock.time.budget(J.JitParams.default(), 32n), t)), 32n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>}
