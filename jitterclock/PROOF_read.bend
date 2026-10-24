import Base
import ../word64/word64.bend as W
import ../crypto/inst_sha3.bend as S3
import ../jitter/jitter.bend as J
import ../jitter/sha3.bend as JS
import ../jitter/LAWS_constant.bend as JL
import ../jitter/PROOF_constant.bend as JP
import ./time.bend as T
import ./LAWS_read.bend as Laws

# a stopped clock's deltas are all the same
def stopped(m: Nat, +t: W.W64) -> {T.JClock.time.deltas.from(List.replicate(W.W64, m, t), t) == List.replicate(W.W64, m, W.W64.sub(t, t)) : List<&2, W.W64>}:
  match m:
    case 0n:
      {==}
    case 1n+ +q:
      Equal.cong(List<&2, W.W64>, List<&2, W.W64>, z => Con{W.W64.sub(t, t), z}, T.JClock.time.deltas.from(List.replicate(W.W64, q, t), t), List.replicate(W.W64, q, W.W64.sub(t, t)), stopped(q, t))

def Laws.stopped_clock(t):
  %Equal.sym(List<&2, W.W64>, T.JClock.time.deltas.from(List.replicate(W.W64, T.JClock.time.budget(J.JitParams.default(), 32n), t), t), List.replicate(W.W64, T.JClock.time.budget(J.JitParams.default(), 32n), W.W64.sub(t, t)), stopped(T.JClock.time.budget(J.JitParams.default(), 32n), t)) : {JS.JitSha3.generate(J.JitParams.default(), _, 32n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>}
  JL.constant_fails_default(~S3.CrSha3State, ~136n, ~S3.CrSha3.init(), ~S3.CrSha3.update, ~S3.CrSha3.final, ~S3.CrSha3.sha3_256, W.W64.sub(t, t), T.JClock.time.budget(J.JitParams.default(), 32n), 31n, {==})
