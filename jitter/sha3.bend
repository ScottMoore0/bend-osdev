# The jitter core with its named default conditioner: SHA3-256, crypto's
# hash instance (inst_sha3.bend; block size 136, the SHA3-256 rate). Each
# def is the one of jitter.bend with the hash filled in.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../crypto/inst_sha3.bend as S3
import ./jitter.bend as J

def JitSha3.init(+p: J.JitParams) -> J.JitState<S3.CrSha3State>:
  J.Jitter.init(~S3.CrSha3State, ~S3.CrSha3.init(), p)

def JitSha3.absorb(+p: J.JitParams, st: J.JitState<S3.CrSha3State>, +d: W.W64) -> J.JitState<S3.CrSha3State>:
  J.Jitter.absorb(~S3.CrSha3State, ~136n, ~S3.CrSha3.update, ~S3.CrSha3.sha3_256, p, st, d)

def JitSha3.absorb_all(+p: J.JitParams, st: J.JitState<S3.CrSha3State>, ds: List<&2, W.W64>) -> J.JitState<S3.CrSha3State>:
  J.Jitter.absorb_all(~S3.CrSha3State, ~136n, ~S3.CrSha3.update, ~S3.CrSha3.sha3_256, p, st, ds)

def JitSha3.block(+p: J.JitParams, +st: J.JitState<S3.CrSha3State>) -> Result<&2, &2, J.JitError, J.JitBlock<S3.CrSha3State>>:
  J.Jitter.block(~S3.CrSha3State, ~S3.CrSha3.init(), ~S3.CrSha3.update, ~S3.CrSha3.final, p, st)

def JitSha3.read(+p: J.JitParams, +st: J.JitState<S3.CrSha3State>, ds: List<&2, W.W64>, +n: Nat) -> Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>:
  J.Jitter.read(~S3.CrSha3State, ~136n, ~S3.CrSha3.init(), ~S3.CrSha3.update, ~S3.CrSha3.final, ~S3.CrSha3.sha3_256, p, st, ds, n)

def JitSha3.generate(+p: J.JitParams, ds: List<&2, W.W64>, +n: Nat) -> Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>:
  J.Jitter.generate(~S3.CrSha3State, ~136n, ~S3.CrSha3.init(), ~S3.CrSha3.update, ~S3.CrSha3.final, ~S3.CrSha3.sha3_256, p, ds, n)
