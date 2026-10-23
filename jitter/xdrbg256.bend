# The jitter core with the 2026 design's conditioner filled in: XDRBG-256
# over SHAKE256 (xdrbg.bend with JitXdrbgParams.default(), shake.bend),
# each insertion a buffer of 136 bytes (the SHAKE256 rate) whose auxiliary
# data digest is SHA3-256 (crypto's inst_sha3.bend), as in Müller's section
# 3.1.1. Each def is jitter.bend's JitCore one with the conditioner filled in.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../crypto/inst_sha3.bend as S3
import ./jitter.bend as J
import ./shake.bend as S
import ./xdrbg.bend as X

# the pool before any delta
def JitXdrbg256.pool() -> X.JitXdrbgPool<S.JitShakeState>:
  X.JitXdrbg.init(~S.JitShakeState, ~S.JitShake.init())

# the pool after a delta's buffer
def JitXdrbg256.update(pool: X.JitXdrbgPool<S.JitShakeState>, o: B.Octets) -> X.JitXdrbgPool<S.JitShakeState>:
  X.JitXdrbg.update(~S.JitShakeState, ~S.JitShake.update, pool, o)

# the block step
def JitXdrbg256.take(pool: X.JitXdrbgPool<S.JitShakeState>) -> J.JitTaken<X.JitXdrbgPool<S.JitShakeState>>:
  X.JitXdrbg.take(~S.JitShakeState, ~S.JitShake.init(), ~S.JitShake.update, ~S.JitShake.read, ~X.JitXdrbgParams.default(), pool)

def JitXdrbg256.init(+p: J.JitParams) -> J.JitState<X.JitXdrbgPool<S.JitShakeState>>:
  J.Jitter.init(~X.JitXdrbgPool<S.JitShakeState>, ~JitXdrbg256.pool(), p)

def JitXdrbg256.absorb(+p: J.JitParams, st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>, +d: W.W64) -> J.JitState<X.JitXdrbgPool<S.JitShakeState>>:
  J.Jitter.absorb(~X.JitXdrbgPool<S.JitShakeState>, ~136n, ~JitXdrbg256.update, ~S3.CrSha3.sha3_256, p, st, d)

def JitXdrbg256.absorb_all(+p: J.JitParams, st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>, ds: List<&2, W.W64>) -> J.JitState<X.JitXdrbgPool<S.JitShakeState>>:
  J.Jitter.absorb_all(~X.JitXdrbgPool<S.JitShakeState>, ~136n, ~JitXdrbg256.update, ~S3.CrSha3.sha3_256, p, st, ds)

def JitXdrbg256.block(+p: J.JitParams, +st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>) -> Result<&2, &2, J.JitError, J.JitBlock<X.JitXdrbgPool<S.JitShakeState>>>:
  J.JitCore.block(~X.JitXdrbgPool<S.JitShakeState>, ~JitXdrbg256.take, p, st)

def JitXdrbg256.read(+p: J.JitParams, +st: J.JitState<X.JitXdrbgPool<S.JitShakeState>>, ds: List<&2, W.W64>, +n: Nat) -> Result<&2, &2, J.JitError, J.JitOut<X.JitXdrbgPool<S.JitShakeState>>>:
  J.JitCore.read(~X.JitXdrbgPool<S.JitShakeState>, ~136n, ~JitXdrbg256.update, ~S3.CrSha3.sha3_256, ~JitXdrbg256.take, p, st, ds, n)

def JitXdrbg256.generate(+p: J.JitParams, ds: List<&2, W.W64>, +n: Nat) -> Result<&2, &2, J.JitError, J.JitOut<X.JitXdrbgPool<S.JitShakeState>>>:
  J.JitCore.generate(~X.JitXdrbgPool<S.JitShakeState>, ~136n, ~JitXdrbg256.pool(), ~JitXdrbg256.update, ~S3.CrSha3.sha3_256, ~JitXdrbg256.take, p, ds, n)
