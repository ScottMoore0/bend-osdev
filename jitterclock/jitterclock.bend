# bend-osdev-jitterclock: a clock for the jitter core. It reads a
# nanosecond monotonic clock around a hash loop (each SHA3-256 of the
# previous time stamp), and feeds the deltas to jitter (with SHA3-256 as
# the conditioner) to read random bytes.
#
# The clock read is a library effect, as fileio's are: a foreign def whose
# body imports its C side (jitterclock.c: clock_gettime(CLOCK_MONOTONIC))
# and its JavaScript side (jitterclock.js: process.hrtime.bigint()), so it
# runs natively (bend -o) and on the JavaScript lane (bend file.bend). The
# effect is tested, not proved; the pure parts (time.bend) have laws.
#
# Each read takes the previous hash's first byte as its argument, and each
# hash takes the previous stamp as its input, so the reads and the hashes
# alternate in order: a delta is the time one hash took (with the clock
# read), the noise source the jitter core's domain separator 2 (the hash
# loop) names.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../crypto/inst_sha3.bend as S3
import ../jitter/jitter.bend as J
import ../jitter/sha3.bend as JS
import ./time.bend as T

# The effect: CLOCK_MONOTONIC in nanoseconds, as (high, low); dep orders
# the read after the value it is computed from, and is otherwise unused
def JClock.eff.now(dep: U32) -> IO(U32 & U32):
  import "./jitterclock.c"
  import "./jitterclock.js"

# the clock, as a W64
def JClock.now(dep: U32) -> IO(W.W64):
  do IO<W.W64>:
    p : U32 & U32 <- JClock.eff.now(dep)
    return T.JClock.time.join(p)

def jclock.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      x

# the hash loop's work: SHA3-256 of a stamp; its first byte
def JClock.work(t: W.W64) -> U32:
  jclock.head(B.Octets.to_list(S3.CrSha3.sha3_256(B.Octets.of_list(B.le64(t)))))

def jclock.stamps(n: Nat, +prev: W.W64, acc: List<&2, W.W64>) -> IO(List<&2, W.W64>):
  match n:
    case 0n:
      do IO<List<&2, W.W64>>:
        return List.reverse(&2, W.W64, Con{prev, acc})
    case 1n+m:
      do IO<List<&2, W.W64>>:
        t : W.W64 <- JClock.now(JClock.work(prev))
        jclock.stamps(m, t, Con{prev, acc})

# n stamps, each read after hashing the one before
def JClock.stamps(n: Nat) -> IO(List<&2, W.W64>):
  match n:
    case 0n:
      do IO<List<&2, W.W64>>:
        return Nil{}
    case 1n+m:
      do IO<List<&2, W.W64>>:
        t : W.W64 <- JClock.now(0)
        jclock.stamps(m, t, Nil{})

# n deltas: the times of n hashes
def JClock.deltas(n: Nat) -> IO(List<&2, W.W64>):
  do IO<List<&2, W.W64>>:
    ts : List<&2, W.W64> <- JClock.stamps(1n+n)
    return T.JClock.time.deltas(ts)

def jclock.out(r: Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>) -> Result<&2, &2, J.JitError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Done{J.JitOut.out(~S3.CrSha3State, o)}

# n random bytes: the deltas of T.JClock.time.budget(p, n) hashes, then the
# jitter core from a new state; JitNeedMore if too many deltas were stuck
# (a caller may simply try again), JitRctFailure or JitAptFailure if the
# clock looks stuck
def JClock.read(+p: J.JitParams, +n: Nat) -> IO(Result<&2, &2, J.JitError, B.Octets>):
  do IO<Result<&2, &2, J.JitError, B.Octets>>:
    ds : List<&2, W.W64> <- JClock.deltas(T.JClock.time.budget(p, n))
    return jclock.out(JS.JitSha3.generate(p, ds, n))
