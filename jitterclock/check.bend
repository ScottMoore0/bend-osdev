# A runnable check of the clock and of reading through it. The clock's
# values differ from run to run, so this prints only what must hold:
# stamps never go back, the deltas are positive and vary, a read gives the
# bytes asked for, and two reads differ.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../jitter/jitter.bend as J
import ./time.bend as T
import ./jitterclock.bend as C

# no delta has its top bit set: no stamp is below the one before
def forward(ds: List<&2, W.W64>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      Bool.and(U32.is_lt(W.W64.hi(d), 2147483648), forward(t))

def positive(ds: List<&2, W.W64>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      Bool.and(Bool.not(W.W64.is_zero(d)), positive(t))

# some delta differs from the first
def varies.go(+a: W.W64, ds: List<&2, W.W64>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      Bool.or(Bool.not(W.W64.is_eq(a, d)), varies.go(a, t))

def varies(ds: List<&2, W.W64>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      varies.go(d, t)

def len32(r: Result<&2, &2, J.JitError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "failed"
    case Done{o}:
      Nat.show(B.Octets.len(o)) ++ " bytes"

def differ(a: Result<&2, &2, J.JitError, B.Octets>, b: Result<&2, &2, J.JitError, B.Octets>) -> String:
  match a b:
    case Done{x} Done{y}:
      Bool.show(Bool.not(B.Octets.is_eq(x, y)))
    case _ _:
      "failed"

def stamps(+ts: List<&2, W.W64>) -> IO(Unit):
  do IO<Unit>:
    IO.print("1000 stamps, never back: " ++ Bool.show(forward(T.JClock.time.deltas(ts))))

def deltas(+ds: List<&2, W.W64>) -> IO(Unit):
  do IO<Unit>:
    IO.print("1000 deltas, all above 0: " ++ Bool.show(positive(ds)) ++ ", not all equal: " ++ Bool.show(varies(ds)))

def reads(+a: Result<&2, &2, J.JitError, B.Octets>, b: Result<&2, &2, J.JitError, B.Octets>) -> IO(Unit):
  do IO<Unit>:
    IO.print("a read of 32 bytes: " ++ len32(a) ++ "; two reads differ: " ++ differ(a, b))

def main() -> IO(Unit):
  do IO<Unit>:
    ts : List<&2, W.W64> <- C.JClock.stamps(1000n)
    stamps(ts)
    ds : List<&2, W.W64> <- C.JClock.deltas(1000n)
    deltas(ds)
    a : Result<&2, &2, J.JitError, B.Octets> <- C.JClock.read(J.JitParams.default(), 32n)
    b : Result<&2, &2, J.JitError, B.Octets> <- C.JClock.read(J.JitParams.default(), 32n)
    reads(a, b)
    r : Result<&2, &2, J.JitError, B.Octets> <- C.JClock.read(J.JitParams.default(), 100n)
    IO.print("a read of 100 bytes: " ++ len32(r))

#|1000 stamps, never back: True
#|1000 deltas, all above 0: True, not all equal: True
#|a read of 32 bytes: 32 bytes; two reads differ: True
#|a read of 100 bytes: 100 bytes
