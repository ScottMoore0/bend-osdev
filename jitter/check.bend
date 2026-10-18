# The jitter core on small examples: the default parameters and those for
# osr 1, the stuck test, the two health tests at their cutoffs, bytes from
# a pseudo-random source (the values are ref/model.py's too), a read in two
# parts, a constant source refused, and too few deltas. ref/ compares the
# package with the model on recorded deltas.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../crypto/inst_sha3.bend as S3
import ./stuck.bend as Sk
import ./health.bend as Ht
import ./jitter.bend as J
import ./sha3.bend as JS

def why(e: J.JitError) -> String:
  match e:
    case J.JitRctFailure{}:
      "RCT failure"
    case J.JitAptFailure{}:
      "APT failure"
    case J.JitNotEnough{h, n}:
      "not enough deltas: " ++ Nat.show(h) ++ " of " ++ Nat.show(n)
    case J.JitNeedMore{h}:
      "need more deltas (" ++ Nat.show(h) ++ " bytes so far)"

def show(r: Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>) -> String:
  match r:
    case Fail{e}:
      why(e)
    case Done{o}:
      match o:
        case J.JitOut{out, st, rest}:
          B.Octets.hex(out) ++ " (" ++ Nat.show(List.length(&2, W.W64, rest)) ++ " deltas left)"

# a pseudo-random source: 100 + the top 6 bits of an LCG
def lcg(n: Nat, +s: U32) -> List<&2, W.W64>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1664525), 1013904223)
      Con{W.W64.from_u32(U32.add(100, U32.and(U32.shrn(s2, 24n), 63))), lcg(p, s2)}

def w(n: U32) -> W.W64:
  W.W64.from_u32(n)

def params(p: J.JitParams) -> String:
  match p:
    case J.JitParams{o, s, rc, aw, ac, d, pr}:
      "osr " ++ Nat.show(o) ++ ", safety " ++ Nat.show(s) ++ ", RCT cutoff " ++ Nat.show(rc) ++ ", APT cutoff " ++ Nat.show(ac) ++ " of " ++ Nat.show(aw) ++ ", domain " ++ U32.show(d) ++ ", discard " ++ Nat.show(pr)

# the second read, from where the first left off
def again(+p: J.JitParams, r: Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>) -> String:
  match r:
    case Fail{e}:
      why(e)
    case Done{o}:
      match o:
        case J.JitOut{out, st, rest}:
          B.Octets.hex(out) ++ " then " ++ show(JS.JitSha3.read(p, st, rest, 16n))

def main() -> IO(Unit):
  +p = J.JitParams.default()
  +s57 = Sk.JitStuck.next(Sk.JitStuck.next(Sk.JitStuck.new(), w(5)), w(7))
  +ds = lcg(2000n, 7)
  +cst = J.Jitter.absorb_all(~S3.CrSha3State, ~136n, ~S3.CrSha3.update, ~S3.CrSha3.sha3_256, p, JS.JitSha3.init(p), List.replicate(W.W64, 50n, w(1000)))
  do IO<Unit>:
    IO.print("default: " ++ params(p) ++ "; " ++ Nat.show(J.JitParams.need(p)) ++ " counted deltas per block")
    IO.print("osr 1: " ++ params(J.JitParams.for_osr(1n)))
    IO.print("stuck after 5, 7: 9 " ++ Bool.show(Sk.JitStuck.is_stuck(s57, w(9))) ++ ", 10 " ++ Bool.show(Sk.JitStuck.is_stuck(s57, w(10))) ++ ", 7 " ++ Bool.show(Sk.JitStuck.is_stuck(s57, w(7))) ++ ", 0 " ++ Bool.show(Sk.JitStuck.is_stuck(s57, w(0))))
    IO.print("RCT, cutoff 91: 91 equal deltas fail " ++ Bool.show(Ht.JitRct.failed(Ht.JitRct.run(91n, Ht.JitRct.new(), List.replicate(W.W64, 91n, w(3))))) ++ ", 90 " ++ Bool.show(Ht.JitRct.failed(Ht.JitRct.run(91n, Ht.JitRct.new(), List.replicate(W.W64, 90n, w(3))))))
    IO.print("APT, 459 of 512: 459 equal deltas fail " ++ Bool.show(Ht.JitApt.failed(Ht.JitApt.run(512n, 459n, Ht.JitApt.new(), List.replicate(W.W64, 459n, w(3))))) ++ ", 458 " ++ Bool.show(Ht.JitApt.failed(Ht.JitApt.run(512n, 459n, Ht.JitApt.new(), List.replicate(W.W64, 458n, w(3))))))
    IO.print("32 bytes from 2000 LCG deltas: " ++ show(JS.JitSha3.generate(p, ds, 32n)))
    IO.print("16 bytes, then 16 more: " ++ again(p, JS.JitSha3.generate(p, lcg(3000n, 7), 16n)))
    IO.print("50 equal deltas: " ++ Nat.show(J.Jitter.count(~S3.CrSha3State, cst)) ++ " counted, a block can be taken: " ++ Bool.show(J.Jitter.can_block(~S3.CrSha3State, p, cst)))
    IO.print("a constant source: " ++ show(JS.JitSha3.generate(p, List.replicate(W.W64, 2000n, w(1000)), 32n)))
    IO.print("500 deltas: " ++ show(JS.JitSha3.generate(p, lcg(500n, 1), 32n)))

#|default: osr 3, safety 65, RCT cutoff 91, APT cutoff 459 of 512, domain 2, discard 1; 963 counted deltas per block
#|osr 1: osr 1, safety 65, RCT cutoff 31, APT cutoff 325 of 512, domain 2, discard 1
#|stuck after 5, 7: 9 True, 10 False, 7 True, 0 True
#|RCT, cutoff 91: 91 equal deltas fail True, 90 False
#|APT, 459 of 512: 459 equal deltas fail True, 458 False
#|32 bytes from 2000 LCG deltas: 65f5bfe91837721c06f02673ecd0b6c618d60f5cb8cb62ce6e66b3eb4f8c975b (21 deltas left)
#|16 bytes, then 16 more: 65f5bfe91837721c06f02673ecd0b6c6 then 1c39a33e6ccf2acc54915998694e041a (34 deltas left)
#|50 equal deltas: 1 counted, a block can be taken: False
#|a constant source: RCT failure
#|500 deltas: need more deltas (0 bytes so far)
