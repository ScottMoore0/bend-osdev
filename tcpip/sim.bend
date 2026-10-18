# A simulated network of two TCP endpoints, A and B, for tests: a wire that
# delivers, loses or holds segments as a script says, a clock, and a host
# that keeps the timers each connection asks for and fires them when due.
#
# The trace (one line per event) shows each event, the state after it, and
# the actions; ref/gen.py's independent model prints the same trace.
import Base
import ../bytes/bytes.bend as B
import ./seq.bend as S
import ./segment.bend as G
import ./tcp.bend as T
import ./cc.bend as CC
import ./show.bend as W

# One endpoint: its options, connection, the host's timers, and the ISN it
# opens with
type TcpSimSide<-C: Data> is Data:
  TcpSimSide{opts: T.TcpOptions, conn: T.TcpConn<C>, rtx: Maybe<&2, U32>, tw: Maybe<&2, U32>, isn: U32}

# the endpoints, the segments in flight to each, the clock, and the trace
# (newest line first)
type TcpSim<-C: Data> is Data:
  TcpSim{a: TcpSimSide<C>, b: TcpSimSide<C>, to_a: List<&2, G.TcpSeg>, to_b: List<&2, G.TcpSeg>, now: U32, log: List<&2, String>}

# side: True for A
type TcpSimCmd is Data:
  # an application call
  TcpSimCall{side: Bool, ev: T.TcpEvent}
  # the first segment in flight to side arrives
  TcpSimDeliver{side: Bool}
  # the first segment in flight to side is lost
  TcpSimDrop{side: Bool}
  # ms milliseconds pass; due timers fire, A's first
  TcpSimTick{ms: U32}
  # everything in flight arrives, one segment to B then one to A, until
  # nothing is in flight (at most 64 rounds)
  TcpSimFlush{}

def TcpSim.side(+s: Bool) -> String:
  match s:
    case True{}:
      "A"
    case False{}:
      "B"

def TcpSim.event(e: T.TcpEvent) -> String:
  match e:
    case T.TcpCallOpen{a}:
      match a:
        case True{}:
          "open active"
        case False{}:
          "open passive"
    case T.TcpCallSend{d}:
      "send " ++ B.Octets.to_string(d)
    case T.TcpCallRead{n}:
      "read " ++ U32.show(n)
    case T.TcpCallClose{}:
      "close"
    case T.TcpCallAbort{}:
      "abort"
    case T.TcpArrive{s}:
      "recv " ++ W.TcpShow.seg(s)
    case T.TcpFire{t}:
      "fire " ++ W.TcpShow.timer(t)

# the host's timers after the actions
type TcpSimTimers is Data:
  TcpSimTimers{rtx: Maybe<&2, U32>, tw: Maybe<&2, U32>}

def TcpSim.timers(xs: List<&2, T.TcpAction>, rtx: Maybe<&2, U32>, tw: Maybe<&2, U32>) -> TcpSimTimers:
  match xs:
    case Nil{}:
      TcpSimTimers{rtx, tw}
    case Con{T.TcpSetTimer{T.TcpTimerRtx{}, at}, t}:
      TcpSim.timers(t, Some{at}, tw)
    case Con{T.TcpSetTimer{T.TcpTimerTimeWait{}, at}, t}:
      TcpSim.timers(t, rtx, Some{at})
    case Con{T.TcpStopTimer{T.TcpTimerRtx{}}, t}:
      TcpSim.timers(t, None{}, tw)
    case Con{T.TcpStopTimer{T.TcpTimerTimeWait{}}, t}:
      TcpSim.timers(t, rtx, None{})
    case Con{h, t}:
      TcpSim.timers(t, rtx, tw)

def TcpSim.outs(xs: List<&2, T.TcpAction>, acc: List<&2, G.TcpSeg>) -> List<&2, G.TcpSeg>:
  match xs:
    case Nil{}:
      acc
    case Con{T.TcpOut{s}, t}:
      TcpSim.outs(t, List.append(&2, G.TcpSeg, acc, [s]))
    case Con{h, t}:
      TcpSim.outs(t, acc)

def TcpSim.line(+now: U32, +side: Bool, +ev: T.TcpEvent, -C: Data, +c: T.TcpConn<C>, +acts: List<&2, T.TcpAction>) -> String:
  "t=" ++ U32.show(now) ++ " " ++ TcpSim.side(side) ++ " " ++ TcpSim.event(ev) ++ " => " ++ T.TcpState.name(T.TcpConn.state(C, c)) ++ W.TcpShow.actions(acts, "")

def TcpSim.now(-C: Data, s: TcpSim<C>) -> U32:
  match s:
    case TcpSim{a, b, to_a, to_b, now, log}:
      now

def TcpSim.get(-C: Data, side: Bool, s: TcpSim<C>) -> TcpSimSide<C>:
  match side:
    case True{}:
      match s:
        case TcpSim{a, b, to_a, to_b, now, log}:
          a
    case False{}:
      match s:
        case TcpSim{a, b, to_a, to_b, now, log}:
          b

def TcpSim.put(-C: Data, side: Bool, me: TcpSimSide<C>, +line: String, outs: List<&2, G.TcpSeg>, s: TcpSim<C>) -> TcpSim<C>:
  match side:
    case True{}:
      match s:
        case TcpSim{a, b, to_a, to_b, now, log}:
          TcpSim{me, b, to_a, List.append(&2, G.TcpSeg, to_b, outs), now, Con{line, log}}
    case False{}:
      match s:
        case TcpSim{a, b, to_a, to_b, now, log}:
          TcpSim{a, me, List.append(&2, G.TcpSeg, to_a, outs), to_b, now, Con{line, log}}

def TcpSim.me(-C: Data, opts: T.TcpOptions, c: T.TcpConn<C>, isn: U32, t: TcpSimTimers) -> TcpSimSide<C>:
  match t:
    case TcpSimTimers{r, w}:
      TcpSimSide{opts, c, r, w, isn}

def TcpSim.after(-C: Data, +side: Bool, +ev: T.TcpEvent, +opts: T.TcpOptions, +isn: U32, rtx: Maybe<&2, U32>, tw: Maybe<&2, U32>, +s: TcpSim<C>, r: Pair(T.TcpConn<C>, List<&2, T.TcpAction>)) -> TcpSim<C>:
  match r:
    case (+c, +acts):
      TcpSim.put(C, side, TcpSim.me(C, opts, c, isn, TcpSim.timers(acts, rtx, tw)), TcpSim.line(TcpSim.now(C, s), side, ev, C, c, acts), TcpSim.outs(acts, Nil{}), s)

# side steps with ev at the simulated time
def TcpSim.step.go(~C: Data, ~cc: CC.TcpCc<C>, +side: Bool, +ev: T.TcpEvent, me: TcpSimSide<C>, +s: TcpSim<C>) -> TcpSim<C>:
  match me:
    case TcpSimSide{+opts, conn, rtx, tw, +isn}:
      TcpSim.after(C, side, ev, opts, isn, rtx, tw, s, T.Tcp.step(~C, ~cc, opts, conn, ev, TcpSim.now(C, s), isn))

def TcpSim.step(~C: Data, ~cc: CC.TcpCc<C>, +side: Bool, +ev: T.TcpEvent, +s: TcpSim<C>) -> TcpSim<C>:
  TcpSim.step.go(~C, ~cc, side, ev, TcpSim.get(C, side, s), s)

# the first segment in flight to side, taken off the wire
def TcpSim.pop(-C: Data, side: Bool, s: TcpSim<C>) -> Pair(Maybe<&2, G.TcpSeg>, TcpSim<C>):
  match side:
    case True{}:
      match s:
        case TcpSim{a, b, to_a, to_b, now, log}:
          match to_a:
            case Nil{}:
              (None{}, TcpSim{a, b, Nil{}, to_b, now, log})
            case Con{h, t}:
              (Some{h}, TcpSim{a, b, t, to_b, now, log})
    case False{}:
      match s:
        case TcpSim{a, b, to_a, to_b, now, log}:
          match to_b:
            case Nil{}:
              (None{}, TcpSim{a, b, to_a, Nil{}, now, log})
            case Con{h, t}:
              (Some{h}, TcpSim{a, b, to_a, t, now, log})

def TcpSim.deliver.go(~C: Data, ~cc: CC.TcpCc<C>, +side: Bool, r: Pair(Maybe<&2, G.TcpSeg>, TcpSim<C>)) -> TcpSim<C>:
  match r:
    case (m, +s):
      match m:
        case None{}:
          s
        case Some{seg}:
          TcpSim.step(~C, ~cc, side, T.TcpArrive{seg}, s)

def TcpSim.deliver(~C: Data, ~cc: CC.TcpCc<C>, +side: Bool, s: TcpSim<C>) -> TcpSim<C>:
  TcpSim.deliver.go(~C, ~cc, side, TcpSim.pop(C, side, s))

def TcpSim.note(-C: Data, +line: String, s: TcpSim<C>) -> TcpSim<C>:
  match s:
    case TcpSim{a, b, to_a, to_b, now, log}:
      TcpSim{a, b, to_a, to_b, now, Con{line, log}}

def TcpSim.drop.go(-C: Data, +side: Bool, r: Pair(Maybe<&2, G.TcpSeg>, TcpSim<C>)) -> TcpSim<C>:
  match r:
    case (m, +s):
      match m:
        case None{}:
          s
        case Some{seg}:
          TcpSim.note(C, "t=" ++ U32.show(TcpSim.now(C, s)) ++ " lost to " ++ TcpSim.side(side) ++ ": " ++ W.TcpShow.seg(seg), s)

def TcpSim.drop(-C: Data, +side: Bool, s: TcpSim<C>) -> TcpSim<C>:
  TcpSim.drop.go(C, side, TcpSim.pop(C, side, s))

def TcpSim.pending(-C: Data, s: TcpSim<C>) -> Bool:
  match s:
    case TcpSim{a, b, to_a, to_b, now, log}:
      Bool.not(Bool.and(List.is_empty(&2, G.TcpSeg, to_a), List.is_empty(&2, G.TcpSeg, to_b)))

def TcpSim.flush.go(~C: Data, ~cc: CC.TcpCc<C>, fuel: Nat, more: Bool, +s: TcpSim<C>) -> TcpSim<C>:
  match fuel:
    case 0n:
      s
    case 1n+f:
      match more:
        case False{}:
          s
        case True{}:
          +s2 = TcpSim.deliver(~C, ~cc, True{}, TcpSim.deliver(~C, ~cc, False{}, s))
          TcpSim.flush.go(~C, ~cc, f, TcpSim.pending(C, s2), s2)

def TcpSim.flush(~C: Data, ~cc: CC.TcpCc<C>, +s: TcpSim<C>) -> TcpSim<C>:
  TcpSim.flush.go(~C, ~cc, 64n, TcpSim.pending(C, s), s)

def TcpSim.due(+now: U32, m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{at}:
      S.SeqNum.reached(now, at)

def TcpSim.side.due(-C: Data, +now: U32, me: TcpSimSide<C>) -> Pair(Bool, Bool):
  match me:
    case TcpSimSide{opts, conn, rtx, tw, isn}:
      (TcpSim.due(now, rtx), TcpSim.due(now, tw))

def TcpSim.pick(-C: Data, c: Bool, a: TcpSim<C>, b: TcpSim<C>) -> TcpSim<C>:
  match c:
    case True{}:
      a
    case False{}:
      b

def TcpSim.fire.go(~C: Data, ~cc: CC.TcpCc<C>, +side: Bool, d: Pair(Bool, Bool), +s: TcpSim<C>) -> TcpSim<C>:
  match d:
    case (r, w):
      +s2 = TcpSim.pick(C, r, TcpSim.step(~C, ~cc, side, T.TcpFire{T.TcpTimerRtx{}}, s), s)
      TcpSim.pick(C, w, TcpSim.step(~C, ~cc, side, T.TcpFire{T.TcpTimerTimeWait{}}, s2), s2)

def TcpSim.fire(~C: Data, ~cc: CC.TcpCc<C>, +side: Bool, +s: TcpSim<C>) -> TcpSim<C>:
  TcpSim.fire.go(~C, ~cc, side, TcpSim.side.due(C, TcpSim.now(C, s), TcpSim.get(C, side, s)), s)

def TcpSim.advance(-C: Data, +ms: U32, s: TcpSim<C>) -> TcpSim<C>:
  match s:
    case TcpSim{a, b, to_a, to_b, now, log}:
      TcpSim{a, b, to_a, to_b, U32.add(now, ms), log}

def TcpSim.cmd(~C: Data, ~cc: CC.TcpCc<C>, c: TcpSimCmd, +s: TcpSim<C>) -> TcpSim<C>:
  match c:
    case TcpSimCall{side, ev}:
      TcpSim.step(~C, ~cc, side, ev, s)
    case TcpSimDeliver{side}:
      TcpSim.deliver(~C, ~cc, side, s)
    case TcpSimDrop{side}:
      TcpSim.drop(C, side, s)
    case TcpSimTick{ms}:
      TcpSim.fire(~C, ~cc, False{}, TcpSim.fire(~C, ~cc, True{}, TcpSim.advance(C, ms, s)))
    case TcpSimFlush{}:
      TcpSim.flush(~C, ~cc, s)

def TcpSim.run(~C: Data, ~cc: CC.TcpCc<C>, cs: List<&2, TcpSimCmd>, +s: TcpSim<C>) -> TcpSim<C>:
  match cs:
    case Nil{}:
      s
    case Con{c, t}:
      TcpSim.run(~C, ~cc, t, TcpSim.cmd(~C, ~cc, c, s))

# two endpoints with options oa, ob and ISNs ia, ib, at time 0
def TcpSim.new(~C: Data, ~cc: CC.TcpCc<C>, +oa: T.TcpOptions, +ia: U32, +ob: T.TcpOptions, +ib: U32) -> TcpSim<C>:
  TcpSim{TcpSimSide{oa, T.Tcp.new(~C, ~cc, oa), None{}, None{}, ia}, TcpSimSide{ob, T.Tcp.new(~C, ~cc, ob), None{}, None{}, ib}, Nil{}, Nil{}, 0, Nil{}}

def TcpSim.trace.go(xs: List<&2, String>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      TcpSim.trace.go(t, h ++ "\n" ++ acc)

# the trace, oldest line first, one per line
def TcpSim.trace(-C: Data, s: TcpSim<C>) -> String:
  match s:
    case TcpSim{a, b, to_a, to_b, now, log}:
      TcpSim.trace.go(log, "")

def TcpSim.state(-C: Data, side: Bool, s: TcpSim<C>) -> T.TcpState:
  match side:
    case True{}:
      match s:
        case TcpSim{TcpSimSide{oa, ca, ra, ta, ia}, b, to_a, to_b, now, log}:
          T.TcpConn.state(C, ca)
    case False{}:
      match s:
        case TcpSim{a, TcpSimSide{ob, cb, rb, tb, ib}, to_a, to_b, now, log}:
          T.TcpConn.state(C, cb)
