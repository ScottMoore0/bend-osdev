import Base
import ../word64/word64.bend as W
import ./timer.bend as T
import ./timerqueue.bend as Q

def show(xs: List<&2, T.TqTimer>) -> String:
  match xs:
    case Nil{}:
      "-"
    case Con{+x, Nil{}}:
      W.W64.show(T.TqTimer.expiry(x)) ++ "#" ++ Nat.show(T.TqTimer.id(x))
    case Con{+x, t}:
      W.W64.show(T.TqTimer.expiry(x)) ++ "#" ++ Nat.show(T.TqTimer.id(x)) ++ " " ++ show(t)

def next(m: Maybe<&2, W.W64>) -> String:
  match m:
    case None{}:
      "none"
    case Some{t}:
      W.W64.show(t)

def at(x: U32) -> W.W64:
  W.W64.from_u32(x)

def main() -> IO(Unit):
  +a = Q.TimerQueueList.add(Q.TimerQueueList.new(), at(30))
  +b = Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, a), at(10))
  +c = Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, b), at(20))
  +d = Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, c), at(10))
  +e = Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, d), W.W64.from_parts(1, 0))
  +q = Q.TqAdded.queue(List<&2, T.TqTimer>, e)
  +q1 = Q.TimerQueueList.delete(q, Q.TqAdded.timer(List<&2, T.TqTimer>, c))
  +r = Q.TimerQueueList.expire(q1, at(15))
  +q2 = Q.TqExpired.queue(List<&2, T.TqTimer>, r)
  +r2 = Q.TimerQueueList.expire(q2, at(4294967295))
  +q3 = Q.TqExpired.queue(List<&2, T.TqTimer>, r2)
  do IO<Unit>:
    IO.print("pending: " ++ show(Q.TimerQueueList.pending(q)))
    IO.print("next: " ++ next(Q.TimerQueueList.next_expiry(q)))
    IO.print("after deleting 20#2: " ++ show(Q.TimerQueueList.pending(q1)))
    IO.print("expired at 15: " ++ show(Q.TqExpired.fired(List<&2, T.TqTimer>, r)))
    IO.print("left: " ++ show(Q.TimerQueueList.pending(q2)) ++ ", next " ++ next(Q.TimerQueueList.next_expiry(q2)))
    IO.print("expired at 2^32 - 1: " ++ show(Q.TqExpired.fired(List<&2, T.TqTimer>, r2)))
    IO.print("left: " ++ show(Q.TimerQueueList.pending(q3)))
    IO.print("expired at 2^32: " ++ show(Q.TqExpired.fired(List<&2, T.TqTimer>, Q.TimerQueueList.expire(q3, W.W64.from_parts(1, 0)))))
    IO.print("empty: " ++ next(Q.TimerQueueList.next_expiry(Q.TimerQueueList.new())))

#|pending: 10#1 10#3 20#2 30#0 4294967296#4
#|next: 10
#|after deleting 20#2: 10#1 10#3 30#0 4294967296#4
#|expired at 15: 10#1 10#3
#|left: 30#0 4294967296#4, next 30
#|expired at 2^32 - 1: 30#0
#|left: 4294967296#4
#|expired at 2^32: 4294967296#4
#|empty: none
