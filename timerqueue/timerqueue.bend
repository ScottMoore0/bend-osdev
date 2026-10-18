# bend-osdev-timerqueue: timers keyed by expiry, as a pure state machine.
#
# A timer queue holds timers, each an expiry time (a W64, in the caller's
# unit) and an id the queue hands out in the order timers are added. It
# adds a timer, deletes one, tells the next expiry, and expires every timer
# due by a time: TimerQueue.expire(q, now) answers the timers with expiry at
# or before now, in order (by expiry, ties by insertion order), and the
# queue without them. Time is passed in, never read.
#
# The timers are kept in a store (store.bend) taken as a template argument
# (~Q, ~st): any priority queue or ordered map with the six TqStore calls.
# TimerQueueList.* is the named default, on the sorted list of sorted.bend.
#
# A timer carries no payload: the caller keeps what a timer is for under
# its id (in an IDR from bend-osdev-idalloc, say), and a fired timer's id
# finds it.
import Base
import ../word64/word64.bend as W
import ./timer.bend as T
import ./store.bend as S
import ./sorted.bend as L

type TimerQueue<-Q: Data> is Data:
  TimerQueue{store: Q, next: Nat}

# what an add answers: the queue with the timer, and the timer (its handle,
# for delete)
type TqAdded<-Q: Data> is Data:
  TqAdded{queue: TimerQueue<Q>, timer: T.TqTimer}

# what an expiry answers: the queue without the timers that fired, and those
# timers, in order
type TqExpired<-Q: Data> is Data:
  TqExpired{queue: TimerQueue<Q>, fired: List<&2, T.TqTimer>}

def TqAdded.queue(-Q: Data, r: TqAdded<Q>) -> TimerQueue<Q>:
  match r:
    case TqAdded{q, x}:
      q

def TqAdded.timer(-Q: Data, r: TqAdded<Q>) -> T.TqTimer:
  match r:
    case TqAdded{q, x}:
      x

def TqExpired.queue(-Q: Data, r: TqExpired<Q>) -> TimerQueue<Q>:
  match r:
    case TqExpired{q, xs}:
      q

def TqExpired.fired(-Q: Data, r: TqExpired<Q>) -> List<&2, T.TqTimer>:
  match r:
    case TqExpired{q, xs}:
      xs

# the id the next timer added gets
def TimerQueue.next_id(-Q: Data, tq: TimerQueue<Q>) -> Nat:
  match tq:
    case TimerQueue{q, n}:
      n

# whether x was handed out by this queue (or an earlier state of it)
def TimerQueue.issued(-Q: Data, tq: TimerQueue<Q>, x: T.TqTimer) -> Bool:
  Nat.is_lt(T.TqTimer.id(x), TimerQueue.next_id(Q, tq))

def TimerQueue.new(~Q: Data, ~st: S.TqStore<Q>) -> TimerQueue<Q>:
  TimerQueue{S.TqStore.empty(~Q, ~st), 0n}

# the timers held, in order
def TimerQueue.pending(~Q: Data, ~st: S.TqStore<Q>, tq: TimerQueue<Q>) -> List<&2, T.TqTimer>:
  match tq:
    case TimerQueue{q, n}:
      S.TqStore.timers(~Q, ~st, q)

def TimerQueue.contains(~Q: Data, ~st: S.TqStore<Q>, tq: TimerQueue<Q>, +x: T.TqTimer) -> Bool:
  T.TqTimer.member(TimerQueue.pending(~Q, ~st, tq), x)

# a timer expiring at expiry, with the next id (timerqueue_add)
def TimerQueue.add(~Q: Data, ~st: S.TqStore<Q>, tq: TimerQueue<Q>, +expiry: W.W64) -> TqAdded<Q>:
  match tq:
    case TimerQueue{q, +n}:
      TqAdded{TimerQueue{S.TqStore.insert(~Q, ~st, q, T.TqTimer{expiry, n}), 1n+n}, T.TqTimer{expiry, n}}

# the queue without x (timerqueue_del); a timer not held changes nothing
def TimerQueue.delete(~Q: Data, ~st: S.TqStore<Q>, tq: TimerQueue<Q>, x: T.TqTimer) -> TimerQueue<Q>:
  match tq:
    case TimerQueue{q, n}:
      TimerQueue{S.TqStore.remove(~Q, ~st, q, x), n}

def TimerQueue.first_expiry(m: Maybe<&2, T.TqTimer>) -> Maybe<&2, W.W64>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{T.TqTimer.expiry(x)}

# the earliest expiry, if any timer is held (timerqueue_getnext)
def TimerQueue.next_expiry(~Q: Data, ~st: S.TqStore<Q>, tq: TimerQueue<Q>) -> Maybe<&2, W.W64>:
  match tq:
    case TimerQueue{q, n}:
      TimerQueue.first_expiry(S.TqStore.first(~Q, ~st, q))

# Expiring: take first timers while they are due. The fuel is the number of
# timers held, so the loop never runs short.

type TqSplit<-Q: Data> is Data:
  TqSplit{fired: List<&2, T.TqTimer>, store: Q}

def TqSplit.fired(-Q: Data, r: TqSplit<Q>) -> List<&2, T.TqTimer>:
  match r:
    case TqSplit{xs, q}:
      xs

def TqSplit.store(-Q: Data, r: TqSplit<Q>) -> Q:
  match r:
    case TqSplit{xs, q}:
      q

def TimerQueue.expire.cons(-Q: Data, x: T.TqTimer, +r: TqSplit<Q>) -> TqSplit<Q>:
  TqSplit{Con{x, TqSplit.fired(Q, r)}, TqSplit.store(Q, r)}

def TimerQueue.expire.due(m: Maybe<&2, T.TqTimer>, +now: W.W64) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      T.TqTime.le(T.TqTimer.expiry(x), now)

def TimerQueue.expire.go(~Q: Data, ~st: S.TqStore<Q>, fuel: Nat, m: Maybe<&2, T.TqTimer>, due: Bool, +q: Q, +now: W.W64) -> TqSplit<Q>:
  match fuel:
    case 0n:
      TqSplit{Nil{}, q}
    case 1n+f:
      match m:
        case None{}:
          TqSplit{Nil{}, q}
        case Some{x}:
          match due:
            case False{}:
              TqSplit{Nil{}, q}
            case True{}:
              +q1 = S.TqStore.drop_first(~Q, ~st, q)
              +m1 = S.TqStore.first(~Q, ~st, q1)
              TimerQueue.expire.cons(Q, x, TimerQueue.expire.go(~Q, ~st, f, m1, TimerQueue.expire.due(m1, now), q1, now))

def TimerQueue.expire.split(~Q: Data, ~st: S.TqStore<Q>, +q: Q, +now: W.W64) -> TqSplit<Q>:
  +m = S.TqStore.first(~Q, ~st, q)
  TimerQueue.expire.go(~Q, ~st, List.length(&2, T.TqTimer, S.TqStore.timers(~Q, ~st, q)), m, TimerQueue.expire.due(m, now), q, now)

# every timer due by now, in order, and the queue without them (the loop of
# timerqueue_getnext and timerqueue_del that a timer interrupt runs)
def TimerQueue.expire(~Q: Data, ~st: S.TqStore<Q>, tq: TimerQueue<Q>, +now: W.W64) -> TqExpired<Q>:
  match tq:
    case TimerQueue{q, n}:
      +r = TimerQueue.expire.split(~Q, ~st, q, now)
      TqExpired{TimerQueue{TqSplit.store(Q, r), n}, TqSplit.fired(Q, r)}

# The named default: the sorted list of sorted.bend

def TimerQueueList.new() -> TimerQueue<List<&2, T.TqTimer>>:
  TimerQueue.new(~List<&2, T.TqTimer>, ~L.TqSorted.store())

def TimerQueueList.add(tq: TimerQueue<List<&2, T.TqTimer>>, +expiry: W.W64) -> TqAdded<List<&2, T.TqTimer>>:
  TimerQueue.add(~List<&2, T.TqTimer>, ~L.TqSorted.store(), tq, expiry)

def TimerQueueList.delete(tq: TimerQueue<List<&2, T.TqTimer>>, x: T.TqTimer) -> TimerQueue<List<&2, T.TqTimer>>:
  TimerQueue.delete(~List<&2, T.TqTimer>, ~L.TqSorted.store(), tq, x)

def TimerQueueList.next_expiry(tq: TimerQueue<List<&2, T.TqTimer>>) -> Maybe<&2, W.W64>:
  TimerQueue.next_expiry(~List<&2, T.TqTimer>, ~L.TqSorted.store(), tq)

def TimerQueueList.expire(tq: TimerQueue<List<&2, T.TqTimer>>, +now: W.W64) -> TqExpired<List<&2, T.TqTimer>>:
  TimerQueue.expire(~List<&2, T.TqTimer>, ~L.TqSorted.store(), tq, now)

def TimerQueueList.pending(tq: TimerQueue<List<&2, T.TqTimer>>) -> List<&2, T.TqTimer>:
  TimerQueue.pending(~List<&2, T.TqTimer>, ~L.TqSorted.store(), tq)

def TimerQueueList.contains(tq: TimerQueue<List<&2, T.TqTimer>>, +x: T.TqTimer) -> Bool:
  TimerQueue.contains(~List<&2, T.TqTimer>, ~L.TqSorted.store(), tq, x)

# the invariant every queue these defs build keeps: the timers in order,
# and every id below the next
def TimerQueueList.valid(tq: TimerQueue<List<&2, T.TqTimer>>) -> Bool:
  match tq:
    case TimerQueue{+q, +n}:
      Bool.and(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q))
