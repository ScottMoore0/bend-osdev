# The laws are stated for the named default, TimerQueueList (the sorted
# list of sorted.bend), since a law cannot quantify over a template
# argument. "valid" is TimerQueueList.valid: the timers in order, and every
# id below the next one to be handed out; every queue these defs build is
# valid. Properties, for every queue, time and timer:
#
# * the invariant: new, add, delete and expire keep a queue valid;
# * add: the new timer has the next id (so ids, and ties between equal
#   expiries, follow insertion order); it is held afterwards, was not held
#   before, and no other timer handed out by the queue is affected;
# * delete: the timer is not held afterwards, and no other timer is
#   affected;
# * the next expiry is the minimum: it is the first timer's expiry, and
#   every timer held expires at or after it;
# * expire: the timers fired and the timers left are the timers held, in
#   order; the fired ones are due (expiry at or before now) and in order
#   (nondecreasing expiry, ties by id), and every one left expires after
#   now;
# * a deleted timer never fires: a timer not held is not fired, and is not
#   held after an expiry; delete makes a timer not held, and add, delete and
#   expire never make a timer handed out earlier held again;
# * ids: every timer the queue hands out stays "issued" through add, delete
#   and expire.
import Base
import ../word64/word64.bend as W
import ./timer.bend as T
import ./timerqueue.bend as Q

# The invariant

law tq_new_valid:
  {Q.TimerQueueList.valid(Q.TimerQueueList.new()) == True{} : Bool}

law tq_add_valid:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +e: W.W64
  for +v: {Q.TimerQueueList.valid(tq) == True{} : Bool}
  {Q.TimerQueueList.valid(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e))) == True{} : Bool}

law tq_delete_valid:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +x: T.TqTimer
  for +v: {Q.TimerQueueList.valid(tq) == True{} : Bool}
  {Q.TimerQueueList.valid(Q.TimerQueueList.delete(tq, x)) == True{} : Bool}

law tq_expire_valid:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +now: W.W64
  for +v: {Q.TimerQueueList.valid(tq) == True{} : Bool}
  {Q.TimerQueueList.valid(Q.TqExpired.queue(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now))) == True{} : Bool}

law tq_sorted:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +v: {Q.TimerQueueList.valid(tq) == True{} : Bool}
  {T.TqTimer.sorted(Q.TimerQueueList.pending(tq)) == True{} : Bool}

# New

law tq_new_empty:
  {(Q.TimerQueueList.pending(Q.TimerQueueList.new()), Q.TimerQueueList.next_expiry(Q.TimerQueueList.new())) == (Nil{}, None{}) : List<&2, T.TqTimer> & Maybe<&2, W.W64>}

# Add

law tq_add_timer:
  for +tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +e: W.W64
  {(Q.TqAdded.timer(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e)), Q.TimerQueue.next_id(List<&2, T.TqTimer>, Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e)))) == (T.TqTimer{e, Q.TimerQueue.next_id(List<&2, T.TqTimer>, tq)}, 1n+Q.TimerQueue.next_id(List<&2, T.TqTimer>, tq)) : T.TqTimer & Nat}

law tq_add_contains:
  for +tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +e: W.W64
  {Q.TimerQueueList.contains(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e)), Q.TqAdded.timer(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e))) == True{} : Bool}

law tq_add_fresh:
  for +tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +e: W.W64
  for +v: {Q.TimerQueueList.valid(tq) == True{} : Bool}
  {Q.TimerQueueList.contains(tq, Q.TqAdded.timer(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e))) == False{} : Bool}

law tq_add_others:
  for +tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +e: W.W64
  for +x: T.TqTimer
  for i: {Q.TimerQueue.issued(List<&2, T.TqTimer>, tq, x) == True{} : Bool}
  {Q.TimerQueueList.contains(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e)), x) == Q.TimerQueueList.contains(tq, x) : Bool}

# Delete

law tq_delete_gone:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +x: T.TqTimer
  {Q.TimerQueueList.contains(Q.TimerQueueList.delete(tq, x), x) == False{} : Bool}

law tq_delete_others:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +x: T.TqTimer
  for +y: T.TqTimer
  for d: {T.TqTimer.is_eq(x, y) == False{} : Bool}
  {Q.TimerQueueList.contains(Q.TimerQueueList.delete(tq, x), y) == Q.TimerQueueList.contains(tq, y) : Bool}

# The next expiry is the minimum

law tq_next_first:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  {Q.TimerQueueList.next_expiry(tq) == Q.TimerQueue.first_expiry(List.head(&2, T.TqTimer, Q.TimerQueueList.pending(tq))) : Maybe<&2, W.W64>}

law tq_next_min:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +t: W.W64
  for +v: {Q.TimerQueueList.valid(tq) == True{} : Bool}
  for n: {Q.TimerQueueList.next_expiry(tq) == Some{t} : Maybe<&2, W.W64>}
  {T.TqTimer.all_from(t, Q.TimerQueueList.pending(tq)) == True{} : Bool}

# Expire

law tq_expire_split:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +now: W.W64
  {List.append(&2, T.TqTimer, Q.TqExpired.fired(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now)), Q.TimerQueueList.pending(Q.TqExpired.queue(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now)))) == Q.TimerQueueList.pending(tq) : List<&2, T.TqTimer>}

law tq_expire_due:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +now: W.W64
  {T.TqTimer.all_due(now, Q.TqExpired.fired(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now))) == True{} : Bool}

law tq_expire_sorted:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +now: W.W64
  for +v: {Q.TimerQueueList.valid(tq) == True{} : Bool}
  {T.TqTimer.sorted(Q.TqExpired.fired(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now))) == True{} : Bool}

law tq_expire_later:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +now: W.W64
  for +v: {Q.TimerQueueList.valid(tq) == True{} : Bool}
  {T.TqTimer.all_later(now, Q.TimerQueueList.pending(Q.TqExpired.queue(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now)))) == True{} : Bool}

# A deleted timer never fires

law tq_expire_never:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +now: W.W64
  for +x: T.TqTimer
  for c: {Q.TimerQueueList.contains(tq, x) == False{} : Bool}
  {(T.TqTimer.member(Q.TqExpired.fired(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now)), x), Q.TimerQueueList.contains(Q.TqExpired.queue(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now)), x)) == (False{}, False{}) : Bool & Bool}

law tq_deleted_never_fires:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +now: W.W64
  for +x: T.TqTimer
  {T.TqTimer.member(Q.TqExpired.fired(List<&2, T.TqTimer>, Q.TimerQueueList.expire(Q.TimerQueueList.delete(tq, x), now)), x) == False{} : Bool}

# Ids

law tq_issued_add:
  for +tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +e: W.W64
  for +x: T.TqTimer
  for i: {Q.TimerQueue.issued(List<&2, T.TqTimer>, tq, x) == True{} : Bool}
  {(Q.TimerQueue.issued(List<&2, T.TqTimer>, Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e)), x), Q.TimerQueue.issued(List<&2, T.TqTimer>, Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e)), Q.TqAdded.timer(List<&2, T.TqTimer>, Q.TimerQueueList.add(tq, e)))) == (True{}, True{}) : Bool & Bool}

law tq_issued_delete:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +x: T.TqTimer
  {Q.TimerQueue.next_id(List<&2, T.TqTimer>, Q.TimerQueueList.delete(tq, x)) == Q.TimerQueue.next_id(List<&2, T.TqTimer>, tq) : Nat}

law tq_issued_expire:
  for tq: Q.TimerQueue<List<&2, T.TqTimer>>
  for +now: W.W64
  {Q.TimerQueue.next_id(List<&2, T.TqTimer>, Q.TqExpired.queue(List<&2, T.TqTimer>, Q.TimerQueueList.expire(tq, now))) == Q.TimerQueue.next_id(List<&2, T.TqTimer>, tq) : Nat}

# Witnesses and vectors: timers at 30, 10, 20 and 10, the third deleted,
# then an expiry at 15

law tq_vec:
  {(Q.TimerQueueList.pending(Q.TimerQueueList.delete(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TimerQueueList.new(), W.W64.from_u32(30))), W.W64.from_u32(10))), W.W64.from_u32(20))), W.W64.from_u32(10))), T.TqTimer{W.W64.from_u32(20), 2n})), Q.TqExpired.fired(List<&2, T.TqTimer>, Q.TimerQueueList.expire(Q.TimerQueueList.delete(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TimerQueueList.new(), W.W64.from_u32(30))), W.W64.from_u32(10))), W.W64.from_u32(20))), W.W64.from_u32(10))), T.TqTimer{W.W64.from_u32(20), 2n}), W.W64.from_u32(15)))) == ([T.TqTimer{W.W64.from_u32(10), 1n}, T.TqTimer{W.W64.from_u32(10), 3n}, T.TqTimer{W.W64.from_u32(30), 0n}], [T.TqTimer{W.W64.from_u32(10), 1n}, T.TqTimer{W.W64.from_u32(10), 3n}]) : List<&2, T.TqTimer> & List<&2, T.TqTimer>}

law tq_wit:
  {(Q.TimerQueue.issued(List<&2, T.TqTimer>, Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TimerQueueList.new(), W.W64.from_u32(5))), T.TqTimer{W.W64.from_u32(5), 0n}), T.TqTimer.is_eq(T.TqTimer{W.W64.from_u32(5), 0n}, T.TqTimer{W.W64.from_u32(5), 1n}), Q.TimerQueueList.next_expiry(Q.TqAdded.queue(List<&2, T.TqTimer>, Q.TimerQueueList.add(Q.TimerQueueList.new(), W.W64.from_u32(5)))), Q.TimerQueueList.contains(Q.TimerQueueList.new(), T.TqTimer{W.W64.from_u32(5), 0n})) == (True{}, False{}, Some{W.W64.from_u32(5)}, False{}) : Bool & Bool & Maybe<&2, W.W64> & Bool}
