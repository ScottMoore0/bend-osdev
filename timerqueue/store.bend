# bend-osdev-timerqueue: the interface a timer queue keeps its timers
# through.
#
# A store of type Q holds timers in TqTimer order (by expiry, then id) and
# offers six things: the empty store; insert a timer; remove a timer (every
# timer equal to it); the first timer (the least), if any; the store
# without its first timer; and the timers, in order. A sorted list
# (sorted.bend) is the default; a heap, a balanced tree or an ordered map
# keyed by the timer is another TqStore value, which a timer queue takes as
# a template argument (~st), specialised at compile time.
import Base
import ./timer.bend as T

type TqStore<-Q: Data> is Type:
  TqStore{empty: Q, insert: Q -> T.TqTimer -> Q, remove: Q -> T.TqTimer -> Q, first: Q -> Maybe<&2, T.TqTimer>, drop_first: Q -> Q, timers: Q -> List<&2, T.TqTimer>}

# Calls through a store (each a template: the store is inlined)

def TqStore.empty.go(-Q: Data, st: TqStore<Q>) -> Q:
  TqStore{e, i, r, f, d, ts} = st
  e

def TqStore.empty(~Q: Data, ~st: TqStore<Q>) -> Q:
  TqStore.empty.go(Q, st)

def TqStore.insert.go(-Q: Data, st: TqStore<Q>, q: Q, x: T.TqTimer) -> Q:
  TqStore{e, i, r, f, d, ts} = st
  i(q, x)

def TqStore.insert(~Q: Data, ~st: TqStore<Q>, q: Q, x: T.TqTimer) -> Q:
  TqStore.insert.go(Q, st, q, x)

def TqStore.remove.go(-Q: Data, st: TqStore<Q>, q: Q, x: T.TqTimer) -> Q:
  TqStore{e, i, r, f, d, ts} = st
  r(q, x)

def TqStore.remove(~Q: Data, ~st: TqStore<Q>, q: Q, x: T.TqTimer) -> Q:
  TqStore.remove.go(Q, st, q, x)

def TqStore.first.go(-Q: Data, st: TqStore<Q>, q: Q) -> Maybe<&2, T.TqTimer>:
  TqStore{e, i, r, f, d, ts} = st
  f(q)

def TqStore.first(~Q: Data, ~st: TqStore<Q>, q: Q) -> Maybe<&2, T.TqTimer>:
  TqStore.first.go(Q, st, q)

def TqStore.drop_first.go(-Q: Data, st: TqStore<Q>, q: Q) -> Q:
  TqStore{e, i, r, f, d, ts} = st
  d(q)

def TqStore.drop_first(~Q: Data, ~st: TqStore<Q>, q: Q) -> Q:
  TqStore.drop_first.go(Q, st, q)

def TqStore.timers.go(-Q: Data, st: TqStore<Q>, q: Q) -> List<&2, T.TqTimer>:
  TqStore{e, i, r, f, d, ts} = st
  ts(q)

def TqStore.timers(~Q: Data, ~st: TqStore<Q>, q: Q) -> List<&2, T.TqTimer>:
  TqStore.timers.go(Q, st, q)
