# bend-osdev-timerqueue: the default store, a sorted list of timers.
#
# The list is kept in TqTimer order (least first). Insertion walks to the
# first timer greater than the new one, so a timer goes after every timer
# with the same expiry; removal keeps every timer not equal to the one
# removed; the first timer is the head. Insertion and removal take time in
# the number of timers held, the rest constant time: simple, and the
# reference that a faster store (a heap, a tree) can be tested against.
import Base
import ./timer.bend as T
import ./store.bend as S

def TqSorted.insert.put(before: Bool, x: T.TqTimer, y: T.TqTimer, inserted: List<&2, T.TqTimer>, t: List<&2, T.TqTimer>) -> List<&2, T.TqTimer>:
  match before:
    case True{}:
      Con{x, Con{y, t}}
    case False{}:
      Con{y, inserted}

# xs with x inserted before the first timer greater than it
def TqSorted.insert(xs: List<&2, T.TqTimer>, +x: T.TqTimer) -> List<&2, T.TqTimer>:
  match xs:
    case Nil{}:
      Con{x, Nil{}}
    case Con{+y, +t}:
      TqSorted.insert.put(T.TqTimer.lt(x, y), x, y, TqSorted.insert(t, x), t)

def TqSorted.remove.put(same: Bool, y: T.TqTimer, rest: List<&2, T.TqTimer>) -> List<&2, T.TqTimer>:
  match same:
    case True{}:
      rest
    case False{}:
      Con{y, rest}

# xs without the timers equal to x
def TqSorted.remove(xs: List<&2, T.TqTimer>, +x: T.TqTimer) -> List<&2, T.TqTimer>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+y, t}:
      TqSorted.remove.put(T.TqTimer.is_eq(y, x), y, TqSorted.remove(t, x))

def TqSorted.first(xs: List<&2, T.TqTimer>) -> Maybe<&2, T.TqTimer>:
  match xs:
    case Nil{}:
      None{}
    case Con{y, t}:
      Some{y}

def TqSorted.drop_first(xs: List<&2, T.TqTimer>) -> List<&2, T.TqTimer>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      t

def TqSorted.store() -> S.TqStore<List<&2, T.TqTimer>>:
  S.TqStore{Nil{}, q => x => TqSorted.insert(q, x), q => x => TqSorted.remove(q, x), q => TqSorted.first(q), q => TqSorted.drop_first(q), q => q}
