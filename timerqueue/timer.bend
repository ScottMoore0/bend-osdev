# bend-osdev-timerqueue: timers and their order.
#
# A timer is its expiry time (a W64, in the caller's unit) and its id, a
# Nat the queue hands out in the order timers are added. Timers are ordered
# by expiry, and timers with the same expiry by id, so by insertion order:
# TqTimer.cmp. Two timers are the same timer when they compare equal.
#
# The order on W64 times is TqTime.cmp: the high halves first, then the low
# halves, each in U32's order (the order of the values, through word64's
# W64.hi and W64.lo). The package states and proves its laws in this order,
# so they rest only on Base's U32 and word64's interface.
import Base
import ../word64/word64.bend as W

type TqTimer is Data:
  TqTimer{expiry: W.W64, id: Nat}

def TqTimer.expiry(x: TqTimer) -> W.W64:
  match x:
    case TqTimer{e, i}:
      e

def TqTimer.id(x: TqTimer) -> Nat:
  match x:
    case TqTimer{e, i}:
      i

# the first comparison, unless it is EQ: then the second
def TqCmp.lex(c1: Cmp, c2: Cmp) -> Cmp:
  match c1:
    case LT{}:
      LT{}
    case EQ{}:
      c2
    case GT{}:
      GT{}

# Times

def TqTime.cmp(+a: W.W64, +b: W.W64) -> Cmp:
  TqCmp.lex(U32.cmp(W.W64.hi(a), W.W64.hi(b)), U32.cmp(W.W64.lo(a), W.W64.lo(b)))

def TqTime.le(+a: W.W64, +b: W.W64) -> Bool:
  Cmp.is_le(TqTime.cmp(a, b))

def TqTime.lt(+a: W.W64, +b: W.W64) -> Bool:
  Cmp.is_lt(TqTime.cmp(a, b))

# Timers

def TqTimer.cmp(x: TqTimer, y: TqTimer) -> Cmp:
  match x y:
    case TqTimer{ex, ix} TqTimer{ey, iy}:
      TqCmp.lex(TqTime.cmp(ex, ey), Nat.cmp(ix, iy))

def TqTimer.le(x: TqTimer, y: TqTimer) -> Bool:
  Cmp.is_le(TqTimer.cmp(x, y))

def TqTimer.lt(x: TqTimer, y: TqTimer) -> Bool:
  Cmp.is_lt(TqTimer.cmp(x, y))

def TqTimer.is_eq(x: TqTimer, y: TqTimer) -> Bool:
  Cmp.is_eq(TqTimer.cmp(x, y))

# Lists of timers

# whether each timer is at most the next: the expiries never decrease, and
# timers with the same expiry come in id order
def TqTimer.sorted(xs: List<&2, TqTimer>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, Nil{}}:
      True{}
    case Con{+x, Con{+y, t}}:
      Bool.and(TqTimer.le(x, y), TqTimer.sorted(Con{y, t}))

# whether x is among xs
def TqTimer.member(xs: List<&2, TqTimer>, +x: TqTimer) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, t}:
      Bool.or(TqTimer.is_eq(y, x), TqTimer.member(t, x))

# whether every timer of xs expires at or after t
def TqTimer.all_from(+t: W.W64, xs: List<&2, TqTimer>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(TqTime.le(t, TqTimer.expiry(y)), TqTimer.all_from(t, rest))

# whether every timer of xs expires at or before now
def TqTimer.all_due(+now: W.W64, xs: List<&2, TqTimer>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(TqTime.le(TqTimer.expiry(y), now), TqTimer.all_due(now, rest))

# whether every timer of xs expires after now
def TqTimer.all_later(+now: W.W64, xs: List<&2, TqTimer>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(TqTime.lt(now, TqTimer.expiry(y)), TqTimer.all_later(now, rest))

# whether every timer of xs has an id below n
def TqTimer.ids_below(+n: Nat, xs: List<&2, TqTimer>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(Nat.is_lt(TqTimer.id(y), n), TqTimer.ids_below(n, rest))
