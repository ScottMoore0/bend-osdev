# Sequence numbers and clock times: 32-bit counters compared modulo 2^32.
#
# TCP's sequence numbers wrap (RFC 9293 section 3.4: "all arithmetic dealing
# with sequence numbers must be performed modulo 2**32"). b is ahead of a
# when b - a, taken modulo 2^32, is between 1 and 2^31 - 1: within any
# window of 2^31 numbers this is the order of the integers, and two numbers
# exactly 2^31 apart are not ordered either way.
#
# The clock is a U32 of milliseconds that wraps too; a deadline is compared
# with the clock the same way, so deadlines up to 2^31 ms (24.8 days) ahead
# are ordered correctly across the wrap.
import Base

# The most significant bit of an n-bit word, and whether every bit below it
# is zero (Base's words hold the least significant bit first)

def SeqNum.word.top.go(p: Nat, b: Bool, t: Word(p)) -> Bool:
  match p:
    case 0n:
      b
    case 1n+q:
      match t:
        case WCon{h, r}:
          SeqNum.word.top.go(q, h, r)

def SeqNum.word.top(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          SeqNum.word.top.go(p, b, t)

def SeqNum.word.low0.go(p: Nat, b: Bool, t: Word(p)) -> Bool:
  match p:
    case 0n:
      True{}
    case 1n+q:
      match t:
        case WCon{h, r}:
          Bool.and(Bool.not(b), SeqNum.word.low0.go(q, h, r))

def SeqNum.word.low0(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          SeqNum.word.low0.go(p, b, t)

# Distances

# a + n modulo 2^32: the number n places after a
def SeqNum.add(a: U32, n: U32) -> U32:
  U32.add(a, n)

# b - a modulo 2^32: how far b is ahead of a
def SeqNum.sub(b: U32, a: U32) -> U32:
  U32.sub(b, a)

# whether a distance d is between 1 and 2^31 - 1: its top bit clear and some
# other bit set
def SeqNum.in_half(d: U32) -> Bool:
  match d:
    case U32{+w}:
      Bool.and(Bool.not(SeqNum.word.top(32n, w)), Bool.not(SeqNum.word.low0(32n, w)))

# Comparisons (RFC 9293 section 3.4's "<" and "=<" on sequence numbers)

# a < b: b is ahead of a by less than 2^31
def SeqNum.lt(a: U32, b: U32) -> Bool:
  SeqNum.in_half(U32.sub(b, a))

# a =< b
def SeqNum.le(+a: U32, +b: U32) -> Bool:
  Bool.or(U32.is_eq(a, b), SeqNum.lt(a, b))

# a > b
def SeqNum.gt(a: U32, b: U32) -> Bool:
  SeqNum.lt(b, a)

# a >= b
def SeqNum.ge(a: U32, b: U32) -> Bool:
  SeqNum.le(b, a)

def SeqNum.max.pick(b_ahead: Bool, a: U32, b: U32) -> U32:
  match b_ahead:
    case True{}:
      b
    case False{}:
      a

# the later of a and b
def SeqNum.max(+a: U32, +b: U32) -> U32:
  SeqNum.max.pick(SeqNum.lt(a, b), a, b)

def SeqNum.min(+a: U32, +b: U32) -> U32:
  SeqNum.max.pick(SeqNum.lt(b, a), a, b)

# start =< x < start + len: x is in the window of len numbers from start
def SeqNum.in_window(+x: U32, +start: U32, len: U32) -> Bool:
  Bool.and(SeqNum.le(start, x), SeqNum.lt(x, U32.add(start, len)))

# Clock times, in milliseconds

# whether the deadline at has been reached at time now
def SeqNum.reached(now: U32, at: U32) -> Bool:
  SeqNum.le(at, now)
