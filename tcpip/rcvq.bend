# The receive queue: bytes of a stream that arrive in pieces, in any order,
# delivered in order and without gaps (RFC 9293 section 3.10.7.4, seventh
# step: segments past RCV.NXT are held until the gap before them is filled).
#
# Positions are offsets in the stream (a Nat, so they never wrap); a TCP
# connection turns sequence numbers into offsets from RCV.NXT. next is the
# offset of the first byte not yet delivered; held are the pieces that
# arrived ahead of it, sorted by offset.
import Base
import ../bytes/bytes.bend as B

type RcvSeg is Data:
  RcvSeg{at: Nat, data: B.Octets}

type RcvQ is Data:
  RcvQ{next: Nat, held: List<&2, RcvSeg>}

# what an insert answers: the queue (its next offset and held pieces), and
# the bytes delivered, which start at the old next offset
type RcvOut is Data:
  RcvOut{next: Nat, held: List<&2, RcvSeg>, data: B.Octets}

# an empty queue at offset 0
def RcvQ.new() -> RcvQ:
  RcvQ{0n, Nil{}}

# the offset of the next byte to deliver
def RcvQ.next(q: RcvQ) -> Nat:
  match q:
    case RcvQ{n, h}:
      n

def RcvQ.held.count(xs: List<&2, RcvSeg>, k: Nat) -> Nat:
  match xs:
    case Nil{}:
      k
    case Con{h, t}:
      RcvQ.held.count(t, 1n+k)

# the number of pieces held ahead of the next offset
def RcvQ.count(q: RcvQ) -> Nat:
  match q:
    case RcvQ{n, h}:
      RcvQ.held.count(h, 0n)

def RcvOut.queue(o: RcvOut) -> RcvQ:
  match o:
    case RcvOut{n, h, d}:
      RcvQ{n, h}

def RcvOut.data(o: RcvOut) -> B.Octets:
  match o:
    case RcvOut{n, h, d}:
      d

# Delivering: the head of the held list is ready once it starts at or before
# the next offset; its bytes from there on are delivered

def RcvQ.ready(xs: List<&2, RcvSeg>, n: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      match h:
        case RcvSeg{at, d}:
          Nat.is_le(at, n)

def RcvOut.cons(fresh: B.Octets, o: RcvOut) -> RcvOut:
  match o:
    case RcvOut{n, h, d}:
      RcvOut{n, h, B.Octets.append(fresh, d)}

# deliver from the sorted list xs, next offset n; ready is RcvQ.ready(xs, n)
def RcvQ.pull(xs: List<&2, RcvSeg>, +n: Nat, ready: Bool) -> RcvOut:
  match xs:
    case Nil{}:
      RcvOut{n, Nil{}, B.Octets.empty()}
    case Con{RcvSeg{at, d}, t}:
      match ready:
        case False{}:
          RcvOut{n, Con{RcvSeg{at, d}, t}, B.Octets.empty()}
        case True{}:
          +fresh = B.Octets.drop(Nat.sub(n, at), d)
          +n2 = Nat.add(n, B.Octets.len(fresh))
          +t2 = t
          RcvOut.cons(fresh, RcvQ.pull(t2, n2, RcvQ.ready(t2, n2)))

# Holding: insert by offset; a piece at the same offset as one held keeps
# the longer of the two, so a resent piece is not held twice

def RcvQ.longer(new_longer: Bool, s: RcvSeg, h: RcvSeg) -> RcvSeg:
  match new_longer:
    case True{}:
      s
    case False{}:
      h

def RcvQ.same(s: RcvSeg, h: RcvSeg) -> RcvSeg:
  match s h:
    case RcvSeg{a, +sd} RcvSeg{b, +hd}:
      RcvQ.longer(Nat.is_lt(B.Octets.len(hd), B.Octets.len(sd)), RcvSeg{a, sd}, RcvSeg{b, hd})

def RcvQ.head_cmp(+at: Nat, xs: List<&2, RcvSeg>) -> Cmp:
  match xs:
    case Nil{}:
      LT{}
    case Con{h, t}:
      match h:
        case RcvSeg{b, d}:
          Nat.cmp(at, b)

# s (at offset at) inserted in the sorted list xs; c is RcvQ.head_cmp(at, xs)
def RcvQ.ins(xs: List<&2, RcvSeg>, +s: RcvSeg, +at: Nat, c: Cmp) -> List<&2, RcvSeg>:
  match xs:
    case Nil{}:
      Con{s, Nil{}}
    case Con{h, +t}:
      match c:
        case LT{}:
          Con{s, Con{h, t}}
        case EQ{}:
          Con{RcvQ.same(s, h), t}
        case GT{}:
          Con{h, RcvQ.ins(t, s, at, RcvQ.head_cmp(at, t))}

def RcvQ.admit(ok: Bool, +xs: List<&2, RcvSeg>, +s: RcvSeg, +at: Nat) -> List<&2, RcvSeg>:
  match ok:
    case True{}:
      RcvQ.ins(xs, s, at, RcvQ.head_cmp(at, xs))
    case False{}:
      xs

# The bytes d, from offset next + rel of the stream, into the queue q, and
# whatever is now in order delivered. A piece ahead of next is held only
# while fewer than limit pieces are; one at next is always taken.
def RcvQ.insert(+limit: Nat, q: RcvQ, +rel: Nat, +d: B.Octets) -> RcvOut:
  match q:
    case RcvQ{+n, +held}:
      +at = Nat.add(n, rel)
      +room = Bool.or(Nat.is_eq(rel, 0n), Nat.is_lt(RcvQ.held.count(held, 0n), limit))
      +xs = RcvQ.admit(Bool.and(Nat.is_gt(B.Octets.len(d), 0n), room), held, RcvSeg{at, d}, at)
      RcvQ.pull(xs, n, RcvQ.ready(xs, n))
