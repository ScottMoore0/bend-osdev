# Congestion control: the interface a TCP connection calls, and Reno (RFC
# 5681, "TCP Congestion Control") as its default.
#
# A congestion controller is a state of some Data type C and five functions
# over it (TcpCc). A connection takes them as a template argument (~cc), so
# the choice is made at compile time and costs nothing at run time; any other
# algorithm (NewReno, CUBIC, a fixed window for tests) is another TcpCc.
import Base

# What the sender knows when an acknowledgment arrives or a timer expires:
# the bytes newly acknowledged (0 for a duplicate), the sender's maximum
# segment size, and the bytes in flight before this acknowledgment
type TcpAckInfo is Data:
  TcpAckInfo{acked: U32, smss: U32, flight: U32}

# start(smss, iw): the state of a new connection, iw its initial window in
# bytes; cwnd(c): the congestion window in bytes; on_ack: new data was
# acknowledged; on_dupack: a duplicate acknowledgment (RFC 5681 section 2),
# answering the state and whether to resend the first unacknowledged segment
# now (fast retransmit); on_timeout: the retransmission timer expired
type TcpCc<-C: Data> is Type:
  TcpCc{start: U32 -> U32 -> C, cwnd: C -> U32, on_ack: C -> TcpAckInfo -> C, on_dupack: C -> TcpAckInfo -> Pair(C, Bool), on_timeout: C -> TcpAckInfo -> C}

# Reno (RFC 5681 sections 3.1 and 3.2): slow start, congestion avoidance,
# fast retransmit on the third duplicate acknowledgment, and fast recovery.
# cwnd and ssthresh in bytes; dupacks counts duplicate acknowledgments in a
# row; recovering is set during fast recovery.
type RenoState is Data:
  RenoState{cwnd: U32, ssthresh: U32, dupacks: U32, recovering: Bool}

def Reno.min.pick(lt: Bool, a: U32, b: U32) -> U32:
  match lt:
    case True{}:
      a
    case False{}:
      b

def Reno.min(+a: U32, +b: U32) -> U32:
  Reno.min.pick(U32.is_lt(a, b), a, b)

def Reno.max(+a: U32, +b: U32) -> U32:
  Reno.min.pick(U32.is_lt(b, a), a, b)

# the largest window Reno grows to: below 2^30, so that sums stay in 32 bits
def Reno.cap() -> U32:
  1073741823

def Reno.start(ssthresh0: U32, smss: U32, iw: U32) -> RenoState:
  RenoState{iw, ssthresh0, 0, False{}}

def Reno.cwnd(c: RenoState) -> U32:
  match c:
    case RenoState{w, t, d, r}:
      w

# RFC 5681 equation (4): ssthresh = max(FlightSize / 2, 2 * SMSS)
def Reno.halve(+flight: U32, +smss: U32) -> U32:
  Reno.max(U32.shr(flight), U32.add(smss, smss))

# slow start (equation 2) below ssthresh, congestion avoidance (equation 3)
# above it
def Reno.grow.go(slow: Bool, +w: U32, +acked: U32, +smss: U32) -> U32:
  match slow:
    case True{}:
      Reno.min(U32.add(w, Reno.min(acked, smss)), Reno.cap())
    case False{}:
      Reno.min(U32.add(w, Reno.max(1, U32.div(U32.mul(smss, smss), Reno.max(w, 1)))), Reno.cap())

def Reno.grow(+w: U32, +t: U32, acked: U32, smss: U32) -> U32:
  Reno.grow.go(U32.is_lt(w, t), w, acked, smss)

def Reno.on_ack.go(recovering: Bool, +w: U32, +t: U32, info: TcpAckInfo) -> RenoState:
  match recovering:
    case True{}:
      # leaving fast recovery: deflate the window to ssthresh (3.2 step 6)
      RenoState{t, t, 0, False{}}
    case False{}:
      match info:
        case TcpAckInfo{a, s, f}:
          RenoState{Reno.grow(w, t, a, s), t, 0, False{}}

def Reno.on_ack(c: RenoState, info: TcpAckInfo) -> RenoState:
  match c:
    case RenoState{w, t, d, r}:
      Reno.on_ack.go(r, w, t, info)

def Reno.on_dupack.third(third: Bool, w: U32, t: U32, +d: U32, info: TcpAckInfo) -> Pair(RenoState, Bool):
  match third:
    case True{}:
      # fast retransmit, and enter fast recovery (3.2 steps 2 to 4)
      match info:
        case TcpAckInfo{a, +s, f}:
          +t2 = Reno.halve(f, s)
          (RenoState{U32.add(t2, U32.mul(3, s)), t2, d, True{}}, True{})
    case False{}:
      (RenoState{w, t, d, False{}}, False{})

def Reno.on_dupack.go(recovering: Bool, +w: U32, +t: U32, +d: U32, info: TcpAckInfo) -> Pair(RenoState, Bool):
  match recovering:
    case True{}:
      # each further duplicate inflates the window by one segment (3.2 step 5)
      match info:
        case TcpAckInfo{a, s, f}:
          (RenoState{Reno.min(U32.add(w, s), Reno.cap()), t, d, True{}}, False{})
    case False{}:
      Reno.on_dupack.third(U32.is_eq(d, 3), w, t, d, info)

def Reno.on_dupack(c: RenoState, info: TcpAckInfo) -> Pair(RenoState, Bool):
  match c:
    case RenoState{w, t, d, r}:
      Reno.on_dupack.go(r, w, t, U32.add(d, 1), info)

# a retransmission timeout: ssthresh halves, and the window falls to the loss
# window of one segment (3.1)
def Reno.on_timeout(c: RenoState, info: TcpAckInfo) -> RenoState:
  match c info:
    case RenoState{w, t, d, r} TcpAckInfo{a, +s, f}:
      RenoState{s, Reno.halve(f, s), 0, False{}}

# Reno with initial ssthresh ssthresh0
def Reno.cc_with(+ssthresh0: U32) -> TcpCc<RenoState>:
  TcpCc{s => w => Reno.start(ssthresh0, s, w), Reno.cwnd, Reno.on_ack, Reno.on_dupack, Reno.on_timeout}

# the default: ssthresh starts at the largest window a peer can advertise
# without window scaling, 65535 ("arbitrarily high", 3.1)
def Reno.cc() -> TcpCc<RenoState>:
  Reno.cc_with(65535)
