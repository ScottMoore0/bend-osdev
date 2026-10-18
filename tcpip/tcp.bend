# A TCP connection (RFC 9293) as a pure state machine:
#
#   Tcp.step(~C, ~cc, opts, conn, event, now, isn) -> (conn, actions)
#
# An event is a segment arriving, a timer firing, or a call from the
# application; an action is a segment to send, data to deliver, a note for
# the application, or a timer to set or stop. now is the clock (U32
# milliseconds, wrapping); isn is an initial sequence number, used only when
# the event opens the connection (RFC 9293 section 3.4.1 says how to make
# one; the caller supplies it, since there is no randomness here). ~C and
# ~cc are the congestion controller (cc.bend; Reno by default).
#
# The connection's state moves only by Tcp.next_state, a table of RFC 9293's
# state diagram (Figure 5) and of the transitions its text adds; every other
# part of the connection (the TCB) is computed beside it.
import Base
import ../bytes/bytes.bend as B
import ../netheaders/tcp.bend as NT
import ./seq.bend as S
import ./rto.bend as R
import ./cc.bend as CC
import ./rcvq.bend as Q
import ./segment.bend as G

# The states (RFC 9293 section 3.3.2)
type TcpState is Data:
  TcpClosed{}
  TcpListen{}
  TcpSynSent{}
  TcpSynReceived{}
  TcpEstablished{}
  TcpFinWait1{}
  TcpFinWait2{}
  TcpCloseWait{}
  TcpClosing{}
  TcpLastAck{}
  TcpTimeWait{}

# Choices, with RFC 9293's and RFC 6298's values as defaults:
#   mss: the maximum segment size we receive, sent in the MSS option (1460:
#     an Ethernet MTU of 1500 less 40 bytes of headers);
#   rcv_buf: the receive buffer, the most we advertise (65535: no window
#     scaling);
#   snd_buf: the most data held unacknowledged or unsent;
#   iw_bytes: RFC 5681's initial window rule, IW = min(4 * SMSS,
#     max(2 * SMSS, iw_bytes)) (4380 there);
#   msl: the maximum segment lifetime; TIME-WAIT lasts 2 * msl (RFC 9293
#     section 3.4.2: 2 minutes);
#   retries, syn_retries: retransmissions of data and of a SYN before the
#     connection gives up (RFC 9293 section 3.8.3's R2: at least 100 seconds
#     and 3 minutes with the default timer);
#   nagle: Nagle's algorithm (section 3.7.4: SHOULD);
#   app_reads: when set, delivered data fills the receive buffer until the
#     application calls read; when clear, delivered data is consumed at once;
#   ooo_limit: the most out-of-order pieces held;
#   rto: the retransmission timer's parameters (rto.bend)
type TcpOptions is Data:
  TcpOptions{mss: U32, rcv_buf: U32, snd_buf: U32, iw_bytes: U32, msl: U32, retries: U32, syn_retries: U32, nagle: Bool, app_reads: Bool, ooo_limit: U32, rto: R.RtoParams}

def TcpOptions.default() -> TcpOptions:
  TcpOptions{1460, 65535, 65535, 4380, 120000, 8, 7, True{}, False{}, 64, R.RtoParams.default()}

# The transmission control block (RFC 9293 section 3.3.1)

# a round-trip time measurement: the segment ending before seq, sent at start
type TcpRtt is Data:
  TcpRtt{seq: U32, start: U32}

# the send side: ISS, SND.UNA, SND.NXT, the highest sequence number sent
# (max), SND.WND, SND.WL1, SND.WL2, the sender's MSS, the data not yet
# acknowledged (buf, its first byte at sequence number bseq), and whether
# the application has closed (a FIN follows the data)
type TcpSnd is Data:
  TcpSnd{iss: U32, una: U32, nxt: U32, max: U32, wnd: U32, wl1: U32, wl2: U32, smss: U32, buf: B.Octets, bseq: U32, fin: Bool}

# the receive side: IRS, RCV.NXT, the queue of data not yet in order, and the
# delivered bytes the application has not read
type TcpRcv is Data:
  TcpRcv{irs: U32, nxt: U32, q: Q.RcvQ, unread: U32}

# the timers: the RTO estimator, the retransmission and TIME-WAIT deadlines,
# the retransmissions so far, the round-trip measurement, and whether a SYN
# was resent
type TcpTim is Data:
  TcpTim{rto: R.Rto, rtx: Maybe<&2, U32>, tw: Maybe<&2, U32>, retx: U32, rtt: Maybe<&2, TcpRtt>, syn_lost: Bool}

# passive: the connection was opened from LISTEN
type TcpTcb is Data:
  TcpTcb{passive: Bool, snd: TcpSnd, rcv: TcpRcv, tim: TcpTim}

type TcpConn<-C: Data> is Data:
  TcpConn{state: TcpState, tcb: TcpTcb, cc: C}

# Events, actions and notes

type TcpTimer is Data:
  TcpTimerRtx{}
  TcpTimerTimeWait{}

type TcpEvent is Data:
  # OPEN, active (send a SYN) or passive (LISTEN)
  TcpCallOpen{active: Bool}
  # SEND
  TcpCallSend{data: B.Octets}
  # the application read n delivered bytes (with app_reads)
  TcpCallRead{n: U32}
  TcpCallClose{}
  TcpCallAbort{}
  TcpArrive{seg: G.TcpSeg}
  TcpFire{timer: TcpTimer}

type TcpError is Data:
  # "connection does not exist"
  TcpErrNoConnection{}
  # "connection already exists"
  TcpErrExists{}
  # "connection closing"
  TcpErrClosing{}

type TcpNote is Data:
  # the three-way handshake completed
  TcpNoteEstablished{}
  # the peer sent a FIN: no more data will arrive
  TcpNotePeerClosed{}
  # the peer reset the connection
  TcpNoteReset{}
  # an active open was refused (reset)
  TcpNoteRefused{}
  # retransmission gave up
  TcpNoteTimedOut{}
  # SEND: how many bytes the send buffer took
  TcpNoteQueued{n: U32}
  TcpNoteError{error: TcpError}
  # the connection is closed: its TCB may be deleted
  TcpNoteClosed{}

type TcpAction is Data:
  TcpOut{seg: G.TcpSeg}
  TcpDeliver{data: B.Octets}
  TcpNotify{note: TcpNote}
  TcpSetTimer{timer: TcpTimer, at: U32}
  TcpStopTimer{timer: TcpTimer}

# The control plane: the state diagram

# The inputs the state diagram reacts to: what Tcp.step makes of an event
type TcpInput is Data:
  # OPEN in CLOSED
  TcpInPassiveOpen{}
  TcpInActiveOpen{}
  # CLOSE, ABORT
  TcpInClose{}
  TcpInAbort{}
  # nothing that moves the state: a dropped or ignored segment, an error, a
  # SEND, a retransmission
  TcpInNone{}
  # an acceptable reset (to_listen: in SYN-RECEIVED after a passive open)
  TcpInReset{to_listen: Bool}
  # a SYN, in LISTEN, or without an ACK in SYN-SENT
  TcpInSyn{}
  # in SYN-SENT, a SYN acknowledging ours; fin: it carries a FIN too
  TcpInSynAck{fin: Bool}
  # in a synchronized state, a segment that passed the checks: acks_fin, our
  # FIN is acknowledged; fin, it carries the peer's FIN, in order
  TcpInSeg{acks_fin: Bool, fin: Bool}
  # the retransmissions gave up
  TcpInGiveUp{}
  # the TIME-WAIT timer expired
  TcpInTimeWaitEnd{}

def TcpState.index(s: TcpState) -> U32:
  match s:
    case TcpClosed{}:
      0
    case TcpListen{}:
      1
    case TcpSynSent{}:
      2
    case TcpSynReceived{}:
      3
    case TcpEstablished{}:
      4
    case TcpFinWait1{}:
      5
    case TcpFinWait2{}:
      6
    case TcpCloseWait{}:
      7
    case TcpClosing{}:
      8
    case TcpLastAck{}:
      9
    case TcpTimeWait{}:
      10

def TcpState.is(+s: TcpState, i: U32) -> Bool:
  U32.is_eq(TcpState.index(s), i)

def TcpState.name(s: TcpState) -> String:
  match s:
    case TcpClosed{}:
      "CLOSED"
    case TcpListen{}:
      "LISTEN"
    case TcpSynSent{}:
      "SYN-SENT"
    case TcpSynReceived{}:
      "SYN-RECEIVED"
    case TcpEstablished{}:
      "ESTABLISHED"
    case TcpFinWait1{}:
      "FIN-WAIT-1"
    case TcpFinWait2{}:
      "FIN-WAIT-2"
    case TcpCloseWait{}:
      "CLOSE-WAIT"
    case TcpClosing{}:
      "CLOSING"
    case TcpLastAck{}:
      "LAST-ACK"
    case TcpTimeWait{}:
      "TIME-WAIT"

def Tcp.pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# a reset, abort or give-up closes; anything else leaves s
def Tcp.next.common(s: TcpState, k: TcpInput) -> TcpState:
  match k:
    case TcpInReset{l}:
      TcpClosed{}
    case TcpInAbort{}:
      TcpClosed{}
    case TcpInGiveUp{}:
      TcpClosed{}
    case _:
      s

# The state after input k in state s (RFC 9293 section 3.10)
def Tcp.next_state(s: TcpState, k: TcpInput) -> TcpState:
  match s:
    case TcpClosed{}:
      match k:
        case TcpInPassiveOpen{}:
          TcpListen{}
        case TcpInActiveOpen{}:
          TcpSynSent{}
        case _:
          TcpClosed{}
    case TcpListen{}:
      match k:
        case TcpInSyn{}:
          TcpSynReceived{}
        case TcpInClose{}:
          TcpClosed{}
        case TcpInAbort{}:
          TcpClosed{}
        case _:
          TcpListen{}
    case TcpSynSent{}:
      match k:
        case TcpInSynAck{fin}:
          Tcp.pick(TcpState, fin, TcpCloseWait{}, TcpEstablished{})
        case TcpInSyn{}:
          TcpSynReceived{}
        case TcpInClose{}:
          TcpClosed{}
        case _:
          Tcp.next.common(TcpSynSent{}, k)
    case TcpSynReceived{}:
      match k:
        case TcpInSeg{af, fin}:
          Tcp.pick(TcpState, fin, TcpCloseWait{}, TcpEstablished{})
        case TcpInReset{l}:
          Tcp.pick(TcpState, l, TcpListen{}, TcpClosed{})
        case TcpInClose{}:
          TcpFinWait1{}
        case _:
          Tcp.next.common(TcpSynReceived{}, k)
    case TcpEstablished{}:
      match k:
        case TcpInSeg{af, fin}:
          Tcp.pick(TcpState, fin, TcpCloseWait{}, TcpEstablished{})
        case TcpInClose{}:
          TcpFinWait1{}
        case _:
          Tcp.next.common(TcpEstablished{}, k)
    case TcpFinWait1{}:
      match k:
        case TcpInSeg{af, +fin}:
          Tcp.pick(TcpState, af, Tcp.pick(TcpState, fin, TcpTimeWait{}, TcpFinWait2{}), Tcp.pick(TcpState, fin, TcpClosing{}, TcpFinWait1{}))
        case _:
          Tcp.next.common(TcpFinWait1{}, k)
    case TcpFinWait2{}:
      match k:
        case TcpInSeg{af, fin}:
          Tcp.pick(TcpState, fin, TcpTimeWait{}, TcpFinWait2{})
        case _:
          Tcp.next.common(TcpFinWait2{}, k)
    case TcpCloseWait{}:
      match k:
        case TcpInClose{}:
          TcpLastAck{}
        case _:
          Tcp.next.common(TcpCloseWait{}, k)
    case TcpClosing{}:
      match k:
        case TcpInSeg{af, fin}:
          Tcp.pick(TcpState, af, TcpTimeWait{}, TcpClosing{})
        case _:
          Tcp.next.common(TcpClosing{}, k)
    case TcpLastAck{}:
      match k:
        case TcpInSeg{af, fin}:
          Tcp.pick(TcpState, af, TcpClosed{}, TcpLastAck{})
        case _:
          Tcp.next.common(TcpLastAck{}, k)
    case TcpTimeWait{}:
      match k:
        case TcpInTimeWaitEnd{}:
          TcpClosed{}
        case _:
          Tcp.next.common(TcpTimeWait{}, k)

# The transitions of RFC 9293's state diagram (Figure 5)
def Tcp.diagram(s: TcpState, +t: TcpState) -> Bool:
  match s:
    case TcpClosed{}:
      Bool.or(TcpState.is(t, 1), TcpState.is(t, 2))
    case TcpListen{}:
      Bool.or(TcpState.is(t, 3), Bool.or(TcpState.is(t, 2), TcpState.is(t, 0)))
    case TcpSynSent{}:
      Bool.or(TcpState.is(t, 3), Bool.or(TcpState.is(t, 4), TcpState.is(t, 0)))
    case TcpSynReceived{}:
      Bool.or(TcpState.is(t, 4), TcpState.is(t, 5))
    case TcpEstablished{}:
      Bool.or(TcpState.is(t, 5), TcpState.is(t, 7))
    case TcpFinWait1{}:
      Bool.or(TcpState.is(t, 6), TcpState.is(t, 8))
    case TcpFinWait2{}:
      TcpState.is(t, 10)
    case TcpCloseWait{}:
      TcpState.is(t, 9)
    case TcpClosing{}:
      TcpState.is(t, 10)
    case TcpLastAck{}:
      TcpState.is(t, 0)
    case TcpTimeWait{}:
      TcpState.is(t, 0)

# The transitions RFC 9293's text adds to the diagram: SYN-RECEIVED returns
# to LISTEN on a reset after a passive open (section 3.10.7.4); and one
# segment can take two edges of the diagram, as a SYN, ACK and FIN takes
# SYN-SENT to ESTABLISHED to CLOSE-WAIT, an ACK and FIN takes SYN-RECEIVED
# to ESTABLISHED to CLOSE-WAIT, and an ACK of our FIN with the peer's FIN
# takes FIN-WAIT-1 to FIN-WAIT-2 (or CLOSING) to TIME-WAIT
def Tcp.text_edge(s: TcpState, +t: TcpState) -> Bool:
  match s:
    case TcpSynSent{}:
      TcpState.is(t, 7)
    case TcpSynReceived{}:
      Bool.or(TcpState.is(t, 1), TcpState.is(t, 7))
    case TcpFinWait1{}:
      TcpState.is(t, 10)
    case _:
      False{}

# Whether one step may take s to t: staying, closing (a reset, ABORT, or a
# timeout closes any connection: section 3.10), the diagram, or the text
def Tcp.allowed(+s: TcpState, +t: TcpState) -> Bool:
  Bool.or(U32.is_eq(TcpState.index(s), TcpState.index(t)), Bool.or(TcpState.is(t, 0), Bool.or(Tcp.diagram(s, t), Tcp.text_edge(s, t))))

# The data plane

def Tcp.min.pick(lt: Bool, a: U32, b: U32) -> U32:
  match lt:
    case True{}:
      a
    case False{}:
      b

def Tcp.min(+a: U32, +b: U32) -> U32:
  Tcp.min.pick(U32.is_lt(a, b), a, b)

def Tcp.nmin.pick(lt: Bool, a: Nat, b: Nat) -> Nat:
  match lt:
    case True{}:
      a
    case False{}:
      b

def Tcp.nmin(+a: Nat, +b: Nat) -> Nat:
  Tcp.nmin.pick(Nat.is_lt(a, b), a, b)

def Tcp.u32(n: Nat) -> U32:
  U32.from_nat(n)

def Tcp.opt.mss(o: TcpOptions) -> U32:
  match o:
    case TcpOptions{m, rb, sb, iw, msl, r, sr, ng, ar, ool, rp}:
      m

def Tcp.opt.rto(o: TcpOptions) -> R.RtoParams:
  match o:
    case TcpOptions{m, rb, sb, iw, msl, r, sr, ng, ar, ool, rp}:
      rp

def Tcp.opt.msl2(o: TcpOptions) -> U32:
  match o:
    case TcpOptions{m, rb, sb, iw, +msl, r, sr, ng, ar, ool, rp}:
      U32.add(msl, msl)

# the window we advertise: the receive buffer not filled with unread data,
# at most 65535 (no window scaling)
def Tcp.rcv_wnd(+o: TcpOptions, +r: TcpRcv) -> U32:
  match o r:
    case TcpOptions{m, +rb, sb, iw, msl, rt, sr, ng, ar, ool, rp} TcpRcv{irs, n, q, +u}:
      Tcp.min(U32.sub(rb, Tcp.min(u, rb)), 65535)

# the sender's MSS: the peer's MSS option (536 without one, section 3.7.1),
# at most our own
def Tcp.smss(+o: TcpOptions, m: Maybe<&2, U32>) -> U32:
  Tcp.min(Maybe.default(&2, U32, m, 536), Tcp.opt.mss(o))

# RFC 5681's initial window (equation 1); one segment if the SYN was resent
def Tcp.iw(syn_lost: Bool, +o: TcpOptions, +smss: U32) -> U32:
  match syn_lost:
    case True{}:
      smss
    case False{}:
      match o:
        case TcpOptions{m, rb, sb, +iw, msl, r, sr, ng, ar, ool, rp}:
          Tcp.min(U32.mul(4, smss), CC.Reno.max(U32.mul(2, smss), iw))

def Tcp.flags(+syn: Bool, +ack: Bool, +fin: Bool, +rst: Bool, +psh: Bool) -> U32:
  U32.or(U32.or(U32.mul(Bool.to_u32(fin), 1), U32.mul(Bool.to_u32(syn), 2)), U32.or(U32.or(U32.mul(Bool.to_u32(rst), 4), U32.mul(Bool.to_u32(psh), 8)), U32.mul(Bool.to_u32(ack), 16)))

# Segments the connection sends

def Tcp.seg.ack(+snd: TcpSnd, +rcv: TcpRcv, +o: TcpOptions) -> G.TcpSeg:
  match snd rcv:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin} TcpRcv{irs, rn, q, u}:
      G.TcpSeg{nxt, rn, NT.TcpHeader.ACK(), Tcp.rcv_wnd(o, rcv), None{}, B.Octets.empty()}

# <SEQ=s><CTL=RST>
def Tcp.seg.rst(s: U32) -> G.TcpSeg:
  G.TcpSeg{s, 0, NT.TcpHeader.RST(), 0, None{}, B.Octets.empty()}

# <SEQ=0><ACK=a><CTL=RST,ACK>
def Tcp.seg.rst_ack(a: U32) -> G.TcpSeg:
  G.TcpSeg{0, a, U32.or(NT.TcpHeader.RST(), NT.TcpHeader.ACK()), 0, None{}, B.Octets.empty()}

# our SYN, or SYN,ACK when we have the peer's (has_peer)
def Tcp.seg.syn(has_peer: Bool, +snd: TcpSnd, +rcv: TcpRcv, +o: TcpOptions) -> G.TcpSeg:
  match has_peer:
    case True{}:
      match snd rcv:
        case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin} TcpRcv{irs, rn, q, u}:
          G.TcpSeg{iss, rn, U32.or(NT.TcpHeader.SYN(), NT.TcpHeader.ACK()), Tcp.rcv_wnd(o, rcv), Some{Tcp.opt.mss(o)}, B.Octets.empty()}
    case False{}:
      match snd:
        case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
          G.TcpSeg{iss, 0, NT.TcpHeader.SYN(), Tcp.rcv_wnd(o, rcv), Some{Tcp.opt.mss(o)}, B.Octets.empty()}

# The reply to a segment for a connection that does not exist (section
# 3.10.7.1): nothing to a reset; <SEQ=SEG.ACK><CTL=RST> to an ACK;
# <SEQ=0><ACK=SEG.SEQ+SEG.LEN><CTL=RST,ACK> otherwise
def Tcp.reset_reply.go(rst: Bool, ack: Bool, +s: G.TcpSeg) -> Maybe<&2, G.TcpSeg>:
  match rst:
    case True{}:
      None{}
    case False{}:
      match ack:
        case True{}:
          Some{Tcp.seg.rst(G.TcpSeg.ack(s))}
        case False{}:
          Some{Tcp.seg.rst_ack(U32.add(G.TcpSeg.seq(s), G.TcpSeg.len(s)))}

def Tcp.reset_reply(+s: G.TcpSeg) -> Maybe<&2, G.TcpSeg>:
  Tcp.reset_reply.go(G.TcpSeg.rst(s), G.TcpSeg.is_ack(s), s)

# Send-side facts

# the sequence number of our FIN: just after the data
def Tcp.fin_seq(+snd: TcpSnd) -> U32:
  match snd:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      U32.add(bseq, Tcp.u32(B.Octets.len(buf)))

def Tcp.syn_acked(+snd: TcpSnd) -> Bool:
  match snd:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      S.SeqNum.lt(iss, una)

def Tcp.fin_acked(+snd: TcpSnd) -> Bool:
  match snd:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      Bool.and(fin, S.SeqNum.lt(Tcp.fin_seq(snd), una))

def Tcp.outstanding(+snd: TcpSnd) -> Bool:
  match snd:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      S.SeqNum.lt(una, max)

# the data offset of sequence number x in buf
def Tcp.off(+bseq: U32, +x: U32) -> Nat:
  U32.to_nat(Tcp.pick(U32, S.SeqNum.lt(x, bseq), 0, U32.sub(x, bseq)))

def Tcp.unsent(+snd: TcpSnd) -> Nat:
  match snd:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      Nat.sub(B.Octets.len(buf), Tcp.off(bseq, nxt))

# the usable window (section 3.8.6.2.1): SND.UNA + min(SND.WND, cwnd) - SND.NXT
def Tcp.usable(+snd: TcpSnd, +cwnd: U32) -> U32:
  match snd:
    case TcpSnd{iss, +una, +nxt, max, +wnd, wl1, wl2, smss, buf, bseq, fin}:
      +edge = U32.add(una, Tcp.min(wnd, cwnd))
      Tcp.pick(U32, S.SeqNum.lt(nxt, edge), U32.sub(edge, nxt), 0)

# a zero window holds back data with nothing in flight: probe it
def Tcp.needs_probe(+snd: TcpSnd, +cwnd: U32) -> Bool:
  Bool.and(Nat.is_gt(Tcp.unsent(snd), 0n), Bool.and(U32.is_eq(Tcp.usable(snd, cwnd), 0), Bool.not(Tcp.outstanding(snd))))

# Sending data (section 3.8.6.2.1, with Nagle's algorithm, section 3.7.4)

# what the next segment holds: n bytes, a FIN, whether it goes now
type TcpPlan is Data:
  TcpPlan{go: Bool, n: Nat, fin: Bool}

def Tcp.plan(+o: TcpOptions, +snd: TcpSnd, +cwnd: U32) -> TcpPlan:
  match o snd:
    case TcpOptions{m, rb, sb, iw, msl, r, sr, nagle, ar, ool, rp} TcpSnd{iss, +una, +nxt, max, wnd, wl1, wl2, +smss, +buf, +bseq, fin}:
      +blen = B.Octets.len(buf)
      +off = Tcp.off(bseq, nxt)
      +n = Tcp.nmin(U32.to_nat(smss), Tcp.nmin(Nat.sub(blen, off), U32.to_nat(Tcp.usable(snd, cwnd))))
      +fin_now = Bool.and(fin, Nat.is_eq(Nat.add(off, n), blen))
      +hold = Bool.and(nagle, Bool.and(Nat.is_gt(n, 0n), Bool.and(Nat.is_lt(n, U32.to_nat(smss)), S.SeqNum.lt(una, nxt))))
      TcpPlan{Bool.and(Bool.not(hold), Bool.or(Nat.is_gt(n, 0n), fin_now)), n, fin_now}

# the result of sending: the send side, timers, actions so far (newest
# first), and whether anything was sent
type TcpSent is Data:
  TcpSent{snd: TcpSnd, tim: TcpTim, acts: List<&2, TcpAction>, sent: Bool}

def TcpSent.snd(r: TcpSent) -> TcpSnd:
  match r:
    case TcpSent{s, t, a, x}:
      s

# start timing a segment ending before end, if nothing is being timed and the
# segment is new (Karn's algorithm: never time a retransmission)
def Tcp.time_seg(fresh: Bool, +tim: TcpTim, +end: U32, +now: U32) -> TcpTim:
  match fresh:
    case False{}:
      tim
    case True{}:
      match tim:
        case TcpTim{rto, rtx, tw, retx, rtt, sl}:
          match rtt:
            case None{}:
              TcpTim{rto, rtx, tw, retx, Some{TcpRtt{end, now}}, sl}
            case Some{x}:
              TcpTim{rto, rtx, tw, retx, Some{x}, sl}

# one segment of n bytes (and a FIN) from SND.NXT
def Tcp.emit(snd: TcpSnd, +rcv: TcpRcv, +o: TcpOptions, +now: U32, +n: Nat, +fin_now: Bool, tim: TcpTim, acts: List<&2, TcpAction>) -> TcpSent:
  match snd rcv:
    case TcpSnd{iss, una, +nxt, +max, wnd, wl1, wl2, smss, +buf, +bseq, fin} TcpRcv{irs, +rn, q, u}:
      +k = Tcp.u32(n)
      +data = B.Octets.slice(Tcp.off(bseq, nxt), n, buf)
      +nxt2 = U32.add(nxt, U32.add(k, Bool.to_u32(fin_now)))
      +seg = {G.TcpSeg{nxt, rn, Tcp.flags(False{}, True{}, fin_now, False{}, U32.is_ne(k, 0)), Tcp.rcv_wnd(o, rcv), None{}, data} : G.TcpSeg}
      +snd2 = {TcpSnd{iss, una, nxt2, S.SeqNum.max(max, nxt2), wnd, wl1, wl2, smss, buf, bseq, fin} : TcpSnd}
      TcpSent{snd2, Tcp.time_seg(S.SeqNum.le(max, nxt), tim, nxt2, now), Con{TcpOut{seg}, acts}, True{}}

# send while the plan says so; fuel bounds the loop (each segment takes at
# least one sequence number)
def Tcp.output.go(fuel: Nat, plan: TcpPlan, +o: TcpOptions, +rcv: TcpRcv, +now: U32, +cwnd: U32, r: TcpSent) -> TcpSent:
  match fuel:
    case 0n:
      r
    case 1n+f:
      match plan:
        case TcpPlan{go, +n, +fin_now}:
          match go:
            case False{}:
              r
            case True{}:
              match r:
                case TcpSent{snd, tim, acts, sent}:
                  +r2 = Tcp.emit(snd, rcv, o, now, n, fin_now, tim, acts)
                  Tcp.output.go(f, Tcp.plan(o, TcpSent.snd(r2), cwnd), o, rcv, now, cwnd, r2)

def Tcp.output(+o: TcpOptions, +rcv: TcpRcv, +now: U32, +cwnd: U32, +snd: TcpSnd, tim: TcpTim, acts: List<&2, TcpAction>) -> TcpSent:
  Tcp.output.go(1n+Tcp.unsent(snd), Tcp.plan(o, snd, cwnd), o, rcv, now, cwnd, TcpSent{snd, tim, acts, False{}})

# a probe of a zero window: one byte past it (section 3.8.6.1)
def Tcp.probe(tim: TcpTim, +o: TcpOptions, +rcv: TcpRcv, +now: U32, +snd: TcpSnd, acts: List<&2, TcpAction>) -> TcpSent:
  match tim:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      Tcp.emit(snd, rcv, o, now, 1n, False{}, TcpTim{rto, rtx, tw, retx, None{}, sl}, acts)

# the first unacknowledged segment again (fast retransmit, or a timeout
# before the SYN is acknowledged); SND.NXT does not move
def Tcp.resend_first.go(syn_done: Bool, has_peer: Bool, +snd: TcpSnd, +rcv: TcpRcv, +o: TcpOptions) -> G.TcpSeg:
  match syn_done:
    case False{}:
      Tcp.seg.syn(has_peer, snd, rcv, o)
    case True{}:
      match snd rcv:
        case TcpSnd{iss, +una, nxt, +max, wnd, wl1, wl2, +smss, +buf, +bseq, +fin} TcpRcv{irs, +rn, q, u}:
          +off = Tcp.off(bseq, una)
          +blen = B.Octets.len(buf)
          +n = Tcp.nmin(U32.to_nat(smss), Nat.sub(blen, off))
          +fin_now = Bool.and(Bool.and(fin, S.SeqNum.lt(Tcp.fin_seq(snd), max)), Nat.is_eq(Nat.add(off, n), blen))
          G.TcpSeg{una, rn, Tcp.flags(False{}, True{}, fin_now, False{}, Nat.is_gt(n, 0n)), Tcp.rcv_wnd(o, rcv), None{}, B.Octets.slice(off, n, buf)}

# (has_peer: the peer's SYN has arrived, so a SYN goes out as SYN,ACK)
def Tcp.resend_first(+o: TcpOptions, +rcv: TcpRcv, +snd: TcpSnd, has_peer: Bool) -> G.TcpSeg:
  Tcp.resend_first.go(Tcp.syn_acked(snd), has_peer, snd, rcv, o)

# Field readers

def TcpSnd.una(s: TcpSnd) -> U32:
  match s:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      una

def TcpSnd.nxt(s: TcpSnd) -> U32:
  match s:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      nxt

def TcpSnd.max(s: TcpSnd) -> U32:
  match s:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      max

def TcpSnd.wnd(s: TcpSnd) -> U32:
  match s:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      wnd

def TcpSnd.smss(s: TcpSnd) -> U32:
  match s:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      smss

def TcpSnd.iss(s: TcpSnd) -> U32:
  match s:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      iss

def TcpSnd.buf(s: TcpSnd) -> B.Octets:
  match s:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      buf

def TcpRcv.nxt(r: TcpRcv) -> U32:
  match r:
    case TcpRcv{irs, n, q, u}:
      n

def TcpTim.rto(t: TcpTim) -> R.Rto:
  match t:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      rto

def TcpTim.retx(t: TcpTim) -> U32:
  match t:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      retx

def TcpTim.syn_lost(t: TcpTim) -> Bool:
  match t:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      sl

def TcpTcb.snd(t: TcpTcb) -> TcpSnd:
  match t:
    case TcpTcb{p, s, r, m}:
      s

def TcpTcb.rcv(t: TcpTcb) -> TcpRcv:
  match t:
    case TcpTcb{p, s, r, m}:
      r

def TcpTcb.tim(t: TcpTcb) -> TcpTim:
  match t:
    case TcpTcb{p, s, r, m}:
      m

def TcpTcb.passive(t: TcpTcb) -> Bool:
  match t:
    case TcpTcb{p, s, r, m}:
      p

def TcpSeg.wnd(s: G.TcpSeg) -> U32:
  match s:
    case G.TcpSeg{q, a, f, w, m, d}:
      w

def TcpSeg.mss(s: G.TcpSeg) -> Maybe<&2, U32>:
  match s:
    case G.TcpSeg{q, a, f, w, m, d}:
      m

def TcpSeg.dlen(+s: G.TcpSeg) -> Nat:
  B.Octets.len(G.TcpSeg.data(s))

# Congestion control calls (cc is a template: each use inlines it)

def Tcp.cc_start.go(-C: Data, cc: CC.TcpCc<C>, smss: U32, iw: U32) -> C:
  CC.TcpCc{s, w, a, d, t} = cc
  s(smss, iw)

def Tcp.cc_start(~C: Data, ~cc: CC.TcpCc<C>, smss: U32, iw: U32) -> C:
  Tcp.cc_start.go(C, cc, smss, iw)

def Tcp.cc_cwnd.go(-C: Data, cc: CC.TcpCc<C>, c: C) -> U32:
  CC.TcpCc{s, w, a, d, t} = cc
  w(c)

def Tcp.cc_cwnd(~C: Data, ~cc: CC.TcpCc<C>, c: C) -> U32:
  Tcp.cc_cwnd.go(C, cc, c)

def Tcp.cc_ack.go(-C: Data, cc: CC.TcpCc<C>, c: C, info: CC.TcpAckInfo) -> C:
  CC.TcpCc{s, w, a, d, t} = cc
  a(c, info)

def Tcp.cc_ack(~C: Data, ~cc: CC.TcpCc<C>, c: C, info: CC.TcpAckInfo) -> C:
  Tcp.cc_ack.go(C, cc, c, info)

def Tcp.cc_dupack.go(-C: Data, cc: CC.TcpCc<C>, c: C, info: CC.TcpAckInfo) -> Pair(C, Bool):
  CC.TcpCc{s, w, a, d, t} = cc
  d(c, info)

def Tcp.cc_dupack(~C: Data, ~cc: CC.TcpCc<C>, c: C, info: CC.TcpAckInfo) -> Pair(C, Bool):
  Tcp.cc_dupack.go(C, cc, c, info)

def Tcp.cc_timeout.go(-C: Data, cc: CC.TcpCc<C>, c: C, info: CC.TcpAckInfo) -> C:
  CC.TcpCc{s, w, a, d, t} = cc
  t(c, info)

def Tcp.cc_timeout(~C: Data, ~cc: CC.TcpCc<C>, c: C, info: CC.TcpAckInfo) -> C:
  Tcp.cc_timeout.go(C, cc, c, info)

# Work in progress on one event: whether processing goes on, the input for
# the state diagram, the TCB, the congestion state, the actions (newest
# first), whether an ACK is due, and whether new data was acknowledged
type TcpW<-C: Data> is Data:
  TcpW{go: Bool, input: TcpInput, tcb: TcpTcb, cc: C, acts: List<&2, TcpAction>, ack_now: Bool, acked_new: Bool}

def TcpW.tcb(-C: Data, w: TcpW<C>) -> TcpTcb:
  match w:
    case TcpW{g, k, t, c, a, n, x}:
      t

# What one event does
type TcpFx<-C: Data> is Data:
  TcpFx{input: TcpInput, tcb: TcpTcb, cc: C, acts: List<&2, TcpAction>}

def TcpFx.input(-C: Data, f: TcpFx<C>) -> TcpInput:
  match f:
    case TcpFx{k, t, c, a}:
      k

def TcpFx.tcb(-C: Data, f: TcpFx<C>) -> TcpTcb:
  match f:
    case TcpFx{k, t, c, a}:
      t

def TcpFx.cc(-C: Data, f: TcpFx<C>) -> C:
  match f:
    case TcpFx{k, t, c, a}:
      c

def TcpFx.acts(-C: Data, f: TcpFx<C>) -> List<&2, TcpAction>:
  match f:
    case TcpFx{k, t, c, a}:
      a

# stop here with input k
def Tcp.stop(-C: Data, k: TcpInput, tcb: TcpTcb, c: C, acts: List<&2, TcpAction>) -> TcpW<C>:
  TcpW{False{}, k, tcb, c, acts, False{}, False{}}

def Tcp.push(-A: Data, c: Bool, x: A, xs: List<&2, A>) -> List<&2, A>:
  match c:
    case True{}:
      Con{x, xs}
    case False{}:
      xs

# Acknowledgments (section 3.10.7.4, fifth step; RFC 6298; RFC 5681)

# whether SEG.ACK = ack acknowledges new data: SND.UNA < SEG.ACK =< SND.MAX
# (section 3.10.7.4, fifth step; SND.MAX, the highest sequence number sent,
# stands for SND.NXT, which a retransmission timeout moves back)
def Tcp.acks_new(+snd: TcpSnd, +ack: U32) -> Bool:
  Bool.and(S.SeqNum.lt(TcpSnd.una(snd), ack), S.SeqNum.le(ack, TcpSnd.max(snd)))

# whether SND.UNA, from una0, stayed or moved forward to at most max0: what
# an acknowledgment of data that was sent may do
def Tcp.acked_sent(+una0: U32, +max0: U32, +una1: U32) -> Bool:
  Bool.or(U32.is_eq(una1, una0), Bool.and(S.SeqNum.lt(una0, una1), S.SeqNum.le(una1, max0)))

# SEG.ACK = ack acknowledged new data: SND.UNA moves, acknowledged data
# leaves the buffer
def Tcp.ack_new(+snd: TcpSnd, +ack: U32) -> TcpSnd:
  match snd:
    case TcpSnd{iss, una, +nxt, max, wnd, wl1, wl2, smss, +buf, +bseq, fin}:
      +dacked = Tcp.nmin(Tcp.off(bseq, ack), B.Octets.len(buf))
      TcpSnd{iss, ack, S.SeqNum.max(nxt, ack), max, wnd, wl1, wl2, smss, B.Octets.drop(dacked, buf), U32.add(bseq, Tcp.u32(dacked)), fin}

# the window update rule: SND.WL1 < SEG.SEQ, or SND.WL1 = SEG.SEQ and
# SND.WL2 =< SEG.ACK
def Tcp.wnd_update.go(upd: Bool, +snd: TcpSnd, +sq: U32, +ack: U32, +sw: U32) -> TcpSnd:
  match upd:
    case False{}:
      snd
    case True{}:
      match snd:
        case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
          TcpSnd{iss, una, nxt, max, sw, sq, ack, smss, buf, bseq, fin}

def Tcp.wnd_update(inrange: Bool, +snd: TcpSnd, +sq: U32, +ack: U32, +sw: U32) -> TcpSnd:
  match inrange:
    case False{}:
      snd
    case True{}:
      match snd:
        case TcpSnd{iss, una, nxt, max, wnd, +wl1, +wl2, smss, buf, bseq, fin}:
          Tcp.wnd_update.go(Bool.or(S.SeqNum.lt(wl1, sq), Bool.and(U32.is_eq(wl1, sq), S.SeqNum.le(wl2, ack))), snd, sq, ack, sw)

# a new acknowledgment ends a round-trip measurement it covers (a sample),
# and resets the retransmission count
def Tcp.rtt_ack.go(covered: Bool, +p: R.RtoParams, +now: U32, +start: U32, +tim: TcpTim) -> TcpTim:
  match covered:
    case True{}:
      match tim:
        case TcpTim{rto, rtx, tw, retx, rtt, sl}:
          TcpTim{R.Rto.sample(p, rto, U32.sub(now, start)), rtx, tw, 0, None{}, sl}
    case False{}:
      match tim:
        case TcpTim{rto, rtx, tw, retx, rtt, sl}:
          TcpTim{rto, rtx, tw, 0, rtt, sl}

def Tcp.rtt_ack(+p: R.RtoParams, +now: U32, +ack: U32, +tim: TcpTim) -> TcpTim:
  match tim:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      match rtt:
        case None{}:
          TcpTim{rto, rtx, tw, 0, None{}, sl}
        case Some{TcpRtt{+s, +t}}:
          Tcp.rtt_ack.go(S.SeqNum.le(s, ack), p, now, t, TcpTim{rto, rtx, tw, retx, Some{TcpRtt{s, t}}, sl})

def Tcp.retx_reset(+tim: TcpTim) -> TcpTim:
  match tim:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      TcpTim{rto, rtx, tw, 0, rtt, sl}

# a duplicate acknowledgment: RFC 5681 section 2's definition
def Tcp.is_dupack(+snd: TcpSnd, +seg: G.TcpSeg) -> Bool:
  Bool.and(U32.is_eq(G.TcpSeg.ack(seg), TcpSnd.una(snd)), Bool.and(Nat.is_eq(TcpSeg.dlen(seg), 0n), Bool.and(Bool.not(Bool.or(G.TcpSeg.fin(seg), G.TcpSeg.syn(seg))), Bool.and(U32.is_eq(TcpSeg.wnd(seg), TcpSnd.wnd(snd)), Tcp.outstanding(snd)))))

def Tcp.on_dup.fast(-C: Data, r: Pair(C, Bool), seg: G.TcpSeg, acts: List<&2, TcpAction>) -> Pair(C, List<&2, TcpAction>):
  match r:
    case (c2, fast):
      (c2, Tcp.push(TcpAction, fast, TcpOut{seg}, acts))

def Tcp.on_dup(~C: Data, ~cc: CC.TcpCc<C>, dup: Bool, +o: TcpOptions, +tcb: TcpTcb, c: C, acts: List<&2, TcpAction>) -> Pair(C, List<&2, TcpAction>):
  match dup:
    case False{}:
      (c, acts)
    case True{}:
      +snd = TcpTcb.snd(tcb)
      Tcp.on_dup.fast(C, Tcp.cc_dupack(~C, ~cc, c, CC.TcpAckInfo{0, TcpSnd.smss(snd), U32.sub(TcpSnd.max(snd), TcpSnd.una(snd))}), Tcp.resend_first(o, TcpTcb.rcv(tcb), snd, True{}), acts)

def Tcp.on_new(~C: Data, ~cc: CC.TcpCc<C>, new: Bool, +o: TcpOptions, +now: U32, +ack: U32, +tcb: TcpTcb, c: C) -> Pair(TcpTcb, C):
  match new:
    case False{}:
      (tcb, c)
    case True{}:
      match tcb:
        case TcpTcb{p, +snd, rcv, tim}:
          +info = {CC.TcpAckInfo{U32.sub(ack, TcpSnd.una(snd)), TcpSnd.smss(snd), U32.sub(TcpSnd.max(snd), TcpSnd.una(snd))} : CC.TcpAckInfo}
          (TcpTcb{p, Tcp.ack_new(snd, ack), rcv, Tcp.rtt_ack(Tcp.opt.rto(o), now, ack, tim)}, Tcp.cc_ack(~C, ~cc, c, info))

def Tcp.on_ack.fin(-C: Data, +inrange: Bool, +new: Bool, +seg: G.TcpSeg, an: Bool, acts: List<&2, TcpAction>, r: Pair(TcpTcb, C)) -> TcpW<C>:
  match r:
    case (TcpTcb{p, snd2, rcv2, +tim2}, c2):
      +tim3 = Tcp.pick(TcpTim, inrange, Tcp.retx_reset(tim2), tim2)
      +snd3 = Tcp.wnd_update(inrange, snd2, G.TcpSeg.seq(seg), G.TcpSeg.ack(seg), TcpSeg.wnd(seg))
      TcpW{True{}, TcpInNone{}, TcpTcb{p, snd3, rcv2, tim3}, c2, acts, an, new}

def Tcp.on_ack.dup(~C: Data, ~cc: CC.TcpCc<C>, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: TcpTcb, an: Bool, r: Pair(C, List<&2, TcpAction>)) -> TcpW<C>:
  match r:
    case (c1, acts1):
      +ack = G.TcpSeg.ack(seg)
      +snd = TcpTcb.snd(tcb)
      +new = Tcp.acks_new(snd, ack)
      Tcp.on_ack.fin(C, Bool.and(S.SeqNum.le(TcpSnd.una(snd), ack), S.SeqNum.le(ack, TcpSnd.max(snd))), new, seg, an, acts1, Tcp.on_new(~C, ~cc, new, o, now, ack, tcb, c1))

def Tcp.on_ack.go(~C: Data, ~cc: CC.TcpCc<C>, future: Bool, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: TcpTcb, c: C, acts: List<&2, TcpAction>, an: Bool) -> TcpW<C>:
  match future:
    case True{}:
      # it acknowledges something not yet sent: ACK, and drop the segment
      Tcp.stop(C, TcpInNone{}, tcb, c, Con{TcpOut{Tcp.seg.ack(TcpTcb.snd(tcb), TcpTcb.rcv(tcb), o)}, acts})
    case False{}:
      Tcp.on_ack.dup(~C, ~cc, o, now, seg, tcb, an, Tcp.on_dup(~C, ~cc, Tcp.is_dupack(TcpTcb.snd(tcb), seg), o, tcb, c, acts))

def Tcp.on_ack(~C: Data, ~cc: CC.TcpCc<C>, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, w: TcpW<C>) -> TcpW<C>:
  match w:
    case TcpW{go, k, +tcb, c, acts, an, nw}:
      match go:
        case False{}:
          TcpW{False{}, k, tcb, c, acts, an, nw}
        case True{}:
          Tcp.on_ack.go(~C, ~cc, S.SeqNum.lt(TcpSnd.max(TcpTcb.snd(tcb)), G.TcpSeg.ack(seg)), o, now, seg, tcb, c, acts, an)

# Data and FIN (section 3.10.7.4, seventh and eighth steps)

def Tcp.ooo_limit(o: TcpOptions) -> Nat:
  match o:
    case TcpOptions{m, rb, sb, iw, msl, r, sr, ng, ar, ool, rp}:
      U32.to_nat(ool)

def Tcp.app_reads(o: TcpOptions) -> Bool:
  match o:
    case TcpOptions{m, rb, sb, iw, msl, r, sr, ng, ar, ool, rp}:
      ar

# the input a segment that passed the checks gives: from SYN-SENT, a SYN,ACK
def Tcp.seg_input(synsent: Bool, af: Bool, fin: Bool) -> TcpInput:
  match synsent:
    case True{}:
      TcpInSynAck{fin}
    case False{}:
      TcpInSeg{af, fin}

# what the receive side made of a segment: the receive side, whether its FIN
# was taken, and the actions
type TcpText is Data:
  TcpText{rcv: TcpRcv, fin: Bool, acts: List<&2, TcpAction>}

def Tcp.text.out(+o: TcpOptions, +seg: G.TcpSeg, +dseq: U32, +kept: B.Octets, irs: U32, +rn: U32, +unread: U32, acts: List<&2, TcpAction>, out: Q.RcvOut) -> TcpText:
  match out:
    case Q.RcvOut{qn, qh, +got}:
      +glen = B.Octets.len(got)
      +rn2 = U32.add(rn, Tcp.u32(glen))
      +fin_kept = Bool.and(G.TcpSeg.fin(seg), Nat.is_eq(B.Octets.len(kept), B.Octets.len(G.TcpSeg.data(seg))))
      +fin_ok = Bool.and(fin_kept, U32.is_eq(rn2, U32.add(dseq, Tcp.u32(B.Octets.len(kept)))))
      +unread2 = Tcp.pick(U32, Tcp.app_reads(o), U32.add(unread, Tcp.u32(glen)), unread)
      TcpText{TcpRcv{irs, U32.add(rn2, Bool.to_u32(fin_ok)), Q.RcvQ{qn, qh}, unread2}, fin_ok, Tcp.push(TcpAction, Nat.is_gt(glen, 0n), TcpDeliver{got}, acts)}

# the data of seg past RCV.NXT (fresh: it starts there or later), within the
# window, into the receive queue
def Tcp.text.go(fresh: Bool, +o: TcpOptions, +seg: G.TcpSeg, +dseq: U32, +rcv: TcpRcv, acts: List<&2, TcpAction>) -> TcpText:
  match fresh:
    case False{}:
      TcpText{rcv, False{}, acts}
    case True{}:
      match rcv:
        case TcpRcv{irs, +rn, q, +unread}:
          +rel = U32.to_nat(U32.sub(dseq, rn))
          +room = Nat.sub(U32.to_nat(Tcp.rcv_wnd(o, rcv)), rel)
          +kept = B.Octets.take(room, G.TcpSeg.data(seg))
          Tcp.text.out(o, seg, dseq, kept, irs, rn, unread, acts, Q.RcvQ.insert(Tcp.ooo_limit(o), q, rel, kept))

# seg's data starts after its SYN; the bytes before RCV.NXT are here already
def Tcp.text(+o: TcpOptions, +seg: G.TcpSeg, +rcv: TcpRcv, acts: List<&2, TcpAction>) -> TcpText:
  +rn = TcpRcv.nxt(rcv)
  +dseq0 = U32.add(G.TcpSeg.seq(seg), Bool.to_u32(G.TcpSeg.syn(seg)))
  +skip = Tcp.nmin(Tcp.off(dseq0, rn), TcpSeg.dlen(seg))
  +dseq = U32.add(dseq0, Tcp.u32(skip))
  +seg2 = {G.TcpSeg{dseq, G.TcpSeg.ack(seg), G.TcpSeg.flags(seg), TcpSeg.wnd(seg), None{}, B.Octets.drop(skip, G.TcpSeg.data(seg))} : G.TcpSeg}
  Tcp.text.go(S.SeqNum.le(rn, dseq), o, seg2, dseq, rcv, acts)

def Tcp.on_text.done(-C: Data, +synsent: Bool, +af: Bool, p: Bool, snd: TcpSnd, tim: TcpTim, c: C, an: Bool, nw: Bool, t: TcpText) -> TcpW<C>:
  match t:
    case TcpText{rcv2, +fin_ok, acts2}:
      TcpW{True{}, Tcp.seg_input(synsent, af, fin_ok), TcpTcb{p, snd, rcv2, tim}, c, acts2, Bool.or(an, fin_ok), nw}

def Tcp.on_text.go(-C: Data, takes: Bool, +synsent: Bool, +o: TcpOptions, +seg: G.TcpSeg, +tcb: TcpTcb, c: C, acts: List<&2, TcpAction>, an: Bool, nw: Bool) -> TcpW<C>:
  match takes:
    case False{}:
      TcpW{True{}, TcpInSeg{Tcp.fin_acked(TcpTcb.snd(tcb)), False{}}, tcb, c, acts, Bool.or(an, Bool.or(Nat.is_gt(TcpSeg.dlen(seg), 0n), G.TcpSeg.fin(seg))), nw}
    case True{}:
      match tcb:
        case TcpTcb{p, +snd, rcv, tim}:
          Tcp.on_text.done(C, synsent, Tcp.fin_acked(snd), p, snd, tim, c, Bool.or(an, Nat.is_gt(TcpSeg.dlen(seg), 0n)), nw, Tcp.text(o, seg, rcv, acts))

# takes: the state takes data (SYN-RECEIVED, ESTABLISHED, FIN-WAIT-1 and 2);
# synsent: the segment completes an active open
def Tcp.on_text(-C: Data, +takes: Bool, +synsent: Bool, +o: TcpOptions, +seg: G.TcpSeg, w: TcpW<C>) -> TcpW<C>:
  match w:
    case TcpW{go, k, tcb, c, acts, an, nw}:
      match go:
        case False{}:
          TcpW{False{}, k, tcb, c, acts, an, nw}
        case True{}:
          Tcp.on_text.go(C, takes, synsent, o, seg, tcb, c, acts, an, nw)

def TcpState.takes_text(s: TcpState) -> Bool:
  match s:
    case TcpSynReceived{}:
      True{}
    case TcpEstablished{}:
      True{}
    case TcpFinWait1{}:
      True{}
    case TcpFinWait2{}:
      True{}
    case _:
      False{}

# Segment arrival in a synchronized state (SYN-RECEIVED to TIME-WAIT)

# section 3.10.7.4, first step: the four cases of Table 6, and RCV.WND = 0
# still takes a segment at RCV.NXT (its data is then trimmed away), so that
# ACKs keep working
def Tcp.acceptable.go(zl: Bool, zw: Bool, +sq: U32, +slen: U32, +rn: U32, +wnd: U32) -> Bool:
  match zl zw:
    case True{} True{}:
      U32.is_eq(sq, rn)
    case True{} False{}:
      S.SeqNum.in_window(sq, rn, wnd)
    case False{} True{}:
      False{}
    case False{} False{}:
      Bool.or(S.SeqNum.in_window(sq, rn, wnd), S.SeqNum.in_window(U32.sub(U32.add(sq, slen), 1), rn, wnd))

def Tcp.acceptable(+slen: U32, +sq: U32, +rn: U32, +wnd: U32) -> Bool:
  Bool.or(U32.is_eq(sq, rn), Tcp.acceptable.go(U32.is_eq(slen, 0), U32.is_eq(wnd, 0), sq, slen, rn, wnd))

def TcpTim.set_tw(+tim: TcpTim, at: Maybe<&2, U32>) -> TcpTim:
  match tim:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      TcpTim{rto, rtx, at, retx, rtt, sl}

def TcpTim.set_rtx(+tim: TcpTim, at: Maybe<&2, U32>) -> TcpTim:
  match tim:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      TcpTim{rto, at, tw, retx, rtt, sl}

def TcpTcb.set_tim(+tcb: TcpTcb, tim: TcpTim) -> TcpTcb:
  match tcb:
    case TcpTcb{p, s, r, m}:
      TcpTcb{p, s, r, tim}

def TcpTcb.set_snd(+tcb: TcpTcb, snd: TcpSnd) -> TcpTcb:
  match tcb:
    case TcpTcb{p, s, r, m}:
      TcpTcb{p, snd, r, m}

def TcpTcb.set_rcv(+tcb: TcpTcb, rcv: TcpRcv) -> TcpTcb:
  match tcb:
    case TcpTcb{p, s, r, m}:
      TcpTcb{p, s, rcv, m}

def Tcp.ack_of(+o: TcpOptions, +tcb: TcpTcb) -> TcpAction:
  TcpOut{Tcp.seg.ack(TcpTcb.snd(tcb), TcpTcb.rcv(tcb), o)}

# not acceptable: ACK it (unless it is a reset) and drop it; in TIME-WAIT a
# resent FIN also restarts the 2 MSL timer
def Tcp.sync.unacceptable(+tw: Bool, -C: Data, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: TcpTcb, c: C, acts: List<&2, TcpAction>) -> TcpW<C>:
  +tcb2 = Tcp.pick(TcpTcb, Bool.and(tw, G.TcpSeg.fin(seg)), TcpTcb.set_tim(tcb, TcpTim.set_tw(TcpTcb.tim(tcb), Some{U32.add(now, Tcp.opt.msl2(o))})), tcb)
  Tcp.stop(C, TcpInNone{}, tcb2, c, Tcp.push(TcpAction, Bool.not(G.TcpSeg.rst(seg)), Tcp.ack_of(o, tcb), acts))

# a reset in the window: exactly at RCV.NXT it resets; elsewhere it gets a
# challenge ACK (RFC 9293 section 3.10.7.4 second step, from RFC 5961)
def Tcp.sync.rst(exact: Bool, -C: Data, +to_listen: Bool, +o: TcpOptions, +tcb: TcpTcb, c: C, acts: List<&2, TcpAction>) -> TcpW<C>:
  match exact:
    case True{}:
      Tcp.stop(C, TcpInReset{to_listen}, tcb, c, acts)
    case False{}:
      Tcp.stop(C, TcpInNone{}, tcb, c, Con{Tcp.ack_of(o, tcb), acts})

# a SYN: in SYN-RECEIVED after a passive open, back to LISTEN; otherwise a
# challenge ACK (fourth step)
def Tcp.sync.syn(back: Bool, -C: Data, +o: TcpOptions, +tcb: TcpTcb, c: C, acts: List<&2, TcpAction>) -> TcpW<C>:
  match back:
    case True{}:
      Tcp.stop(C, TcpInReset{True{}}, tcb, c, acts)
    case False{}:
      Tcp.stop(C, TcpInNone{}, tcb, c, Con{Tcp.ack_of(o, tcb), acts})

# in SYN-RECEIVED, an ACK that does not acknowledge our SYN gets
# <SEQ=SEG.ACK><CTL=RST> (fifth step)
def Tcp.sync.synrcvd(bad: Bool, -C: Data, +seg: G.TcpSeg, +tcb: TcpTcb, c: C, acts: List<&2, TcpAction>) -> TcpW<C>:
  match bad:
    case True{}:
      Tcp.stop(C, TcpInNone{}, tcb, c, Con{TcpOut{Tcp.seg.rst(G.TcpSeg.ack(seg))}, acts})
    case False{}:
      TcpW{True{}, TcpInNone{}, tcb, c, acts, False{}, False{}}

def Tcp.sync.checks(acc: Bool, rst: Bool, syn: Bool, ackf: Bool, -C: Data, +st: TcpState, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match acc:
    case False{}:
      Tcp.sync.unacceptable(TcpState.is(st, 10), C, o, now, seg, tcb, c, Nil{})
    case True{}:
      match rst:
        case True{}:
          Tcp.sync.rst(U32.is_eq(G.TcpSeg.seq(seg), TcpRcv.nxt(TcpTcb.rcv(tcb))), C, Bool.and(TcpState.is(st, 3), TcpTcb.passive(tcb)), o, tcb, c, Nil{})
        case False{}:
          match syn:
            case True{}:
              Tcp.sync.syn(Bool.and(TcpState.is(st, 3), TcpTcb.passive(tcb)), C, o, tcb, c, Nil{})
            case False{}:
              match ackf:
                case False{}:
                  Tcp.stop(C, TcpInNone{}, tcb, c, Nil{})
                case True{}:
                  +ack = G.TcpSeg.ack(seg)
                  +snd = TcpTcb.snd(tcb)
                  Tcp.sync.synrcvd(Bool.and(TcpState.is(st, 3), Bool.not(Bool.and(S.SeqNum.lt(TcpSnd.una(snd), ack), S.SeqNum.le(ack, TcpSnd.max(snd))))), C, seg, tcb, c, Nil{})

def Tcp.arrive.sync(~C: Data, ~cc: CC.TcpCc<C>, +st: TcpState, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: TcpTcb, c: C) -> TcpW<C>:
  +rcv = TcpTcb.rcv(tcb)
  +acc = Tcp.acceptable(G.TcpSeg.len(seg), G.TcpSeg.seq(seg), TcpRcv.nxt(rcv), Tcp.rcv_wnd(o, rcv))
  +w = Tcp.sync.checks(acc, G.TcpSeg.rst(seg), G.TcpSeg.syn(seg), G.TcpSeg.is_ack(seg), C, st, o, now, seg, tcb, c)
  Tcp.on_text(C, TcpState.takes_text(st), False{}, o, seg, Tcp.on_ack(~C, ~cc, o, now, seg, w))

# Segment arrival in SYN-SENT (section 3.10.7.3)

# the TCB once the peer's SYN is in: IRS, RCV.NXT, the send window
def Tcp.synsent.tcb(+o: TcpOptions, +seg: G.TcpSeg, tcb: TcpTcb) -> TcpTcb:
  match tcb:
    case TcpTcb{p, snd, rcv, tim}:
      match snd:
        case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
          +sq = G.TcpSeg.seq(seg)
          TcpTcb{p, TcpSnd{iss, una, nxt, max, TcpSeg.wnd(seg), sq, G.TcpSeg.ack(seg), Tcp.smss(o, TcpSeg.mss(seg)), buf, bseq, fin}, TcpRcv{sq, U32.add(sq, 1), Q.RcvQ.new(), 0}, tim}

def Tcp.synsent.syn(~C: Data, ~cc: CC.TcpCc<C>, ackf: Bool, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb2: TcpTcb, c: C) -> TcpW<C>:
  match ackf:
    case True{}:
      # our SYN is acknowledged: ESTABLISHED, and the rest of the segment
      # (data, FIN) is processed (sixth step on)
      Tcp.on_text(C, True{}, True{}, o, seg, Tcp.on_ack(~C, ~cc, o, now, seg, TcpW{True{}, TcpInNone{}, tcb2, c, Nil{}, True{}, False{}}))
    case False{}:
      # a simultaneous open: SYN-RECEIVED, and our SYN again with an ACK
      Tcp.stop(C, TcpInSyn{}, tcb2, c, [TcpOut{Tcp.seg.syn(True{}, TcpTcb.snd(tcb2), TcpTcb.rcv(tcb2), o)}])

def Tcp.synsent.go(~C: Data, ~cc: CC.TcpCc<C>, bad_ack: Bool, rst: Bool, syn: Bool, +ackf: Bool, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match bad_ack:
    case True{}:
      Tcp.stop(C, TcpInNone{}, tcb, c, Tcp.push(TcpAction, Bool.not(rst), TcpOut{Tcp.seg.rst(G.TcpSeg.ack(seg))}, Nil{}))
    case False{}:
      match rst:
        case True{}:
          Tcp.stop(C, Tcp.pick(TcpInput, ackf, TcpInReset{False{}}, TcpInNone{}), tcb, c, Nil{})
        case False{}:
          match syn:
            case False{}:
              Tcp.stop(C, TcpInNone{}, tcb, c, Nil{})
            case True{}:
              Tcp.synsent.syn(~C, ~cc, ackf, o, now, seg, Tcp.synsent.tcb(o, seg, tcb), c)

def Tcp.arrive.synsent(~C: Data, ~cc: CC.TcpCc<C>, +o: TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: TcpTcb, c: C) -> TcpW<C>:
  +snd = TcpTcb.snd(tcb)
  +ack = G.TcpSeg.ack(seg)
  +ackf = G.TcpSeg.is_ack(seg)
  +rst = G.TcpSeg.rst(seg)
  +ack_ok = Bool.and(S.SeqNum.lt(TcpSnd.iss(snd), ack), S.SeqNum.le(ack, TcpSnd.max(snd)))
  Tcp.synsent.go(~C, ~cc, Bool.and(ackf, Bool.not(ack_ok)), rst, G.TcpSeg.syn(seg), ackf, o, now, seg, tcb, c)

# Segment arrival in LISTEN (section 3.10.7.2)

# a TCB for a connection with ISS isn: SND.UNA = ISS, SND.NXT = ISS + 1, and
# the SYN timed for a round-trip sample
def Tcp.tcb.open(+o: TcpOptions, +now: U32, +isn: U32, passive: Bool, wnd: U32, wl1: U32, smss: U32, rcv: TcpRcv) -> TcpTcb:
  +n1 = U32.add(isn, 1)
  TcpTcb{passive, TcpSnd{isn, isn, n1, n1, wnd, wl1, isn, smss, B.Octets.empty(), n1, False{}}, rcv, TcpTim{R.Rto.start(Tcp.opt.rto(o)), None{}, None{}, 0, Some{TcpRtt{n1, now}}, False{}}}

def Tcp.listen.go(rst: Bool, ackf: Bool, syn: Bool, -C: Data, +o: TcpOptions, +now: U32, +isn: U32, +seg: G.TcpSeg, tcb: TcpTcb, c: C) -> TcpW<C>:
  match rst:
    case True{}:
      Tcp.stop(C, TcpInNone{}, tcb, c, Nil{})
    case False{}:
      match ackf:
        case True{}:
          Tcp.stop(C, TcpInNone{}, tcb, c, [TcpOut{Tcp.seg.rst(G.TcpSeg.ack(seg))}])
        case False{}:
          match syn:
            case False{}:
              Tcp.stop(C, TcpInNone{}, tcb, c, Nil{})
            case True{}:
              +sq = G.TcpSeg.seq(seg)
              +tcb2 = Tcp.tcb.open(o, now, isn, True{}, TcpSeg.wnd(seg), sq, Tcp.smss(o, TcpSeg.mss(seg)), TcpRcv{sq, U32.add(sq, 1), Q.RcvQ.new(), 0})
              Tcp.stop(C, TcpInSyn{}, tcb2, c, [TcpOut{Tcp.seg.syn(True{}, TcpTcb.snd(tcb2), TcpTcb.rcv(tcb2), o)}])

def Tcp.reply_acts(m: Maybe<&2, G.TcpSeg>) -> List<&2, TcpAction>:
  match m:
    case None{}:
      Nil{}
    case Some{s}:
      [TcpOut{s}]

# Segment arrival, by state
def Tcp.arrive(~C: Data, ~cc: CC.TcpCc<C>, st: TcpState, +o: TcpOptions, +now: U32, +isn: U32, +seg: G.TcpSeg, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match st:
    case TcpClosed{}:
      # section 3.10.7.1
      Tcp.stop(C, TcpInNone{}, tcb, c, Tcp.reply_acts(Tcp.reset_reply(seg)))
    case TcpListen{}:
      Tcp.listen.go(G.TcpSeg.rst(seg), G.TcpSeg.is_ack(seg), G.TcpSeg.syn(seg), C, o, now, isn, seg, tcb, c)
    case TcpSynSent{}:
      Tcp.arrive.synsent(~C, ~cc, o, now, seg, tcb, c)
    case TcpSynReceived{}:
      Tcp.arrive.sync(~C, ~cc, TcpSynReceived{}, o, now, seg, tcb, c)
    case TcpEstablished{}:
      Tcp.arrive.sync(~C, ~cc, TcpEstablished{}, o, now, seg, tcb, c)
    case TcpFinWait1{}:
      Tcp.arrive.sync(~C, ~cc, TcpFinWait1{}, o, now, seg, tcb, c)
    case TcpFinWait2{}:
      Tcp.arrive.sync(~C, ~cc, TcpFinWait2{}, o, now, seg, tcb, c)
    case TcpCloseWait{}:
      Tcp.arrive.sync(~C, ~cc, TcpCloseWait{}, o, now, seg, tcb, c)
    case TcpClosing{}:
      Tcp.arrive.sync(~C, ~cc, TcpClosing{}, o, now, seg, tcb, c)
    case TcpLastAck{}:
      Tcp.arrive.sync(~C, ~cc, TcpLastAck{}, o, now, seg, tcb, c)
    case TcpTimeWait{}:
      Tcp.arrive.sync(~C, ~cc, TcpTimeWait{}, o, now, seg, tcb, c)

# Calls from the application (section 3.10.1 to 3.10.5)

def Tcp.error(-C: Data, e: TcpError, tcb: TcpTcb, c: C) -> TcpW<C>:
  Tcp.stop(C, TcpInNone{}, tcb, c, [TcpNotify{TcpNoteError{e}}])

def Tcp.call.open(active: Bool, -C: Data, +o: TcpOptions, +now: U32, +isn: U32, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match active:
    case True{}:
      +tcb2 = Tcp.tcb.open(o, now, isn, False{}, 0, 0, Tcp.opt.mss(o), TcpRcv{0, 0, Q.RcvQ.new(), 0})
      Tcp.stop(C, TcpInActiveOpen{}, tcb2, c, [TcpOut{Tcp.seg.syn(False{}, TcpTcb.snd(tcb2), TcpTcb.rcv(tcb2), o)}])
    case False{}:
      match tcb:
        case TcpTcb{p, s, r, m}:
          Tcp.stop(C, TcpInPassiveOpen{}, TcpTcb{True{}, s, r, m}, c, Nil{})

def Tcp.snd_buf(o: TcpOptions) -> Nat:
  match o:
    case TcpOptions{m, rb, sb, iw, msl, r, sr, ng, ar, ool, rp}:
      U32.to_nat(sb)

# SEND: the data the send buffer has room for is queued
def Tcp.call.queue(-C: Data, +o: TcpOptions, +data: B.Octets, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match tcb:
    case TcpTcb{p, snd, r, m}:
      match snd:
        case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, +buf, bseq, fin}:
          +take = B.Octets.take(Nat.sub(Tcp.snd_buf(o), B.Octets.len(buf)), data)
          +snd2 = {TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, B.Octets.append(buf, take), bseq, fin} : TcpSnd}
          TcpW{False{}, TcpInNone{}, TcpTcb{p, snd2, r, m}, c, [TcpNotify{TcpNoteQueued{Tcp.u32(B.Octets.len(take))}}], False{}, False{}}

def Tcp.call.send(st: TcpState, -C: Data, +o: TcpOptions, +data: B.Octets, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match st:
    case TcpClosed{}:
      Tcp.error(C, TcpErrNoConnection{}, tcb, c)
    case TcpListen{}:
      Tcp.error(C, TcpErrNoConnection{}, tcb, c)
    case TcpSynSent{}:
      Tcp.call.queue(C, o, data, tcb, c)
    case TcpSynReceived{}:
      Tcp.call.queue(C, o, data, tcb, c)
    case TcpEstablished{}:
      Tcp.call.queue(C, o, data, tcb, c)
    case TcpCloseWait{}:
      Tcp.call.queue(C, o, data, tcb, c)
    case _:
      Tcp.error(C, TcpErrClosing{}, tcb, c)

def TcpOptions.rcv_buf(o: TcpOptions) -> U32:
  match o:
    case TcpOptions{m, rb, sb, iw, msl, r, sr, ng, ar, ool, rp}:
      rb

# RECEIVE: the application read n bytes; the window it opens is advertised
# when it grows by min(rcv_buf / 2, SMSS) or from zero (receiver-side silly
# window avoidance, section 3.8.6.2.2)
def Tcp.call.read(sync: Bool, -C: Data, +o: TcpOptions, +n: U32, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match sync:
    case False{}:
      Tcp.stop(C, TcpInNone{}, tcb, c, Nil{})
    case True{}:
      match tcb:
        case TcpTcb{p, s, +r, m}:
          match r:
            case TcpRcv{irs, rn, q, +u}:
              +r2 = {TcpRcv{irs, rn, q, U32.sub(u, Tcp.min(n, u))} : TcpRcv}
              +w1 = Tcp.rcv_wnd(o, r)
              +w2 = Tcp.rcv_wnd(o, r2)
              +step = Tcp.min(U32.shr(TcpOptions.rcv_buf(o)), TcpSnd.smss(s))
              +update = Bool.or(U32.is_eq(w1, 0), U32.is_le(step, U32.sub(w2, w1)))
              TcpW{False{}, TcpInNone{}, TcpTcb{p, s, r2, m}, c, Nil{}, Bool.and(update, Bool.not(U32.is_eq(w1, w2))), False{}}

def TcpSnd.set_fin(+snd: TcpSnd) -> TcpSnd:
  match snd:
    case TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, True{}}

# CLOSE: our FIN follows the data (FIN-WAIT-1 or LAST-ACK)
def Tcp.call.fin(-C: Data, +tcb: TcpTcb, c: C) -> TcpW<C>:
  Tcp.stop(C, TcpInClose{}, TcpTcb.set_snd(tcb, TcpSnd.set_fin(TcpTcb.snd(tcb))), c, Nil{})

def Tcp.call.close(st: TcpState, -C: Data, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match st:
    case TcpClosed{}:
      Tcp.error(C, TcpErrNoConnection{}, tcb, c)
    case TcpListen{}:
      Tcp.stop(C, TcpInClose{}, tcb, c, Nil{})
    case TcpSynSent{}:
      Tcp.stop(C, TcpInClose{}, tcb, c, Nil{})
    case TcpSynReceived{}:
      Tcp.call.fin(C, tcb, c)
    case TcpEstablished{}:
      Tcp.call.fin(C, tcb, c)
    case TcpCloseWait{}:
      Tcp.call.fin(C, tcb, c)
    case _:
      Tcp.error(C, TcpErrClosing{}, tcb, c)

# ABORT: a reset <SEQ=SND.NXT><CTL=RST> where the peer has a connection
def Tcp.call.abort.rst(-C: Data, +tcb: TcpTcb, c: C) -> TcpW<C>:
  Tcp.stop(C, TcpInAbort{}, tcb, c, [TcpOut{Tcp.seg.rst(TcpSnd.nxt(TcpTcb.snd(tcb)))}])

def Tcp.call.abort(st: TcpState, -C: Data, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match st:
    case TcpClosed{}:
      Tcp.error(C, TcpErrNoConnection{}, tcb, c)
    case TcpListen{}:
      Tcp.stop(C, TcpInAbort{}, tcb, c, Nil{})
    case TcpSynSent{}:
      Tcp.stop(C, TcpInAbort{}, tcb, c, Nil{})
    case TcpClosing{}:
      Tcp.stop(C, TcpInAbort{}, tcb, c, Nil{})
    case TcpLastAck{}:
      Tcp.stop(C, TcpInAbort{}, tcb, c, Nil{})
    case TcpTimeWait{}:
      Tcp.stop(C, TcpInAbort{}, tcb, c, Nil{})
    case _:
      Tcp.call.abort.rst(C, tcb, c)

# Timers (section 3.10.8; RFC 6298 section 5)

def TcpTim.rtx_at(t: TcpTim) -> Maybe<&2, U32>:
  match t:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      rtx

def TcpTim.tw_at(t: TcpTim) -> Maybe<&2, U32>:
  match t:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      tw

def Tcp.due(+now: U32, m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{at}:
      S.SeqNum.reached(now, at)

def Tcp.retries(syn: Bool, o: TcpOptions) -> U32:
  match o:
    case TcpOptions{m, rb, sb, iw, msl, r, sr, ng, ar, ool, rp}:
      Tcp.pick(U32, syn, sr, r)

# after a timeout: RTO doubled, one more retransmission, no measurement
# (Karn), and the timer set again
def Tcp.backed_off(+o: TcpOptions, +now: U32, +syn: Bool, tim: TcpTim) -> TcpTim:
  match tim:
    case TcpTim{rto, rtx, tw, retx, rtt, sl}:
      +rto2 = R.Rto.backoff(Tcp.opt.rto(o), rto)
      TcpTim{rto2, Some{U32.add(now, R.Rto.current(rto2))}, tw, U32.add(retx, 1), None{}, Bool.or(sl, syn)}

def Tcp.go_back(+snd: TcpSnd) -> TcpSnd:
  match snd:
    case TcpSnd{iss, +una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
      TcpSnd{iss, una, una, max, wnd, wl1, wl2, smss, buf, bseq, fin}

# the retransmission timer expired with the SYN unacknowledged: resend it
def Tcp.rtx.syn(give_up: Bool, -C: Data, +st: TcpState, +o: TcpOptions, +now: U32, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match give_up:
    case True{}:
      Tcp.stop(C, TcpInGiveUp{}, tcb, c, Nil{})
    case False{}:
      match tcb:
        case TcpTcb{p, +snd, +rcv, tim}:
          Tcp.stop(C, TcpInNone{}, TcpTcb{p, snd, rcv, Tcp.backed_off(o, now, True{}, tim)}, c, [TcpOut{Tcp.resend_first(o, rcv, snd, Bool.not(TcpState.is(st, 2)))}])

# with data or a FIN outstanding: back to SND.UNA, resent from there by the
# output that follows; the congestion controller hears of the loss
def Tcp.rtx.data(~C: Data, ~cc: CC.TcpCc<C>, give_up: Bool, +o: TcpOptions, +now: U32, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match give_up:
    case True{}:
      Tcp.stop(C, TcpInGiveUp{}, tcb, c, Nil{})
    case False{}:
      match tcb:
        case TcpTcb{p, +snd, rcv, tim}:
          +info = {CC.TcpAckInfo{0, TcpSnd.smss(snd), U32.sub(TcpSnd.max(snd), TcpSnd.una(snd))} : CC.TcpAckInfo}
          Tcp.stop(C, TcpInNone{}, TcpTcb{p, Tcp.go_back(snd), rcv, Tcp.backed_off(o, now, False{}, tim)}, Tcp.cc_timeout(~C, ~cc, c, info), Nil{})

def Tcp.rtx.probed(-C: Data, p: Bool, rcv: TcpRcv, c: C, r: TcpSent) -> TcpW<C>:
  match r:
    case TcpSent{snd2, tim2, acts2, sent2}:
      Tcp.stop(C, TcpInNone{}, TcpTcb{p, snd2, rcv, tim2}, c, acts2)

# nothing outstanding: a zero-window probe if data waits, else nothing
def Tcp.rtx.probe(probe: Bool, -C: Data, +o: TcpOptions, +now: U32, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match probe:
    case False{}:
      Tcp.stop(C, TcpInNone{}, TcpTcb.set_tim(tcb, TcpTim.set_rtx(TcpTcb.tim(tcb), None{})), c, Nil{})
    case True{}:
      match tcb:
        case TcpTcb{p, snd, +rcv, tim}:
          Tcp.rtx.probed(C, p, rcv, c, Tcp.probe(Tcp.backed_off(o, now, False{}, tim), o, rcv, now, snd, Nil{}))

def Tcp.rtx.which(~C: Data, ~cc: CC.TcpCc<C>, syn_done: Bool, out: Bool, +st: TcpState, +o: TcpOptions, +now: U32, +retx: U32, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match syn_done:
    case False{}:
      Tcp.rtx.syn(U32.is_ge(retx, Tcp.retries(True{}, o)), C, st, o, now, tcb, c)
    case True{}:
      match out:
        case True{}:
          Tcp.rtx.data(~C, ~cc, U32.is_ge(retx, Tcp.retries(False{}, o)), o, now, tcb, c)
        case False{}:
          Tcp.rtx.probe(Bool.and(Nat.is_gt(Tcp.unsent(TcpTcb.snd(tcb)), 0n), U32.is_lt(retx, Tcp.retries(False{}, o))), C, o, now, tcb, c)

def Tcp.rtx.fire(~C: Data, ~cc: CC.TcpCc<C>, due: Bool, +st: TcpState, +o: TcpOptions, +now: U32, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match due:
    case False{}:
      Tcp.stop(C, TcpInNone{}, tcb, c, Nil{})
    case True{}:
      +snd = TcpTcb.snd(tcb)
      +retx = TcpTim.retx(TcpTcb.tim(tcb))
      Tcp.rtx.which(~C, ~cc, Tcp.syn_acked(snd), Tcp.outstanding(snd), st, o, now, retx, tcb, c)

def Tcp.fire(~C: Data, ~cc: CC.TcpCc<C>, t: TcpTimer, +st: TcpState, +o: TcpOptions, +now: U32, +tcb: TcpTcb, c: C) -> TcpW<C>:
  match t:
    case TcpTimerRtx{}:
      Tcp.rtx.fire(~C, ~cc, Tcp.due(now, TcpTim.rtx_at(TcpTcb.tim(tcb))), st, o, now, tcb, c)
    case TcpTimerTimeWait{}:
      Tcp.stop(C, Tcp.pick(TcpInput, Tcp.due(now, TcpTim.tw_at(TcpTcb.tim(tcb))), TcpInTimeWaitEnd{}, TcpInNone{}), tcb, c, Nil{})

# Finishing an event: what entering the new state does, sending, the ACK,
# the retransmission timer, notes, and the timer actions

def TcpState.opening(s: TcpState) -> Bool:
  match s:
    case TcpSynSent{}:
      True{}
    case TcpSynReceived{}:
      True{}
    case _:
      False{}

def TcpState.est_like(s: TcpState) -> Bool:
  match s:
    case TcpEstablished{}:
      True{}
    case TcpCloseWait{}:
      True{}
    case _:
      False{}

# whether data or a FIN may be sent in s
def TcpState.can_send(s: TcpState) -> Bool:
  match s:
    case TcpEstablished{}:
      True{}
    case TcpFinWait1{}:
      True{}
    case TcpCloseWait{}:
      True{}
    case TcpClosing{}:
      True{}
    case TcpLastAck{}:
      True{}
    case _:
      False{}

# whether s is synchronized (SYN-RECEIVED to TIME-WAIT)
def TcpState.sync(+s: TcpState) -> Bool:
  U32.is_ge(TcpState.index(s), 3)

# whether the retransmission timer runs in s (SYN-SENT to LAST-ACK)
def TcpState.timed(+s: TcpState) -> Bool:
  Bool.and(U32.is_ge(TcpState.index(s), 2), U32.is_le(TcpState.index(s), 9))

def TcpInput.peer_fin(k: TcpInput) -> Bool:
  match k:
    case TcpInSeg{af, f}:
      f
    case TcpInSynAck{f}:
      f
    case _:
      False{}

def TcpInput.is_seg(k: TcpInput) -> Bool:
  match k:
    case TcpInSeg{af, f}:
      True{}
    case _:
      False{}

# the reason a connection closed, from the state it left and the input
def Tcp.close_note(k: TcpInput, +st: TcpState) -> List<&2, TcpAction>:
  match k:
    case TcpInReset{l}:
      Tcp.pick(List<&2, TcpAction>, TcpState.opening(st), [TcpNotify{TcpNoteRefused{}}], Tcp.pick(List<&2, TcpAction>, Bool.and(U32.is_ge(TcpState.index(st), 4), U32.is_le(TcpState.index(st), 7)), [TcpNotify{TcpNoteReset{}}], Nil{}))
    case TcpInGiveUp{}:
      [TcpNotify{TcpNoteTimedOut{}}]
    case _:
      Nil{}

def Tcp.rev_onto(xs: List<&2, TcpAction>, acc: List<&2, TcpAction>) -> List<&2, TcpAction>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Tcp.rev_onto(t, Con{h, acc})

# acts (newest first) with xs (in order) after them
def Tcp.push_all(xs: List<&2, TcpAction>, acts: List<&2, TcpAction>) -> List<&2, TcpAction>:
  match xs:
    case Nil{}:
      acts
    case Con{h, t}:
      Tcp.push_all(t, Con{h, acts})

# entering ESTABLISHED (or CLOSE-WAIT) from an open: the congestion
# controller starts with the initial window, and the RTO is re-initialised
# if the SYN was resent (RFC 6298 section 5.7)
def Tcp.fin.enter(~C: Data, ~cc: CC.TcpCc<C>, entered: Bool, +o: TcpOptions, +tcb: TcpTcb, c: C) -> Pair(TcpTcb, C):
  match entered:
    case False{}:
      (tcb, c)
    case True{}:
      match tcb:
        case TcpTcb{p, +snd, r, tim}:
          match tim:
            case TcpTim{+rto, rtx, tw, retx, rtt, +sl}:
              +smss = TcpSnd.smss(snd)
              (TcpTcb{p, snd, r, TcpTim{Tcp.pick(R.Rto, sl, R.Rto.syn_lost(Tcp.opt.rto(o), rto), rto), rtx, tw, retx, rtt, sl}}, Tcp.cc_start(~C, ~cc, smss, Tcp.iw(sl, o, smss)))

# TIME-WAIT: entered, or a segment arrived in it: 2 MSL from now, and no
# retransmissions; CLOSED and LISTEN: no timers
def Tcp.fin.timers(tw: Bool, quiet: Bool, +o: TcpOptions, +now: U32, +tcb: TcpTcb) -> TcpTcb:
  match tw:
    case True{}:
      TcpTcb.set_tim(tcb, TcpTim.set_rtx(TcpTim.set_tw(TcpTcb.tim(tcb), Some{U32.add(now, Tcp.opt.msl2(o))}), None{}))
    case False{}:
      match quiet:
        case True{}:
          TcpTcb.set_tim(tcb, TcpTim.set_rtx(TcpTim.set_tw(TcpTcb.tim(tcb), None{}), None{}))
        case False{}:
          tcb

def Tcp.fin.output.done(+an: Bool, p: Bool, rcv: TcpRcv, r: TcpSent) -> Pair(TcpTcb, Pair(Bool, List<&2, TcpAction>)):
  match r:
    case TcpSent{snd, tim, acts, sent}:
      (TcpTcb{p, snd, rcv, tim}, (Bool.and(an, Bool.not(sent)), acts))

# send what the windows allow, once our SYN is acknowledged
def Tcp.fin.output(can: Bool, +o: TcpOptions, +now: U32, +cwnd: U32, +tcb: TcpTcb, an: Bool, acts: List<&2, TcpAction>) -> Pair(TcpTcb, Pair(Bool, List<&2, TcpAction>)):
  match can:
    case False{}:
      (tcb, (an, acts))
    case True{}:
      match tcb:
        case TcpTcb{p, snd, +rcv, tim}:
          Tcp.fin.output.done(an, p, rcv, Tcp.output(o, rcv, now, cwnd, snd, tim, acts))

# RFC 6298 section 5: with data outstanding (or a zero window to probe) the
# timer runs, restarted when new data is acknowledged (5.3); with nothing
# outstanding it stops (5.2)
def Tcp.fin.rtx(timed: Bool, +now: U32, +cwnd: U32, +acked_new: Bool, +tcb: TcpTcb) -> TcpTcb:
  match timed:
    case False{}:
      tcb
    case True{}:
      +snd = TcpTcb.snd(tcb)
      +tim = TcpTcb.tim(tcb)
      +run = Bool.or(Tcp.outstanding(snd), Tcp.needs_probe(snd, cwnd))
      +old = TcpTim.rtx_at(tim)
      +fresh = {Some{U32.add(now, R.Rto.current(TcpTim.rto(tim)))} : Maybe<&2, U32>}
      +restart = Bool.or(Maybe.is_none(&2, U32, old), acked_new)
      TcpTcb.set_tim(tcb, TcpTim.set_rtx(tim, Tcp.pick(Maybe<&2, U32>, run, Tcp.pick(Maybe<&2, U32>, restart, fresh, old), None{})))

def Tcp.timer_acts.go(same: Bool, t: TcpTimer, +at: U32, acts: List<&2, TcpAction>) -> List<&2, TcpAction>:
  match same:
    case True{}:
      acts
    case False{}:
      Con{TcpSetTimer{t, at}, acts}

def Tcp.timer_acts(t: TcpTimer, old: Maybe<&2, U32>, new: Maybe<&2, U32>, acts: List<&2, TcpAction>) -> List<&2, TcpAction>:
  match old new:
    case None{} None{}:
      acts
    case Some{a} None{}:
      Con{TcpStopTimer{t}, acts}
    case None{} Some{+b}:
      Con{TcpSetTimer{t, b}, acts}
    case Some{a} Some{+b}:
      Tcp.timer_acts.go(U32.is_eq(a, b), t, b, acts)

def Tcp.fin.notes(+st: TcpState, +st2: TcpState, +k: TcpInput, +entered: Bool, acts: List<&2, TcpAction>) -> List<&2, TcpAction>:
  +closed = Bool.and(TcpState.is(st2, 0), Bool.not(TcpState.is(st, 0)))
  +a1 = Tcp.push(TcpAction, entered, TcpNotify{TcpNoteEstablished{}}, acts)
  +a2 = Tcp.push(TcpAction, TcpInput.peer_fin(k), TcpNotify{TcpNotePeerClosed{}}, a1)
  +a3 = Tcp.push_all(Tcp.pick(List<&2, TcpAction>, closed, Tcp.close_note(k, st), Nil{}), a2)
  Tcp.push(TcpAction, closed, TcpNotify{TcpNoteClosed{}}, a3)

def Tcp.finish.go(-C: Data, +st: TcpState, +st2: TcpState, +k: TcpInput, +entered: Bool, +o: TcpOptions, +now: U32, +cwnd: U32, +old: TcpTim, nw: Bool, tcb: TcpTcb, c: C, r: Pair(TcpTcb, Pair(Bool, List<&2, TcpAction>))) -> TcpFx<C>:
  match r:
    case (+tcb2, rest):
      match rest:
        case (an, acts):
          +acts2 = Tcp.push(TcpAction, Bool.and(an, TcpState.sync(st2)), Tcp.ack_of(o, tcb2), acts)
          +tcb3 = Tcp.fin.rtx(TcpState.timed(st2), now, cwnd, nw, tcb2)
          +tim3 = TcpTcb.tim(tcb3)
          +acts3 = Tcp.fin.notes(st, st2, k, entered, acts2)
          +acts4 = Tcp.timer_acts(TcpTimerTimeWait{}, TcpTim.tw_at(old), TcpTim.tw_at(tim3), Tcp.timer_acts(TcpTimerRtx{}, TcpTim.rtx_at(old), TcpTim.rtx_at(tim3), acts3))
          TcpFx{k, tcb3, c, Tcp.rev_onto(acts4, Nil{})}

def Tcp.finish.cc(~C: Data, ~cc: CC.TcpCc<C>, +st: TcpState, +st2: TcpState, +k: TcpInput, +entered: Bool, +o: TcpOptions, +now: U32, old: TcpTim, an: Bool, nw: Bool, acts: List<&2, TcpAction>, r: Pair(TcpTcb, C)) -> TcpFx<C>:
  match r:
    case (tcb1, +c1):
      +tw = Bool.and(TcpState.is(st2, 10), Bool.or(Bool.not(TcpState.is(st, 10)), TcpInput.is_seg(k)))
      +quiet = Bool.or(TcpState.is(st2, 0), TcpState.is(st2, 1))
      +tcb2 = Tcp.fin.timers(tw, quiet, o, now, tcb1)
      +cwnd = Tcp.cc_cwnd(~C, ~cc, c1)
      +can = Bool.and(TcpState.can_send(st2), Tcp.syn_acked(TcpTcb.snd(tcb2)))
      Tcp.finish.go(C, st, st2, k, entered, o, now, cwnd, old, nw, tcb2, c1, Tcp.fin.output(can, o, now, cwnd, tcb2, an, acts))

def Tcp.finish(~C: Data, ~cc: CC.TcpCc<C>, +st: TcpState, +o: TcpOptions, +now: U32, old: TcpTim, w: TcpW<C>) -> TcpFx<C>:
  match w:
    case TcpW{go, +k, tcb, c, acts, an, nw}:
      +st2 = Tcp.next_state(st, k)
      +entered = Bool.and(TcpState.opening(st), TcpState.est_like(st2))
      Tcp.finish.cc(~C, ~cc, st, st2, k, entered, o, now, old, an, nw, acts, Tcp.fin.enter(~C, ~cc, entered, o, tcb, c))

# The event, by kind
def Tcp.dispatch(~C: Data, ~cc: CC.TcpCc<C>, ev: TcpEvent, +st: TcpState, +o: TcpOptions, +now: U32, +isn: U32, +tcb: TcpTcb, +c: C) -> TcpW<C>:
  match ev:
    case TcpCallOpen{active}:
      Tcp.pick(TcpW<C>, TcpState.is(st, 0), Tcp.call.open(active, C, o, now, isn, tcb, c), Tcp.error(C, TcpErrExists{}, tcb, c))
    case TcpCallSend{data}:
      Tcp.call.send(st, C, o, data, tcb, c)
    case TcpCallRead{n}:
      Tcp.call.read(TcpState.sync(st), C, o, n, tcb, c)
    case TcpCallClose{}:
      Tcp.call.close(st, C, tcb, c)
    case TcpCallAbort{}:
      Tcp.call.abort(st, C, tcb, c)
    case TcpArrive{seg}:
      Tcp.arrive(~C, ~cc, st, o, now, isn, seg, tcb, c)
    case TcpFire{t}:
      Tcp.fire(~C, ~cc, t, st, o, now, tcb, c)

def Tcp.process(~C: Data, ~cc: CC.TcpCc<C>, +o: TcpOptions, +st: TcpState, +tcb: TcpTcb, c: C, ev: TcpEvent, +now: U32, +isn: U32) -> TcpFx<C>:
  Tcp.finish(~C, ~cc, st, o, now, TcpTcb.tim(tcb), Tcp.dispatch(~C, ~cc, ev, st, o, now, isn, tcb, c))

# The connection

def TcpConn.state(-C: Data, c: TcpConn<C>) -> TcpState:
  match c:
    case TcpConn{s, t, k}:
      s

def TcpConn.tcb(-C: Data, c: TcpConn<C>) -> TcpTcb:
  match c:
    case TcpConn{s, t, k}:
      t

# SND.UNA and the highest sequence number sent
def TcpConn.una(-C: Data, c: TcpConn<C>) -> U32:
  match c:
    case TcpConn{s, t, k}:
      TcpSnd.una(TcpTcb.snd(t))

def TcpConn.max(-C: Data, c: TcpConn<C>) -> U32:
  match c:
    case TcpConn{s, t, k}:
      TcpSnd.max(TcpTcb.snd(t))

def TcpConn.cc(-C: Data, c: TcpConn<C>) -> C:
  match c:
    case TcpConn{s, t, k}:
      k

# One event: the connection after it, and what it does. The state moves by
# Tcp.next_state alone.
def Tcp.step(~C: Data, ~cc: CC.TcpCc<C>, +o: TcpOptions, conn: TcpConn<C>, ev: TcpEvent, +now: U32, +isn: U32) -> Pair(TcpConn<C>, List<&2, TcpAction>):
  match conn:
    case TcpConn{+st, tcb, c}:
      +fx = Tcp.process(~C, ~cc, o, st, tcb, c, ev, now, isn)
      (TcpConn{Tcp.next_state(st, TcpFx.input(C, fx)), TcpFx.tcb(C, fx), TcpFx.cc(C, fx)}, TcpFx.acts(C, fx))

# A connection in CLOSED; an OPEN event opens it
def Tcp.new(~C: Data, ~cc: CC.TcpCc<C>, +o: TcpOptions) -> TcpConn<C>:
  +snd = {TcpSnd{0, 0, 0, 0, 0, 0, 0, 536, B.Octets.empty(), 0, False{}} : TcpSnd}
  +tim = {TcpTim{R.Rto.start(Tcp.opt.rto(o)), None{}, None{}, 0, None{}, False{}} : TcpTim}
  TcpConn{TcpClosed{}, TcpTcb{False{}, snd, TcpRcv{0, 0, Q.RcvQ.new(), 0}, tim}, Tcp.cc_start(~C, ~cc, 536, Tcp.iw(False{}, o, 536))}
