# Properties, for every input:
# * sequence numbers (seq.bend): comparison is irreflexive, asymmetric, and
#   total but for numbers exactly 2^31 apart; within a window of 2^31 it is
#   the order of the distances (b is ahead of a + d exactly when d is in
#   (0, 2^31)), distances add, and so the order is transitive: a strict
#   total order within any window of 2^31;
# * the receive queue (rcvq.bend): what an insert delivers starts at the next
#   offset and moves it by exactly its length, so data reaches the
#   application in order and without gaps;
# * the TCP state machine (tcp.bend): no step takes a transition that RFC
#   9293's state diagram, or the transitions its text adds, does not allow;
# * acknowledgments (tcp.bend): no step moves SND.UNA except forward to at
#   most the highest sequence number sent, so an ACK of data that was not
#   sent is never taken;
# * the retransmission timer (rto.bend): a timeout doubles the RTO up to the
#   maximum, and every RTO is at most the maximum;
# * the demultiplexer (demux.bend): a socket is found under its key, not
#   after it is removed, and not under another key; a segment goes to the
#   socket with its exact key;
# * UDP (udp.bend): a datagram to a bound port is delivered to its socket
#   with its source and data, and one to an unbound port is reported for
#   ICMP port unreachable;
# * ICMP (icmp.bend): an echo request is answered by an echo reply with the
#   same identifier, sequence number and data, and nothing else is answered.
#
# The TCP laws are stated for the default congestion controller (Reno): a
# law cannot quantify over a template argument. Neither depends on it.
#
# Vectors: RFC 6298's estimator, Reno's window changes (RFC 5681), sequence
# numbers across the wrap, ICMP echo bytes, a SYN answered, resets for
# segments to no connection; and, for every law with a hypothesis, an input
# that meets it.
import Base
import ../bytes/bytes.bend as B
import ./seq.bend as S
import ./rcvq.bend as Q
import ./cc.bend as CC
import ./segment.bend as G
import ./tcp.bend as T
import ./demux.bend as D
import ./rto.bend as R
import ./udp.bend as U
import ./icmp.bend as IC

# Sequence numbers (RFC 9293 section 3.4)

law seq_lt_irrefl:
  for a: U32
  {S.SeqNum.lt(a, a) == False{} : Bool}

# the window: b = a + d is ahead of a exactly when d is in (0, 2^31)
law seq_lt_add:
  for +a: U32
  for d: U32
  {S.SeqNum.lt(a, S.SeqNum.add(a, d)) == S.SeqNum.in_half(d) : Bool}

law seq_lt_asym:
  for +a: U32
  for +b: U32
  for h: {S.SeqNum.lt(a, b) == True{} : Bool}
  {S.SeqNum.lt(b, a) == False{} : Bool}

# any two are ordered one way or the other, or equal, or exactly 2^31 apart
law seq_lt_total:
  for +a: U32
  for +b: U32
  {Bool.or(S.SeqNum.lt(a, b), Bool.or(S.SeqNum.lt(b, a), Bool.or(U32.is_eq(a, b), U32.is_eq(S.SeqNum.sub(b, a), 2147483648)))) == True{} : Bool}

# distances add: c - a = (b - a) + (c - b)
law seq_dist_add:
  for +a: U32
  for +b: U32
  for +c: U32
  {S.SeqNum.sub(c, a) == S.SeqNum.add(S.SeqNum.sub(b, a), S.SeqNum.sub(c, b)) : U32}

# transitive while the total distance stays within the window
law seq_lt_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for h1: {S.SeqNum.lt(a, b) == True{} : Bool}
  for h2: {S.SeqNum.lt(b, c) == True{} : Bool}
  for h3: {S.SeqNum.in_half(S.SeqNum.add(S.SeqNum.sub(b, a), S.SeqNum.sub(c, b))) == True{} : Bool}
  {S.SeqNum.lt(a, c) == True{} : Bool}

# The receive queue: delivery is contiguous

law rcvq_contiguous:
  for +limit: Nat
  for +q: Q.RcvQ
  for +rel: Nat
  for +d: B.Octets
  {Q.RcvQ.next(Q.RcvOut.queue(Q.RcvQ.insert(limit, q, rel, d))) == Nat.add(Q.RcvQ.next(q), B.Octets.len(Q.RcvOut.data(Q.RcvQ.insert(limit, q, rel, d)))) : Nat}

# The TCP state diagram: every step's transition is one Tcp.allowed lists

law tcp_step_allowed:
  for +o: T.TcpOptions
  for +conn: T.TcpConn<CC.RenoState>
  for +ev: T.TcpEvent
  for +now: U32
  for +isn: U32
  {T.Tcp.allowed(T.TcpConn.state(CC.RenoState, conn), T.TcpConn.state(CC.RenoState, Pair.fst(T.TcpConn<CC.RenoState>, List<&2, T.TcpAction>, T.Tcp.step(~CC.RenoState, ~CC.Reno.cc(), o, conn, ev, now, isn)))) == True{} : Bool}

# The demultiplexer

law demux_find_insert:
  for -S: Data
  for d: D.Demux<S>
  for +k: D.DemuxKey
  for +s: S
  {D.Demux.find(S, D.Demux.insert(S, d, k, s), k) == Some{s} : Maybe<&2, S>}

law demux_find_remove:
  for -S: Data
  for d: D.Demux<S>
  for +k: D.DemuxKey
  {D.Demux.find(S, D.Demux.remove(S, d, k), k) == None{} : Maybe<&2, S>}

law demux_route_exact:
  for -S: Data
  for +d: D.Demux<S>
  for +p: U32
  for +a: U32
  for +r: U32
  for +s: S
  {D.Demux.route(S, D.Demux.insert(S, d, D.DemuxKey{p, a, r}, s), p, a, r) == Some{D.DemuxHit{D.DemuxKey{p, a, r}, s}} : Maybe<&2, D.DemuxHit<S>>}

# RFC 6298 section 5.5: on a timeout the RTO doubles, up to the maximum

law rto_backoff_bounded:
  for +p: R.RtoParams
  for r: R.Rto
  {U32.is_le(R.Rto.current(R.Rto.backoff(p, r)), R.RtoParams.max(p)) == True{} : Bool}

law rto_backoff_doubles:
  for +p: R.RtoParams
  for +r: R.Rto
  for h1: {U32.is_lt(R.Rto.current(r), 2147483648) == True{} : Bool}
  for h2: {U32.is_le(U32.add(R.Rto.current(r), R.Rto.current(r)), R.RtoParams.max(p)) == True{} : Bool}
  {R.Rto.current(R.Rto.backoff(p, r)) == U32.add(R.Rto.current(r), R.Rto.current(r)) : U32}

# sections 2.4 and 2.5: every RTO a sample gives is at most the maximum
law rto_sample_bounded:
  for +p: R.RtoParams
  for r: R.Rto
  for rtt: U32
  {U32.is_le(R.Rto.current(R.Rto.sample(p, r, rtt)), R.RtoParams.max(p)) == True{} : Bool}

# vectors (RFC 6298 2.2, 2.3): a first sample of 100 ms gives SRTT 100, RTTVAR
# 50, RTO 100 + 4 * 50 = 300, clamped up to the 1 s minimum; with no minimum,
# 300; a second sample of 200 ms gives RTTVAR 3/4 * 50 + 1/4 * 100 = 62.5
# (4 * RTTVAR = 250) and SRTT 7/8 * 100 + 1/8 * 200 = 112.5 (8 * SRTT = 900),
# so RTO 112 + 250 = 362
law rto_vector_first:
  {R.Rto.current(R.Rto.sample(R.RtoParams.default(), R.Rto.start(R.RtoParams.default()), 100)) == 1000 : U32}

law rto_vector_unclamped:
  {R.Rto.sample(R.RtoParams{1000, 1, 60000, 1, 3000}, R.Rto.start(R.RtoParams{1000, 1, 60000, 1, 3000}), 100) == R.Rto{800, 200, 300, True{}} : R.Rto}

law rto_vector_second:
  {R.Rto.sample(R.RtoParams{1000, 1, 60000, 1, 3000}, R.Rto.sample(R.RtoParams{1000, 1, 60000, 1, 3000}, R.Rto.start(R.RtoParams{1000, 1, 60000, 1, 3000}), 100), 200) == R.Rto{900, 250, 362, True{}} : R.Rto}

# timeouts from 1 s: 2 s, 4 s, ... 32 s, then 60 s, and 60 s again
law rto_vector_backoff:
  {R.Rto.current(R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.start(R.RtoParams.default()))))))))) == 60000 : U32}

law rto_vector_backoff_32:
  {R.Rto.current(R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.backoff(R.RtoParams.default(), R.Rto.start(R.RtoParams.default()))))))) == 32000 : U32}

# UDP (RFC 768; RFC 1122 4.1.3.1): a datagram to a port just bound, from an
# address and port no socket is connected to, goes to that port's socket with
# its source and data; a datagram to a port nothing is bound to is reported
# for ICMP port unreachable

law udp_bound_delivers:
  for +a: U32
  for +d: D.Demux<U.UdpSock>
  for +p: U32
  for +tag: U32
  for +src: U32
  for +dst: U32
  for +sport: U32
  for +data: B.Octets
  for h1: {D.Demux.find(U.UdpSock, d, D.DemuxKey.any(p)) == None{} : Maybe<&2, U.UdpSock>}
  for h2: {D.Demux.find(U.UdpSock, d, D.DemuxKey{p, src, sport}) == None{} : Maybe<&2, U.UdpSock>}
  {U.Udp.receive(Pair.fst(U.UdpState, List<&2, U.UdpAction>, U.Udp.bind(U.UdpState{a, d}, p, tag)), src, dst, sport, p, data) == [U.UdpDeliver{tag, src, sport, p, data}] : List<&2, U.UdpAction>}

law udp_unbound_unreachable:
  for +a: U32
  for +d: D.Demux<U.UdpSock>
  for +src: U32
  for +dst: U32
  for +sport: U32
  for +dport: U32
  for +data: B.Octets
  for h1: {D.Demux.find(U.UdpSock, d, D.DemuxKey{dport, src, sport}) == None{} : Maybe<&2, U.UdpSock>}
  for h2: {D.Demux.find(U.UdpSock, d, D.DemuxKey.any(dport)) == None{} : Maybe<&2, U.UdpSock>}
  {U.Udp.receive(U.UdpState{a, d}, src, dst, sport, dport, data) == [U.UdpNoPort{src, dst}] : List<&2, U.UdpAction>}

# both laws' hypotheses hold for an empty table
law udp_hypotheses_hold:
  {D.Demux.find(U.UdpSock, D.Demux.empty(U.UdpSock), D.DemuxKey{7, 167772161, 9}) == None{} : Maybe<&2, U.UdpSock>}

# the demultiplexer: a socket under another key leaves a lookup alone
law demux_find_insert_other:
  for -S: Data
  for d: D.Demux<S>
  for +k1: D.DemuxKey
  for +k2: D.DemuxKey
  for +s: S
  for +ne: {D.DemuxKey.is_eq(k1, k2) == False{} : Bool}
  {D.Demux.find(S, D.Demux.insert(S, d, k2, s), k1) == D.Demux.find(S, d, k1) : Maybe<&2, S>}

law demux_keys_differ:
  {D.DemuxKey.is_eq(D.DemuxKey{7, 1, 2}, D.DemuxKey.any(7)) == False{} : Bool}

# ICMP (RFC 792): an echo request is answered by an echo reply with the same
# identifier, sequence number and data; an echo reply, and every error, is
# not answered (RFC 1122 3.2.2)

law icmp_echo_answered:
  for id: U32
  for seq: U32
  for data: B.Octets
  {IC.Icmp.respond(IC.IcmpEchoRequest{id, seq, data}) == Some{IC.IcmpEchoReply{id, seq, data}} : Maybe<&2, IC.IcmpMsg>}

law icmp_reply_not_answered:
  for id: U32
  for seq: U32
  for data: B.Octets
  {IC.Icmp.respond(IC.IcmpEchoReply{id, seq, data}) == None{} : Maybe<&2, IC.IcmpMsg>}

law icmp_unreachable_not_answered:
  for code: U32
  for q: B.Octets
  {IC.Icmp.respond(IC.IcmpUnreachable{code, q}) == None{} : Maybe<&2, IC.IcmpMsg>}

law icmp_exceeded_not_answered:
  for code: U32
  for q: B.Octets
  {IC.Icmp.respond(IC.IcmpTimeExceeded{code, q}) == None{} : Maybe<&2, IC.IcmpMsg>}

# vectors: the bytes of an echo request (identifier 0x1234, sequence 1, data
# "abcd", checksum 0x2104) decode, and are answered by the reply's bytes
# (checksum 0x2904)
law icmp_vector_decode:
  {IC.Icmp.decode(B.Octets.of_list([8, 0, 33, 4, 18, 52, 0, 1, 97, 98, 99, 100])) == Done{IC.IcmpEchoRequest{4660, 1, B.Octets.of_string("abcd")}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}

law icmp_vector_answer:
  {Pair.snd(IC.IcmpState, List<&2, IC.IcmpAction>, IC.Icmp.step(IC.IcmpState{IC.IcmpOptions.default()}, IC.IcmpRecv{167772161, 167772162, B.Octets.of_list([8, 0, 33, 4, 18, 52, 0, 1, 97, 98, 99, 100])})) == [IC.IcmpOut{167772161, B.Octets.of_list([0, 0, 41, 4, 18, 52, 0, 1, 97, 98, 99, 100])}] : List<&2, IC.IcmpAction>}

# a corrupted checksum is not answered
law icmp_vector_bad_checksum:
  {Pair.snd(IC.IcmpState, List<&2, IC.IcmpAction>, IC.Icmp.step(IC.IcmpState{IC.IcmpOptions.default()}, IC.IcmpRecv{167772161, 167772162, B.Octets.of_list([8, 0, 33, 5, 18, 52, 0, 1, 97, 98, 99, 100])})) == [] : List<&2, IC.IcmpAction>}

# RFC 9293 section 3.10.7.4: an acknowledgment moves SND.UNA only when
# SND.UNA < SEG.ACK =< SND.NXT; so after any event, in any state but CLOSED
# and LISTEN (where an OPEN or a SYN sets up a new send side), SND.UNA has
# stayed, or moved forward to at most the highest sequence number sent: no
# acknowledgment of data that was not sent is ever taken
law tcp_acks_only_sent:
  for +o: T.TcpOptions
  for +conn: T.TcpConn<CC.RenoState>
  for +ev: T.TcpEvent
  for +now: U32
  for +isn: U32
  for h: {Bool.or(T.TcpState.is(T.TcpConn.state(CC.RenoState, conn), 0), T.TcpState.is(T.TcpConn.state(CC.RenoState, conn), 1)) == False{} : Bool}
  {T.Tcp.acked_sent(T.TcpConn.una(CC.RenoState, conn), T.TcpConn.max(CC.RenoState, conn), T.TcpConn.una(CC.RenoState, Pair.fst(T.TcpConn<CC.RenoState>, List<&2, T.TcpAction>, T.Tcp.step(~CC.RenoState, ~CC.Reno.cc(), o, conn, ev, now, isn)))) == True{} : Bool}

# Satisfiability: every law with a hypothesis has an input meeting it

# seq_lt_asym: 0 < 1
law seq_lt_asym_sat:
  {S.SeqNum.lt(0, 1) == True{} : Bool}

# seq_lt_trans: 0 < 1 < 2, and 1 + 1 is within the window
law seq_lt_trans_sat:
  {Bool.and(S.SeqNum.lt(0, 1), Bool.and(S.SeqNum.lt(1, 2), S.SeqNum.in_half(S.SeqNum.add(S.SeqNum.sub(1, 0), S.SeqNum.sub(2, 1))))) == True{} : Bool}

# rto_backoff_doubles: the initial 1 s doubles within the 60 s maximum
law rto_backoff_doubles_sat:
  {Bool.and(U32.is_lt(R.Rto.current(R.Rto.start(R.RtoParams.default())), 2147483648), U32.is_le(U32.add(R.Rto.current(R.Rto.start(R.RtoParams.default())), R.Rto.current(R.Rto.start(R.RtoParams.default()))), R.RtoParams.max(R.RtoParams.default()))) == True{} : Bool}

# udp_bound_delivers, udp_unbound_unreachable: an empty table has neither
# socket
law udp_sat:
  {Bool.and(Maybe.is_none(&2, U.UdpSock, D.Demux.find(U.UdpSock, D.Demux.empty(U.UdpSock), D.DemuxKey.any(7))), Maybe.is_none(&2, U.UdpSock, D.Demux.find(U.UdpSock, D.Demux.empty(U.UdpSock), D.DemuxKey{7, 167772161, 9}))) == True{} : Bool}

# tcp_acks_only_sent: a connection in ESTABLISHED
law tcp_acks_only_sent_sat:
  {Bool.or(T.TcpState.is(T.TcpEstablished{}, 0), T.TcpState.is(T.TcpEstablished{}, 1)) == False{} : Bool}

# Vectors

# sequence numbers across the wrap
law seq_vector_wrap:
  {Bool.and(S.SeqNum.lt(4294967295, 0), Bool.and(S.SeqNum.lt(4294967000, 100), Bool.and(Bool.not(S.SeqNum.lt(0, 2147483648)), Bool.not(S.SeqNum.lt(2147483648, 0))))) == True{} : Bool}

# Reno (RFC 5681): slow start grows by one SMSS per ACK of a full segment
# (3.1, equation 2); the third duplicate ACK halves the flight into ssthresh
# (equation 4) and inflates the window by three segments (3.2 step 3); the
# ACK of new data deflates it to ssthresh (step 6); a timeout leaves one
# segment (the loss window)
law reno_vector_slow_start:
  {CC.Reno.on_ack(CC.Reno.start(65535, 1460, 4380), CC.TcpAckInfo{1460, 1460, 4380}) == CC.RenoState{5840, 65535, 0, False{}} : CC.RenoState}

law reno_vector_avoidance:
  {CC.Reno.on_ack(CC.RenoState{10000, 8000, 0, False{}}, CC.TcpAckInfo{1000, 1000, 10000}) == CC.RenoState{10100, 8000, 0, False{}} : CC.RenoState}

law reno_vector_fast_retransmit:
  {CC.Reno.on_dupack(CC.RenoState{14600, 65535, 2, False{}}, CC.TcpAckInfo{0, 1460, 14600}) == (CC.RenoState{11680, 7300, 3, True{}}, True{}) : Pair(CC.RenoState, Bool)}

law reno_vector_recovery_ends:
  {CC.Reno.on_ack(CC.RenoState{13140, 7300, 4, True{}}, CC.TcpAckInfo{1460, 1460, 14600}) == CC.RenoState{7300, 7300, 0, False{}} : CC.RenoState}

law reno_vector_timeout:
  {CC.Reno.on_timeout(CC.RenoState{14600, 65535, 0, False{}}, CC.TcpAckInfo{0, 1460, 14600}) == CC.RenoState{1460, 7300, 0, False{}} : CC.RenoState}

# a SYN (seq 1000, MSS 1460) to a listening connection is answered by a
# SYN,ACK with the ISN 5000 and our MSS, and the retransmission timer is set
# for the initial RTO (RFC 9293 3.10.7.2; RFC 6298 2.1)
law tcp_vector_syn_ack:
  {Pair.snd(T.TcpConn<CC.RenoState>, List<&2, T.TcpAction>, T.Tcp.step(~CC.RenoState, ~CC.Reno.cc(), T.TcpOptions.default(), Pair.fst(T.TcpConn<CC.RenoState>, List<&2, T.TcpAction>, T.Tcp.step(~CC.RenoState, ~CC.Reno.cc(), T.TcpOptions.default(), T.Tcp.new(~CC.RenoState, ~CC.Reno.cc(), T.TcpOptions.default()), T.TcpCallOpen{False{}}, 0, 0)), T.TcpArrive{G.TcpSeg{1000, 0, 2, 65535, Some{1460}, B.Octets.empty()}}, 0, 5000)) == [T.TcpOut{G.TcpSeg{5000, 1001, 18, 65535, Some{1460}, B.Octets.empty()}}, T.TcpSetTimer{T.TcpTimerRtx{}, 1000}] : List<&2, T.TcpAction>}

# a segment to a connection that does not exist is answered by a reset
# (3.10.7.1): <SEQ=0><ACK=SEG.SEQ+SEG.LEN><CTL=RST,ACK> without an ACK,
# <SEQ=SEG.ACK><CTL=RST> with one, nothing to a reset
law tcp_vector_reset_reply:
  {T.Tcp.reset_reply(G.TcpSeg{1000, 0, 2, 0, None{}, B.Octets.empty()}) == Some{G.TcpSeg{0, 1001, 20, 0, None{}, B.Octets.empty()}} : Maybe<&2, G.TcpSeg>}

law tcp_vector_reset_reply_ack:
  {T.Tcp.reset_reply(G.TcpSeg{1000, 777, 16, 0, None{}, B.Octets.of_string("ab")}) == Some{G.TcpSeg{777, 0, 4, 0, None{}, B.Octets.empty()}} : Maybe<&2, G.TcpSeg>}

law tcp_vector_no_reply_to_reset:
  {T.Tcp.reset_reply(G.TcpSeg{1000, 777, 4, 0, None{}, B.Octets.empty()}) == None{} : Maybe<&2, G.TcpSeg>}
