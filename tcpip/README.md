# bend-osdev-tcpip

A TCP/IP stack as a pure state machine: ARP, IPv4 with fragment reassembly,
ICMP echo, UDP sockets, TCP connections with the whole RFC 9293 state
machine, and the demultiplexer that routes packets to sockets. Every layer
is a function

```
step(state, event) -> (state, actions)
```

Events are a packet arriving, a timer firing, or a call from the
application; actions are a packet to send, data to deliver, a note for the
application, or a timer to set or stop. There is no IO inside the package:
the clock is a parameter (`now`, U32 milliseconds that wrap), and the caller
moves frames and keeps timers. So the stack runs in a kernel, over a TAP
device or a UDP tunnel in a user program (as `ref/peer.bend` does), or in a
test that scripts every packet and every millisecond (as `sim.bend` does).

Headers are parsed and built, and checksums computed, by
bend-osdev-netheaders; byte strings are bend-osdev-bytes' `Octets`.

## Specifications

* RFC 9293, Transmission Control Protocol (2022): the state machine (sections
  3.3.2 and 3.10), sequence numbers (3.4), the initial sequence number
  (3.4.1), MSS (3.7.1), Nagle's algorithm (3.7.4), retransmission limits
  (3.8.3), windows and zero-window probes (3.8.6), event processing (3.10.1
  to 3.10.8), including RFC 5961's challenge ACKs as section 3.10.7.4 asks;
* RFC 6298, Computing TCP's Retransmission Timer;
* RFC 5681, TCP Congestion Control (Reno: slow start, congestion avoidance,
  fast retransmit, fast recovery), with RFC 3390's initial window as RFC
  5681 restates it;
* RFC 6528, Defending against Sequence Number Attacks (the shape of the
  default ISN function; see Extension points);
* RFC 791, Internet Protocol (version 4), with fragmentation and reassembly;
* RFC 792, Internet Control Message Protocol;
* RFC 768, User Datagram Protocol;
* RFC 826, An Ethernet Address Resolution Protocol (the packet reception
  algorithm);
* RFC 1122, Requirements for Internet Hosts: Communication Layers (ARP cache
  timeout and queueing, ICMP errors not answered with errors, port and
  protocol unreachable, UDP checksums);
* RFC 6335's dynamic port range for active opens; RFC 8200 is not used (IPv6
  is not implemented; netheaders has its headers).

Written from these documents only; no other implementation's source was
read.

Where the RFC leaves a choice, the package makes one and says so:
* An acknowledgment is new when SND.UNA < SEG.ACK =< SND.MAX, where SND.MAX
  is the highest sequence number sent: it stands for the RFC's SND.NXT,
  which a retransmission timeout moves back (go-back-N from SND.UNA).
* In a simultaneous open, the peer's SYN,ACK reaching SYN-RECEIVED is not
  acceptable by section 3.10.7.4's sequence test (its SYN is already
  acknowledged), so it is answered with an ACK, as the text says; the
  connection becomes ESTABLISHED when that ACK arrives, one half round trip
  later than Figure 8 draws it.
* A FIN that arrives out of order is not held: the segment's data is queued,
  the FIN is dropped, and the peer resends it.
* A SYN's data is not queued (the peer resends it after the handshake).
* CLOSE before the handshake completes (SYN-RECEIVED) goes to FIN-WAIT-1 at
  once, and the FIN follows the data once our SYN is acknowledged.
* ACKs are sent at once, not delayed (delayed ACKs are a SHOULD the
  package does not take yet).

## Files

| File | Holds |
|---|---|
| `tcpip.bend` | the stack: the layers joined, the Ethernet or bare IPv4 link, application calls, timers (`Tcpip.step`) |
| `tcp.bend` | one TCP connection: the state diagram (`Tcp.next_state`, `Tcp.allowed`), the TCB, `Tcp.step` |
| `segment.bend` | `TcpSeg`, a segment as a connection sees it; the MSS option; conversion to and from netheaders' `TcpHeader` |
| `seq.bend` | sequence numbers and clock times compared modulo 2^32 (`SeqNum`) |
| `rcvq.bend` | the receive queue: pieces of a stream in any order, delivered in order (`RcvQ`); TCP's and IPv4 reassembly's |
| `rto.bend` | RFC 6298's retransmission timeout (`Rto`) |
| `cc.bend` | the congestion control interface (`TcpCc`) and Reno (`Reno.cc()`) |
| `demux.bend` | the socket table and routing (`Demux`) |
| `arp.bend` | ARP: the cache, resolution, waiting packets (`Arp.step`) |
| `ipv4.bend` | IPv4 input, reassembly, output, fragmentation (`Ipv4.step`) |
| `icmp.bend` | ICMP echo and errors (`Icmp.step`) |
| `udp.bend` | UDP sockets (`Udp.step`) |
| `sim.bend` | a simulated network of two TCP endpoints, for tests (`TcpSim`) |
| `show.bend` | text forms of segments, actions and notes (`TcpShow`) |

Bend imports do not re-export: import the files whose names you use.

## API

### The stack (`tcpip.bend`)

| Def or type | Meaning |
|---|---|
| `Tcpip.new(C, link, cfg, opts)` | a stack on `link` (`TcpipEthernet{mac}` or `TcpipRawIp{}`) with address, netmask and gateway `cfg` (`Ipv4Config`) |
| `Tcpip.step(~C, ~cc, ~isn, net, ev, now)` | one event: `(net, actions)` |
| `Tcpip.step_default(net, ev, now)` | the same with Reno and `Tcpip.isn_default` |
| `TcpipOptions{tcp, ipv4, arp, icmp, eph_lo, eph_hi, isn_secret}`, `TcpipOptions.default()` | every layer's options |
| events `TcpipEvent` | `TcpipFrame{bytes}` (from the link), `TcpipFire{timer}`, `TcpipCalled{call}` |
| calls `TcpipCall` | `TcpipTcpListen{port}`, `TcpipTcpConnect{dst, dport}`, `TcpipTcpSend{key, data}`, `TcpipTcpRead{key, n}`, `TcpipTcpClose{key}`, `TcpipTcpAbort{key}`, `TcpipUdpBind{port, tag}`, `TcpipUdpUnbind{port}`, `TcpipUdpSend{sport, dst, dport, data}`, `TcpipPing{dst, id, seq, data}` |
| actions `TcpipAction` | `TcpipTx{bytes}` (to the link), `TcpipTcpOpened{key}`, `TcpipTcpNote{key, note}`, `TcpipTcpData{key, data}`, `TcpipUdpData{tag, src, sport, dport, data}`, `TcpipUdpError{e}`, `TcpipPong{src, id, seq, data}`, `TcpipIcmpError{src, msg}`, `TcpipUnreachable{ip}`, `TcpipSetTimer{timer, at}`, `TcpipStopTimer{timer}`, `TcpipCallError{e}` |
| timers `TcpipTimer` | `TcpipTimerArp{}`, `TcpipTimerIp{}`, `TcpipTimerTcp{key, timer}` |

A connection is named by its `DemuxKey{lport, rip, rport}`; an accepted
connection is announced by `TcpipTcpNote{key, TcpNoteEstablished{}}`. A
listener is the wildcard key `DemuxKey.any(port)`; a SYN to it starts a
connection under the segment's full key, and the listener stays. A segment
to no connection is answered by a reset; a datagram to an unbound port, or a
packet of an unknown protocol, by ICMP unreachable (not when it was
broadcast). Outgoing Ethernet frames are padded to 60 bytes.

### A TCP connection (`tcp.bend`)

| Def or type | Meaning |
|---|---|
| `Tcp.new(~C, ~cc, opts)` | a connection in CLOSED |
| `Tcp.step(~C, ~cc, opts, conn, ev, now, isn)` | one event; `isn` is used only when the event opens the connection |
| `TcpEvent` | `TcpCallOpen{active}`, `TcpCallSend{data}`, `TcpCallRead{n}`, `TcpCallClose{}`, `TcpCallAbort{}`, `TcpArrive{seg}`, `TcpFire{timer}` |
| `TcpAction` | `TcpOut{seg}`, `TcpDeliver{data}`, `TcpNotify{note}`, `TcpSetTimer{timer, at}`, `TcpStopTimer{timer}` |
| `TcpNote` | `TcpNoteEstablished`, `TcpNotePeerClosed`, `TcpNoteReset`, `TcpNoteRefused`, `TcpNoteTimedOut`, `TcpNoteQueued{n}` (how much of a SEND the buffer took), `TcpNoteError{e}`, `TcpNoteClosed` |
| `TcpError` | `TcpErrNoConnection`, `TcpErrExists`, `TcpErrClosing` (RFC 9293's "connection does not exist", "already exists", "closing") |
| `TcpState`, `TcpState.name`, `TcpConn.state`, `TcpConn.una`, `TcpConn.max` | the eleven states; SND.UNA and the highest sequence number sent |
| `Tcp.next_state(s, input)`, `Tcp.allowed(s, t)`, `Tcp.diagram`, `Tcp.text_edge` | the state diagram, apart from the data |
| `Tcp.acks_new(snd, ack)`, `Tcp.acked_sent(una0, max0, una1)` | SND.UNA < SEG.ACK =< SND.MAX; SND.UNA stayed or moved forward to at most what was sent |
| `Tcp.reset_reply(seg)` | the reset answering a segment to no connection (3.10.7.1) |
| `TcpOptions{...}`, `TcpOptions.default()` | see Choices |

A timer event whose deadline has not come (or that was stopped) is ignored,
so a host may fire timers late or twice.

### The other layers

| File | Step | Notes |
|---|---|---|
| `arp.bend` | `Arp.step(st, ArpRecv{packet} / ArpSend{ip, packet} / ArpFire{}, now)` | actions `ArpFrame{dst, ethertype, payload}`, `ArpSetTimer{at}`, `ArpStopTimer{}`, `ArpUnreachable{ip, packets}`; `ArpState.new(opts, mac, ip)`; `ArpCache.lookup`, `ArpCache.put` |
| `ipv4.bend` | `Ipv4.step(st, Ipv4Recv{packet} / Ipv4Send{dst, proto, payload} / Ipv4Fire{}, now)` | actions `Ipv4Deliver{src, dst, proto, payload, head}` (head: the header and 8 bytes, for ICMP errors), `Ipv4Out{hop, packet}`, timer actions; `Ipv4State.new(cfg, opts)` |
| `icmp.bend` | `Icmp.step(st, IcmpRecv{src, dst, msg} / IcmpPing{...} / IcmpReport{dst, type, code, head})` | `IcmpMsg` (echo request and reply, unreachable, time exceeded, other), `Icmp.decode`, `Icmp.encode`, `Icmp.respond` |
| `udp.bend` | `Udp.step(st, UdpBind{port, tag} / UdpUnbind{port} / UdpSendTo{...} / UdpRecv{src, dst, dgram})` | actions `UdpOut{dst, dgram}`, `UdpDeliver{tag, src, sport, dport, data}`, `UdpNoPort{src, dst}`, `UdpErr{e}`; `Udp.receive` (a decoded datagram) |
| `demux.bend` | `Demux.find`, `insert`, `remove`, `route(d, lport, rip, rport)`, `port_used`, `keys` | any socket type `S` |
| `rcvq.bend` | `RcvQ.insert(limit, q, rel, data) -> RcvOut` | `RcvQ.new`, `RcvQ.next`, `RcvQ.count`, `RcvOut.queue`, `RcvOut.data` |
| `rto.bend` | `Rto.start`, `Rto.sample`, `Rto.backoff`, `Rto.syn_lost`, `Rto.current` | `RtoParams{initial, min, max, granularity, after_syn_loss}` |
| `cc.bend` | `TcpCc{start, cwnd, on_ack, on_dupack, on_timeout}` | `Reno.cc()`, `Reno.cc_with(ssthresh0)`, `RenoState`, `TcpAckInfo{acked, smss, flight}` |
| `seq.bend` | `SeqNum.lt/le/gt/ge/add/sub/max/min/in_half/in_window/reached` | |
| `sim.bend` | `TcpSim.new`, `TcpSim.run(~C, ~cc, cmds, sim)`, `TcpSim.trace`, `TcpSim.state` | commands `TcpSimCall`, `TcpSimDeliver`, `TcpSimDrop`, `TcpSimTick`, `TcpSimFlush` |

## Choices (parameters with named defaults)

| Option | Default | |
|---|---|---|
| `TcpOptions.mss` | 1460 | the MSS we advertise (Ethernet MTU 1500 less 40); the sender's MSS is the peer's option (536 without one, 3.7.1), at most ours |
| `rcv_buf` | 65535 | the receive buffer; the most we advertise (no window scaling) |
| `snd_buf` | 65535 | data held unacknowledged or unsent; SEND takes what fits (`TcpNoteQueued{n}`) |
| `iw_bytes` | 4380 | RFC 5681's IW = min(4 SMSS, max(2 SMSS, 4380)); one segment after a lost SYN |
| `msl` | 120000 | TIME-WAIT lasts 2 MSL (4 minutes) |
| `retries`, `syn_retries` | 8, 7 | retransmissions before giving up (R2: about 4 minutes of data, 3 of SYN) |
| `nagle` | true | Nagle's algorithm |
| `app_reads` | false | when true, delivered data fills the window until `TcpCallRead{n}` |
| `ooo_limit` | 64 | out-of-order pieces held |
| `rto` | `RtoParams.default()` | RTO 1 s initially, at least 1 s, at most 60 s, granularity 1 ms, 3 s after a lost SYN |
| `Ipv4Options` | MTU 1500, TTL 64, reassembly 15 s, 8 datagrams, 64 pieces each | at most 65515 bytes a datagram |
| `ArpOptions` | entries live 60 s, retry every 1 s, 3 requests, 4 packets wait, 64 entries | |
| `IcmpOptions.answer_echo` | true | |
| `TcpipOptions` | ports 49152 to 65535, ISN secret 0 | |
| congestion control | `~CC.Reno.cc()` | a template argument |
| ISN | `~Tcpip.isn_default` | a template argument |

## Extension points

* **Congestion control** is a template argument `~cc: TcpCc<C>` over any
  state type `C`: five functions (`start`, `cwnd`, `on_ack`, `on_dupack`,
  `on_timeout`). Reno is the default; NewReno, CUBIC or a fixed window for
  tests is another `TcpCc` value, specialised at compile time.
* **Initial sequence numbers**: `Tcp.step` takes the ISN as a parameter, and
  the stack takes the function that makes them as a template argument
  `~isn(secret, now, tuple)`. `Tcpip.isn_default` follows RFC 6528's shape,
  a 4-microsecond clock plus a keyed function of the connection's addresses
  and ports, but its keyed function is a simple integer hash, not a
  pseudorandom function: a stack facing untrusted peers passes a real one
  (a keyed SipHash, for example) and a secret.
* **Every limit and timer** is an option (Choices above).
* **Streaming** is the shape of every layer: data arrives a segment or a
  fragment at a time and is delivered as soon as it is in order (the
  receive queue, IPv4 reassembly); sending takes data in pieces as the send
  buffer has room (`TcpNoteQueued{n}`). There is no one-shot interface.
* **The link**: `TcpipEthernet{mac}` (with ARP) or `TcpipRawIp{}` (a TUN
  device, a point-to-point link); a host moves `TcpipTx` frames out and
  `TcpipFrame` frames in.
* **Each layer stands alone**: a TCP connection over another network layer
  needs only `tcp.bend` (segments as `TcpSeg`, `segment.bend` for the wire);
  `arp.bend`, `ipv4.bend`, `udp.bend` and `icmp.bend` have their own steps.
* **The state diagram** is a table (`Tcp.next_state`) apart from the data
  plane, and `Tcp.allowed` states what it may do; a changed transition is a
  change in one place, which the law checks.
* **Not yet there**, each a self-contained addition: window scaling and
  timestamps (RFC 7323), SACK (RFC 2018), delayed ACKs, keep-alives, urgent
  data (ignored), the user timeout option, path MTU discovery, IPv6 (RFC
  8200; netheaders parses it), ICMP time exceeded on a reassembly timeout,
  forwarding, IP options (passed over).

## Laws

`LAWS.bend`; every law is
proved in `PROOF.bend`.

**For every input:**
* sequence numbers: `SeqNum.lt` is irreflexive (`seq_lt_irrefl`),
  asymmetric (`seq_lt_asym`), total except for numbers exactly 2^31 apart
  (`seq_lt_total`); `lt(a, a + d) == in_half(d)` (`seq_lt_add`, the
  window); distances add (`seq_dist_add`); so transitive within a window
  (`seq_lt_trans`). Together: a strict total order within any window of
  2^31. Proved on Base's 32-bit words by induction on the bits, with the
  carries of two subtractions related by a small table of states found by
  enumeration;
* `rcvq_contiguous`: an insert into the receive queue delivers bytes that
  start at the next offset and move it by exactly their length, so delivery
  is in order and without gaps, whatever arrives in whatever order;
* `tcp_step_allowed`: for every connection, event, time and ISN, the state
  after `Tcp.step` is one `Tcp.allowed` lists from the state before: staying,
  CLOSED (a reset, ABORT, or a timeout), an edge of RFC 9293's Figure 5, or
  a transition its text adds (SYN-RECEIVED back to LISTEN; two edges taken
  by one segment: SYN-SENT to CLOSE-WAIT, SYN-RECEIVED to CLOSE-WAIT,
  FIN-WAIT-1 to TIME-WAIT);
* `tcp_acks_only_sent`: for every connection not in CLOSED or LISTEN, every
  event, time and ISN, SND.UNA after the step is the same or moved forward
  to at most the highest sequence number sent before it: an acknowledgment
  of data that was never sent is never taken. Proved by following SND.UNA
  through every stage of a step;
* `rto_backoff_bounded`, `rto_backoff_doubles`, `rto_sample_bounded`: a
  timeout doubles the RTO when that stays within the maximum, never exceeds
  the maximum, and no sample gives more than the maximum;
* `demux_find_insert`, `demux_find_remove`, `demux_find_insert_other`,
  `demux_route_exact`: a socket is found under its key, not after it is
  removed, another key's socket leaves a lookup alone, and a packet goes to
  the socket with its exact key;
* `udp_bound_delivers`, `udp_unbound_unreachable`: a datagram to a port
  just bound (with no more specific socket) is delivered with its source and
  data; one to a port nothing is bound to is reported for ICMP port
  unreachable;
* `icmp_echo_answered` and three `*_not_answered`: an echo request is
  answered by an echo reply with the same identifier, sequence number and
  data; a reply and the errors are not answered.

**Vectors**: RFC 6298's estimator (first and second samples, the 1 s
minimum, backoff to 60 s), Reno's windows (slow start, avoidance, fast
retransmit, the end of recovery, a timeout), sequence numbers across the
wrap, ICMP echo bytes decoded and answered (a corrupted checksum is not),
a SYN to a listener answered by SYN,ACK, and the resets for a segment to no
connection. Every law with a hypothesis has a satisfiability law (`*_sat`).

The TCP laws are stated for Reno, since a law cannot quantify over a
template argument; neither depends on the congestion controller. Not proved
for every input: that the delivered bytes are the stream's (the receive
queue law says where they start and how far they reach; the differential
tests compare the bytes), and the packet-level answers of UDP and ICMP
(their checksums need one's complement lemmas; vectors and the Linux test
cover them).

## Tests

* `check.bend`: five TCP walk-throughs through `sim.bend` (the three-way
  handshake, data both ways and both closes with TIME-WAIT; a segment lost
  three times, with the RTO doubling from 1 s to 2 s to 4 s; segments out of
  order, held and then delivered in order with duplicate ACKs; a
  simultaneous open and a simultaneous close through CLOSING; a refused
  open and an abort), whose expected traces come from the independent model;
  sequence numbers across the wrap; and two whole stacks on one Ethernet:
  ARP and ping, a 4000-byte UDP datagram fragmented into three and
  reassembled in reverse order, and a TCP connection's open, data and
  closes.
* `ref/run.sh`, two differential tests:
  1. `ref/gen.py` writes 100 random event scripts (opens of three kinds,
     data of up to 5000 bytes, losses, delays to every timer, reads, closes,
     aborts, with random options: MSS, buffer sizes, Nagle, `app_reads`,
     retry limits, MSL, out-of-order limit; and ISNs that wrap) and runs
     them through `ref/model.py`, an independent Python model of the
     connection written from RFC 9293, 6298 and 5681 and the choices above
     (it shares an author with the package; it is ordinary Python, not a
     translation); the Bend traces (6671 lines) must match exactly;
  2. the stack against Linux's own, when that is possible without
     privileges: `ref/linux.py` runs in a user and network namespace
     (`unshare -rn`), creates `tap0` there with 10.0.0.1/24, and bridges its
     frames to `ref/peer.bend` (the Bend stack at 10.0.0.2, built natively)
     as UDP datagrams on the namespace's loopback. Linux's `ping` (56 bytes,
     and 4000 bytes, fragmented both ways), UDP echo, TCP echo of 1 byte and
     200,000 bytes with closes from each side, the Bend stack's active open
     to a Linux listener with a half close, and TCP and UDP echo again with
     10% of frames lost each way: 12 checks. It is skipped (and said so)
     where `unshare -rn`, `/dev/net/tun`, `ip` or `ping` is missing (Ubuntu
     24.04 restricts unprivileged user namespaces by default; a CI runner
     may need `sysctl kernel.apparmor_restrict_unprivileged_userns=0`).

## Speed

Measured on native builds (Bend 2.0.37, WSL2):
* a TCP bulk transfer of 1 MB between two connections, segments handed
  straight across: 3.6 s, 16 MB peak. The send buffer is an `Octets`, which
  a segment slices from the front, so each segment costs time in the bytes
  held; a buffer of chunks would make it constant.
* `ref/linux.py`'s whole run against Linux (the 12 checks, 200 KB echoed,
  50 KB echoed with 10% loss): 13 s.
* `ref/run.sh` (both tests, building the cases and the peer): about 85 s.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (47 laws), `--verdict` ALL PROOFS
CHECK, `check.bend` passes, `ref/run.sh` 100 cases (6671 trace lines) match
the model and 12 of 12 checks pass against Linux 6.6, `scripts/deps.sh` ok.
