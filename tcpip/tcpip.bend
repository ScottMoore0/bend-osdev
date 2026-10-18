# bend-osdev-tcpip: a TCP/IP stack as a pure state machine.
#
#   Tcpip.step(~C, ~cc, ~isn, net, event, now) -> (net, actions)
#
# Events: a frame arrives from the link (an Ethernet frame, or an IPv4
# packet on a link without one), a timer fires, the application calls.
# Actions: a frame to send, data and notes for the application, timers to
# set or stop. There is no IO inside: now is the clock (U32 milliseconds),
# and the caller moves frames and keeps the timers.
#
# This file joins the layers, each a state machine of its own file: ARP
# (arp.bend), IPv4 (ipv4.bend), ICMP (icmp.bend), UDP (udp.bend), TCP
# connections (tcp.bend), and the demultiplexer that routes segments to them
# (demux.bend). ~C and ~cc are the congestion controller (cc.bend); ~isn
# makes initial sequence numbers (Tcpip.isn_default by default).
import Base
import ../bytes/bytes.bend as B
import ../netheaders/netheaders.bend as N
import ../netheaders/ethernet.bend as E
import ../netheaders/ipv4.bend as I4
import ../netheaders/tcp.bend as NT
import ./seq.bend as S
import ./segment.bend as G
import ./tcp.bend as T
import ./cc.bend as CC
import ./demux.bend as D
import ./arp.bend as A
import ./ipv4.bend as IP
import ./icmp.bend as IC
import ./udp.bend as U

# The link: Ethernet with our hardware address (ARP resolves next hops), or
# bare IPv4 packets (a TUN device, a point-to-point link)
type TcpipLink is Data:
  TcpipEthernet{mac: E.MacAddr}
  TcpipRawIp{}

# The layers' options; the ports connections are opened from (RFC 6335's
# dynamic range, 49152 to 65535); and the secret the ISN function keys on
type TcpipOptions is Data:
  TcpipOptions{tcp: T.TcpOptions, ipv4: IP.Ipv4Options, arp: A.ArpOptions, icmp: IC.IcmpOptions, eph_lo: U32, eph_hi: U32, isn_secret: U32}

def TcpipOptions.default() -> TcpipOptions:
  TcpipOptions{T.TcpOptions.default(), IP.Ipv4Options.default(), A.ArpOptions.default(), IC.IcmpOptions.default(), 49152, 65535, 0}

# A connection's addresses and ports, for the ISN function
type TcpipTuple is Data:
  TcpipTuple{laddr: U32, lport: U32, raddr: U32, rport: U32}

type Tcpip<-C: Data> is Data:
  Tcpip{link: TcpipLink, cfg: IP.Ipv4Config, opts: TcpipOptions, arp: A.ArpState, ip: IP.Ipv4State, icmp: IC.IcmpState, udp: U.UdpState, tcp: D.Demux<T.TcpConn<C>>, port: U32}

type TcpipTimer is Data:
  TcpipTimerArp{}
  TcpipTimerIp{}
  TcpipTimerTcp{key: D.DemuxKey, timer: T.TcpTimer}

type TcpipCall is Data:
  TcpipTcpListen{port: U32}
  TcpipTcpConnect{dst: U32, dport: U32}
  TcpipTcpSend{key: D.DemuxKey, data: B.Octets}
  TcpipTcpRead{key: D.DemuxKey, n: U32}
  TcpipTcpClose{key: D.DemuxKey}
  TcpipTcpAbort{key: D.DemuxKey}
  TcpipUdpBind{port: U32, tag: U32}
  TcpipUdpUnbind{port: U32}
  TcpipUdpSend{sport: U32, dst: U32, dport: U32, data: B.Octets}
  TcpipPing{dst: U32, id: U32, seq: U32, data: B.Octets}

type TcpipEvent is Data:
  TcpipFrame{bytes: B.Octets}
  TcpipFire{timer: TcpipTimer}
  TcpipCalled{call: TcpipCall}

type TcpipError is Data:
  TcpipErrNoConnection{key: D.DemuxKey}
  TcpipErrPortInUse{port: U32}
  TcpipErrNoFreePort{}

type TcpipAction is Data:
  # a frame (or IPv4 packet) for the link
  TcpipTx{bytes: B.Octets}
  # a connection opened by TcpipTcpConnect has this key
  TcpipTcpOpened{key: D.DemuxKey}
  TcpipTcpNote{key: D.DemuxKey, note: T.TcpNote}
  TcpipTcpData{key: D.DemuxKey, data: B.Octets}
  TcpipUdpData{tag: U32, src: U32, sport: U32, dport: U32, data: B.Octets}
  TcpipUdpError{error: U.UdpError}
  TcpipPong{src: U32, id: U32, seq: U32, data: B.Octets}
  TcpipIcmpError{src: U32, msg: IC.IcmpMsg}
  # ARP gave up on a next hop
  TcpipUnreachable{ip: U32}
  TcpipSetTimer{timer: TcpipTimer, at: U32}
  TcpipStopTimer{timer: TcpipTimer}
  TcpipCallError{error: TcpipError}

def Tcpip.pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# The default ISN function (RFC 9293 section 3.4.1, RFC 6528): a clock M
# that ticks every 4 microseconds, plus F, a mix of the connection's
# addresses and ports keyed by secret. This F is a simple integer hash, not
# the pseudorandom function RFC 6528 asks for: a stack facing the Internet
# passes one (a keyed SipHash, say) as ~isn instead.
def Tcpip.isn_default(secret: U32, now: U32, t: TcpipTuple) -> U32:
  match t:
    case TcpipTuple{la, lp, ra, rp}:
      +h1 = U32.mul(U32.xor(secret, la), 2654435761)
      +h2 = U32.mul(U32.xor(h1, U32.or(U32.shln(lp, 16n), rp)), 2246822519)
      +h3 = U32.mul(U32.xor(h2, ra), 3266489917)
      U32.add(U32.mul(now, 250), U32.xor(h3, U32.shrn(h3, 16n)))

def Tcpip.link_mac(l: TcpipLink) -> E.MacAddr:
  match l:
    case TcpipEthernet{m}:
      m
    case TcpipRawIp{}:
      E.MacAddr{0, 0, 0, 0, 0, 0}

# Field access

def Tcpip.new(-C: Data, +link: TcpipLink, +cfg: IP.Ipv4Config, +opts: TcpipOptions) -> Tcpip<C>:
  match opts:
    case TcpipOptions{tcp, +ipo, +arpo, +icmpo, +lo, hi, sec}:
      Tcpip{link, cfg, opts, A.ArpState.new(arpo, Tcpip.link_mac(link), IP.Ipv4Config.addr(cfg)), IP.Ipv4State.new(cfg, ipo), IC.IcmpState{icmpo}, U.UdpState.new(IP.Ipv4Config.addr(cfg)), D.Demux.empty(T.TcpConn<C>), lo}

def Tcpip.addr(-C: Data, n: Tcpip<C>) -> U32:
  match n:
    case Tcpip{l, cfg, o, a, i, c, u, t, p}:
      IP.Ipv4Config.addr(cfg)

def Tcpip.tcp_opts(-C: Data, n: Tcpip<C>) -> T.TcpOptions:
  match n:
    case Tcpip{l, cfg, TcpipOptions{to, io, ao, co, lo, hi, sec}, a, i, c, u, t, p}:
      to

def Tcpip.secret(-C: Data, n: Tcpip<C>) -> U32:
  match n:
    case Tcpip{l, cfg, TcpipOptions{to, io, ao, co, lo, hi, sec}, a, i, c, u, t, p}:
      sec

def Tcpip.tcp(-C: Data, n: Tcpip<C>) -> D.Demux<T.TcpConn<C>>:
  match n:
    case Tcpip{l, cfg, o, a, i, c, u, t, p}:
      t

def Tcpip.set_tcp(-C: Data, n: Tcpip<C>, t: D.Demux<T.TcpConn<C>>) -> Tcpip<C>:
  match n:
    case Tcpip{l, cfg, o, a, i, c, u, t0, p}:
      Tcpip{l, cfg, o, a, i, c, u, t, p}

def Tcpip.set_arp(-C: Data, n: Tcpip<C>, a: A.ArpState) -> Tcpip<C>:
  match n:
    case Tcpip{l, cfg, o, a0, i, c, u, t, p}:
      Tcpip{l, cfg, o, a, i, c, u, t, p}

def Tcpip.set_ip(-C: Data, n: Tcpip<C>, i: IP.Ipv4State) -> Tcpip<C>:
  match n:
    case Tcpip{l, cfg, o, a, i0, c, u, t, p}:
      Tcpip{l, cfg, o, a, i, c, u, t, p}

def Tcpip.set_udp(-C: Data, n: Tcpip<C>, u: U.UdpState) -> Tcpip<C>:
  match n:
    case Tcpip{l, cfg, o, a, i, c, u0, t, p}:
      Tcpip{l, cfg, o, a, i, c, u, t, p}

def Tcpip.set_port(-C: Data, n: Tcpip<C>, p: U32) -> Tcpip<C>:
  match n:
    case Tcpip{l, cfg, o, a, i, c, u, t, p0}:
      Tcpip{l, cfg, o, a, i, c, u, t, p}

# The stack while it works on an event: its state, and the actions so far
# (newest first)
type TcpipR<-C: Data> is Data:
  TcpipR{net: Tcpip<C>, acts: List<&2, TcpipAction>}

def TcpipR.push(-C: Data, r: TcpipR<C>, a: TcpipAction) -> TcpipR<C>:
  match r:
    case TcpipR{n, xs}:
      TcpipR{n, Con{a, xs}}

def TcpipR.net(-C: Data, r: TcpipR<C>) -> Tcpip<C>:
  match r:
    case TcpipR{n, xs}:
      n

# The link: Ethernet frames carry our address as source, and are padded to
# the 60-byte minimum (IEEE 802.3)
def Tcpip.frame(+mac: E.MacAddr, dst: E.MacAddr, +ethertype: U32, +payload: B.Octets) -> B.Octets:
  +f = B.Octets.append(E.EthHeader.build(E.EthHeader{dst, mac, None{}, ethertype}), payload)
  B.Octets.append(f, B.Octets.zeros(Nat.sub(60n, B.Octets.len(f))))

def Tcpip.arp_frame(-C: Data, dst: E.MacAddr, +ty: U32, +pl: B.Octets, r: TcpipR<C>) -> TcpipR<C>:
  match r:
    case TcpipR{Tcpip{l, cfg, o, a, i, c, u, t, p}, xs}:
      match l:
        case TcpipEthernet{+mac}:
          TcpipR{Tcpip{TcpipEthernet{mac}, cfg, o, a, i, c, u, t, p}, Con{TcpipTx{Tcpip.frame(mac, dst, ty, pl)}, xs}}
        case TcpipRawIp{}:
          TcpipR{Tcpip{TcpipRawIp{}, cfg, o, a, i, c, u, t, p}, xs}

def Tcpip.arp_acts(-C: Data, xs: List<&2, A.ArpAction>, r: TcpipR<C>) -> TcpipR<C>:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      match h:
        case A.ArpFrame{dst, ty, pl}:
          Tcpip.arp_acts(C, t, Tcpip.arp_frame(C, dst, ty, pl, r))
        case A.ArpSetTimer{at}:
          Tcpip.arp_acts(C, t, TcpipR.push(C, r, TcpipSetTimer{TcpipTimerArp{}, at}))
        case A.ArpStopTimer{}:
          Tcpip.arp_acts(C, t, TcpipR.push(C, r, TcpipStopTimer{TcpipTimerArp{}}))
        case A.ArpUnreachable{ip, ps}:
          Tcpip.arp_acts(C, t, TcpipR.push(C, r, TcpipUnreachable{ip}))

def Tcpip.arp_done(-C: Data, r: TcpipR<C>, res: Pair(A.ArpState, List<&2, A.ArpAction>)) -> TcpipR<C>:
  match r:
    case TcpipR{n, xs}:
      match res:
        case (a2, acts):
          Tcpip.arp_acts(C, acts, TcpipR{Tcpip.set_arp(C, n, a2), xs})

def Tcpip.arp_step(-C: Data, r: TcpipR<C>, ev: A.ArpEvent, +now: U32) -> TcpipR<C>:
  match r:
    case TcpipR{Tcpip{l, cfg, o, +a, i, c, u, t, p}, xs}:
      Tcpip.arp_done(C, TcpipR{Tcpip{l, cfg, o, a, i, c, u, t, p}, xs}, A.Arp.step(a, ev, now))

# an IPv4 packet to the next hop hop
def Tcpip.link_out(-C: Data, +hop: U32, +pkt: B.Octets, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match r:
    case TcpipR{Tcpip{l, cfg, o, a, i, c, u, t, p}, xs}:
      match l:
        case TcpipEthernet{mac}:
          Tcpip.arp_step(C, TcpipR{Tcpip{TcpipEthernet{mac}, cfg, o, a, i, c, u, t, p}, xs}, A.ArpSend{hop, pkt}, now)
        case TcpipRawIp{}:
          TcpipR{Tcpip{TcpipRawIp{}, cfg, o, a, i, c, u, t, p}, Con{TcpipTx{pkt}, xs}}

# IPv4 output: what sending produces (packets and the reassembly timer)
def Tcpip.ip_out_acts(-C: Data, xs: List<&2, IP.Ipv4Action>, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      match h:
        case IP.Ipv4Out{hop, pkt}:
          Tcpip.ip_out_acts(C, t, now, Tcpip.link_out(C, hop, pkt, now, r))
        case IP.Ipv4SetTimer{at}:
          Tcpip.ip_out_acts(C, t, now, TcpipR.push(C, r, TcpipSetTimer{TcpipTimerIp{}, at}))
        case IP.Ipv4StopTimer{}:
          Tcpip.ip_out_acts(C, t, now, TcpipR.push(C, r, TcpipStopTimer{TcpipTimerIp{}}))
        case IP.Ipv4Deliver{s, d, pr, pl, hd}:
          Tcpip.ip_out_acts(C, t, now, r)

def Tcpip.ip_done(-C: Data, +now: U32, r: TcpipR<C>, res: Pair(IP.Ipv4State, List<&2, IP.Ipv4Action>)) -> TcpipR<C>:
  match r:
    case TcpipR{n, xs}:
      match res:
        case (i2, acts):
          Tcpip.ip_out_acts(C, acts, now, TcpipR{Tcpip.set_ip(C, n, i2), xs})

# send payload to dst as protocol proto
def Tcpip.ip_out(-C: Data, +dst: U32, +proto: U32, +payload: B.Octets, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match r:
    case TcpipR{Tcpip{l, cfg, o, a, +i, c, u, t, p}, xs}:
      Tcpip.ip_done(C, now, TcpipR{Tcpip{l, cfg, o, a, i, c, u, t, p}, xs}, IP.Ipv4.step(i, IP.Ipv4Send{dst, proto, payload}, now))

# ICMP

def Tcpip.icmp_acts(-C: Data, xs: List<&2, IC.IcmpAction>, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      match h:
        case IC.IcmpOut{dst, msg}:
          Tcpip.icmp_acts(C, t, now, Tcpip.ip_out(C, dst, 1, msg, now, r))
        case IC.IcmpEchoed{src, id, seq, d}:
          Tcpip.icmp_acts(C, t, now, TcpipR.push(C, r, TcpipPong{src, id, seq, d}))
        case IC.IcmpGotError{src, m}:
          Tcpip.icmp_acts(C, t, now, TcpipR.push(C, r, TcpipIcmpError{src, m}))

def Tcpip.icmp_done(-C: Data, +now: U32, r: TcpipR<C>, res: Pair(IC.IcmpState, List<&2, IC.IcmpAction>)) -> TcpipR<C>:
  match res:
    case (c2, acts):
      Tcpip.icmp_acts(C, acts, now, r)

def Tcpip.icmp_step(-C: Data, ev: IC.IcmpEvent, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match r:
    case TcpipR{Tcpip{l, cfg, o, a, i, +c, u, t, p}, xs}:
      Tcpip.icmp_done(C, now, TcpipR{Tcpip{l, cfg, o, a, i, c, u, t, p}, xs}, IC.Icmp.step(c, ev))

# an ICMP error about a packet that arrived (quoting its header and 8
# bytes), unless that packet was to a broadcast (RFC 1122 section 3.2.2)
def Tcpip.report.go(-C: Data, bcast: Bool, +src: U32, code: U32, head: B.Octets, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match bcast:
    case True{}:
      r
    case False{}:
      Tcpip.icmp_step(C, IC.IcmpReport{src, 3, code, head}, now, r)

def Tcpip.report(-C: Data, +src: U32, +dst: U32, code: U32, head: B.Octets, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  Tcpip.report.go(C, U32.is_eq(dst, 4294967295), src, code, head, now, r)

# UDP

def Tcpip.udp_acts(-C: Data, xs: List<&2, U.UdpAction>, +head: B.Octets, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      match h:
        case U.UdpOut{dst, dg}:
          Tcpip.udp_acts(C, t, head, now, Tcpip.ip_out(C, dst, 17, dg, now, r))
        case U.UdpDeliver{tag, src, sp, dp, d}:
          Tcpip.udp_acts(C, t, head, now, TcpipR.push(C, r, TcpipUdpData{tag, src, sp, dp, d}))
        case U.UdpNoPort{src, dst}:
          Tcpip.udp_acts(C, t, head, now, Tcpip.report(C, src, dst, IC.Icmp.PORT_UNREACHABLE(), head, now, r))
        case U.UdpErr{e}:
          Tcpip.udp_acts(C, t, head, now, TcpipR.push(C, r, TcpipUdpError{e}))

def Tcpip.udp_done(-C: Data, +head: B.Octets, +now: U32, r: TcpipR<C>, res: Pair(U.UdpState, List<&2, U.UdpAction>)) -> TcpipR<C>:
  match r:
    case TcpipR{n, xs}:
      match res:
        case (u2, acts):
          Tcpip.udp_acts(C, acts, head, now, TcpipR{Tcpip.set_udp(C, n, u2), xs})

def Tcpip.udp_step(-C: Data, ev: U.UdpEvent, +head: B.Octets, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match r:
    case TcpipR{Tcpip{l, cfg, o, a, i, c, +u, t, p}, xs}:
      Tcpip.udp_done(C, head, now, TcpipR{Tcpip{l, cfg, o, a, i, c, u, t, p}, xs}, U.Udp.step(u, ev))

# TCP: a connection's actions, under its key

def Tcpip.tcp_seg(-C: Data, +k: D.DemuxKey, +s: G.TcpSeg, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match k:
    case D.DemuxKey{lp, +rip, rp}:
      +bytes = NT.TcpHeader.build_ipv4(Tcpip.addr(C, TcpipR.net(C, r)), rip, G.TcpSeg.header(lp, rp, s), G.TcpSeg.data(s))
      Tcpip.ip_out(C, rip, 6, bytes, now, r)

def Tcpip.tcp_acts(-C: Data, xs: List<&2, T.TcpAction>, +k: D.DemuxKey, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      match h:
        case T.TcpOut{s}:
          Tcpip.tcp_acts(C, t, k, now, Tcpip.tcp_seg(C, k, s, now, r))
        case T.TcpDeliver{d}:
          Tcpip.tcp_acts(C, t, k, now, TcpipR.push(C, r, TcpipTcpData{k, d}))
        case T.TcpNotify{n}:
          Tcpip.tcp_acts(C, t, k, now, TcpipR.push(C, r, TcpipTcpNote{k, n}))
        case T.TcpSetTimer{tm, at}:
          Tcpip.tcp_acts(C, t, k, now, TcpipR.push(C, r, TcpipSetTimer{TcpipTimerTcp{k, tm}, at}))
        case T.TcpStopTimer{tm}:
          Tcpip.tcp_acts(C, t, k, now, TcpipR.push(C, r, TcpipStopTimer{TcpipTimerTcp{k, tm}}))

# whether a connection is finished: CLOSED, or back in LISTEN under a full
# key (a connection a listener spawned, RFC 9293 3.10.7.4)
def Tcpip.finished(+st: T.TcpState, +k: D.DemuxKey) -> Bool:
  match k:
    case D.DemuxKey{lp, rip, rp}:
      Bool.or(T.TcpState.is(st, 0), Bool.and(T.TcpState.is(st, 1), Bool.not(Bool.and(U32.is_eq(rip, 0), U32.is_eq(rp, 0)))))

# the connection after a step goes back into the table (or leaves it), and
# its actions are carried out
def Tcpip.tcp_after(-C: Data, +k: D.DemuxKey, +now: U32, r: TcpipR<C>, res: Pair(T.TcpConn<C>, List<&2, T.TcpAction>)) -> TcpipR<C>:
  match r:
    case TcpipR{+n, xs}:
      match res:
        case (+conn, acts):
          +gone = Tcpip.finished(T.TcpConn.state(C, conn), k)
          +tcp = Tcpip.tcp(C, n)
          +tcp2 = Tcpip.pick(D.Demux<T.TcpConn<C>>, gone, D.Demux.remove(T.TcpConn<C>, tcp, k), D.Demux.insert(T.TcpConn<C>, tcp, k, conn))
          Tcpip.tcp_acts(C, acts, k, now, TcpipR{Tcpip.set_tcp(C, n, tcp2), xs})

def Tcpip.tuple(-C: Data, +n: Tcpip<C>, k: D.DemuxKey) -> TcpipTuple:
  match k:
    case D.DemuxKey{lp, rip, rp}:
      TcpipTuple{Tcpip.addr(C, n), lp, rip, rp}

# conn steps with ev; its ISN, should it need one, from ~isn
def Tcpip.tcp_step(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, +k: D.DemuxKey, conn: T.TcpConn<C>, ev: T.TcpEvent, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  +n = TcpipR.net(C, r)
  +i = isn(Tcpip.secret(C, n), now, Tcpip.tuple(C, n, k))
  Tcpip.tcp_after(C, k, now, r, T.Tcp.step(~C, ~cc, Tcpip.tcp_opts(C, n), conn, ev, now, i))

# a segment to no connection is answered by a reset (section 3.10.7.1)
def Tcpip.tcp_reset(-C: Data, +k: D.DemuxKey, m: Maybe<&2, G.TcpSeg>, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match m:
    case None{}:
      r
    case Some{s}:
      Tcpip.tcp_seg(C, k, s, now, r)

# a segment from src: to its connection, or to a listener (which spawns a
# connection under the segment's full key), or answered by a reset
def Tcpip.tcp_route(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, m: Maybe<&2, D.DemuxHit<T.TcpConn<C>>>, +exact: D.DemuxKey, +seg: G.TcpSeg, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match m:
    case None{}:
      Tcpip.tcp_reset(C, exact, T.Tcp.reset_reply(seg), now, r)
    case Some{D.DemuxHit{k, conn}}:
      Tcpip.tcp_step(~C, ~cc, ~isn, exact, conn, T.TcpArrive{seg}, now, r)

def Tcpip.tcp_header(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, h: Result<&2, &2, N.NetError, NT.TcpHeader>, +src: U32, +bytes: B.Octets, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match h:
    case Fail{e}:
      r
    case Done{+hd}:
      match hd:
        case NT.TcpHeader{+sp, +dp, sq, ak, off, rs, fl, win, ck, ur, o}:
          +seg = G.TcpSeg.of_header(hd, B.Octets.drop(NT.TcpHeader.length(hd), bytes))
          +exact = {D.DemuxKey{dp, src, sp} : D.DemuxKey}
          Tcpip.tcp_route(~C, ~cc, ~isn, D.Demux.route(T.TcpConn<C>, Tcpip.tcp(C, TcpipR.net(C, r)), dp, src, sp), exact, seg, now, r)

def Tcpip.tcp_in(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, ok: Bool, +src: U32, +bytes: B.Octets, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match ok:
    case False{}:
      r
    case True{}:
      Tcpip.tcp_header(~C, ~cc, ~isn, NT.TcpHeader.parse(bytes), src, bytes, now, r)

def Tcpip.deliver.go(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, icmp: Bool, tcp: Bool, udp: Bool, +src: U32, +dst: U32, +pl: B.Octets, +head: B.Octets, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match icmp tcp udp:
    case True{} _ _:
      Tcpip.icmp_step(C, IC.IcmpRecv{src, dst, pl}, now, r)
    case False{} True{} _:
      Tcpip.tcp_in(~C, ~cc, ~isn, NT.TcpHeader.verify_ipv4(src, dst, pl), src, pl, now, r)
    case False{} False{} True{}:
      Tcpip.udp_step(C, U.UdpRecv{src, dst, pl}, head, now, r)
    case False{} False{} False{}:
      Tcpip.report(C, src, dst, IC.Icmp.PROTO_UNREACHABLE(), head, now, r)

# A payload IPv4 delivered, to its protocol (RFC 1122 section 3.2.2: an
# unknown protocol gets protocol unreachable)
def Tcpip.deliver(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, +src: U32, +dst: U32, +proto: U32, +pl: B.Octets, +head: B.Octets, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  Tcpip.deliver.go(~C, ~cc, ~isn, U32.is_eq(proto, 1), U32.is_eq(proto, 6), U32.is_eq(proto, 17), src, dst, pl, head, now, r)

def Tcpip.ip_in_acts(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, xs: List<&2, IP.Ipv4Action>, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      match h:
        case IP.Ipv4Deliver{s, d, pr, pl, hd}:
          Tcpip.ip_in_acts(~C, ~cc, ~isn, t, now, Tcpip.deliver(~C, ~cc, ~isn, s, d, pr, pl, hd, now, r))
        case _:
          Tcpip.ip_in_acts(~C, ~cc, ~isn, t, now, Tcpip.ip_out_acts(C, [h], now, r))

def Tcpip.ip_in_done(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, +now: U32, r: TcpipR<C>, res: Pair(IP.Ipv4State, List<&2, IP.Ipv4Action>)) -> TcpipR<C>:
  match r:
    case TcpipR{n, xs}:
      match res:
        case (i2, acts):
          Tcpip.ip_in_acts(~C, ~cc, ~isn, acts, now, TcpipR{Tcpip.set_ip(C, n, i2), xs})

def Tcpip.ip_step(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, ev: IP.Ipv4Event, +now: U32, r: TcpipR<C>) -> TcpipR<C>:
  match r:
    case TcpipR{Tcpip{l, cfg, o, a, +i, c, u, t, p}, xs}:
      Tcpip.ip_in_done(~C, ~cc, ~isn, now, TcpipR{Tcpip{l, cfg, o, a, i, c, u, t, p}, xs}, IP.Ipv4.step(i, ev, now))

# A frame from the link

def Tcpip.mac_eq(a: E.MacAddr, b: E.MacAddr) -> Bool:
  B.Octets.is_eq(E.MacAddr.bytes(a), E.MacAddr.bytes(b))

def Tcpip.eth_type(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, mine: Bool, arp: Bool, ipv4: Bool, +pl: B.Octets, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match mine arp ipv4:
    case False{} _ _:
      r
    case True{} True{} _:
      Tcpip.arp_step(C, r, A.ArpRecv{pl}, now)
    case True{} False{} True{}:
      Tcpip.ip_step(~C, ~cc, ~isn, IP.Ipv4Recv{pl}, now, r)
    case True{} False{} False{}:
      r

def Tcpip.eth_in(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, h: Result<&2, &2, N.NetError, E.EthHeader>, +mac: E.MacAddr, +frame: B.Octets, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match h:
    case Fail{e}:
      r
    case Done{+hd}:
      match hd:
        case E.EthHeader{+dst, s, v, +ty}:
          +pl = B.Octets.drop(E.EthHeader.length(hd), frame)
          +mine = Bool.or(Tcpip.mac_eq(dst, mac), Tcpip.mac_eq(dst, E.MacAddr.broadcast()))
          Tcpip.eth_type(~C, ~cc, ~isn, mine, U32.is_eq(ty, E.EthHeader.TYPE_ARP()), U32.is_eq(ty, E.EthHeader.TYPE_IPV4()), pl, now, r)

def Tcpip.frame_in(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, +bytes: B.Octets, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match r:
    case TcpipR{Tcpip{l, cfg, o, a, i, c, u, t, p}, xs}:
      match l:
        case TcpipEthernet{+mac}:
          Tcpip.eth_in(~C, ~cc, ~isn, E.EthHeader.parse(bytes), mac, bytes, now, TcpipR{Tcpip{TcpipEthernet{mac}, cfg, o, a, i, c, u, t, p}, xs})
        case TcpipRawIp{}:
          Tcpip.ip_step(~C, ~cc, ~isn, IP.Ipv4Recv{bytes}, now, TcpipR{Tcpip{TcpipRawIp{}, cfg, o, a, i, c, u, t, p}, xs})

# Calls from the application

def Tcpip.no_conn(-C: Data, +k: D.DemuxKey, r: TcpipR<C>) -> TcpipR<C>:
  TcpipR.push(C, r, TcpipCallError{TcpipErrNoConnection{k}})

# a call on the connection with key k
def Tcpip.tcp_call(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, m: Maybe<&2, T.TcpConn<C>>, +k: D.DemuxKey, ev: T.TcpEvent, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match m:
    case None{}:
      Tcpip.no_conn(C, k, r)
    case Some{conn}:
      Tcpip.tcp_step(~C, ~cc, ~isn, k, conn, ev, now, r)

def Tcpip.tcp_on(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, +k: D.DemuxKey, ev: T.TcpEvent, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  Tcpip.tcp_call(~C, ~cc, ~isn, D.Demux.find(T.TcpConn<C>, Tcpip.tcp(C, TcpipR.net(C, r)), k), k, ev, now, r)

# LISTEN on port: a passive open, under the port's wildcard key
def Tcpip.listen(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, used: Bool, +port: U32, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match used:
    case True{}:
      TcpipR.push(C, r, TcpipCallError{TcpipErrPortInUse{port}})
    case False{}:
      Tcpip.tcp_step(~C, ~cc, ~isn, D.DemuxKey.any(port), T.Tcp.new(~C, ~cc, Tcpip.tcp_opts(C, TcpipR.net(C, r))), T.TcpCallOpen{False{}}, now, r)

# a free port from p on, wrapping within lo..hi; used is whether p is
def Tcpip.free_port(-C: Data, fuel: Nat, +t: D.Demux<T.TcpConn<C>>, +p: U32, +lo: U32, +hi: U32, used: Bool) -> Maybe<&2, U32>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match used:
        case False{}:
          Some{p}
        case True{}:
          +p2 = Tcpip.pick(U32, U32.is_ge(p, hi), lo, U32.add(p, 1))
          Tcpip.free_port(C, f, t, p2, lo, hi, D.Demux.port_used(T.TcpConn<C>, t, p2))

def Tcpip.find_port(-C: Data, n: Tcpip<C>) -> Maybe<&2, U32>:
  match n:
    case Tcpip{l, cfg, TcpipOptions{to, io, ao, co, +lo, +hi, sec}, a, i, c, u, +t, +p}:
      Tcpip.free_port(C, 16385n, t, p, lo, hi, D.Demux.port_used(T.TcpConn<C>, t, p))

def TcpipR.acts(-C: Data, r: TcpipR<C>) -> List<&2, TcpipAction>:
  match r:
    case TcpipR{n, xs}:
      xs

def Tcpip.port(-C: Data, n: Tcpip<C>) -> U32:
  match n:
    case Tcpip{l, cfg, o, a, i, c, u, t, p}:
      p

def Tcpip.next_port(-C: Data, n: Tcpip<C>, +p: U32) -> U32:
  match n:
    case Tcpip{l, cfg, TcpipOptions{to, io, ao, co, lo, +hi, sec}, a, i, c, u, t, p0}:
      Tcpip.pick(U32, U32.is_ge(p, hi), lo, U32.add(p, 1))

def Tcpip.connect.go(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, m: Maybe<&2, U32>, +dst: U32, +dport: U32, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match m:
    case None{}:
      TcpipR.push(C, r, TcpipCallError{TcpipErrNoFreePort{}})
    case Some{+p}:
      +k = {D.DemuxKey{p, dst, dport} : D.DemuxKey}
      +n = TcpipR.net(C, r)
      +r2 = {TcpipR{Tcpip.set_port(C, n, Tcpip.next_port(C, n, p)), Con{TcpipTcpOpened{k}, TcpipR.acts(C, r)}} : TcpipR<C>}
      Tcpip.tcp_step(~C, ~cc, ~isn, k, T.Tcp.new(~C, ~cc, Tcpip.tcp_opts(C, n)), T.TcpCallOpen{True{}}, now, r2)

# a connection to dst, dport from a free port
def Tcpip.connect(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, +dst: U32, +dport: U32, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  +n = TcpipR.net(C, r)
  Tcpip.connect.go(~C, ~cc, ~isn, Tcpip.find_port(C, n), dst, dport, now, r)

def Tcpip.call(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, c: TcpipCall, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match c:
    case TcpipTcpListen{+port}:
      Tcpip.listen(~C, ~cc, ~isn, D.Demux.port_used(T.TcpConn<C>, Tcpip.tcp(C, TcpipR.net(C, r)), port), port, now, r)
    case TcpipTcpConnect{dst, dport}:
      Tcpip.connect(~C, ~cc, ~isn, dst, dport, now, r)
    case TcpipTcpSend{k, d}:
      Tcpip.tcp_on(~C, ~cc, ~isn, k, T.TcpCallSend{d}, now, r)
    case TcpipTcpRead{k, n}:
      Tcpip.tcp_on(~C, ~cc, ~isn, k, T.TcpCallRead{n}, now, r)
    case TcpipTcpClose{k}:
      Tcpip.tcp_on(~C, ~cc, ~isn, k, T.TcpCallClose{}, now, r)
    case TcpipTcpAbort{k}:
      Tcpip.tcp_on(~C, ~cc, ~isn, k, T.TcpCallAbort{}, now, r)
    case TcpipUdpBind{port, tag}:
      Tcpip.udp_step(C, U.UdpBind{port, tag}, B.Octets.empty(), now, r)
    case TcpipUdpUnbind{port}:
      Tcpip.udp_step(C, U.UdpUnbind{port}, B.Octets.empty(), now, r)
    case TcpipUdpSend{sp, dst, dp, d}:
      Tcpip.udp_step(C, U.UdpSendTo{sp, dst, dp, d}, B.Octets.empty(), now, r)
    case TcpipPing{dst, id, seq, d}:
      Tcpip.icmp_step(C, IC.IcmpPing{dst, id, seq, d}, now, r)

# A timer
def Tcpip.fire(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, t: TcpipTimer, +now: U32, +r: TcpipR<C>) -> TcpipR<C>:
  match t:
    case TcpipTimerArp{}:
      Tcpip.arp_step(C, r, A.ArpFire{}, now)
    case TcpipTimerIp{}:
      Tcpip.ip_step(~C, ~cc, ~isn, IP.Ipv4Fire{}, now, r)
    case TcpipTimerTcp{k, tm}:
      Tcpip.tcp_on(~C, ~cc, ~isn, k, T.TcpFire{tm}, now, r)

def Tcpip.rev(xs: List<&2, TcpipAction>, acc: List<&2, TcpipAction>) -> List<&2, TcpipAction>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Tcpip.rev(t, Con{h, acc})

def Tcpip.finish(-C: Data, r: TcpipR<C>) -> Pair(Tcpip<C>, List<&2, TcpipAction>):
  match r:
    case TcpipR{n, xs}:
      (n, Tcpip.rev(xs, Nil{}))

# One event at time now: the stack after it, and its actions in order
def Tcpip.step(~C: Data, ~cc: CC.TcpCc<C>, ~isn: U32 -> U32 -> TcpipTuple -> U32, net: Tcpip<C>, ev: TcpipEvent, +now: U32) -> Pair(Tcpip<C>, List<&2, TcpipAction>):
  match ev:
    case TcpipFrame{bytes}:
      Tcpip.finish(C, Tcpip.frame_in(~C, ~cc, ~isn, bytes, now, TcpipR{net, Nil{}}))
    case TcpipFire{t}:
      Tcpip.finish(C, Tcpip.fire(~C, ~cc, ~isn, t, now, TcpipR{net, Nil{}}))
    case TcpipCalled{c}:
      Tcpip.finish(C, Tcpip.call(~C, ~cc, ~isn, c, now, TcpipR{net, Nil{}}))

# the default stack: Reno, and the default ISN function
def Tcpip.step_default(net: Tcpip<CC.RenoState>, ev: TcpipEvent, +now: U32) -> Pair(Tcpip<CC.RenoState>, List<&2, TcpipAction>):
  Tcpip.step(~CC.RenoState, ~CC.Reno.cc(), ~Tcpip.isn_default, net, ev, now)
