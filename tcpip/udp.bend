# UDP (RFC 768): sockets bound to ports, datagrams sent and received.
# Datagrams are built and checked by bend-osdev-netheaders (the checksum over
# the IPv4 pseudo-header; a zero checksum, "none computed", is accepted).
#
#   Udp.step(st, event) -> (st, actions)
#
# Events: bind a port (with a tag naming the socket to the application),
# unbind it, send a datagram, a datagram arrives. Actions: a datagram to send
# (the IPv4 payload, protocol 17), data delivered to a socket, a datagram to
# no socket (the stack answers it with ICMP port unreachable, RFC 1122
# section 4.1.3.1), and errors.
import Base
import ../bytes/bytes.bend as B
import ../netheaders/netheaders.bend as N
import ../netheaders/udp.bend as NU
import ./demux.bend as D

# a bound socket, as the application names it
type UdpSock is Data:
  UdpSock{tag: U32}

type UdpState is Data:
  UdpState{addr: U32, socks: D.Demux<UdpSock>}

type UdpError is Data:
  UdpErrPortInUse{port: U32}
  UdpErrNotBound{port: U32}
  UdpErrTooLong{}

type UdpEvent is Data:
  UdpBind{port: U32, tag: U32}
  UdpUnbind{port: U32}
  UdpSendTo{sport: U32, dst: U32, dport: U32, data: B.Octets}
  UdpRecv{src: U32, dst: U32, dgram: B.Octets}

type UdpAction is Data:
  UdpOut{dst: U32, dgram: B.Octets}
  UdpDeliver{tag: U32, src: U32, sport: U32, dport: U32, data: B.Octets}
  UdpNoPort{src: U32, dst: U32}
  UdpErr{error: UdpError}

def UdpState.new(addr: U32) -> UdpState:
  UdpState{addr, D.Demux.empty(UdpSock)}

# Sockets

def Udp.bind.go(m: Maybe<&2, UdpSock>, +st: UdpState, +port: U32, +tag: U32) -> Pair(UdpState, List<&2, UdpAction>):
  match m:
    case Some{s}:
      (st, [UdpErr{UdpErrPortInUse{port}}])
    case None{}:
      match st:
        case UdpState{a, d}:
          (UdpState{a, D.Demux.insert(UdpSock, d, D.DemuxKey.any(port), UdpSock{tag})}, Nil{})

# bind port to the socket tag; a port already bound is refused
def Udp.bind(+st: UdpState, +port: U32, +tag: U32) -> Pair(UdpState, List<&2, UdpAction>):
  match st:
    case UdpState{a, +d}:
      Udp.bind.go(D.Demux.find(UdpSock, d, D.DemuxKey.any(port)), st, port, tag)

def Udp.unbind.go(m: Maybe<&2, UdpSock>, +st: UdpState, +port: U32) -> Pair(UdpState, List<&2, UdpAction>):
  match m:
    case None{}:
      (st, [UdpErr{UdpErrNotBound{port}}])
    case Some{s}:
      match st:
        case UdpState{a, d}:
          (UdpState{a, D.Demux.remove(UdpSock, d, D.DemuxKey.any(port))}, Nil{})

def Udp.unbind(+st: UdpState, +port: U32) -> Pair(UdpState, List<&2, UdpAction>):
  match st:
    case UdpState{a, +d}:
      Udp.unbind.go(D.Demux.find(UdpSock, d, D.DemuxKey.any(port)), st, port)

# Receiving

def Udp.deliver(m: Maybe<&2, D.DemuxHit<UdpSock>>, +src: U32, +dst: U32, +sport: U32, +dport: U32, data: B.Octets) -> List<&2, UdpAction>:
  match m:
    case None{}:
      [UdpNoPort{src, dst}]
    case Some{D.DemuxHit{k, UdpSock{tag}}}:
      [UdpDeliver{tag, src, sport, dport, data}]

# a datagram from src, sport to our port dport, once decoded: delivered to
# the socket bound to dport, else reported as to no port (RFC 768: the port
# "names the user"; RFC 1122 4.1.3.1)
def Udp.receive(st: UdpState, +src: U32, +dst: U32, +sport: U32, +dport: U32, data: B.Octets) -> List<&2, UdpAction>:
  match st:
    case UdpState{a, d}:
      Udp.deliver(D.Demux.route(UdpSock, d, dport, src, sport), src, dst, sport, dport, data)

def Udp.recv.payload(r: Result<&2, &2, N.NetError, B.Octets>, +st: UdpState, +src: U32, +dst: U32, h: NU.UdpHeader) -> List<&2, UdpAction>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{data}:
      match h:
        case NU.UdpHeader{sp, dp, len, ck}:
          Udp.receive(st, src, dst, sp, dp, data)

def Udp.recv.header(r: Result<&2, &2, N.NetError, NU.UdpHeader>, +st: UdpState, +src: U32, +dst: U32, +dg: B.Octets) -> List<&2, UdpAction>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{+h}:
      Udp.recv.payload(NU.UdpHeader.payload(h, dg), st, src, dst, h)

def Udp.recv.go(ok: Bool, +st: UdpState, +src: U32, +dst: U32, +dg: B.Octets) -> List<&2, UdpAction>:
  match ok:
    case False{}:
      Nil{}
    case True{}:
      Udp.recv.header(NU.UdpHeader.parse(dg), st, src, dst, dg)

def Udp.recv.trim_length(ok: Bool, +st: UdpState, +src: U32, +dst: U32, +dg: B.Octets, n: Nat) -> List<&2, UdpAction>:
  match ok:
    case False{}:
      Nil{}
    case True{}:
      +trimmed = B.Octets.take(n, dg)
      Udp.recv.go(NU.UdpHeader.verify_ipv4(src, dst, trimmed), st, src, dst, trimmed)

def Udp.recv.trim_header(r: Result<&2, &2, N.NetError, NU.UdpHeader>, +st: UdpState, +src: U32, +dst: U32, +dg: B.Octets) -> List<&2, UdpAction>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{NU.UdpHeader{sp, dp, len, ck}}:
      +n = U32.to_nat(len)
      Udp.recv.trim_length(Bool.and(Nat.is_ge(n, 8n), Nat.is_le(n, B.Octets.len(dg))), st, src, dst, dg, n)

# RFC 768: the checksum covers only the declared UDP length. The IPv4
# payload may contain a surplus area (RFC 9868 sections 7-9); validate the
# length before trimming, so take cannot hide a truncated datagram.
def Udp.recv(+st: UdpState, +src: U32, +dst: U32, +dg: B.Octets) -> Pair(UdpState, List<&2, UdpAction>):
  (st, Udp.recv.trim_header(NU.UdpHeader.parse(dg), st, src, dst, dg))

# Sending: the header, with its checksum over the pseudo-header from our
# address to dst; at most 65507 bytes of data fit an IPv4 packet
def Udp.send.go(ok: Bool, +st: UdpState, +sport: U32, +dst: U32, +dport: U32, +data: B.Octets) -> Pair(UdpState, List<&2, UdpAction>):
  match ok:
    case False{}:
      (st, [UdpErr{UdpErrTooLong{}}])
    case True{}:
      match st:
        case UdpState{+a, d}:
          +h = {NU.UdpHeader{sport, dport, U32.add(8, U32.from_nat(B.Octets.len(data))), 0} : NU.UdpHeader}
          (st, [UdpOut{dst, NU.UdpHeader.build_ipv4(a, dst, h, data)}])

def Udp.send(+st: UdpState, +sport: U32, +dst: U32, +dport: U32, +data: B.Octets) -> Pair(UdpState, List<&2, UdpAction>):
  Udp.send.go(Nat.is_le(B.Octets.len(data), 65507n), st, sport, dst, dport, data)

def Udp.step(+st: UdpState, ev: UdpEvent) -> Pair(UdpState, List<&2, UdpAction>):
  match ev:
    case UdpBind{port, tag}:
      Udp.bind(st, port, tag)
    case UdpUnbind{port}:
      Udp.unbind(st, port)
    case UdpSendTo{sp, dst, dp, data}:
      Udp.send(st, sp, dst, dp, data)
    case UdpRecv{src, dst, dg}:
      Udp.recv(st, src, dst, dg)
