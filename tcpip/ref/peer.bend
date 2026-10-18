# The Bend stack as a host on a link, for ref/linux.py: Ethernet frames come
# and go as UDP datagrams to and from a bridge (which moves them to and from
# a TAP device), and the stack runs these services:
#   * ICMP echo (built in);
#   * UDP echo on port 7;
#   * TCP echo on port 7: every byte received is sent back, and the
#     connection is closed when the peer closes;
#   * one active open, to 10.0.0.1 port 9000: sends a greeting, closes, and
#     prints what comes back.
# Usage: peer <bridge port> <own port> <seconds>
import Base
import ../../bytes/bytes.bend as B
import ../../netheaders/ethernet.bend as E
import ../tcp.bend as T
import ../cc.bend as CC
import ../demux.bend as D
import ../ipv4.bend as IP
import ../seq.bend as S
import ../show.bend as W
import ../tcpip.bend as Z

def Stack() -> Data:
  Z.Tcpip<CC.RenoState>

# the host's timers
type PeerTimer is Data:
  PeerTimer{timer: Z.TcpipTimer, at: U32}

def Peer.same_tcp(a: T.TcpTimer, b: T.TcpTimer) -> Bool:
  match a b:
    case T.TcpTimerRtx{} T.TcpTimerRtx{}:
      True{}
    case T.TcpTimerTimeWait{} T.TcpTimerTimeWait{}:
      True{}
    case _ _:
      False{}

def Peer.same(a: Z.TcpipTimer, b: Z.TcpipTimer) -> Bool:
  match a b:
    case Z.TcpipTimerArp{} Z.TcpipTimerArp{}:
      True{}
    case Z.TcpipTimerIp{} Z.TcpipTimerIp{}:
      True{}
    case Z.TcpipTimerTcp{k1, t1} Z.TcpipTimerTcp{k2, t2}:
      Bool.and(D.DemuxKey.is_eq(k1, k2), Peer.same_tcp(t1, t2))
    case _ _:
      False{}

def Peer.unset.go(same: Bool, p: PeerTimer, rest: List<&2, PeerTimer>) -> List<&2, PeerTimer>:
  match same:
    case True{}:
      rest
    case False{}:
      Con{p, rest}

def Peer.unset(ts: List<&2, PeerTimer>, +t: Z.TcpipTimer) -> List<&2, PeerTimer>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{PeerTimer{+x, +at}, rest}:
      Peer.unset.go(Peer.same(x, t), PeerTimer{x, at}, Peer.unset(rest, t))

# what the services make of the stack's actions: the stack, timers, frames
# to send, lines to print, the calls the services make in answer, and the
# echo data not yet taken by a send buffer
type Peer is Data:
  Peer{net: Z.Tcpip<CC.RenoState>, timers: List<&2, PeerTimer>, frames: List<&2, B.Octets>, lines: List<&2, String>, calls: List<&2, PeerCall>, pend: List<&2, PeerPend>}

# The echo service reads (opening the window) only what its send buffer took;
# the rest waits here, and the connection closes once it has all gone
type PeerPend is Data:
  PeerPend{key: D.DemuxKey, data: B.Octets, closing: Bool}

type PeerCall is Data:
  PeerNet{call: Z.TcpipCall}
  # send what waits for connection key
  PeerFlush{key: D.DemuxKey}

def Peer.key(k: D.DemuxKey) -> String:
  match k:
    case D.DemuxKey{p, r, q}:
      U32.show(p) ++ "-" ++ U32.show(q)

def Peer.echo_port(k: D.DemuxKey) -> Bool:
  match k:
    case D.DemuxKey{p, r, q}:
      U32.is_eq(p, 7)

# Pending echo data, by connection

def Peer.pick.pend(c: Bool, a: PeerPend, b: PeerPend) -> PeerPend:
  match c:
    case True{}:
      a
    case False{}:
      b

def Peer.pend.get(ps: List<&2, PeerPend>, +k: D.DemuxKey) -> PeerPend:
  match ps:
    case Nil{}:
      PeerPend{k, B.Octets.empty(), False{}}
    case Con{PeerPend{+k2, +d, +c}, t}:
      Peer.pick.pend(D.DemuxKey.is_eq(k, k2), PeerPend{k2, d, c}, Peer.pend.get(t, k))

def Peer.pend.del.go(hit: Bool, x: PeerPend, rest: List<&2, PeerPend>) -> List<&2, PeerPend>:
  match hit:
    case True{}:
      rest
    case False{}:
      Con{x, rest}

def Peer.pend.del(ps: List<&2, PeerPend>, +k: D.DemuxKey) -> List<&2, PeerPend>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{PeerPend{+k2, d, c}, t}:
      Peer.pend.del.go(D.DemuxKey.is_eq(k, k2), PeerPend{k2, d, c}, Peer.pend.del(t, k))

def Peer.pend.set(+ps: List<&2, PeerPend>, x: PeerPend) -> List<&2, PeerPend>:
  match x:
    case PeerPend{+k, d, c}:
      Con{PeerPend{k, d, c}, Peer.pend.del(ps, k)}

def Peer.flushes(ps: List<&2, PeerPend>, acc: List<&2, PeerCall>) -> List<&2, PeerCall>:
  match ps:
    case Nil{}:
      acc
    case Con{PeerPend{k, d, c}, t}:
      Peer.flushes(t, Con{PeerFlush{k}, acc})

def Peer.pend.closing(+k: D.DemuxKey, +ps: List<&2, PeerPend>, x: PeerPend) -> Pair(List<&2, PeerPend>, List<&2, PeerCall>):
  match x:
    case PeerPend{k2, d, c}:
      (Peer.pend.set(ps, PeerPend{k, d, True{}}), [PeerFlush{k}])

def Peer.pend.queued(+k: D.DemuxKey, +q: U32, +ps: List<&2, PeerPend>, x: PeerPend) -> Pair(List<&2, PeerPend>, List<&2, PeerCall>):
  match x:
    case PeerPend{k2, d, c}:
      (Peer.pend.set(ps, PeerPend{k, B.Octets.drop(U32.to_nat(q), d), c}), [PeerNet{Z.TcpipTcpRead{k, q}}])

def Peer.on_note(n: T.TcpNote, echo: Bool, +k: D.DemuxKey, +ps: List<&2, PeerPend>) -> Pair(List<&2, PeerPend>, List<&2, PeerCall>):
  match n:
    case T.TcpNotePeerClosed{}:
      match echo:
        case True{}:
          Peer.pend.closing(k, ps, Peer.pend.get(ps, k))
        case False{}:
          (ps, Nil{})
    case T.TcpNoteEstablished{}:
      match echo:
        case True{}:
          (ps, Nil{})
        case False{}:
          (ps, [PeerNet{Z.TcpipTcpSend{k, B.Octets.of_string("hello from bend\n")}}, PeerNet{Z.TcpipTcpClose{k}}])
    case T.TcpNoteQueued{+q}:
      match echo:
        case True{}:
          Peer.pend.queued(k, q, ps, Peer.pend.get(ps, k))
        case False{}:
          (ps, Nil{})
    case T.TcpNoteClosed{}:
      (Peer.pend.del(ps, k), Nil{})
    case _:
      (ps, Nil{})

def Peer.data.add(+k: D.DemuxKey, +d: B.Octets, p: Peer, x: PeerPend) -> Peer:
  match p x:
    case Peer{n, ts, fs, ls, cs, +pd} PeerPend{k2, d0, c}:
      Peer{n, ts, fs, ls, List.append(&2, PeerCall, cs, [PeerFlush{k}]), Peer.pend.set(pd, PeerPend{k, B.Octets.append(d0, d), c})}

def Peer.data(echo: Bool, +k: D.DemuxKey, +d: B.Octets, p: Peer) -> Peer:
  match echo:
    case True{}:
      match p:
        case Peer{n, ts, fs, ls, cs, +pd}:
          Peer.data.add(k, d, Peer{n, ts, fs, ls, cs, pd}, Peer.pend.get(pd, k))
    case False{}:
      match p:
        case Peer{n, ts, fs, ls, cs, pd}:
          Peer{n, ts, fs, Con{"got " ++ B.Octets.to_string(d), ls}, cs, pd}

def Peer.noted(+k: D.DemuxKey, +note: T.TcpNote, p: Peer, r: Pair(List<&2, PeerPend>, List<&2, PeerCall>)) -> Peer:
  match p:
    case Peer{n, ts, fs, ls, cs, pd}:
      match r:
        case (pd2, more):
          Peer{n, ts, fs, Con{"tcp " ++ Peer.key(k) ++ " " ++ W.TcpShow.note(note), ls}, List.append(&2, PeerCall, cs, more), pd2}

def Peer.act(p: Peer, a: Z.TcpipAction) -> Peer:
  match p:
    case Peer{n, +ts, fs, ls, cs, +pd}:
      match a:
        case Z.TcpipTx{b}:
          Peer{n, ts, Con{b, fs}, ls, cs, pd}
        case Z.TcpipSetTimer{+t, at}:
          Peer{n, Con{PeerTimer{t, at}, Peer.unset(ts, t)}, fs, ls, cs, pd}
        case Z.TcpipStopTimer{+t}:
          Peer{n, Peer.unset(ts, t), fs, ls, cs, pd}
        case Z.TcpipTcpNote{+k, +note}:
          Peer.noted(k, note, Peer{n, ts, fs, ls, cs, pd}, Peer.on_note(note, Peer.echo_port(k), k, pd))
        case Z.TcpipTcpData{+k, +d}:
          Peer.data(Peer.echo_port(k), k, d, Peer{n, ts, fs, ls, cs, pd})
        case Z.TcpipUdpData{tag, src, sp, dp, +d}:
          Peer{n, ts, fs, Con{"udp " ++ Nat.show(B.Octets.len(d)), ls}, List.append(&2, PeerCall, cs, [PeerNet{Z.TcpipUdpSend{dp, src, sp, d}}]), pd}
        case Z.TcpipTcpOpened{k}:
          Peer{n, ts, fs, Con{"opened " ++ Peer.key(k), ls}, cs, pd}
        case _:
          Peer{n, ts, fs, ls, cs, pd}

def Peer.acts(xs: List<&2, Z.TcpipAction>, p: Peer) -> Peer:
  match xs:
    case Nil{}:
      p
    case Con{h, t}:
      Peer.acts(t, Peer.act(p, h))

def Peer.with_net(p: Peer, r: Pair(Z.Tcpip<CC.RenoState>, List<&2, Z.TcpipAction>)) -> Peer:
  match p:
    case Peer{n0, ts, fs, ls, cs, pd}:
      match r:
        case (n, acts):
          Peer.acts(acts, Peer{n, ts, fs, ls, cs, pd})

def Peer.event(+now: U32, ev: Z.TcpipEvent, p: Peer) -> Peer:
  match p:
    case Peer{+n, ts, fs, ls, cs, pd}:
      Peer.with_net(Peer{n, ts, fs, ls, cs, pd}, Z.Tcpip.step_default(n, ev, now))

# a flush: what waits goes to the send buffer; once nothing waits on a
# closing connection, it closes
def Peer.flush.go(some: Bool, closing: Bool, +now: U32, +k: D.DemuxKey, +d: B.Octets, p: Peer) -> Peer:
  match some:
    case True{}:
      Peer.event(now, Z.TcpipCalled{Z.TcpipTcpSend{k, d}}, p)
    case False{}:
      match closing:
        case True{}:
          match p:
            case Peer{n, ts, fs, ls, cs, pd}:
              Peer.event(now, Z.TcpipCalled{Z.TcpipTcpClose{k}}, Peer{n, ts, fs, ls, cs, Peer.pend.del(pd, k)})
        case False{}:
          p

def Peer.flush(+now: U32, +k: D.DemuxKey, x: PeerPend, p: Peer) -> Peer:
  match x:
    case PeerPend{k2, +d, c}:
      Peer.flush.go(Nat.is_gt(B.Octets.len(d), 0n), c, now, k, d, p)

def Peer.call(+now: U32, c: PeerCall, p: Peer) -> Peer:
  match c:
    case PeerNet{x}:
      Peer.event(now, Z.TcpipCalled{x}, p)
    case PeerFlush{+k}:
      match p:
        case Peer{n, ts, fs, ls, cs, +pd}:
          Peer.flush(now, k, Peer.pend.get(pd, k), Peer{n, ts, fs, ls, cs, pd})

# the services' calls, until they make no more (fuel bounds it)
def Peer.settle(fuel: Nat, +now: U32, p: Peer) -> Peer:
  match fuel:
    case 0n:
      p
    case 1n+f:
      match p:
        case Peer{n, ts, fs, ls, cs, pd}:
          match cs:
            case Nil{}:
              Peer{n, ts, fs, ls, Nil{}, pd}
            case Con{c, rest}:
              Peer.settle(f, now, Peer.call(now, c, Peer{n, ts, fs, ls, rest, pd}))

# every turn, what waits is offered to the send buffers again
def Peer.retry(+now: U32, p: Peer) -> Peer:
  match p:
    case Peer{n, ts, fs, ls, cs, +pd}:
      Peer.settle(256n, now, Peer{n, ts, fs, ls, List.append(&2, PeerCall, cs, Peer.flushes(pd, Nil{})), pd})

def Peer.due.go(due: Bool, t: Z.TcpipTimer, acc: List<&2, Z.TcpipTimer>) -> List<&2, Z.TcpipTimer>:
  match due:
    case True{}:
      Con{t, acc}
    case False{}:
      acc

# the timers due at now, fired
def Peer.due(ts: List<&2, PeerTimer>, +now: U32, acc: List<&2, Z.TcpipTimer>) -> List<&2, Z.TcpipTimer>:
  match ts:
    case Nil{}:
      acc
    case Con{PeerTimer{t, +at}, rest}:
      Peer.due(rest, now, Peer.due.go(S.SeqNum.reached(now, at), t, acc))

def Peer.drop_timer(+t: Z.TcpipTimer, p: Peer) -> Peer:
  match p:
    case Peer{n, ts, fs, ls, cs, pd}:
      Peer{n, Peer.unset(ts, t), fs, ls, cs, pd}

def Peer.fire(ts: List<&2, Z.TcpipTimer>, +now: U32, p: Peer) -> Peer:
  match ts:
    case Nil{}:
      p
    case Con{+t, rest}:
      Peer.fire(rest, now, Peer.settle(256n, now, Peer.event(now, Z.TcpipFire{t}, Peer.drop_timer(t, p))))

def Peer.timers(p: Peer) -> List<&2, PeerTimer>:
  match p:
    case Peer{n, ts, fs, ls, cs, pd}:
      ts

def Peer.tick(+now: U32, +p: Peer) -> Peer:
  Peer.retry(now, Peer.fire(Peer.due(Peer.timers(p), now, Nil{}), now, p))

# the defaults, but the application reads: the echo service's window closes
# while its data waits
def Peer.tcp_options(o: T.TcpOptions) -> T.TcpOptions:
  match o:
    case T.TcpOptions{m, rb, sb, iw, msl, r, sr, ng, ar, ool, rp}:
      T.TcpOptions{m, rb, sb, iw, msl, r, sr, ng, True{}, ool, rp}

def Peer.options.go(o: Z.TcpipOptions) -> Z.TcpipOptions:
  match o:
    case Z.TcpipOptions{t, i, a, c, lo, hi, s}:
      Z.TcpipOptions{Peer.tcp_options(t), i, a, c, lo, hi, s}

def Peer.options() -> Z.TcpipOptions:
  Peer.options.go(Z.TcpipOptions.default())

# One turn of the loop: the record, frames to send, lines to print, and
# whether to go on
type PeerTurn is Data:
  PeerTurn{peer: Peer, frames: List<&2, B.Octets>, lines: List<&2, String>, go: Bool}

def Peer.turn(go: Bool, p: Peer) -> PeerTurn:
  match p:
    case Peer{n, ts, fs, ls, cs, pd}:
      PeerTurn{Peer{n, ts, Nil{}, Nil{}, cs, pd}, List.reverse(&2, B.Octets, fs), List.reverse(&2, String, ls), go}

def Peer.is_quit(+bytes: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(B.len(bytes), 4n), B.list_eq(bytes, B.of_string("quit")))

def Peer.frame(quit: Bool, +now: U32, +bytes: List<&2, U32>, p: Peer) -> PeerTurn:
  match quit:
    case True{}:
      Peer.turn(False{}, p)
    case False{}:
      Peer.turn(True{}, Peer.tick(now, Peer.settle(256n, now, Peer.event(now, Z.TcpipFrame{B.Octets.of_list(bytes)}, p))))

def Peer.frame2(+b: List<&2, U32>, +now: U32, p: Peer) -> PeerTurn:
  Peer.frame(Peer.is_quit(b), now, b, p)

def Peer.datagram(d: String & U32 & List<&2, U32>, +now: U32, p: Peer) -> PeerTurn:
  match d:
    case (h, sp, b):
      Peer.frame2(b, now, p)

def Peer.process(+now: U32, +end: U32, p: Peer, got: Poll<&1, &1, Result<&1, &1, U32 & String, String & U32 & List<&2, U32>>, Unit>) -> PeerTurn:
  match got:
    case Wait{u}:
      Peer.turn(Bool.not(S.SeqNum.reached(now, end)), Peer.tick(now, p))
    case Ready{res}:
      match res:
        case Fail{e}:
          Peer.turn(True{}, p)
        case Done{d}:
          Peer.datagram(d, now, p)

def PeerTurn.peer(t: PeerTurn) -> Peer:
  match t:
    case PeerTurn{p, f, l, g}:
      p

def PeerTurn.frames(t: PeerTurn) -> List<&2, B.Octets>:
  match t:
    case PeerTurn{p, f, l, g}:
      f

def PeerTurn.lines(t: PeerTurn) -> List<&2, String>:
  match t:
    case PeerTurn{p, f, l, g}:
      l

def PeerTurn.go(t: PeerTurn) -> Bool:
  match t:
    case PeerTurn{p, f, l, g}:
      g

def Peer.wait.min(due: Bool, +d: U32, +w: U32) -> U32:
  match due:
    case True{}:
      0
    case False{}:
      CC.Reno.min(d, w)

# how long to wait for a frame: until the next timer, at most 20 ms
def Peer.wait.go(ts: List<&2, PeerTimer>, +now: U32, w: U32) -> U32:
  match ts:
    case Nil{}:
      w
    case Con{PeerTimer{t, +at}, rest}:
      Peer.wait.go(rest, now, Peer.wait.min(S.SeqNum.reached(now, at), U32.sub(at, now), w))

def Peer.wait(+p: Peer, +now: U32) -> U32:
  Peer.wait.go(Peer.timers(p), now, 20)

# IO

def Peer.sock(m: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> Socket:
  (s, r) = m
  s

def Peer.send(fs: List<&2, B.Octets>, sock: Socket, +port: U32) -> IO(Socket):
  match fs:
    case Nil{}:
      IO.pure(Socket, sock)
    case Con{f, t}:
      IO.bind(Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>, Socket, UDP.send_bytes_to(sock, "127.0.0.1", port, B.Octets.to_list(f)), m => Peer.send(t, Peer.sock(m), port))

def Peer.print(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        Peer.print(t)

def Peer.now() -> IO(U32):
  do IO<U32>:
    t : Nat <- IO.now()
    return U32.from_nat(t)

def Peer.loop(fuel: Nat, go: Bool, got: Socket & Poll<&1, &1, Result<&1, &1, U32 & String, String & U32 & List<&2, U32>>, Unit>, +port: U32, +end: U32, +p: Peer) -> IO(Unit):
  match fuel:
    case 0n:
      IO.print("out of fuel")
    case 1n+f:
      match go:
        case False{}:
          IO.print("done")
        case True{}:
          (s2, poll) = got
          do IO<Unit>:
            now : U32 <- Peer.now()
            +t : PeerTurn = Peer.process(now, end, p, poll)
            Peer.print(PeerTurn.lines(t))
            s3 : Socket <- Peer.send(PeerTurn.frames(t), s2, port)
            now2 : U32 <- Peer.now()
            +p2 : Peer = PeerTurn.peer(t)
            next : Socket & Poll<&1, &1, Result<&1, &1, U32 & String, String & U32 & List<&2, U32>>, Unit> <- UDP.try_recv_bytes_from(s3, 65536, Peer.wait(p2, now2))
            Peer.loop(f, PeerTurn.go(t), next, port, end, p2)

type PeerArgs is Data:
  PeerArgs{bridge: U32, own: U32, secs: U32}

def Peer.num(m: Maybe<&2, U32>) -> U32:
  Maybe.default(&2, U32, m, 0)

def Peer.args(xs: List<String>) -> PeerArgs:
  match xs:
    case Con{p, Con{a, Con{b, Con{c, r}}}}:
      PeerArgs{Peer.num(U32.read(a)), Peer.num(U32.read(b)), Peer.num(U32.read(c))}
    case _:
      PeerArgs{0, 0, 0}

def PeerArgs.bridge(a: PeerArgs) -> U32:
  match a:
    case PeerArgs{b, o, s}:
      b

def PeerArgs.own(a: PeerArgs) -> U32:
  match a:
    case PeerArgs{b, o, s}:
      o

def PeerArgs.secs(a: PeerArgs) -> U32:
  match a:
    case PeerArgs{b, o, s}:
      s

# 10.0.0.2/24, gateway 10.0.0.1, hardware address 02:00:00:00:00:02
def Peer.start(+now: U32) -> PeerTurn:
  +net = Z.Tcpip.new(CC.RenoState, Z.TcpipEthernet{E.MacAddr{2, 0, 0, 0, 0, 2}}, IP.Ipv4Config{167772162, 4294967040, 167772161}, Peer.options())
  Peer.turn(True{}, Peer.settle(64n, now, Peer{net, Nil{}, Nil{}, Nil{}, [PeerNet{Z.TcpipTcpListen{7}}, PeerNet{Z.TcpipUdpBind{7, 1}}, PeerNet{Z.TcpipTcpConnect{167772161, 9000}}], Nil{}}))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +a : PeerArgs = Peer.args(args)
    sock : Socket <- IO.try(Socket, UDP.bind("127.0.0.1", PeerArgs.own(a)))
    +now : U32 <- Peer.now()
    +t : PeerTurn = Peer.start(now)
    Peer.print(PeerTurn.lines(t))
    s2 : Socket <- Peer.send(PeerTurn.frames(t), sock, PeerArgs.bridge(a))
    first : Socket & Poll<&1, &1, Result<&1, &1, U32 & String, String & U32 & List<&2, U32>>, Unit> <- UDP.try_recv_bytes_from(s2, 65536, 1)
    Peer.loop(100000000n, True{}, first, PeerArgs.bridge(a), U32.add(now, U32.mul(PeerArgs.secs(a), 1000)), PeerTurn.peer(t))
