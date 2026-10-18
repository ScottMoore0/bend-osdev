# The walk-through vectors: TCP connections through sim.bend's simulated
# network (the expected traces come from ref/model.py, the independent
# model), then whole stacks exchanging Ethernet frames: ARP, ping, UDP with
# IPv4 fragmentation and reassembly out of order, and TCP.
import Base
import ../bytes/bytes.bend as B
import ../netheaders/ethernet.bend as E
import ./seq.bend as S
import ./rto.bend as R
import ./tcp.bend as T
import ./cc.bend as CC
import ./demux.bend as D
import ./ipv4.bend as IP
import ./show.bend as W
import ./sim.bend as M
import ./tcpip.bend as Z

def a() -> Bool:
  True{}

def b() -> Bool:
  False{}

# MSS 100, so that a few hundred bytes make several segments
def small() -> T.TcpOptions:
  T.TcpOptions{100, 65535, 65535, 4380, 120000, 8, 7, True{}, False{}, 64, R.RtoParams.default()}

# handshake, data both ways, A closes first, B closes, TIME-WAIT ends
def scenario0() -> List<&2, M.TcpSimCmd>:
  [M.TcpSimCall{b(), T.TcpCallOpen{False{}}}, M.TcpSimCall{a(), T.TcpCallOpen{True{}}}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimDeliver{b()}, M.TcpSimCall{a(), T.TcpCallSend{B.Octets.of_string("hello")}}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimCall{b(), T.TcpCallSend{B.Octets.of_string("world")}}, M.TcpSimDeliver{a()}, M.TcpSimDeliver{b()}, M.TcpSimCall{a(), T.TcpCallClose{}}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimCall{b(), T.TcpCallClose{}}, M.TcpSimDeliver{a()}, M.TcpSimDeliver{b()}, M.TcpSimTick{240000}]

# loss and retransmission: the RTO doubles (1 s, 2 s, 4 s) until the data gets through
def scenario1() -> List<&2, M.TcpSimCmd>:
  [M.TcpSimCall{b(), T.TcpCallOpen{False{}}}, M.TcpSimCall{a(), T.TcpCallOpen{True{}}}, M.TcpSimFlush{}, M.TcpSimTick{100}, M.TcpSimCall{a(), T.TcpCallSend{B.Octets.of_string("lost")}}, M.TcpSimDrop{b()}, M.TcpSimTick{1000}, M.TcpSimDrop{b()}, M.TcpSimTick{1000}, M.TcpSimTick{1000}, M.TcpSimDrop{b()}, M.TcpSimTick{4000}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}]

# segments out of order: held, then delivered in order once the gap fills (MSS 100)
def scenario2() -> List<&2, M.TcpSimCmd>:
  [M.TcpSimCall{b(), T.TcpCallOpen{False{}}}, M.TcpSimCall{a(), T.TcpCallOpen{True{}}}, M.TcpSimFlush{}, M.TcpSimCall{a(), T.TcpCallSend{B.Octets.of_string("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")}}, M.TcpSimDrop{b()}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimDeliver{a()}, M.TcpSimTick{1000}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}]

# simultaneous open, then simultaneous close (CLOSING)
def scenario3() -> List<&2, M.TcpSimCmd>:
  [M.TcpSimCall{a(), T.TcpCallOpen{True{}}}, M.TcpSimCall{b(), T.TcpCallOpen{True{}}}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimCall{a(), T.TcpCallClose{}}, M.TcpSimCall{b(), T.TcpCallClose{}}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimTick{240000}]

# an open to a closed port is refused; an abort resets the peer
def scenario4() -> List<&2, M.TcpSimCmd>:
  [M.TcpSimCall{a(), T.TcpCallOpen{True{}}}, M.TcpSimDeliver{b()}, M.TcpSimDeliver{a()}, M.TcpSimCall{b(), T.TcpCallOpen{False{}}}, M.TcpSimCall{a(), T.TcpCallOpen{True{}}}, M.TcpSimFlush{}, M.TcpSimCall{a(), T.TcpCallAbort{}}, M.TcpSimDeliver{b()}, M.TcpSimCall{b(), T.TcpCallSend{B.Octets.of_string("x")}}]


def trace(oa: T.TcpOptions, ob: T.TcpOptions, cs: List<&2, M.TcpSimCmd>) -> String:
  M.TcpSim.trace(CC.RenoState, M.TcpSim.run(~CC.RenoState, ~CC.Reno.cc(), cs, M.TcpSim.new(~CC.RenoState, ~CC.Reno.cc(), oa, 1000, ob, 5000)))

# Two stacks on one Ethernet: A at 10.0.0.1 (02:00:00:00:00:01), B at
# 10.0.0.2 (02:00:00:00:00:02); frames in flight each way, and a log

type Two is Data:
  Two{a: Z.Tcpip<CC.RenoState>, b: Z.Tcpip<CC.RenoState>, to_a: List<&2, B.Octets>, to_b: List<&2, B.Octets>, log: List<&2, String>}

def show(x: Z.TcpipAction) -> String:
  match x:
    case Z.TcpipTx{f}:
      "frame " ++ Nat.show(B.Octets.len(f))
    case Z.TcpipTcpOpened{k}:
      "tcp opened"
    case Z.TcpipTcpNote{k, n}:
      "tcp " ++ W.TcpShow.note(n)
    case Z.TcpipTcpData{k, d}:
      "tcp data " ++ B.Octets.to_string(d)
    case Z.TcpipUdpData{t, s, sp, dp, d}:
      "udp " ++ Nat.show(B.Octets.len(d)) ++ " bytes from port " ++ U32.show(sp) ++ " to " ++ U32.show(dp)
    case Z.TcpipPong{s, i, q, d}:
      "pong id " ++ U32.show(i) ++ " seq " ++ U32.show(q) ++ " " ++ B.Octets.to_string(d)
    case Z.TcpipSetTimer{t, at}:
      "timer " ++ U32.show(at)
    case Z.TcpipStopTimer{t}:
      "timer stopped"
    case _:
      "other"

def shows(xs: List<&2, Z.TcpipAction>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      shows(t, acc ++ "; " ++ show(h))

def frames(xs: List<&2, Z.TcpipAction>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      acc
    case Con{Z.TcpipTx{f}, t}:
      frames(t, List.append(&2, B.Octets, acc, [f]))
    case Con{h, t}:
      frames(t, acc)

def put(side: Bool, two: Two, label: String, r: Pair(Z.Tcpip<CC.RenoState>, List<&2, Z.TcpipAction>)) -> Two:
  match side:
    case True{}:
      match two:
        case Two{x, y, ta, tb, log}:
          match r:
            case (n, +acts):
              Two{n, y, ta, List.append(&2, B.Octets, tb, frames(acts, Nil{})), Con{"A " ++ label ++ shows(acts, ""), log}}
    case False{}:
      match two:
        case Two{x, y, ta, tb, log}:
          match r:
            case (n, +acts):
              Two{x, n, List.append(&2, B.Octets, ta, frames(acts, Nil{})), tb, Con{"B " ++ label ++ shows(acts, ""), log}}

def Two.a(t: Two) -> Z.Tcpip<CC.RenoState>:
  match t:
    case Two{x, y, ta, tb, l}:
      x

def Two.b(t: Two) -> Z.Tcpip<CC.RenoState>:
  match t:
    case Two{x, y, ta, tb, l}:
      y

def ev(side: Bool, +two: Two, e: Z.TcpipEvent, label: String) -> Two:
  match side:
    case True{}:
      put(True{}, two, label, Z.Tcpip.step_default(Two.a(two), e, 0))
    case False{}:
      put(False{}, two, label, Z.Tcpip.step_default(Two.b(two), e, 0))

# one frame arrives: the first to B, else the first to A
def pop(two: Two) -> Two:
  match two:
    case Two{x, y, ta, tb, log}:
      match ta tb:
        case ta2 Con{+f, t}:
          ev(False{}, Two{x, y, ta2, t, log}, Z.TcpipFrame{f}, "frame " ++ Nat.show(B.Octets.len(f)) ++ " arrives")
        case Con{+f, t} Nil{}:
          ev(True{}, Two{x, y, t, Nil{}, log}, Z.TcpipFrame{f}, "frame " ++ Nat.show(B.Octets.len(f)) ++ " arrives")
        case Nil{} Nil{}:
          Two{x, y, Nil{}, Nil{}, log}

def flush(n: Nat, two: Two) -> Two:
  match n:
    case 0n:
      two
    case 1n+m:
      flush(m, pop(two))

# the frames in flight to B, in reverse order
def reverse_b(two: Two) -> Two:
  match two:
    case Two{x, y, ta, tb, log}:
      Two{x, y, ta, List.reverse(&2, B.Octets, tb), Con{"(the frames to B are reordered)", log}}

def mac(k: U32) -> E.MacAddr:
  E.MacAddr{2, 0, 0, 0, 0, k}

def stack(k: U32, addr: U32) -> Z.Tcpip<CC.RenoState>:
  Z.Tcpip.new(CC.RenoState, Z.TcpipEthernet{mac(k)}, IP.Ipv4Config{addr, 4294967040, 167772161}, Z.TcpipOptions.default())

def big() -> B.Octets:
  B.Octets.of_list(List.replicate(U32, 4000n, 120))

def call(side: Bool, +two: Two, c: Z.TcpipCall, label: String) -> Two:
  ev(side, two, Z.TcpipCalled{c}, label)

def stacks() -> Two:
  +t0 = {Two{stack(1, 167772161), stack(2, 167772162), Nil{}, Nil{}, Nil{}} : Two}
  +t1 = flush(8n, call(a(), t0, Z.TcpipPing{167772162, 7, 1, B.Octets.of_string("ping")}, "ping 10.0.0.2"))
  +t2 = call(b(), t1, Z.TcpipUdpBind{9, 1}, "udp bind 9")
  +t3 = reverse_b(call(a(), t2, Z.TcpipUdpSend{5000, 167772162, 9, big()}, "udp send 4000 bytes"))
  +t4 = flush(8n, t3)
  +t5 = call(b(), t4, Z.TcpipTcpListen{80}, "tcp listen 80")
  +t6 = flush(8n, call(a(), t5, Z.TcpipTcpConnect{167772162, 80}, "tcp connect"))
  +t7 = flush(8n, call(a(), t6, Z.TcpipTcpSend{D.DemuxKey{49152, 167772162, 80}, B.Octets.of_string("GET /")}, "tcp send"))
  +t8 = flush(8n, call(a(), t7, Z.TcpipTcpClose{D.DemuxKey{49152, 167772162, 80}}, "tcp close"))
  flush(8n, call(b(), t8, Z.TcpipTcpClose{D.DemuxKey{80, 167772161, 49152}}, "tcp close"))

def Two.lines(t: Two) -> List<&2, String>:
  match t:
    case Two{x, y, ta, tb, l}:
      List.reverse(&2, String, l)

def print_all(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        print_all(t)

def show_bool(x: Bool) -> String:
  match x:
    case True{}:
      "true"
    case False{}:
      "false"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("== handshake, data both ways, A closes first, B closes, TIME-WAIT ends")
    IO.print(trace(T.TcpOptions.default(), T.TcpOptions.default(), scenario0()))
    IO.print("== loss and retransmission: the RTO doubles (1 s, 2 s, 4 s) until the data gets through")
    IO.print(trace(T.TcpOptions.default(), T.TcpOptions.default(), scenario1()))
    IO.print("== segments out of order: held, then delivered in order once the gap fills (MSS 100)")
    IO.print(trace(small(), small(), scenario2()))
    IO.print("== simultaneous open, then simultaneous close (CLOSING)")
    IO.print(trace(T.TcpOptions.default(), T.TcpOptions.default(), scenario3()))
    IO.print("== an open to a closed port is refused; an abort resets the peer")
    IO.print(trace(T.TcpOptions.default(), T.TcpOptions.default(), scenario4()))
    IO.print("== sequence numbers across the wrap: 4294967295 < 0, 0 < 2147483647, not 0 < 2147483648, not 2147483648 < 0")
    IO.print(show_bool(S.SeqNum.lt(4294967295, 0)) ++ " " ++ show_bool(S.SeqNum.lt(0, 2147483647)) ++ " " ++ show_bool(S.SeqNum.lt(0, 2147483648)) ++ " " ++ show_bool(S.SeqNum.lt(2147483648, 0)))
    IO.print("== two stacks: ARP and ping; UDP fragmented, reassembled out of order; TCP")
    print_all(Two.lines(stacks()))

#|== handshake, data both ways, A closes first, B closes, TIME-WAIT ends
#|t=0 B open passive => LISTEN
#|t=0 A open active => SYN-SENT; send S seq=1000 ack=0 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 B recv S seq=1000 ack=0 wnd=65535 len=0 mss=1460 => SYN-RECEIVED; send SA seq=5000 ack=1001 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 A recv SA seq=5000 ack=1001 wnd=65535 len=0 mss=1460 => ESTABLISHED; send A seq=1001 ack=5001 wnd=65535 len=0; note established; stop rtx
#|t=0 B recv A seq=1001 ack=5001 wnd=65535 len=0 => ESTABLISHED; note established; stop rtx
#|t=0 A send hello => ESTABLISHED; note queued 5; send AP seq=1001 ack=5001 wnd=65535 len=5; timer rtx 1000
#|t=0 B recv AP seq=1001 ack=5001 wnd=65535 len=5 => ESTABLISHED; deliver hello; send A seq=5001 ack=1006 wnd=65535 len=0
#|t=0 A recv A seq=5001 ack=1006 wnd=65535 len=0 => ESTABLISHED; stop rtx
#|t=0 B send world => ESTABLISHED; note queued 5; send AP seq=5001 ack=1006 wnd=65535 len=5; timer rtx 1000
#|t=0 A recv AP seq=5001 ack=1006 wnd=65535 len=5 => ESTABLISHED; deliver world; send A seq=1006 ack=5006 wnd=65535 len=0
#|t=0 B recv A seq=1006 ack=5006 wnd=65535 len=0 => ESTABLISHED; stop rtx
#|t=0 A close => FIN-WAIT-1; send AF seq=1006 ack=5006 wnd=65535 len=0; timer rtx 1000
#|t=0 B recv AF seq=1006 ack=5006 wnd=65535 len=0 => CLOSE-WAIT; send A seq=5006 ack=1007 wnd=65535 len=0; note peer closed
#|t=0 A recv A seq=5006 ack=1007 wnd=65535 len=0 => FIN-WAIT-2; stop rtx
#|t=0 B close => LAST-ACK; send AF seq=5006 ack=1007 wnd=65535 len=0; timer rtx 1000
#|t=0 A recv AF seq=5006 ack=1007 wnd=65535 len=0 => TIME-WAIT; send A seq=1007 ack=5007 wnd=65535 len=0; note peer closed; timer time-wait 240000
#|t=0 B recv A seq=1007 ack=5007 wnd=65535 len=0 => CLOSED; note closed; stop rtx
#|t=240000 A fire time-wait => CLOSED; note closed; stop time-wait
#|
#|== loss and retransmission: the RTO doubles (1 s, 2 s, 4 s) until the data gets through
#|t=0 B open passive => LISTEN
#|t=0 A open active => SYN-SENT; send S seq=1000 ack=0 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 B recv S seq=1000 ack=0 wnd=65535 len=0 mss=1460 => SYN-RECEIVED; send SA seq=5000 ack=1001 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 A recv SA seq=5000 ack=1001 wnd=65535 len=0 mss=1460 => ESTABLISHED; send A seq=1001 ack=5001 wnd=65535 len=0; note established; stop rtx
#|t=0 B recv A seq=1001 ack=5001 wnd=65535 len=0 => ESTABLISHED; note established; stop rtx
#|t=100 A send lost => ESTABLISHED; note queued 4; send AP seq=1001 ack=5001 wnd=65535 len=4; timer rtx 1100
#|t=100 lost to B: AP seq=1001 ack=5001 wnd=65535 len=4
#|t=1100 A fire rtx => ESTABLISHED; send AP seq=1001 ack=5001 wnd=65535 len=4; timer rtx 3100
#|t=1100 lost to B: AP seq=1001 ack=5001 wnd=65535 len=4
#|t=3100 A fire rtx => ESTABLISHED; send AP seq=1001 ack=5001 wnd=65535 len=4; timer rtx 7100
#|t=3100 lost to B: AP seq=1001 ack=5001 wnd=65535 len=4
#|t=7100 A fire rtx => ESTABLISHED; send AP seq=1001 ack=5001 wnd=65535 len=4; timer rtx 15100
#|t=7100 B recv AP seq=1001 ack=5001 wnd=65535 len=4 => ESTABLISHED; deliver lost; send A seq=5001 ack=1005 wnd=65535 len=0
#|t=7100 A recv A seq=5001 ack=1005 wnd=65535 len=0 => ESTABLISHED; stop rtx
#|
#|== segments out of order: held, then delivered in order once the gap fills (MSS 100)
#|t=0 B open passive => LISTEN
#|t=0 A open active => SYN-SENT; send S seq=1000 ack=0 wnd=65535 len=0 mss=100; timer rtx 1000
#|t=0 B recv S seq=1000 ack=0 wnd=65535 len=0 mss=100 => SYN-RECEIVED; send SA seq=5000 ack=1001 wnd=65535 len=0 mss=100; timer rtx 1000
#|t=0 A recv SA seq=5000 ack=1001 wnd=65535 len=0 mss=100 => ESTABLISHED; send A seq=1001 ack=5001 wnd=65535 len=0; note established; stop rtx
#|t=0 B recv A seq=1001 ack=5001 wnd=65535 len=0 => ESTABLISHED; note established; stop rtx
#|t=0 A send aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc => ESTABLISHED; note queued 300; send AP seq=1001 ack=5001 wnd=65535 len=100; send AP seq=1101 ack=5001 wnd=65535 len=100; send AP seq=1201 ack=5001 wnd=65535 len=100; timer rtx 1000
#|t=0 lost to B: AP seq=1001 ack=5001 wnd=65535 len=100
#|t=0 B recv AP seq=1101 ack=5001 wnd=65535 len=100 => ESTABLISHED; send A seq=5001 ack=1001 wnd=65535 len=0
#|t=0 B recv AP seq=1201 ack=5001 wnd=65535 len=100 => ESTABLISHED; send A seq=5001 ack=1001 wnd=65535 len=0
#|t=0 A recv A seq=5001 ack=1001 wnd=65535 len=0 => ESTABLISHED
#|t=0 A recv A seq=5001 ack=1001 wnd=65535 len=0 => ESTABLISHED
#|t=1000 A fire rtx => ESTABLISHED; send AP seq=1001 ack=5001 wnd=65535 len=100; timer rtx 3000
#|t=1000 B recv AP seq=1001 ack=5001 wnd=65535 len=100 => ESTABLISHED; deliver aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc; send A seq=5001 ack=1301 wnd=65535 len=0
#|t=1000 A recv A seq=5001 ack=1301 wnd=65535 len=0 => ESTABLISHED; stop rtx
#|
#|== simultaneous open, then simultaneous close (CLOSING)
#|t=0 A open active => SYN-SENT; send S seq=1000 ack=0 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 B open active => SYN-SENT; send S seq=5000 ack=0 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 B recv S seq=1000 ack=0 wnd=65535 len=0 mss=1460 => SYN-RECEIVED; send SA seq=5000 ack=1001 wnd=65535 len=0 mss=1460
#|t=0 A recv S seq=5000 ack=0 wnd=65535 len=0 mss=1460 => SYN-RECEIVED; send SA seq=1000 ack=5001 wnd=65535 len=0 mss=1460
#|t=0 B recv SA seq=1000 ack=5001 wnd=65535 len=0 mss=1460 => SYN-RECEIVED; send A seq=5001 ack=1001 wnd=65535 len=0
#|t=0 A recv SA seq=5000 ack=1001 wnd=65535 len=0 mss=1460 => SYN-RECEIVED; send A seq=1001 ack=5001 wnd=65535 len=0
#|t=0 A close => FIN-WAIT-1
#|t=0 B close => FIN-WAIT-1
#|t=0 B recv A seq=1001 ack=5001 wnd=65535 len=0 => FIN-WAIT-1; send AF seq=5001 ack=1001 wnd=65535 len=0
#|t=0 A recv A seq=5001 ack=1001 wnd=65535 len=0 => FIN-WAIT-1; send AF seq=1001 ack=5001 wnd=65535 len=0
#|t=0 B recv AF seq=1001 ack=5001 wnd=65535 len=0 => CLOSING; send A seq=5002 ack=1002 wnd=65535 len=0; note peer closed
#|t=0 A recv AF seq=5001 ack=1001 wnd=65535 len=0 => CLOSING; send A seq=1002 ack=5002 wnd=65535 len=0; note peer closed
#|t=0 B recv A seq=1002 ack=5002 wnd=65535 len=0 => TIME-WAIT; stop rtx; timer time-wait 240000
#|t=0 A recv A seq=5002 ack=1002 wnd=65535 len=0 => TIME-WAIT; stop rtx; timer time-wait 240000
#|t=240000 A fire time-wait => CLOSED; note closed; stop time-wait
#|t=240000 B fire time-wait => CLOSED; note closed; stop time-wait
#|
#|== an open to a closed port is refused; an abort resets the peer
#|t=0 A open active => SYN-SENT; send S seq=1000 ack=0 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 B recv S seq=1000 ack=0 wnd=65535 len=0 mss=1460 => CLOSED; send AR seq=0 ack=1001 wnd=0 len=0
#|t=0 A recv AR seq=0 ack=1001 wnd=0 len=0 => CLOSED; note refused; note closed; stop rtx
#|t=0 B open passive => LISTEN
#|t=0 A open active => SYN-SENT; send S seq=1000 ack=0 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 B recv S seq=1000 ack=0 wnd=65535 len=0 mss=1460 => SYN-RECEIVED; send SA seq=5000 ack=1001 wnd=65535 len=0 mss=1460; timer rtx 1000
#|t=0 A recv SA seq=5000 ack=1001 wnd=65535 len=0 mss=1460 => ESTABLISHED; send A seq=1001 ack=5001 wnd=65535 len=0; note established; stop rtx
#|t=0 B recv A seq=1001 ack=5001 wnd=65535 len=0 => ESTABLISHED; note established; stop rtx
#|t=0 A abort => CLOSED; send R seq=1001 ack=0 wnd=0 len=0; note closed
#|t=0 B recv R seq=1001 ack=0 wnd=0 len=0 => CLOSED; note reset; note closed
#|t=0 B send x => CLOSED; note error no connection
#|
#|== sequence numbers across the wrap: 4294967295 < 0, 0 < 2147483647, not 0 < 2147483648, not 2147483648 < 0
#|true true false false
#|== two stacks: ARP and ping; UDP fragmented, reassembled out of order; TCP
#|A ping 10.0.0.2; frame 60; timer 1000
#|B frame 60 arrives; frame 60
#|A frame 60 arrives; frame 60; timer stopped
#|B frame 60 arrives; frame 60
#|A frame 60 arrives; pong id 7 seq 1 ping
#|B udp bind 9
#|A udp send 4000 bytes; frame 1514; frame 1514; frame 1082
#|(the frames to B are reordered)
#|B frame 1082 arrives; timer 15000
#|B frame 1514 arrives
#|B frame 1514 arrives; udp 4000 bytes from port 5000 to 9; timer stopped
#|B tcp listen 80
#|A tcp connect; tcp opened; frame 60; timer 1000
#|B frame 60 arrives; frame 60; timer 1000
#|A frame 60 arrives; frame 60; tcp established; timer stopped
#|B frame 60 arrives; tcp established; timer stopped
#|A tcp send; tcp queued 5; frame 60; timer 1000
#|B frame 60 arrives; tcp data GET /; frame 60
#|A frame 60 arrives; timer stopped
#|A tcp close; frame 60; timer 1000
#|B frame 60 arrives; frame 60; tcp peer closed
#|A frame 60 arrives; timer stopped
#|B tcp close; frame 60; timer 1000
#|A frame 60 arrives; frame 60; tcp peer closed; timer 240000
#|B frame 60 arrives; tcp closed; timer stopped
