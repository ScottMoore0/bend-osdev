# ICMP (RFC 792): echo (ping) answered and sent, and error messages sent and
# received. Messages are parsed and built by bend-osdev-netheaders.
#
#   Icmp.step(st, event) -> (st, actions)
#
# Events: a message arrives (from src, to dst); the application pings; the
# stack reports an error about a packet it received (destination
# unreachable, time exceeded), quoting that packet's header and first 8
# bytes. Actions: a message to send, a reply to our ping, an error report
# that arrived.
import Base
import ../bytes/bytes.bend as B
import ../netheaders/netheaders.bend as N
import ../netheaders/icmp.bend as NI

# A message, decoded
type IcmpMsg is Data:
  IcmpEchoRequest{id: U32, seq: U32, data: B.Octets}
  IcmpEchoReply{id: U32, seq: U32, data: B.Octets}
  # destination unreachable (type 3), with the quoted header and 8 bytes
  IcmpUnreachable{code: U32, quoted: B.Octets}
  # time exceeded (type 11)
  IcmpTimeExceeded{code: U32, quoted: B.Octets}
  IcmpOther{msg_type: U32, code: U32, rest: U32, data: B.Octets}

type IcmpError is Data:
  IcmpBadChecksum{}
  IcmpBad{error: N.NetError}

# Codes of destination unreachable (RFC 792)
def Icmp.PROTO_UNREACHABLE() -> U32:
  2

def Icmp.PORT_UNREACHABLE() -> U32:
  3

def Icmp.rest(+id: U32, seq: U32) -> U32:
  U32.or(U32.shln(U32.and(id, 65535), 16n), U32.and(seq, 65535))

def Icmp.header(m: IcmpMsg) -> NI.IcmpHeader:
  match m:
    case IcmpEchoRequest{id, seq, d}:
      NI.IcmpHeader{8, 0, 0, Icmp.rest(id, seq)}
    case IcmpEchoReply{id, seq, d}:
      NI.IcmpHeader{0, 0, 0, Icmp.rest(id, seq)}
    case IcmpUnreachable{c, q}:
      NI.IcmpHeader{3, c, 0, 0}
    case IcmpTimeExceeded{c, q}:
      NI.IcmpHeader{11, c, 0, 0}
    case IcmpOther{t, c, r, d}:
      NI.IcmpHeader{t, c, 0, r}

def Icmp.body(m: IcmpMsg) -> B.Octets:
  match m:
    case IcmpEchoRequest{id, seq, d}:
      d
    case IcmpEchoReply{id, seq, d}:
      d
    case IcmpUnreachable{c, q}:
      q
    case IcmpTimeExceeded{c, q}:
      q
    case IcmpOther{t, c, r, d}:
      d

# the message's bytes, with its checksum
def Icmp.encode(+m: IcmpMsg) -> B.Octets:
  NI.IcmpHeader.build_checksum(Icmp.header(m), Icmp.body(m))

def Icmp.classify(echo: Bool, reply: Bool, unreach: Bool, exceeded: Bool, t: U32, c: U32, +r: U32, d: B.Octets) -> IcmpMsg:
  match echo reply unreach exceeded:
    case True{} _ _ _:
      IcmpEchoRequest{U32.shrn(r, 16n), U32.and(r, 65535), d}
    case False{} True{} _ _:
      IcmpEchoReply{U32.shrn(r, 16n), U32.and(r, 65535), d}
    case False{} False{} True{} _:
      IcmpUnreachable{c, d}
    case False{} False{} False{} True{}:
      IcmpTimeExceeded{c, d}
    case False{} False{} False{} False{}:
      IcmpOther{t, c, r, d}

def Icmp.of_header(h: NI.IcmpHeader, d: B.Octets) -> IcmpMsg:
  match h:
    case NI.IcmpHeader{+t, +c, k, +r}:
      Icmp.classify(U32.is_eq(t, 8), U32.is_eq(t, 0), U32.is_eq(t, 3), U32.is_eq(t, 11), t, c, r, d)

def Icmp.decode.go(ok: Bool, r: Result<&2, &2, N.NetError, NI.IcmpHeader>, +o: B.Octets) -> Result<&2, &2, IcmpError, IcmpMsg>:
  match ok:
    case False{}:
      Fail{IcmpBadChecksum{}}
    case True{}:
      match r:
        case Fail{e}:
          Fail{IcmpBad{e}}
        case Done{h}:
          Done{Icmp.of_header(h, B.Octets.drop(8n, o))}

# a message from its bytes: the checksum must verify
def Icmp.decode(+o: B.Octets) -> Result<&2, &2, IcmpError, IcmpMsg>:
  Icmp.decode.go(NI.IcmpHeader.verify(o), NI.IcmpHeader.parse(o), o)

# The answer RFC 792 gives a message: an echo request is answered by an
# echo reply with the same identifier, sequence number and data; nothing
# else is answered (RFC 1122 section 3.2.2: never an error about an error)
def Icmp.respond(m: IcmpMsg) -> Maybe<&2, IcmpMsg>:
  match m:
    case IcmpEchoRequest{id, seq, d}:
      Some{IcmpEchoReply{id, seq, d}}
    case _:
      None{}

# answer_echo: whether echo requests are answered
type IcmpOptions is Data:
  IcmpOptions{answer_echo: Bool}

def IcmpOptions.default() -> IcmpOptions:
  IcmpOptions{True{}}

type IcmpState is Data:
  IcmpState{opts: IcmpOptions}

type IcmpEvent is Data:
  IcmpRecv{src: U32, dst: U32, msg: B.Octets}
  IcmpPing{dst: U32, id: U32, seq: U32, data: B.Octets}
  # an error to send to dst about a packet of theirs: msg_type 3 or 11, its
  # code, and the packet's header and first 8 bytes
  IcmpReport{dst: U32, msg_type: U32, code: U32, head: B.Octets}

type IcmpAction is Data:
  IcmpOut{dst: U32, msg: B.Octets}
  IcmpEchoed{src: U32, id: U32, seq: U32, data: B.Octets}
  IcmpGotError{src: U32, msg: IcmpMsg}

def Icmp.answer(answer: Bool, +src: U32, m: Maybe<&2, IcmpMsg>) -> List<&2, IcmpAction>:
  match answer:
    case False{}:
      Nil{}
    case True{}:
      match m:
        case None{}:
          Nil{}
        case Some{r}:
          [IcmpOut{src, Icmp.encode(r)}]

def Icmp.recv.msg(+st: IcmpState, +src: U32, +m: IcmpMsg) -> List<&2, IcmpAction>:
  match st:
    case IcmpState{IcmpOptions{ae}}:
      match m:
        case IcmpEchoReply{id, seq, d}:
          [IcmpEchoed{src, id, seq, d}]
        case IcmpUnreachable{c, q}:
          [IcmpGotError{src, IcmpUnreachable{c, q}}]
        case IcmpTimeExceeded{c, q}:
          [IcmpGotError{src, IcmpTimeExceeded{c, q}}]
        case _:
          Icmp.answer(ae, src, Icmp.respond(m))

def Icmp.recv(+st: IcmpState, +src: U32, r: Result<&2, &2, IcmpError, IcmpMsg>) -> Pair(IcmpState, List<&2, IcmpAction>):
  match r:
    case Fail{e}:
      (st, Nil{})
    case Done{m}:
      (st, Icmp.recv.msg(st, src, m))

def Icmp.report(exceeded: Bool, c: U32, q: B.Octets) -> IcmpMsg:
  match exceeded:
    case True{}:
      IcmpTimeExceeded{c, q}
    case False{}:
      IcmpUnreachable{c, q}

def Icmp.step(+st: IcmpState, ev: IcmpEvent) -> Pair(IcmpState, List<&2, IcmpAction>):
  match ev:
    case IcmpRecv{src, dst, msg}:
      Icmp.recv(st, src, Icmp.decode(msg))
    case IcmpPing{dst, id, seq, d}:
      (st, [IcmpOut{dst, Icmp.encode(IcmpEchoRequest{id, seq, d})}])
    case IcmpReport{dst, t, c, head}:
      (st, [IcmpOut{dst, Icmp.encode(Icmp.report(U32.is_eq(t, 11), c, head))}])
