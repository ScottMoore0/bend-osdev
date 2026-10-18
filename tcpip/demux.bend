# The demultiplexer: a table of sockets, keyed by local port and remote
# address and port, that routes an arriving packet to the socket it belongs
# to (RFC 9293 section 3.10.7: a connection is identified by its socket
# pair; RFC 768: a datagram goes to the port it names).
#
# A key whose remote address and port are 0 is a wildcard: a listening TCP
# socket or an unconnected UDP socket. A packet goes to the socket with its
# exact key if there is one, else to the wildcard socket on its port.
# Sockets are of any Data type S (a TCP connection, a UDP socket's tag).
import Base

type DemuxKey is Data:
  DemuxKey{lport: U32, rip: U32, rport: U32}

type DemuxEntry<-S: Data> is Data:
  DemuxEntry{key: DemuxKey, sock: S}

type Demux<-S: Data> is Data:
  Demux{entries: List<&2, DemuxEntry<S>>}

# what a route finds: the socket's key and the socket
type DemuxHit<-S: Data> is Data:
  DemuxHit{key: DemuxKey, sock: S}

def Demux.empty(-S: Data) -> Demux<S>:
  Demux{Nil{}}

# the wildcard key of port p
def DemuxKey.any(p: U32) -> DemuxKey:
  DemuxKey{p, 0, 0}

def DemuxKey.is_eq(a: DemuxKey, b: DemuxKey) -> Bool:
  match a b:
    case DemuxKey{p1, a1, r1} DemuxKey{p2, a2, r2}:
      Bool.and(U32.is_eq(p1, p2), Bool.and(U32.is_eq(a1, a2), U32.is_eq(r1, r2)))

def DemuxKey.lport(k: DemuxKey) -> U32:
  match k:
    case DemuxKey{p, a, r}:
      p

# whether the first entry of xs has key k
def Demux.head_is(-S: Data, xs: List<&2, DemuxEntry<S>>, +k: DemuxKey) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{DemuxEntry{e, s}, t}:
      DemuxKey.is_eq(k, e)

# hit is Demux.head_is(S, xs, k)
def Demux.find.go(-S: Data, xs: List<&2, DemuxEntry<S>>, +k: DemuxKey, hit: Bool) -> Maybe<&2, S>:
  match xs:
    case Nil{}:
      None{}
    case Con{DemuxEntry{e, s}, +t}:
      match hit:
        case True{}:
          Some{s}
        case False{}:
          Demux.find.go(S, t, k, Demux.head_is(S, t, k))

def Demux.remove.go(-S: Data, xs: List<&2, DemuxEntry<S>>, +k: DemuxKey, hit: Bool) -> List<&2, DemuxEntry<S>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, +t}:
      match hit:
        case True{}:
          Demux.remove.go(S, t, k, Demux.head_is(S, t, k))
        case False{}:
          Con{h, Demux.remove.go(S, t, k, Demux.head_is(S, t, k))}

# the socket with key k
def Demux.find(-S: Data, d: Demux<S>, +k: DemuxKey) -> Maybe<&2, S>:
  match d:
    case Demux{+xs}:
      Demux.find.go(S, xs, k, Demux.head_is(S, xs, k))

# the table without the socket with key k
def Demux.remove(-S: Data, d: Demux<S>, +k: DemuxKey) -> Demux<S>:
  match d:
    case Demux{+xs}:
      Demux{Demux.remove.go(S, xs, k, Demux.head_is(S, xs, k))}

# the table with s under key k (replacing any socket with that key)
def Demux.insert(-S: Data, d: Demux<S>, +k: DemuxKey, s: S) -> Demux<S>:
  match d:
    case Demux{+xs}:
      Demux{Con{DemuxEntry{k, s}, Demux.remove.go(S, xs, k, Demux.head_is(S, xs, k))}}

def Demux.hit(-S: Data, k: DemuxKey, m: Maybe<&2, S>) -> Maybe<&2, DemuxHit<S>>:
  match m:
    case Some{s}:
      Some{DemuxHit{k, s}}
    case None{}:
      None{}

def Demux.route.go(-S: Data, m: Maybe<&2, S>, +d: Demux<S>, +exact: DemuxKey, +lp: U32) -> Maybe<&2, DemuxHit<S>>:
  match m:
    case Some{s}:
      Some{DemuxHit{exact, s}}
    case None{}:
      Demux.hit(S, DemuxKey.any(lp), Demux.find(S, d, DemuxKey.any(lp)))

# where a packet to local port lp from rip, rport goes: the socket with that
# exact key, else the wildcard socket on lp
def Demux.route(-S: Data, +d: Demux<S>, +lp: U32, rip: U32, rport: U32) -> Maybe<&2, DemuxHit<S>>:
  +exact = {DemuxKey{lp, rip, rport} : DemuxKey}
  Demux.route.go(S, Demux.find(S, d, exact), d, exact, lp)

def Demux.used.go(-S: Data, xs: List<&2, DemuxEntry<S>>, +p: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{DemuxEntry{e, s}, t}:
      Bool.or(U32.is_eq(DemuxKey.lport(e), p), Demux.used.go(S, t, p))

# whether any socket has local port p
def Demux.port_used(-S: Data, d: Demux<S>, +p: U32) -> Bool:
  match d:
    case Demux{xs}:
      Demux.used.go(S, xs, p)

def Demux.keys.go(-S: Data, xs: List<&2, DemuxEntry<S>>, acc: List<&2, DemuxKey>) -> List<&2, DemuxKey>:
  match xs:
    case Nil{}:
      acc
    case Con{DemuxEntry{e, s}, t}:
      Demux.keys.go(S, t, Con{e, acc})

# every key in the table
def Demux.keys(-S: Data, d: Demux<S>) -> List<&2, DemuxKey>:
  match d:
    case Demux{xs}:
      Demux.keys.go(S, xs, Nil{})
