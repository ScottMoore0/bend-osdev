# ARP (RFC 826) for IPv4 over Ethernet: the cache of addresses learned, and
# resolution, with the packets that wait for it.
#
#   Arp.step(st, event, now) -> (st, actions)
#
# Events: an ARP packet arrives; an IPv4 packet is to go to a next-hop
# address; the timer fires. Actions: a frame to send (its destination and
# EtherType; the caller adds the Ethernet header), the timer to set or stop,
# and packets given up on when an address does not resolve.
import Base
import ../bytes/bytes.bend as B
import ../netheaders/ethernet.bend as E
import ../netheaders/netheaders.bend as N
import ../netheaders/arp.bend as NA
import ./seq.bend as S

# ttl: how long a learned address is kept (RFC 1122 section 2.3.2.1 asks for
# a timeout); retry: the time between requests; tries: requests before giving
# up; queue: packets kept per unresolved address (RFC 1122: at least one);
# entries: the most addresses cached
type ArpOptions is Data:
  ArpOptions{ttl: U32, retry: U32, tries: U32, queue: U32, entries: U32}

def ArpOptions.default() -> ArpOptions:
  ArpOptions{60000, 1000, 3, 4, 64}

type ArpEntry is Data:
  ArpEntry{ip: U32, mac: E.MacAddr, expires: U32}

# an address being resolved: the packets for it (oldest first), the requests
# sent, and when the next is due
type ArpWait is Data:
  ArpWait{ip: U32, packets: List<&2, B.Octets>, tries: U32, next: U32}

# our addresses, the cache, the addresses being resolved, and the timer set
type ArpState is Data:
  ArpState{opts: ArpOptions, mac: E.MacAddr, ip: U32, cache: List<&2, ArpEntry>, waits: List<&2, ArpWait>, timer: Maybe<&2, U32>}

type ArpEvent is Data:
  ArpRecv{packet: B.Octets}
  ArpSend{ip: U32, packet: B.Octets}
  ArpFire{}

type ArpAction is Data:
  ArpFrame{dst: E.MacAddr, ethertype: U32, payload: B.Octets}
  ArpSetTimer{at: U32}
  ArpStopTimer{}
  # ip did not resolve; these packets for it are dropped
  ArpUnreachable{ip: U32, packets: List<&2, B.Octets>}

def ArpState.new(opts: ArpOptions, mac: E.MacAddr, ip: U32) -> ArpState:
  ArpState{opts, mac, ip, Nil{}, Nil{}, None{}}

def Arp.pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# The cache

# whether the first entry of xs is a live entry for ip
def ArpCache.head(xs: List<&2, ArpEntry>, +ip: U32, +now: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{ArpEntry{a, m, x}, t}:
      Bool.and(U32.is_eq(ip, a), S.SeqNum.lt(now, x))

# hit is ArpCache.head(xs, ip, now)
def ArpCache.find(xs: List<&2, ArpEntry>, +ip: U32, +now: U32, hit: Bool) -> Maybe<&2, E.MacAddr>:
  match xs:
    case Nil{}:
      None{}
    case Con{ArpEntry{a, m, x}, +t}:
      match hit:
        case True{}:
          Some{m}
        case False{}:
          ArpCache.find(t, ip, now, ArpCache.head(t, ip, now))

# the hardware address of ip, if learned and not expired at now
def ArpCache.lookup(+xs: List<&2, ArpEntry>, +ip: U32, +now: U32) -> Maybe<&2, E.MacAddr>:
  ArpCache.find(xs, ip, now, ArpCache.head(xs, ip, now))

def ArpCache.is(xs: List<&2, ArpEntry>, +ip: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{ArpEntry{a, m, x}, t}:
      U32.is_eq(ip, a)

# xs without the entries for ip; hit is ArpCache.is(xs, ip)
def ArpCache.drop(xs: List<&2, ArpEntry>, +ip: U32, hit: Bool) -> List<&2, ArpEntry>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, +t}:
      match hit:
        case True{}:
          ArpCache.drop(t, ip, ArpCache.is(t, ip))
        case False{}:
          Con{h, ArpCache.drop(t, ip, ArpCache.is(t, ip))}

def ArpCache.take(n: Nat, xs: List<&2, ArpEntry>) -> List<&2, ArpEntry>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, ArpCache.take(m, t)}

# the cache with ip at mac until exp, first; at most max entries (the oldest
# fall off)
def ArpCache.put(+xs: List<&2, ArpEntry>, +ip: U32, mac: E.MacAddr, exp: U32, max: Nat) -> List<&2, ArpEntry>:
  ArpCache.take(max, Con{ArpEntry{ip, mac, exp}, ArpCache.drop(xs, ip, ArpCache.is(xs, ip))})

def ArpCache.has(xs: List<&2, ArpEntry>, +ip: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{ArpEntry{a, m, x}, t}:
      Bool.or(U32.is_eq(ip, a), ArpCache.has(t, ip))

# Packets

def Arp.request(+st: ArpState, +ip: U32) -> ArpAction:
  match st:
    case ArpState{o, mac, me, c, w, t}:
      ArpFrame{E.MacAddr.broadcast(), E.EthHeader.TYPE_ARP(), NA.ArpPacket.build(NA.ArpPacket{NA.ArpPacket.REQUEST(), mac, me, E.MacAddr{0, 0, 0, 0, 0, 0}, ip})}

def Arp.frames(+mac: E.MacAddr, xs: List<&2, B.Octets>, acc: List<&2, ArpAction>) -> List<&2, ArpAction>:
  match xs:
    case Nil{}:
      acc
    case Con{p, t}:
      Arp.frames(mac, t, Con{ArpFrame{mac, E.EthHeader.TYPE_IPV4(), p}, acc})

def ArpWait.ip(w: ArpWait) -> U32:
  match w:
    case ArpWait{ip, p, n, x}:
      ip

def ArpWait.is(ws: List<&2, ArpWait>, +ip: U32) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{ArpWait{a, ps, n, x}, t}:
      U32.is_eq(a, ip)

# what resolving one address does to the waits: those left, and the packets
# released (oldest first)
type ArpRelease is Data:
  ArpRelease{waits: List<&2, ArpWait>, packets: List<&2, B.Octets>}

def Arp.release.add(ps: List<&2, B.Octets>, r: ArpRelease) -> ArpRelease:
  match r:
    case ArpRelease{w, q}:
      ArpRelease{w, List.append(&2, B.Octets, ps, q)}

def Arp.release.keep(x: ArpWait, r: ArpRelease) -> ArpRelease:
  match r:
    case ArpRelease{w, q}:
      ArpRelease{Con{x, w}, q}

# the waits for ip leave, their packets released; hit is ArpWait.is(ws, ip)
def Arp.release(ws: List<&2, ArpWait>, +ip: U32, hit: Bool) -> ArpRelease:
  match ws:
    case Nil{}:
      ArpRelease{Nil{}, Nil{}}
    case Con{ArpWait{a, ps, n, x}, +t}:
      match hit:
        case True{}:
          Arp.release.add(ps, Arp.release(t, ip, ArpWait.is(t, ip)))
        case False{}:
          Arp.release.keep(ArpWait{a, ps, n, x}, Arp.release(t, ip, ArpWait.is(t, ip)))

def Arp.earliest.min(m: Maybe<&2, U32>, +x: U32) -> U32:
  match m:
    case None{}:
      x
    case Some{+y}:
      S.SeqNum.min(x, y)

# The earliest request due, for the timer
def Arp.earliest(ws: List<&2, ArpWait>, acc: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ws:
    case Nil{}:
      acc
    case Con{ArpWait{a, ps, n, +x}, t}:
      Arp.earliest(t, Some{Arp.earliest.min(acc, x)})

# the actions with the timer moved from old to the earliest request due
def Arp.timer(old: Maybe<&2, U32>, new: Maybe<&2, U32>, +acts: List<&2, ArpAction>) -> List<&2, ArpAction>:
  match old new:
    case None{} None{}:
      acts
    case Some{a} None{}:
      List.append(&2, ArpAction, acts, [ArpStopTimer{}])
    case None{} Some{b}:
      List.append(&2, ArpAction, acts, [ArpSetTimer{b}])
    case Some{a} Some{+b}:
      Arp.pick(List<&2, ArpAction>, U32.is_eq(a, b), acts, List.append(&2, ArpAction, acts, [ArpSetTimer{b}]))

def Arp.done(st: ArpState, acts: List<&2, ArpAction>) -> Pair(ArpState, List<&2, ArpAction>):
  match st:
    case ArpState{o, mac, me, c, +w, t}:
      +next = Arp.earliest(w, None{})
      (ArpState{o, mac, me, c, w, next}, Arp.timer(t, next, acts))

# Receiving (RFC 826, "Packet Reception")

def ArpOptions.ttl(o: ArpOptions) -> U32:
  match o:
    case ArpOptions{ttl, r, n, q, e}:
      ttl

def ArpOptions.entries(o: ArpOptions) -> Nat:
  match o:
    case ArpOptions{ttl, r, n, q, e}:
      U32.to_nat(e)

# Merge: the sender's address is updated if cached; added if we are the
# target; then a request for us is answered, and packets waiting for the
# sender go out
def Arp.recv.out(st: ArpState, rel: ArpRelease, +sha: E.MacAddr, acts: List<&2, ArpAction>) -> Pair(ArpState, List<&2, ArpAction>):
  match st rel:
    case ArpState{o, mac, me, c, w0, t} ArpRelease{w, ps}:
      Arp.done(ArpState{o, mac, me, c, w, t}, List.reverse(&2, ArpAction, Arp.frames(sha, ps, List.reverse(&2, ArpAction, acts))))

def Arp.recv.go(+st: ArpState, p: NA.ArpPacket, +now: U32) -> Pair(ArpState, List<&2, ArpAction>):
  match st p:
    case ArpState{+o, +mac, +me, +c, w, t} NA.ArpPacket{+oper, +sha, +spa, tha, +tpa}:
      +for_me = U32.is_eq(tpa, me)
      +learn = Bool.and(Bool.not(U32.is_eq(spa, 0)), Bool.or(ArpCache.has(c, spa), for_me))
      +c2 = Arp.pick(List<&2, ArpEntry>, learn, ArpCache.put(c, spa, sha, U32.add(now, ArpOptions.ttl(o)), ArpOptions.entries(o)), c)
      +rel = Arp.pick(ArpRelease, learn, Arp.release(w, spa, ArpWait.is(w, spa)), ArpRelease{w, Nil{}})
      +reply = Bool.and(for_me, U32.is_eq(oper, NA.ArpPacket.REQUEST()))
      +ans = {ArpFrame{sha, E.EthHeader.TYPE_ARP(), NA.ArpPacket.build(NA.ArpPacket{NA.ArpPacket.REPLY(), mac, me, sha, spa})} : ArpAction}
      Arp.recv.out(ArpState{o, mac, me, c2, Nil{}, t}, rel, sha, Arp.pick(List<&2, ArpAction>, reply, [ans], Nil{}))

def Arp.recv(+st: ArpState, r: Result<&2, &2, N.NetError, NA.ArpPacket>, +now: U32) -> Pair(ArpState, List<&2, ArpAction>):
  match r:
    case Done{pk}:
      Arp.recv.go(st, pk, now)
    case Fail{e}:
      (st, Nil{})

# Sending: a packet for a next-hop address goes out if it is cached, and
# waits for a request's answer otherwise

def ArpOptions.queue(o: ArpOptions) -> Nat:
  match o:
    case ArpOptions{ttl, r, n, q, e}:
      U32.to_nat(q)

def ArpOptions.retry(o: ArpOptions) -> U32:
  match o:
    case ArpOptions{ttl, r, n, q, e}:
      r

def ArpOptions.tries(o: ArpOptions) -> U32:
  match o:
    case ArpOptions{ttl, r, n, q, e}:
      n

# the packets, at most max, the oldest dropped first
def Arp.cap(+ps: List<&2, B.Octets>, +max: Nat) -> List<&2, B.Octets>:
  List.drop(&2, B.Octets, ps, Nat.sub(List.length(&2, B.Octets, ps), max))

# packet joins the wait for ip; hit is ArpWait.is(ws, ip)
def Arp.enqueue(ws: List<&2, ArpWait>, +ip: U32, +packet: B.Octets, +max: Nat, hit: Bool) -> List<&2, ArpWait>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{ArpWait{a, ps, n, x}, +t}:
      match hit:
        case True{}:
          Con{ArpWait{a, Arp.cap(List.append(&2, B.Octets, ps, [packet]), max), n, x}, t}
        case False{}:
          Con{ArpWait{a, ps, n, x}, Arp.enqueue(t, ip, packet, max, ArpWait.is(t, ip))}

def Arp.wait(waiting: Bool, +st: ArpState, +ip: U32, +packet: B.Octets, +now: U32) -> Pair(ArpState, List<&2, ArpAction>):
  match waiting:
    case True{}:
      match st:
        case ArpState{+o, mac, me, c, w, t}:
          Arp.done(ArpState{o, mac, me, c, Arp.enqueue(w, ip, packet, ArpOptions.queue(o), True{}), t}, Nil{})
    case False{}:
      match st:
        case ArpState{+o, mac, me, c, w, t}:
          +w2 = {Con{ArpWait{ip, [packet], 1, U32.add(now, ArpOptions.retry(o))}, w} : List<&2, ArpWait>}
          Arp.done(ArpState{o, mac, me, c, w2, t}, [Arp.request(st, ip)])

def Arp.send.go(m: Maybe<&2, E.MacAddr>, +st: ArpState, +ip: U32, +packet: B.Octets, +now: U32) -> Pair(ArpState, List<&2, ArpAction>):
  match m:
    case Some{mac}:
      (st, [ArpFrame{mac, E.EthHeader.TYPE_IPV4(), packet}])
    case None{}:
      match st:
        case ArpState{o, mac, me, c, +w, t}:
          Arp.wait(ArpWait.is(w, ip), st, ip, packet, now)

def Arp.send(+st: ArpState, +ip: U32, +packet: B.Octets, +now: U32) -> Pair(ArpState, List<&2, ArpAction>):
  match st:
    case ArpState{o, mac, me, +c, w, t}:
      Arp.send.go(Arp.pick(Maybe<&2, E.MacAddr>, U32.is_eq(ip, 4294967295), Some{E.MacAddr.broadcast()}, ArpCache.lookup(c, ip, now)), st, ip, packet, now)

# The timer: requests due go out again, or give up after tries

def Arp.fire.one(due: Bool, out: Bool, +st: ArpState, w: ArpWait, +now: U32, acc: Pair(List<&2, ArpWait>, List<&2, ArpAction>)) -> Pair(List<&2, ArpWait>, List<&2, ArpAction>):
  match due:
    case False{}:
      match acc:
        case (ws, acts):
          (Con{w, ws}, acts)
    case True{}:
      match out:
        case True{}:
          match w:
            case ArpWait{a, ps, n, x}:
              match acc:
                case (ws, acts):
                  (ws, Con{ArpUnreachable{a, ps}, acts})
        case False{}:
          match st w:
            case ArpState{o, mac, me, c, w0, t} ArpWait{+a, ps, n, x}:
              match acc:
                case (ws, acts):
                  (Con{ArpWait{a, ps, U32.add(n, 1), U32.add(now, ArpOptions.retry(o))}, ws}, Con{Arp.request(st, a), acts})

def Arp.fire.go(ws: List<&2, ArpWait>, +st: ArpState, +now: U32, acc: Pair(List<&2, ArpWait>, List<&2, ArpAction>)) -> Pair(List<&2, ArpWait>, List<&2, ArpAction>):
  match ws:
    case Nil{}:
      acc
    case Con{ArpWait{a, ps, +n, +x}, t}:
      match st:
        case ArpState{+o, mac, me, c, w0, tm}:
          Arp.fire.go(t, st, now, Arp.fire.one(S.SeqNum.reached(now, x), U32.is_ge(n, ArpOptions.tries(o)), st, ArpWait{a, ps, n, x}, now, acc))

def Arp.fire.out(st: ArpState, r: Pair(List<&2, ArpWait>, List<&2, ArpAction>)) -> Pair(ArpState, List<&2, ArpAction>):
  match st:
    case ArpState{o, mac, me, c, w, t}:
      match r:
        case (ws, acts):
          Arp.done(ArpState{o, mac, me, c, List.reverse(&2, ArpWait, ws), t}, List.reverse(&2, ArpAction, acts))

def Arp.fire(+st: ArpState, +now: U32) -> Pair(ArpState, List<&2, ArpAction>):
  match st:
    case ArpState{o, mac, me, c, w, t}:
      Arp.fire.out(st, Arp.fire.go(w, st, now, (Nil{}, Nil{})))

# One event at time now
def Arp.step(+st: ArpState, ev: ArpEvent, +now: U32) -> Pair(ArpState, List<&2, ArpAction>):
  match ev:
    case ArpRecv{packet}:
      Arp.recv(st, NA.ArpPacket.parse(packet), now)
    case ArpSend{ip, packet}:
      Arp.send(st, ip, packet, now)
    case ArpFire{}:
      Arp.fire(st, now)
