# IPv4 (RFC 791): input, with fragment reassembly; output, with
# fragmentation and the choice of next hop. Headers are parsed and built by
# bend-osdev-netheaders.
#
#   Ipv4.step(st, event, now) -> (st, actions)
#
# Events: a packet arrives; the transport layer sends a payload; the timer
# fires. Actions: a payload delivered to its protocol (with the header and
# the first 8 bytes of payload, which an ICMP error quotes), a packet to send
# to a next hop, and the reassembly timer to set or stop.
#
# Reassembly holds at most reasm_max datagrams, each at most 65515 bytes of
# payload in at most reasm_pieces pieces out of order, for reasm_timeout ms
# (RFC 791 section 3.2 suggests 15 seconds); anything past a limit is
# dropped. Options are passed over, not interpreted; nothing is forwarded.
import Base
import ../bytes/bytes.bend as B
import ../netheaders/netheaders.bend as N
import ../netheaders/ipv4.bend as I4
import ./seq.bend as S
import ./rcvq.bend as Q

type Ipv4Options is Data:
  Ipv4Options{mtu: U32, ttl: U32, reasm_timeout: U32, reasm_max: U32, reasm_pieces: U32}

def Ipv4Options.default() -> Ipv4Options:
  Ipv4Options{1500, 64, 15000, 8, 64}

# our address, the netmask, and the gateway for addresses off the link
type Ipv4Config is Data:
  Ipv4Config{addr: U32, mask: U32, gateway: U32}

# a datagram being reassembled: its identity (RFC 791: source, destination,
# protocol, identification), the queue of pieces, the bytes assembled so far,
# its length once the last fragment is in, the first fragment's header and 8
# bytes, and when it is given up
type Ipv4Reasm is Data:
  Ipv4Reasm{src: U32, dst: U32, proto: U32, ident: U32, q: Q.RcvQ, data: B.Octets, total: Maybe<&2, Nat>, head: B.Octets, expires: U32}

type Ipv4State is Data:
  Ipv4State{cfg: Ipv4Config, opts: Ipv4Options, ident: U32, reasm: List<&2, Ipv4Reasm>, timer: Maybe<&2, U32>}

type Ipv4Event is Data:
  Ipv4Recv{packet: B.Octets}
  Ipv4Send{dst: U32, proto: U32, payload: B.Octets}
  Ipv4Fire{}

type Ipv4Action is Data:
  Ipv4Deliver{src: U32, dst: U32, proto: U32, payload: B.Octets, head: B.Octets}
  Ipv4Out{hop: U32, packet: B.Octets}
  Ipv4SetTimer{at: U32}
  Ipv4StopTimer{}

def Ipv4Config.addr(c: Ipv4Config) -> U32:
  match c:
    case Ipv4Config{a, m, g}:
      a

def Ipv4State.new(cfg: Ipv4Config, opts: Ipv4Options) -> Ipv4State:
  Ipv4State{cfg, opts, 1, Nil{}, None{}}

def Ipv4.pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# whether dst is ours: our address, the limited broadcast, or the broadcast
# of our subnet
def Ipv4.ours(+cfg: Ipv4Config, +dst: U32) -> Bool:
  match cfg:
    case Ipv4Config{+addr, +mask, gw}:
      Bool.or(U32.is_eq(dst, addr), Bool.or(U32.is_eq(dst, 4294967295), U32.is_eq(dst, U32.or(addr, U32.not(mask)))))

# the next hop for dst: dst itself on the link (or a broadcast), else the
# gateway
def Ipv4.hop(+cfg: Ipv4Config, +dst: U32) -> U32:
  match cfg:
    case Ipv4Config{+addr, +mask, gw}:
      Ipv4.pick(U32, Bool.or(U32.is_eq(dst, 4294967295), U32.is_eq(U32.and(dst, mask), U32.and(addr, mask))), dst, gw)

# Output

# one packet: header (IHL 5, no options) and checksum, then the payload
def Ipv4.packet(+o: Ipv4Options, +cfg: Ipv4Config, +ident: U32, +dst: U32, +proto: U32, +mf: Bool, +off: Nat, +piece: B.Octets) -> B.Octets:
  match o cfg:
    case Ipv4Options{m, ttl, rt, rm, rp} Ipv4Config{addr, mask, gw}:
      +len = U32.add(20, U32.from_nat(B.Octets.len(piece)))
      +h = {I4.Ipv4Header{4, 5, 0, 0, len, ident, Bool.to_u32(mf), U32.from_nat(Nat.div(off, 8n)), ttl, proto, 0, addr, dst, B.Octets.empty()} : I4.Ipv4Header}
      B.Octets.append(I4.Ipv4Header.build_checksum(h), piece)

# the fragments of payload from offset off, chunk bytes each (a multiple of
# 8), oldest first onto acc
def Ipv4.fragments(fuel: Nat, +o: Ipv4Options, +cfg: Ipv4Config, +ident: U32, +dst: U32, +proto: U32, +chunk: Nat, +off: Nat, +payload: B.Octets, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      +rest = Nat.sub(B.Octets.len(payload), off)
      +last = Nat.is_le(rest, chunk)
      +p = Ipv4.packet(o, cfg, ident, dst, proto, Bool.not(last), off, B.Octets.slice(off, chunk, payload))
      Ipv4.fragments(f, o, cfg, ident, dst, proto, chunk, Nat.add(off, chunk), payload, List.append(&2, B.Octets, acc, [p]))

def Ipv4.outs(+hop: U32, ps: List<&2, B.Octets>) -> List<&2, Ipv4Action>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{Ipv4Out{hop, p}, Ipv4.outs(hop, t)}

def Ipv4Options.mtu(o: Ipv4Options) -> U32:
  match o:
    case Ipv4Options{m, ttl, rt, rm, rp}:
      m

# send payload to dst as protocol proto: one packet if it fits the MTU, else
# fragments of (MTU - 20) rounded down to 8 bytes; a payload over 65515
# bytes cannot be sent
def Ipv4.send(+st: Ipv4State, +dst: U32, +proto: U32, +payload: B.Octets) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match st:
    case Ipv4State{+cfg, +o, +ident, r, t}:
      +len = B.Octets.len(payload)
      +chunk = Nat.mul(8n, Nat.div(Nat.sub(U32.to_nat(Ipv4Options.mtu(o)), 20n), 8n))
      +pieces = Nat.div(Nat.add(len, Nat.sub(chunk, 1n)), chunk)
      +ok = Bool.and(Nat.is_le(len, 65515n), Nat.is_gt(chunk, 0n))
      +ps = Ipv4.fragments(Ipv4.pick(Nat, ok, Nat.max(pieces, 1n), 0n), o, cfg, ident, dst, proto, chunk, 0n, payload, Nil{})
      (Ipv4State{cfg, o, U32.add(ident, 1), r, t}, Ipv4.outs(Ipv4.hop(cfg, dst), ps))

# Reassembly

# the datagrams being reassembled, and what a step delivers
type Ipv4Res is Data:
  Ipv4Res{reasm: List<&2, Ipv4Reasm>, acts: List<&2, Ipv4Action>}

def Ipv4.earliest.min(m: Maybe<&2, U32>, +x: U32) -> U32:
  match m:
    case None{}:
      x
    case Some{+y}:
      S.SeqNum.min(x, y)

def Ipv4.earliest(rs: List<&2, Ipv4Reasm>, acc: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match rs:
    case Nil{}:
      acc
    case Con{Ipv4Reasm{s, d, p, i, q, data, tot, head, +x}, t}:
      Ipv4.earliest(t, Some{Ipv4.earliest.min(acc, x)})

def Ipv4.timer(old: Maybe<&2, U32>, new: Maybe<&2, U32>, +acts: List<&2, Ipv4Action>) -> List<&2, Ipv4Action>:
  match old new:
    case None{} None{}:
      acts
    case Some{a} None{}:
      List.append(&2, Ipv4Action, acts, [Ipv4StopTimer{}])
    case None{} Some{b}:
      List.append(&2, Ipv4Action, acts, [Ipv4SetTimer{b}])
    case Some{a} Some{+b}:
      Ipv4.pick(List<&2, Ipv4Action>, U32.is_eq(a, b), acts, List.append(&2, Ipv4Action, acts, [Ipv4SetTimer{b}]))

# the state with its timer at the earliest datagram given up next
def Ipv4.done(st: Ipv4State, acts: List<&2, Ipv4Action>) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match st:
    case Ipv4State{cfg, o, id, +rs, t}:
      +next = Ipv4.earliest(rs, None{})
      (Ipv4State{cfg, o, id, rs, next}, Ipv4.timer(t, next, acts))

def Ipv4Reasm.is(rs: List<&2, Ipv4Reasm>, +src: U32, +dst: U32, +proto: U32, +ident: U32) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{Ipv4Reasm{s, d, p, i, q, data, tot, head, x}, t}:
      Bool.and(Bool.and(U32.is_eq(s, src), U32.is_eq(d, dst)), Bool.and(U32.is_eq(p, proto), U32.is_eq(i, ident)))

# the datagram (src, dst, proto, ident) taken out of the list, if there
type Ipv4Taken is Data:
  Ipv4Taken{found: Maybe<&2, Ipv4Reasm>, rest: List<&2, Ipv4Reasm>}

def Ipv4.taken.keep(h: Ipv4Reasm, r: Ipv4Taken) -> Ipv4Taken:
  match r:
    case Ipv4Taken{f, rest}:
      Ipv4Taken{f, Con{h, rest}}

def Ipv4.take(rs: List<&2, Ipv4Reasm>, +src: U32, +dst: U32, +proto: U32, +ident: U32, hit: Bool) -> Ipv4Taken:
  match rs:
    case Nil{}:
      Ipv4Taken{None{}, Nil{}}
    case Con{h, +t}:
      match hit:
        case True{}:
          Ipv4Taken{Some{h}, t}
        case False{}:
          Ipv4.taken.keep(h, Ipv4.take(t, src, dst, proto, ident, Ipv4Reasm.is(t, src, dst, proto, ident)))

# one piece into a datagram: at offset off; mf, more fragments follow it
def Ipv4.piece(+limit: Nat, r: Ipv4Reasm, +off: Nat, +mf: Bool, +data: B.Octets, +head: B.Octets) -> Ipv4Reasm:
  match r:
    case Ipv4Reasm{s, d, p, i, +q, +got, tot, h0, x}:
      +n = Q.RcvQ.next(q)
      +early = Nat.is_lt(off, n)
      +d2 = Ipv4.pick(B.Octets, early, B.Octets.drop(Nat.sub(n, off), data), data)
      +rel = Ipv4.pick(Nat, early, 0n, Nat.sub(off, n))
      +out = Q.RcvQ.insert(limit, q, rel, d2)
      +tot2 = Ipv4.pick(Maybe<&2, Nat>, mf, tot, Some{Nat.add(off, B.Octets.len(data))})
      +h2 = Ipv4.pick(B.Octets, Nat.is_eq(off, 0n), head, h0)
      Ipv4Reasm{s, d, p, i, Q.RcvOut.queue(out), B.Octets.append(got, Q.RcvOut.data(out)), tot2, h2, x}

def Ipv4Reasm.complete(r: Ipv4Reasm) -> Bool:
  match r:
    case Ipv4Reasm{s, d, p, i, q, data, tot, head, x}:
      match tot:
        case None{}:
          False{}
        case Some{n}:
          Nat.is_eq(Q.RcvQ.next(q), n)

def Ipv4.reasm.done(complete: Bool, +r: Ipv4Reasm, rest: List<&2, Ipv4Reasm>) -> Ipv4Res:
  match complete:
    case False{}:
      Ipv4Res{Con{r, rest}, Nil{}}
    case True{}:
      match r:
        case Ipv4Reasm{s, d, p, i, q, data, tot, head, x}:
          Ipv4Res{rest, [Ipv4Deliver{s, d, p, data, head}]}

def Ipv4Options.pieces(o: Ipv4Options) -> Nat:
  match o:
    case Ipv4Options{m, ttl, rt, rm, rp}:
      U32.to_nat(rp)

def Ipv4Options.timeout(o: Ipv4Options) -> U32:
  match o:
    case Ipv4Options{m, ttl, rt, rm, rp}:
      rt

def Ipv4.reasm.found(m: Maybe<&2, Ipv4Reasm>, room: Bool, +o: Ipv4Options, +now: U32, +src: U32, +dst: U32, +proto: U32, +ident: U32, +off: Nat, +mf: Bool, +data: B.Octets, +head: B.Octets, rest: List<&2, Ipv4Reasm>) -> Ipv4Res:
  match m:
    case Some{r}:
      +r2 = Ipv4.piece(Ipv4Options.pieces(o), r, off, mf, data, head)
      Ipv4.reasm.done(Ipv4Reasm.complete(r2), r2, rest)
    case None{}:
      match room:
        case False{}:
          Ipv4Res{rest, Nil{}}
        case True{}:
          +r0 = {Ipv4Reasm{src, dst, proto, ident, Q.RcvQ.new(), B.Octets.empty(), None{}, B.Octets.empty(), U32.add(now, Ipv4Options.timeout(o))} : Ipv4Reasm}
          +r2 = Ipv4.piece(Ipv4Options.pieces(o), r0, off, mf, data, head)
          Ipv4.reasm.done(Ipv4Reasm.complete(r2), r2, rest)

def Ipv4Options.reasm_max(o: Ipv4Options) -> Nat:
  match o:
    case Ipv4Options{m, ttl, rt, rm, rp}:
      U32.to_nat(rm)

def Ipv4.taken(+o: Ipv4Options, +now: U32, +src: U32, +dst: U32, +proto: U32, +ident: U32, +off: Nat, +mf: Bool, +data: B.Octets, +head: B.Octets, +count: Nat, tk: Ipv4Taken) -> Ipv4Res:
  match tk:
    case Ipv4Taken{m, rest}:
      Ipv4.reasm.found(m, Nat.is_lt(count, Ipv4Options.reasm_max(o)), o, now, src, dst, proto, ident, off, mf, data, head, rest)

def Ipv4.fragment.out(cfg: Ipv4Config, o: Ipv4Options, id: U32, t: Maybe<&2, U32>, r: Ipv4Res) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match r:
    case Ipv4Res{rs, acts}:
      Ipv4.done(Ipv4State{cfg, o, id, rs, t}, acts)

# Input

# a fragment: into its datagram's reassembly, which is delivered once whole
def Ipv4.fragment(+st: Ipv4State, h: I4.Ipv4Header, +payload: B.Octets, +head: B.Octets, +now: U32) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match st h:
    case Ipv4State{cfg, +o, id, +rs, t} I4.Ipv4Header{v, ihl, dscp, ecn, tl, +ident, +fl, +fo, ttl, +proto, ck, +src, +dst, opts}:
      +off = Nat.mul(8n, U32.to_nat(fo))
      +fits = Nat.is_le(Nat.add(off, B.Octets.len(payload)), 65515n)
      +tk = Ipv4.pick(Ipv4Taken, fits, Ipv4.take(rs, src, dst, proto, ident, Ipv4Reasm.is(rs, src, dst, proto, ident)), Ipv4Taken{None{}, rs})
      +cnt = List.length(&2, Ipv4Reasm, rs)
      +r = Ipv4.pick(Ipv4Res, fits, Ipv4.taken(o, now, src, dst, proto, ident, off, U32.is_ne(U32.and(fl, 1), 0), payload, head, cnt, tk), Ipv4Res{rs, Nil{}})
      Ipv4.fragment.out(cfg, o, id, t, r)

def Ipv4.head(+h: I4.Ipv4Header, +packet: B.Octets) -> B.Octets:
  B.Octets.take(Nat.add(I4.Ipv4Header.length(h), 8n), packet)

def Ipv4Header.whole(h: I4.Ipv4Header) -> Bool:
  match h:
    case I4.Ipv4Header{v, ihl, dscp, ecn, tl, ident, +fl, +fo, ttl, proto, ck, src, dst, opts}:
      Bool.and(U32.is_eq(U32.and(fl, 1), 0), U32.is_eq(fo, 0))

def Ipv4Header.dst(h: I4.Ipv4Header) -> U32:
  match h:
    case I4.Ipv4Header{v, ihl, dscp, ecn, tl, ident, fl, fo, ttl, proto, ck, src, dst, opts}:
      dst

def Ipv4.deliver(+h: I4.Ipv4Header, payload: B.Octets, head: B.Octets) -> Ipv4Action:
  match h:
    case I4.Ipv4Header{v, ihl, dscp, ecn, tl, ident, fl, fo, ttl, proto, ck, src, dst, opts}:
      Ipv4Deliver{src, dst, proto, payload, head}

def Ipv4.accept(ours: Bool, whole: Bool, +st: Ipv4State, +h: I4.Ipv4Header, +payload: B.Octets, +head: B.Octets, +now: U32) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match ours:
    case False{}:
      (st, Nil{})
    case True{}:
      match whole:
        case True{}:
          (st, [Ipv4.deliver(h, payload, head)])
        case False{}:
          Ipv4.fragment(st, h, payload, head, now)

def Ipv4.recv.payload(r: Result<&2, &2, N.NetError, B.Octets>, +st: Ipv4State, +h: I4.Ipv4Header, +packet: B.Octets, +now: U32) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match r:
    case Fail{e}:
      (st, Nil{})
    case Done{pl}:
      match st:
        case Ipv4State{+cfg, o, id, rs, t}:
          Ipv4.accept(Ipv4.ours(cfg, Ipv4Header.dst(h)), Ipv4Header.whole(h), st, h, pl, Ipv4.head(h, packet), now)

def Ipv4.recv.header(r: Result<&2, &2, N.NetError, I4.Ipv4Header>, +st: Ipv4State, +packet: B.Octets, +now: U32) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match r:
    case Fail{e}:
      (st, Nil{})
    case Done{+h}:
      Ipv4.recv.payload(I4.Ipv4Header.payload(h, packet), st, h, packet, now)

# a packet arrives: its header must parse with a good checksum, its total
# length fit, and its destination be ours
def Ipv4.recv(+st: Ipv4State, +packet: B.Octets, +now: U32) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  Ipv4.recv.header(I4.Ipv4Header.parse_verified(packet), st, packet, now)

# The timer: datagrams past their time are given up

def Ipv4.expire(rs: List<&2, Ipv4Reasm>, +now: U32) -> List<&2, Ipv4Reasm>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Ipv4Reasm{s, d, p, i, q, data, tot, head, +x}, +t}:
      Ipv4.pick(List<&2, Ipv4Reasm>, S.SeqNum.reached(now, x), Ipv4.expire(t, now), Con{Ipv4Reasm{s, d, p, i, q, data, tot, head, x}, Ipv4.expire(t, now)})

def Ipv4.fire(st: Ipv4State, +now: U32) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match st:
    case Ipv4State{cfg, o, id, rs, t}:
      Ipv4.done(Ipv4State{cfg, o, id, Ipv4.expire(rs, now), t}, Nil{})

# One event at time now
def Ipv4.step(+st: Ipv4State, ev: Ipv4Event, +now: U32) -> Pair(Ipv4State, List<&2, Ipv4Action>):
  match ev:
    case Ipv4Recv{packet}:
      Ipv4.recv(st, packet, now)
    case Ipv4Send{dst, proto, payload}:
      Ipv4.send(st, dst, proto, payload)
    case Ipv4Fire{}:
      Ipv4.fire(st, now)
