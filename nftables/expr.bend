# bend-osdev-nftables: packets, expressions and rules (nft(8), "PAYLOAD
# EXPRESSION", "RAW PAYLOAD EXPRESSION", "META EXPRESSIONS", "CONNTRACK
# EXPRESSIONS", "COUNTER STATEMENT", "LIMIT STATEMENT", "META STATEMENT").
#
# A packet is its parsed headers (bend-osdev-netheaders), the bytes after
# them, its meta data and its conntrack state. A rule is a list of
# expressions run in order: a match that fails ends the rule (the next rule
# runs), a statement acts, and a verdict ends the rule with that verdict.
#
# Values are byte strings in network byte order. A payload expression loads
# len bytes from offset bytes into a base: the link layer header (ll), the
# network header (nh) or the transport header (th), each followed by the
# rest of the packet, as nft's raw payload expression @base,offset,length
# does; a load past the packet's end, or from a header the packet does not
# have, fails, and the rule does not match. A field narrower than a byte is
# a payload load and a bitwise mask.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../netheaders/netheaders.bend as N
import ../netheaders/ethernet.bend as E
import ../netheaders/arp.bend as A
import ../netheaders/ipv4.bend as I4
import ../netheaders/ipv6.bend as I6
import ../netheaders/icmp.bend as IC
import ../netheaders/udp.bend as U
import ../netheaders/tcp.bend as T
import ./family.bend as F
import ./verdict.bend as V
import ./sets.bend as S

# Packets

# meta data: input and output interface index, mark, transport protocol,
# length in bytes, protocol family (the NFPROTO_* number). Open type.
type NftMeta is Data:
  NftMeta{iif: U32, oif: U32, mark: U32, l4proto: U32, length: U32, nfproto: U32}

# conntrack: the state bits and the connection's mark. Open type.
type NftCt is Data:
  NftCt{state: U32, mark: U32}

# The conntrack state bits (nft(8), "CONNTRACK EXPRESSIONS": ct state)
def NftCt.INVALID() -> U32:
  1

def NftCt.ESTABLISHED() -> U32:
  2

def NftCt.RELATED() -> U32:
  4

def NftCt.NEW() -> U32:
  8

def NftCt.UNTRACKED() -> U32:
  64

type NftL2 is Data:
  NftL2None{}
  NftL2Eth{h: E.EthHeader}

type NftL3 is Data:
  NftL3None{}
  NftL3Ipv4{h: I4.Ipv4Header}
  NftL3Ipv6{h: I6.Ipv6Header}
  NftL3Arp{p: A.ArpPacket}

# the transport header: TCP, UDP, or ICMP / ICMPv6
type NftL4 is Data:
  NftL4None{}
  NftL4Tcp{h: T.TcpHeader}
  NftL4Udp{h: U.UdpHeader}
  NftL4Icmp{h: IC.IcmpHeader}

# Open type: meta, ct, the headers, and the bytes after the last header
type NftPacket is Data:
  NftPacket{meta: NftMeta, ct: NftCt, l2: NftL2, l3: NftL3, l4: NftL4, data: B.Octets}

def NftPacket.meta(p: NftPacket) -> NftMeta:
  match p:
    case NftPacket{m, c, l2, l3, l4, d}:
      m

def NftPacket.ct(p: NftPacket) -> NftCt:
  match p:
    case NftPacket{m, c, l2, l3, l4, d}:
      c

def NftPacket.length(p: NftPacket) -> U32:
  match p:
    case NftPacket{m, c, l2, l3, l4, d}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          len

def NftPacket.mark(p: NftPacket) -> U32:
  match p:
    case NftPacket{m, c, l2, l3, l4, d}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          mark

def NftPacket.ct_mark(p: NftPacket) -> U32:
  match p:
    case NftPacket{m, c, l2, l3, l4, d}:
      match c:
        case NftCt{s, mark}:
          mark

def NftPacket.set_mark(p: NftPacket, v: U32) -> NftPacket:
  match p:
    case NftPacket{m, c, l2, l3, l4, d}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          NftPacket{NftMeta{iif, oif, v, l4p, len, nfp}, c, l2, l3, l4, d}

def NftPacket.set_ct_mark(p: NftPacket, v: U32) -> NftPacket:
  match p:
    case NftPacket{m, c, l2, l3, l4, d}:
      match c:
        case NftCt{s, mark}:
          NftPacket{m, NftCt{s, v}, l2, l3, l4, d}

# Building a packet from its bytes, with the netheaders parsers

# the transport header and what follows it
type NftTail is Data:
  NftTail{l4: NftL4, data: B.Octets}

def NftTail.tcp(r: Result<&2, &2, N.NetError, T.TcpHeader>, +rest: B.Octets) -> NftTail:
  match r:
    case Done{+h}:
      NftTail{NftL4Tcp{h}, B.Octets.drop(T.TcpHeader.length(h), rest)}
    case Fail{e}:
      NftTail{NftL4None{}, rest}

def NftTail.udp(r: Result<&2, &2, N.NetError, U.UdpHeader>, +rest: B.Octets) -> NftTail:
  match r:
    case Done{+h}:
      NftTail{NftL4Udp{h}, B.Octets.drop(U.UdpHeader.header_length(h), rest)}
    case Fail{e}:
      NftTail{NftL4None{}, rest}

def NftTail.icmp(r: Result<&2, &2, N.NetError, IC.IcmpHeader>, +rest: B.Octets) -> NftTail:
  match r:
    case Done{+h}:
      NftTail{NftL4Icmp{h}, B.Octets.drop(IC.IcmpHeader.length(h), rest)}
    case Fail{e}:
      NftTail{NftL4None{}, rest}

def NftTail.go(tcp: Bool, udp: Bool, icmp: Bool, +rest: B.Octets) -> NftTail:
  match tcp:
    case True{}:
      NftTail.tcp(T.TcpHeader.parse(rest), rest)
    case False{}:
      match udp:
        case True{}:
          NftTail.udp(U.UdpHeader.parse(rest), rest)
        case False{}:
          match icmp:
            case True{}:
              NftTail.icmp(IC.IcmpHeader.parse(rest), rest)
            case False{}:
              NftTail{NftL4None{}, rest}

# the transport header of protocol proto (6 TCP, 17 UDP, 1 ICMP, 58 ICMPv6)
# at the start of rest; none if it does not parse
def NftTail.of(+proto: U32, +rest: B.Octets) -> NftTail:
  NftTail.go(U32.is_eq(proto, 6), U32.is_eq(proto, 17), Bool.or(U32.is_eq(proto, 1), U32.is_eq(proto, 58)), rest)

# the network layer and above
type NftUpper is Data:
  NftUpper{l3: NftL3, l4: NftL4, data: B.Octets, l4proto: U32}

def NftUpper.byte(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{b}:
      b
    case None{}:
      0

def NftUpper.mk(l3: NftL3, +p: U32, t: NftTail) -> Result<&2, &2, F.NftError, NftUpper>:
  match t:
    case NftTail{l4, d}:
      Done{NftUpper{l3, l4, d, p}}

def NftUpper.ip4(r: Result<&2, &2, N.NetError, I4.Ipv4Header>, +o: B.Octets) -> Result<&2, &2, F.NftError, NftUpper>:
  match r:
    case Done{+h}:
      +p = NftUpper.byte(B.Octets.at(o, 9n))
      NftUpper.mk(NftL3Ipv4{h}, p, NftTail.of(p, B.Octets.drop(I4.Ipv4Header.length(h), o)))
    case Fail{e}:
      Fail{F.NftErrBadPacket{}}

def NftUpper.ip6(r: Result<&2, &2, N.NetError, I6.Ipv6Header>, +o: B.Octets) -> Result<&2, &2, F.NftError, NftUpper>:
  match r:
    case Done{+h}:
      +p = NftUpper.byte(B.Octets.at(o, 6n))
      NftUpper.mk(NftL3Ipv6{h}, p, NftTail.of(p, B.Octets.drop(I6.Ipv6Header.length(h), o)))
    case Fail{e}:
      Fail{F.NftErrBadPacket{}}

def NftUpper.ip.pick(is4: Bool, is6: Bool, +o: B.Octets) -> Result<&2, &2, F.NftError, NftUpper>:
  match is4:
    case True{}:
      NftUpper.ip4(I4.Ipv4Header.parse(o), o)
    case False{}:
      match is6:
        case True{}:
          NftUpper.ip6(I6.Ipv6Header.parse(o), o)
        case False{}:
          Fail{F.NftErrBadPacket{}}

def NftUpper.ip.go(m: Maybe<&2, U32>, +o: B.Octets) -> Result<&2, &2, F.NftError, NftUpper>:
  match m:
    case Some{b}:
      +v = U32.shrn(b, 4n)
      NftUpper.ip.pick(U32.is_eq(v, 4), U32.is_eq(v, 6), o)
    case None{}:
      Fail{F.NftErrBadPacket{}}

# an IPv4 or IPv6 packet (by its version) and its transport header
def NftUpper.ip(+o: B.Octets) -> Result<&2, &2, F.NftError, NftUpper>:
  NftUpper.ip.go(B.Octets.at(o, 0n), o)

def NftUpper.arp(r: Result<&2, &2, N.NetError, A.ArpPacket>, +o: B.Octets) -> Result<&2, &2, F.NftError, NftUpper>:
  match r:
    case Done{+p}:
      Done{NftUpper{NftL3Arp{p}, NftL4None{}, B.Octets.drop(A.ArpPacket.length(p), o), 0}}
    case Fail{e}:
      Fail{F.NftErrBadPacket{}}

def NftUpper.eth.pick(ip: Bool, arp: Bool, +o: B.Octets) -> Result<&2, &2, F.NftError, NftUpper>:
  match ip:
    case True{}:
      NftUpper.ip(o)
    case False{}:
      match arp:
        case True{}:
          NftUpper.arp(A.ArpPacket.parse(o), o)
        case False{}:
          Done{NftUpper{NftL3None{}, NftL4None{}, o, 0}}

# what follows an Ethernet header of EtherType et
def NftUpper.eth(+et: U32, +o: B.Octets) -> Result<&2, &2, F.NftError, NftUpper>:
  NftUpper.eth.pick(Bool.or(U32.is_eq(et, E.EthHeader.TYPE_IPV4()), U32.is_eq(et, E.EthHeader.TYPE_IPV6())), U32.is_eq(et, E.EthHeader.TYPE_ARP()), o)

# the NFPROTO_* number of a network layer (0 for none)
def NftL3.nfproto(l: NftL3) -> U32:
  match l:
    case NftL3None{}:
      0
    case NftL3Ipv4{h}:
      2
    case NftL3Ipv6{h}:
      10
    case NftL3Arp{p}:
      3

def NftPacket.of_ip.go(r: Result<&2, &2, F.NftError, NftUpper>, iif: U32, oif: U32, mark: U32, ct: NftCt, len: U32) -> Result<&2, &2, F.NftError, NftPacket>:
  match r:
    case Done{u}:
      match u:
        case NftUpper{+l3, l4, d, p}:
          Done{NftPacket{NftMeta{iif, oif, mark, p, len, NftL3.nfproto(l3)}, ct, NftL2None{}, l3, l4, d}}
    case Fail{e}:
      Fail{e}

# the IPv4 or IPv6 packet o (network header first), received on iif, to
# leave by oif, with the mark and conntrack state given: meta l4proto is the
# IPv4 protocol or the IPv6 next header (extension headers are not walked),
# meta length is the length of o, meta nfproto 2 or 10. NftErrBadPacket if
# the network header does not parse; a transport header that does not parse
# is left out, its bytes kept as data.
def NftPacket.of_ip(iif: U32, oif: U32, mark: U32, ct: NftCt, +o: B.Octets) -> Result<&2, &2, F.NftError, NftPacket>:
  NftPacket.of_ip.go(NftUpper.ip(o), iif, oif, mark, ct, U32.from_nat(B.Octets.len(o)))

def NftPacket.of_eth.up(r: Result<&2, &2, F.NftError, NftUpper>, h: E.EthHeader, iif: U32, oif: U32, mark: U32, nfproto: U32, ct: NftCt, len: U32) -> Result<&2, &2, F.NftError, NftPacket>:
  match r:
    case Done{u}:
      match u:
        case NftUpper{l3, l4, d, p}:
          Done{NftPacket{NftMeta{iif, oif, mark, p, len, nfproto}, ct, NftL2Eth{h}, l3, l4, d}}
    case Fail{e}:
      Fail{e}

def NftPacket.of_eth.go(r: Result<&2, &2, N.NetError, E.EthHeader>, iif: U32, oif: U32, mark: U32, nfproto: U32, ct: NftCt, +o: B.Octets) -> Result<&2, &2, F.NftError, NftPacket>:
  match r:
    case Done{+h}:
      +el = E.EthHeader.length(h)
      NftPacket.of_eth.up(NftUpper.eth(NftUpper.byte(B.Octets.be16_at(o, Nat.sub(el, 2n))), B.Octets.drop(el, o)), h, iif, oif, mark, nfproto, ct, U32.from_nat(B.Octets.len(o)))
    case Fail{e}:
      Fail{F.NftErrBadPacket{}}

# the Ethernet frame o (with at most one 802.1Q tag), for the bridge and
# netdev families, whose meta nfproto is given (7 bridge, 5 netdev): IPv4,
# IPv6 and ARP are parsed after the Ethernet header, other EtherTypes left
# as data
def NftPacket.of_eth(iif: U32, oif: U32, mark: U32, nfproto: U32, ct: NftCt, +o: B.Octets) -> Result<&2, &2, F.NftError, NftPacket>:
  NftPacket.of_eth.go(E.EthHeader.parse(o), iif, oif, mark, nfproto, ct, o)

# The bytes of each payload base

def NftL4.bytes(l: NftL4) -> Maybe<&2, B.Octets>:
  match l:
    case NftL4None{}:
      None{}
    case NftL4Tcp{h}:
      Some{T.TcpHeader.build(h)}
    case NftL4Udp{h}:
      Some{U.UdpHeader.build(h)}
    case NftL4Icmp{h}:
      Some{IC.IcmpHeader.build(h)}

def NftL3.bytes(l: NftL3) -> Maybe<&2, B.Octets>:
  match l:
    case NftL3None{}:
      None{}
    case NftL3Ipv4{h}:
      Some{I4.Ipv4Header.build(h)}
    case NftL3Ipv6{h}:
      Some{I6.Ipv6Header.build(h)}
    case NftL3Arp{p}:
      Some{A.ArpPacket.build(p)}

def NftL2.bytes(l: NftL2) -> Maybe<&2, B.Octets>:
  match l:
    case NftL2None{}:
      None{}
    case NftL2Eth{h}:
      Some{E.EthHeader.build(h)}

def NftLayer.or_empty(m: Maybe<&2, B.Octets>) -> B.Octets:
  match m:
    case Some{o}:
      o
    case None{}:
      B.Octets.empty()

def NftLayer.on(m: Maybe<&2, B.Octets>, rest: B.Octets) -> Maybe<&2, B.Octets>:
  match m:
    case Some{o}:
      Some{B.Octets.append(o, rest)}
    case None{}:
      None{}

# A payload base
type NftPayloadBase is Data:
  NftBaseLl{}
  NftBaseNh{}
  NftBaseTh{}

# the bytes from the start of base b to the end of the packet
def NftPacket.base(b: NftPayloadBase, p: NftPacket) -> Maybe<&2, B.Octets>:
  match b:
    case NftBaseTh{}:
      match p:
        case NftPacket{m, c, l2, l3, l4, d}:
          NftLayer.on(NftL4.bytes(l4), d)
    case NftBaseNh{}:
      match p:
        case NftPacket{m, c, l2, l3, l4, d}:
          NftLayer.on(NftL3.bytes(l3), B.Octets.append(NftLayer.or_empty(NftL4.bytes(l4)), d))
    case NftBaseLl{}:
      match p:
        case NftPacket{m, c, l2, l3, l4, d}:
          NftLayer.on(NftL2.bytes(l2), B.Octets.append(NftLayer.or_empty(NftL3.bytes(l3)), B.Octets.append(NftLayer.or_empty(NftL4.bytes(l4)), d)))

def NftPayload.cut(ok: Bool, +off: Nat, +len: Nat, o: B.Octets) -> Maybe<&2, B.Octets>:
  match ok:
    case True{}:
      Some{B.Octets.slice(off, len, o)}
    case False{}:
      None{}

def NftPayload.slice(m: Maybe<&2, B.Octets>, +off: Nat, +len: Nat) -> Maybe<&2, B.Octets>:
  match m:
    case Some{+o}:
      NftPayload.cut(Nat.is_le(Nat.add(off, len), B.Octets.len(o)), off, len, o)
    case None{}:
      None{}

# Sources: what a match compares, a map looks up, a statement sets

type NftMetaKey is Data:
  NftMetaIif{}
  NftMetaOif{}
  NftMetaMark{}
  NftMetaL4proto{}
  NftMetaLength{}
  NftMetaNfproto{}

type NftCtKey is Data:
  NftCtState{}
  NftCtMark{}

# A set, inline (anonymous) or by its name in the table
type NftSetRef is Data:
  NftSetAnon{set: S.NftSet}
  NftSetNamed{name: String}

def NftSetRef.resolve(r: NftSetRef, +sets: List<&2, S.NftNamedSet>) -> Maybe<&2, S.NftSet>:
  match r:
    case NftSetAnon{s}:
      Some{s}
    case NftSetNamed{n}:
      S.NftNamedSet.find(sets, n)

type NftSrc is Data:
  # len bytes from offset in base
  NftSrcPayload{base: NftPayloadBase, offset: Nat, len: Nat}
  NftSrcMeta{key: NftMetaKey}
  NftSrcCt{key: NftCtKey}
  # a constant
  NftSrcImm{value: B.Octets}
  # (src & mask) ^ xor, byte by byte (missing mask bytes are 255, xor 0)
  NftSrcBitwise{src: NftSrc, mask: B.Octets, xor: B.Octets}
  # a . b
  NftSrcConcat{a: NftSrc, b: NftSrc}
  # the value a map holds for the key
  NftSrcMap{key: NftSrc, map: NftSetRef}

# the meta keys' values: iif, oif, mark and length as 32-bit numbers,
# l4proto and nfproto as one byte
def NftMeta.value(k: NftMetaKey, m: NftMeta) -> B.Octets:
  match k:
    case NftMetaIif{}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          B.Octets.of_list(B.be32(iif))
    case NftMetaOif{}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          B.Octets.of_list(B.be32(oif))
    case NftMetaMark{}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          B.Octets.of_list(B.be32(mark))
    case NftMetaL4proto{}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          B.Octets.of_list([B.byte(l4p)])
    case NftMetaLength{}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          B.Octets.of_list(B.be32(len))
    case NftMetaNfproto{}:
      match m:
        case NftMeta{iif, oif, mark, l4p, len, nfp}:
          B.Octets.of_list([B.byte(nfp)])

def NftCt.value(k: NftCtKey, c: NftCt) -> B.Octets:
  match k:
    case NftCtState{}:
      match c:
        case NftCt{s, mark}:
          B.Octets.of_list(B.be32(s))
    case NftCtMark{}:
      match c:
        case NftCt{s, mark}:
          B.Octets.of_list(B.be32(mark))

def NftValue.bitwise(v: List<&2, U32>, m: List<&2, U32>, x: List<&2, U32>) -> List<&2, U32>:
  match v:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      match m:
        case Nil{}:
          match x:
            case Nil{}:
              Con{b, NftValue.bitwise(t, Nil{}, Nil{})}
            case Con{xb, xt}:
              Con{U32.xor(b, U32.and(xb, 255)), NftValue.bitwise(t, Nil{}, xt)}
        case Con{mb, mt}:
          match x:
            case Nil{}:
              Con{U32.and(b, mb), NftValue.bitwise(t, mt, Nil{})}
            case Con{xb, xt}:
              Con{U32.xor(U32.and(b, mb), U32.and(xb, 255)), NftValue.bitwise(t, mt, xt)}

def NftValue.bitwise_m(r: Maybe<&2, B.Octets>, m: B.Octets, x: B.Octets) -> Maybe<&2, B.Octets>:
  match r:
    case Some{v}:
      Some{B.Octets.of_list(NftValue.bitwise(B.Octets.to_list(v), B.Octets.to_list(m), B.Octets.to_list(x)))}
    case None{}:
      None{}

def NftValue.concat_m(a: Maybe<&2, B.Octets>, b: Maybe<&2, B.Octets>) -> Maybe<&2, B.Octets>:
  match a b:
    case Some{x} Some{y}:
      Some{B.Octets.append(x, y)}
    case _ _:
      None{}

def NftValue.of_data(d: Maybe<&2, S.NftData>) -> Maybe<&2, B.Octets>:
  match d:
    case Some{x}:
      match x:
        case S.NftDataValue{v}:
          Some{v}
        case _:
          None{}
    case None{}:
      None{}

def NftValue.map_m(k: Maybe<&2, B.Octets>, s: Maybe<&2, S.NftSet>) -> Maybe<&2, B.Octets>:
  match k s:
    case Some{x} Some{m}:
      NftValue.of_data(S.NftSet.lookup(m, x))
    case _ _:
      None{}

# the value of a source for packet p: None if a payload load falls outside
# the packet or a map has no element for the key (or no value for it)
def NftSrc.load(src: NftSrc, +sets: List<&2, S.NftNamedSet>, +p: NftPacket) -> Maybe<&2, B.Octets>:
  match src:
    case NftSrcPayload{b, off, len}:
      NftPayload.slice(NftPacket.base(b, p), off, len)
    case NftSrcMeta{k}:
      Some{NftMeta.value(k, NftPacket.meta(p))}
    case NftSrcCt{k}:
      Some{NftCt.value(k, NftPacket.ct(p))}
    case NftSrcImm{v}:
      Some{v}
    case NftSrcBitwise{s, m, x}:
      NftValue.bitwise_m(NftSrc.load(s, sets, p), m, x)
    case NftSrcConcat{a, b}:
      NftValue.concat_m(NftSrc.load(a, sets, p), NftSrc.load(b, sets, p))
    case NftSrcMap{k, r}:
      NftValue.map_m(NftSrc.load(k, sets, p), NftSetRef.resolve(r, sets))

# Tests

type NftCmpOp is Data:
  NftOpEq{}
  NftOpNe{}
  NftOpLt{}
  NftOpLe{}
  NftOpGt{}
  NftOpGe{}

def NftCmpOp.holds(op: NftCmpOp, c: Cmp) -> Bool:
  match op:
    case NftOpEq{}:
      Cmp.is_eq(c)
    case NftOpNe{}:
      Bool.not(Cmp.is_eq(c))
    case NftOpLt{}:
      Cmp.is_lt(c)
    case NftOpLe{}:
      Cmp.is_le(c)
    case NftOpGt{}:
      Cmp.is_gt(c)
    case NftOpGe{}:
      Cmp.is_ge(c)

type NftTest is Data:
  # value op v, comparing as keys do (S.NftKey.cmp)
  NftCmp{op: NftCmpOp, value: B.Octets}
  # lo <= value <= hi
  NftRange{lo: B.Octets, hi: B.Octets}
  # not (lo <= value <= hi)
  NftNotRange{lo: B.Octets, hi: B.Octets}
  NftIn{set: NftSetRef}
  NftNotIn{set: NftSetRef}

def NftTest.mem(s: Maybe<&2, S.NftSet>, want: Bool, +v: B.Octets) -> Bool:
  match s:
    case Some{x}:
      Bool.not(Bool.xor(S.NftSet.mem(x, v), want))
    case None{}:
      False{}

# whether the value v passes t; a named set that does not exist passes
# nothing, neither in nor not in
def NftTest.check(t: NftTest, +v: B.Octets, +sets: List<&2, S.NftNamedSet>) -> Bool:
  match t:
    case NftCmp{op, w}:
      NftCmpOp.holds(op, S.NftKey.cmp(v, w))
    case NftRange{lo, hi}:
      Bool.and(S.NftKey.le(lo, v), S.NftKey.le(v, hi))
    case NftNotRange{lo, hi}:
      Bool.not(Bool.and(S.NftKey.le(lo, v), S.NftKey.le(v, hi)))
    case NftIn{r}:
      NftTest.mem(NftSetRef.resolve(r, sets), True{}, v)
    case NftNotIn{r}:
      NftTest.mem(NftSetRef.resolve(r, sets), False{}, v)

# State: counters and the token buckets of limits, by an id the rule set
# gives each one

type NftCounterVal is Data:
  NftCounterVal{id: U32, packets: W.W64, bytes: W.W64}

# a token bucket: its credit (in token-milliseconds) at time last (ms)
type NftBucket is Data:
  NftBucket{id: U32, credit: W.W64, last: W.W64}

type NftState is Data:
  NftState{counters: List<&2, NftCounterVal>, buckets: List<&2, NftBucket>}

def NftState.empty() -> NftState:
  NftState{Nil{}, Nil{}}

def NftCounters.pick(hit: Bool, +cid: U32, pk: W.W64, by: W.W64, t: List<&2, NftCounterVal>, len: U32, rec: List<&2, NftCounterVal>) -> List<&2, NftCounterVal>:
  match hit:
    case True{}:
      Con{NftCounterVal{cid, W.W64.add(pk, W.W64.one()), W.W64.add(by, W.W64.from_u32(len))}, t}
    case False{}:
      Con{NftCounterVal{cid, pk, by}, rec}

# the counters with counter id counting one more packet of len bytes (a new
# counter starts at zero)
def NftCounters.bump(cs: List<&2, NftCounterVal>, +id: U32, +len: U32) -> List<&2, NftCounterVal>:
  match cs:
    case Nil{}:
      Con{NftCounterVal{id, W.W64.one(), W.W64.from_u32(len)}, Nil{}}
    case Con{c, +t}:
      match c:
        case NftCounterVal{+cid, pk, by}:
          NftCounters.pick(U32.is_eq(cid, id), cid, pk, by, t, len, NftCounters.bump(t, id, len))

def NftCounters.find.pick(hit: Bool, c: NftCounterVal, rest: Maybe<&2, NftCounterVal>) -> Maybe<&2, NftCounterVal>:
  match hit:
    case True{}:
      Some{c}
    case False{}:
      rest

def NftCounters.find(cs: List<&2, NftCounterVal>, +id: U32) -> Maybe<&2, NftCounterVal>:
  match cs:
    case Nil{}:
      None{}
    case Con{+c, t}:
      match c:
        case NftCounterVal{+cid, pk, by}:
          NftCounters.find.pick(U32.is_eq(cid, id), NftCounterVal{cid, pk, by}, NftCounters.find(t, id))

# the counter id, if any packet has reached it
def NftState.counter(st: NftState, +id: U32) -> Maybe<&2, NftCounterVal>:
  match st:
    case NftState{cs, bs}:
      NftCounters.find(cs, id)

# limit rate [over] rate/unit [burst burst packets|bytes]: rate packets
# (bytes, if bytes) per unit_ms milliseconds, with a bucket of burst
# packets (bytes), or of rate if burst is 0. over: match the packets over
# the limit instead. Open type.
type NftLimitSpec is Data:
  NftLimitSpec{rate: U32, unit_ms: U32, burst: U32, bytes: Bool, over: Bool}

def NftLimitSpec.second() -> U32:
  1000

def NftLimitSpec.minute() -> U32:
  60000

def NftLimitSpec.hour() -> U32:
  3600000

def NftLimitSpec.day() -> U32:
  86400000

def NftLimitSpec.week() -> U32:
  604800000

# the bucket burst used when none is given (see README, Choices)
def NftLimitSpec.default_burst() -> U32:
  5

# limit rate rate/unit packets, with the default burst
def NftLimitSpec.packets(rate: U32, unit_ms: U32) -> NftLimitSpec:
  NftLimitSpec{rate, unit_ms, NftLimitSpec.default_burst(), False{}, False{}}

def NftBucket.tokens(z: Bool, burst: U32, rate: U32) -> U32:
  match z:
    case True{}:
      rate
    case False{}:
      burst

def NftBucket.cost(bytes: Bool, +unit: U32, len: U32) -> W.W64:
  match bytes:
    case True{}:
      W.W64.mul(W.W64.from_u32(len), W.W64.from_u32(unit))
    case False{}:
      W.W64.from_u32(unit)

def NftBucket.elapsed(fwd: Bool, now: W.W64, last: W.W64) -> W.W64:
  match fwd:
    case True{}:
      W.W64.sub(now, last)
    case False{}:
      W.W64.zero()

def NftBucket.refill.fin(enough: Bool, credit: W.W64, elapsed: W.W64, r: W.W64, cap: W.W64) -> W.W64:
  match enough:
    case True{}:
      cap
    case False{}:
      W.W64.add(credit, W.W64.mul(elapsed, r))

def NftBucket.refill.go(full: Bool, zero: Bool, +credit: W.W64, +elapsed: W.W64, rate: U32, +cap: W.W64) -> W.W64:
  match full:
    case True{}:
      cap
    case False{}:
      match zero:
        case True{}:
          credit
        case False{}:
          +r = W.W64.from_u32(rate)
          +need = W.W64.sub(cap, credit)
          +steps = W.W64.div(W.W64.add(need, W.W64.sub(r, W.W64.one())), r)
          NftBucket.refill.fin(W.W64.is_ge(elapsed, steps), credit, elapsed, r, cap)

# the credit after elapsed ms at rate token-ms per ms, at most cap
def NftBucket.refill(+credit: W.W64, +elapsed: W.W64, +rate: U32, +cap: W.W64) -> W.W64:
  NftBucket.refill.go(W.W64.is_ge(credit, cap), U32.is_eq(rate, 0), credit, elapsed, rate, cap)

type NftBucketStep is Data:
  NftBucketStep{matched: Bool, credit: W.W64}

def NftBucket.take(conform: Bool, over: Bool, +c: W.W64, +cost: W.W64) -> NftBucketStep:
  match conform:
    case True{}:
      NftBucketStep{Bool.xor(True{}, over), W.W64.sub(c, cost)}
    case False{}:
      NftBucketStep{Bool.xor(False{}, over), c}

# one packet of len bytes at time now through a bucket of the given credit
# at time last: a packet conforms if the credit, refilled, covers its cost
# (unit_ms per packet, or per byte), and takes its cost from the credit
def NftBucket.step(spec: NftLimitSpec, credit: W.W64, +last: W.W64, +now: W.W64, len: U32) -> NftBucketStep:
  match spec:
    case NftLimitSpec{+rate, +unit, +burst, bytes, over}:
      +cap = W.W64.mul(W.W64.from_u32(NftBucket.tokens(U32.is_eq(burst, 0), burst, rate)), W.W64.from_u32(unit))
      +c = NftBucket.refill(credit, NftBucket.elapsed(W.W64.is_ge(now, last), now, last), rate, cap)
      +cost = NftBucket.cost(bytes, unit, len)
      NftBucket.take(W.W64.is_ge(c, cost), over, c, cost)

def NftBucket.cap(spec: NftLimitSpec) -> W.W64:
  match spec:
    case NftLimitSpec{+rate, unit, +burst, bytes, over}:
      W.W64.mul(W.W64.from_u32(NftBucket.tokens(U32.is_eq(burst, 0), burst, rate)), W.W64.from_u32(unit))

type NftLimitOut is Data:
  NftLimitOut{matched: Bool, buckets: List<&2, NftBucket>}

def NftLimitOut.hit(s: NftBucketStep, id: U32, now: W.W64, t: List<&2, NftBucket>) -> NftLimitOut:
  match s:
    case NftBucketStep{m, c}:
      NftLimitOut{m, Con{NftBucket{id, c, now}, t}}

def NftLimitOut.cons(b: NftBucket, r: NftLimitOut) -> NftLimitOut:
  match r:
    case NftLimitOut{m, bs}:
      NftLimitOut{m, Con{b, bs}}

def NftLimitOut.pick(hit: Bool, +bid: U32, credit: W.W64, last: W.W64, t: List<&2, NftBucket>, spec: NftLimitSpec, +now: W.W64, len: U32, rec: NftLimitOut) -> NftLimitOut:
  match hit:
    case True{}:
      NftLimitOut.hit(NftBucket.step(spec, credit, last, now, len), bid, now, t)
    case False{}:
      NftLimitOut.cons(NftBucket{bid, credit, last}, rec)

# one packet through the limit id (a new bucket starts full, at time now)
def NftLimitOut.run(bs: List<&2, NftBucket>, +id: U32, +spec: NftLimitSpec, +now: W.W64, +len: U32) -> NftLimitOut:
  match bs:
    case Nil{}:
      NftLimitOut.hit(NftBucket.step(spec, NftBucket.cap(spec), now, now, len), id, now, Nil{})
    case Con{b, +t}:
      match b:
        case NftBucket{+bid, credit, last}:
          NftLimitOut.pick(U32.is_eq(bid, id), bid, credit, last, t, spec, now, len, NftLimitOut.run(t, id, spec, now, len))

# Expressions and rules

type NftExpr is Data:
  # load a value and test it: no match ends the rule
  NftMatch{src: NftSrc, test: NftTest}
  # count the packet and its bytes in counter id
  NftCount{id: U32}
  # the limit statement, with bucket id: a packet over the limit (under it,
  # with over) ends the rule
  NftLimit{id: U32, spec: NftLimitSpec}
  # meta mark set: the first four bytes of the value, as a number
  NftMarkSet{src: NftSrc}
  # ct mark set
  NftCtMarkSet{src: NftSrc}
  # a verdict map: the verdict of the element holding the value; no element
  # ends the rule
  NftVmap{src: NftSrc, map: NftSetRef}
  # a verdict: ends the rule
  NftVerdictStmt{verdict: V.NftVerdict}

type NftRule is Data:
  NftRule{exprs: List<&2, NftExpr>}

def NftRule.exprs(r: NftRule) -> List<&2, NftExpr>:
  match r:
    case NftRule{xs}:
      xs

# What evaluation carries: the packet (statements change its marks), the
# state, and the time now in milliseconds
type NftEnv is Data:
  NftEnv{pkt: NftPacket, st: NftState, now: W.W64}

def NftEnv.pkt(e: NftEnv) -> NftPacket:
  match e:
    case NftEnv{p, s, n}:
      p

def NftEnv.st(e: NftEnv) -> NftState:
  match e:
    case NftEnv{p, s, n}:
      s

type NftExprOut is Data:
  NftExprOk{env: NftEnv}
  NftExprFail{env: NftEnv}
  NftExprVerdict{verdict: V.NftVerdict, env: NftEnv}

def NftExprOut.of(ok: Bool, env: NftEnv) -> NftExprOut:
  match ok:
    case True{}:
      NftExprOk{env}
    case False{}:
      NftExprFail{env}

def NftExpr.match_go(m: Maybe<&2, B.Octets>, t: NftTest, +sets: List<&2, S.NftNamedSet>, env: NftEnv) -> NftExprOut:
  match m:
    case Some{+v}:
      NftExprOut.of(NftTest.check(t, v, sets), env)
    case None{}:
      NftExprFail{env}

def NftExpr.limit_go(r: NftLimitOut, p: NftPacket, cs: List<&2, NftCounterVal>, now: W.W64) -> NftExprOut:
  match r:
    case NftLimitOut{m, bs}:
      NftExprOut.of(m, NftEnv{p, NftState{cs, bs}, now})

def NftExpr.mark_go(m: Maybe<&2, U32>, ct: Bool, p: NftPacket, st: NftState, now: W.W64) -> NftExprOut:
  match m:
    case Some{v}:
      match ct:
        case False{}:
          NftExprOk{NftEnv{NftPacket.set_mark(p, v), st, now}}
        case True{}:
          NftExprOk{NftEnv{NftPacket.set_ct_mark(p, v), st, now}}
    case None{}:
      NftExprFail{NftEnv{p, st, now}}

def NftExpr.mark_load(m: Maybe<&2, B.Octets>) -> Maybe<&2, U32>:
  match m:
    case Some{v}:
      B.Octets.be32_at(v, 0n)
    case None{}:
      None{}

def NftExpr.vmap_data(d: Maybe<&2, S.NftData>, env: NftEnv) -> NftExprOut:
  match d:
    case Some{x}:
      match x:
        case S.NftDataVerdict{v}:
          NftExprVerdict{v, env}
        case _:
          NftExprFail{env}
    case None{}:
      NftExprFail{env}

def NftExpr.vmap_go(k: Maybe<&2, B.Octets>, s: Maybe<&2, S.NftSet>, env: NftEnv) -> NftExprOut:
  match k s:
    case Some{x} Some{m}:
      NftExpr.vmap_data(S.NftSet.lookup(m, x), env)
    case _ _:
      NftExprFail{env}

# one expression, with the table's named sets
def NftExpr.eval(x: NftExpr, +sets: List<&2, S.NftNamedSet>, env: NftEnv) -> NftExprOut:
  match x:
    case NftMatch{src, t}:
      match env:
        case NftEnv{+p, st, now}:
          NftExpr.match_go(NftSrc.load(src, sets, p), t, sets, NftEnv{p, st, now})
    case NftCount{id}:
      match env:
        case NftEnv{+p, st, now}:
          match st:
            case NftState{cs, bs}:
              NftExprOk{NftEnv{p, NftState{NftCounters.bump(cs, id, NftPacket.length(p)), bs}, now}}
    case NftLimit{id, spec}:
      match env:
        case NftEnv{+p, st, +now}:
          match st:
            case NftState{cs, bs}:
              NftExpr.limit_go(NftLimitOut.run(bs, id, spec, now, NftPacket.length(p)), p, cs, now)
    case NftMarkSet{src}:
      match env:
        case NftEnv{+p, st, now}:
          NftExpr.mark_go(NftExpr.mark_load(NftSrc.load(src, sets, p)), False{}, p, st, now)
    case NftCtMarkSet{src}:
      match env:
        case NftEnv{+p, st, now}:
          NftExpr.mark_go(NftExpr.mark_load(NftSrc.load(src, sets, p)), True{}, p, st, now)
    case NftVmap{src, r}:
      match env:
        case NftEnv{+p, st, now}:
          NftExpr.vmap_go(NftSrc.load(src, sets, p), NftSetRef.resolve(r, sets), NftEnv{p, st, now})
    case NftVerdictStmt{v}:
      NftExprVerdict{v, env}

# What a rule gives: no verdict (the next rule runs), or a verdict
type NftRuleOut is Data:
  NftRuleNext{env: NftEnv}
  NftRuleVerdict{verdict: V.NftVerdict, env: NftEnv}

def NftRule.go(xs: List<&2, NftExpr>, +sets: List<&2, S.NftNamedSet>, out: NftExprOut) -> NftRuleOut:
  match xs:
    case Nil{}:
      match out:
        case NftExprOk{env}:
          NftRuleNext{env}
        case NftExprFail{env}:
          NftRuleNext{env}
        case NftExprVerdict{v, env}:
          NftRuleVerdict{v, env}
    case Con{x, rest}:
      match out:
        case NftExprOk{env}:
          NftRule.go(rest, sets, NftExpr.eval(x, sets, env))
        case NftExprFail{env}:
          NftRuleNext{env}
        case NftExprVerdict{v, env}:
          NftRuleVerdict{v, env}

# a rule: its expressions in order, up to the first that fails or gives a
# verdict
def NftRule.eval(r: NftRule, +sets: List<&2, S.NftNamedSet>, env: NftEnv) -> NftRuleOut:
  match r:
    case NftRule{xs}:
      NftRule.go(xs, sets, NftExprOk{env})

# Building expressions

def NftExpr.cmp(op: NftCmpOp, src: NftSrc, v: B.Octets) -> NftExpr:
  NftMatch{src, NftCmp{op, v}}

def NftExpr.eq(src: NftSrc, v: B.Octets) -> NftExpr:
  NftMatch{src, NftCmp{NftOpEq{}, v}}

def NftExpr.ne(src: NftSrc, v: B.Octets) -> NftExpr:
  NftMatch{src, NftCmp{NftOpNe{}, v}}

def NftExpr.range(src: NftSrc, lo: B.Octets, hi: B.Octets) -> NftExpr:
  NftMatch{src, NftRange{lo, hi}}

def NftExpr.in_set(src: NftSrc, r: NftSetRef) -> NftExpr:
  NftMatch{src, NftIn{r}}

def NftExpr.not_in(src: NftSrc, r: NftSetRef) -> NftExpr:
  NftMatch{src, NftNotIn{r}}

def NftExpr.verdict(v: V.NftVerdict) -> NftExpr:
  NftVerdictStmt{v}

# ct state s1,s2,...: some of the state bits in mask are set
def NftExpr.ct_state(mask: U32) -> NftExpr:
  NftMatch{NftSrcBitwise{NftSrcCt{NftCtState{}}, B.Octets.of_list(B.be32(mask)), B.Octets.empty()}, NftCmp{NftOpNe{}, B.Octets.of_list(B.be32(0))}}

# the payload dependencies nft adds before a protocol's fields (the wiki,
# "Matching packet headers"): meta nfproto for a network header in inet,
# meta l4proto for a transport header
def NftExpr.needs_nfproto(n: U32) -> NftExpr:
  NftMatch{NftSrcMeta{NftMetaNfproto{}}, NftCmp{NftOpEq{}, B.Octets.of_list([n])}}

def NftExpr.needs_l4proto(n: U32) -> NftExpr:
  NftMatch{NftSrcMeta{NftMetaL4proto{}}, NftCmp{NftOpEq{}, B.Octets.of_list([n])}}

# Header fields, as payload loads (offsets from RFC 791, RFC 8200, RFC 9293,
# RFC 768, RFC 792, IEEE 802.3)

def NftField.ip_protocol() -> NftSrc:
  NftSrcPayload{NftBaseNh{}, 9n, 1n}

def NftField.ip_saddr() -> NftSrc:
  NftSrcPayload{NftBaseNh{}, 12n, 4n}

def NftField.ip_daddr() -> NftSrc:
  NftSrcPayload{NftBaseNh{}, 16n, 4n}

def NftField.ip_ttl() -> NftSrc:
  NftSrcPayload{NftBaseNh{}, 8n, 1n}

def NftField.ip6_nexthdr() -> NftSrc:
  NftSrcPayload{NftBaseNh{}, 6n, 1n}

def NftField.ip6_hoplimit() -> NftSrc:
  NftSrcPayload{NftBaseNh{}, 7n, 1n}

def NftField.ip6_saddr() -> NftSrc:
  NftSrcPayload{NftBaseNh{}, 8n, 16n}

def NftField.ip6_daddr() -> NftSrc:
  NftSrcPayload{NftBaseNh{}, 24n, 16n}

# TCP and UDP ports
def NftField.th_sport() -> NftSrc:
  NftSrcPayload{NftBaseTh{}, 0n, 2n}

def NftField.th_dport() -> NftSrc:
  NftSrcPayload{NftBaseTh{}, 2n, 2n}

def NftField.tcp_flags() -> NftSrc:
  NftSrcPayload{NftBaseTh{}, 13n, 1n}

def NftField.icmp_type() -> NftSrc:
  NftSrcPayload{NftBaseTh{}, 0n, 1n}

def NftField.icmp_code() -> NftSrc:
  NftSrcPayload{NftBaseTh{}, 1n, 1n}

def NftField.ether_daddr() -> NftSrc:
  NftSrcPayload{NftBaseLl{}, 0n, 6n}

def NftField.ether_saddr() -> NftSrc:
  NftSrcPayload{NftBaseLl{}, 6n, 6n}

# the EtherType of an untagged frame
def NftField.ether_type() -> NftSrc:
  NftSrcPayload{NftBaseLl{}, 12n, 2n}

def NftField.meta(k: NftMetaKey) -> NftSrc:
  NftSrcMeta{k}

def NftField.ct(k: NftCtKey) -> NftSrc:
  NftSrcCt{k}
