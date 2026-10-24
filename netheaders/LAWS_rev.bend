# The reverse round trips: building a header the parser read gives back the
# bytes it was read from, for every input. For a header whose bytes o parse
# to Done{h}, X.build(h) is the first X.length(h) bytes of o (UDP: its
# header_length): every field the parser reads is written back bit for bit,
# and IPv4's and TCP's options are the bytes after the fixed part. The
# builders write the checksum field as parsed (the checksum is not
# recomputed); LAWS_revsum.bend has the builders that recompute it.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./ethernet.bend as E
import ./arp.bend as A
import ./ipv4.bend as I4
import ./ipv6.bend as I6
import ./icmp.bend as C
import ./udp.bend as U
import ./tcp.bend as T

law icmp_reverse:
  for +o: B.Octets
  for +h: C.IcmpHeader
  for e: {C.IcmpHeader.parse(o) == Done{h} : Result<&2, &2, N.NetError, C.IcmpHeader>}
  {C.IcmpHeader.build(h) == B.Octets.take(C.IcmpHeader.length(h), o) : B.Octets}

law udp_reverse:
  for +o: B.Octets
  for +h: U.UdpHeader
  for e: {U.UdpHeader.parse(o) == Done{h} : Result<&2, &2, N.NetError, U.UdpHeader>}
  {U.UdpHeader.build(h) == B.Octets.take(U.UdpHeader.header_length(h), o) : B.Octets}

law eth_reverse:
  for +o: B.Octets
  for +h: E.EthHeader
  for e: {E.EthHeader.parse(o) == Done{h} : Result<&2, &2, N.NetError, E.EthHeader>}
  {E.EthHeader.build(h) == B.Octets.take(E.EthHeader.length(h), o) : B.Octets}

law arp_reverse:
  for +o: B.Octets
  for +h: A.ArpPacket
  for e: {A.ArpPacket.parse(o) == Done{h} : Result<&2, &2, N.NetError, A.ArpPacket>}
  {A.ArpPacket.build(h) == B.Octets.take(A.ArpPacket.length(h), o) : B.Octets}

law ipv4_reverse:
  for +o: B.Octets
  for +h: I4.Ipv4Header
  for e: {I4.Ipv4Header.parse(o) == Done{h} : Result<&2, &2, N.NetError, I4.Ipv4Header>}
  {I4.Ipv4Header.build(h) == B.Octets.take(I4.Ipv4Header.length(h), o) : B.Octets}

law ipv6_reverse:
  for +o: B.Octets
  for +h: I6.Ipv6Header
  for e: {I6.Ipv6Header.parse(o) == Done{h} : Result<&2, &2, N.NetError, I6.Ipv6Header>}
  {I6.Ipv6Header.build(h) == B.Octets.take(I6.Ipv6Header.length(h), o) : B.Octets}

law tcp_reverse:
  for +o: B.Octets
  for +h: T.TcpHeader
  for e: {T.TcpHeader.parse(o) == Done{h} : Result<&2, &2, N.NetError, T.TcpHeader>}
  {T.TcpHeader.build(h) == B.Octets.take(T.TcpHeader.length(h), o) : B.Octets}
