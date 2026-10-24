# The reverse round trips through the builders that recompute the checksum:
# given the header the parser read, they give back the bytes it was read
# from, when those bytes verified with the checksum the builder writes.
#
# The condition on the input's checksum field c:
# * IPv4, ICMP, TCP: the bytes verify, and c is not 0xffff. A field that
#   verifies is the one's complement of the sum of the rest, except that
#   when the rest sums to 0xffff both 0x0000 and 0xffff verify, and the
#   builders write 0x0000;
# * UDP: the datagram verifies with a field that is not 0 ("no checksum",
#   which RFC 768 lets a sender write and verify_ipv4 accepts unchecked); a
#   computed 0 is sent as 0xffff, so every verified nonzero field is the one
#   the builder writes.
#
# A pair of its own (PROOF_revsum.bend): the proofs rest on the reverse round
# trips (LAWS_rev.bend) and on the one's complement lemmas.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./ipv4.bend as I4
import ./ipv6.bend as I6
import ./icmp.bend as C
import ./udp.bend as U
import ./tcp.bend as T

law ipv4_reverse_checksum:
  for +o: B.Octets
  for +h: I4.Ipv4Header
  for +c: U32
  for +e: {I4.Ipv4Header.parse_verified(o) == Done{h} : Result<&2, &2, N.NetError, I4.Ipv4Header>}
  for +hc: {B.Octets.be16_at(o, 10n) == Some{c} : Maybe<&2, U32>}
  for +hk: {U32.is_eq(c, 65535) == False{} : Bool}
  {I4.Ipv4Header.build_checksum(h) == B.Octets.take(I4.Ipv4Header.length(h), o) : B.Octets}

law icmp_reverse_checksum:
  for +o: B.Octets
  for +h: C.IcmpHeader
  for +c: U32
  for +e: {C.IcmpHeader.parse(o) == Done{h} : Result<&2, &2, N.NetError, C.IcmpHeader>}
  for +ev: {C.IcmpHeader.verify(o) == True{} : Bool}
  for +hc: {B.Octets.be16_at(o, 2n) == Some{c} : Maybe<&2, U32>}
  for +hk: {U32.is_eq(c, 65535) == False{} : Bool}
  {C.IcmpHeader.build_checksum(h, B.Octets.drop(8n, o)) == o : B.Octets}

law udp_ipv4_reverse_checksum:
  for +src: U32
  for +dst: U32
  for +dg: B.Octets
  for +h: U.UdpHeader
  for +c: U32
  for +e: {U.UdpHeader.parse(dg) == Done{h} : Result<&2, &2, N.NetError, U.UdpHeader>}
  for +ev: {U.UdpHeader.verify_ipv4(src, dst, dg) == True{} : Bool}
  for +hc: {B.Octets.be16_at(dg, 6n) == Some{c} : Maybe<&2, U32>}
  for +hk: {U32.is_eq(c, 0) == False{} : Bool}
  {U.UdpHeader.build_ipv4(src, dst, h, B.Octets.drop(8n, dg)) == dg : B.Octets}

law udp_ipv6_reverse_checksum:
  for +src: I6.Ipv6Addr
  for +dst: I6.Ipv6Addr
  for +dg: B.Octets
  for +h: U.UdpHeader
  for +c: U32
  for +e: {U.UdpHeader.parse(dg) == Done{h} : Result<&2, &2, N.NetError, U.UdpHeader>}
  for +ev: {U.UdpHeader.verify_ipv6(src, dst, dg) == True{} : Bool}
  for +hc: {B.Octets.be16_at(dg, 6n) == Some{c} : Maybe<&2, U32>}
  {U.UdpHeader.build_ipv6(src, dst, h, B.Octets.drop(8n, dg)) == dg : B.Octets}

law tcp_ipv4_reverse_checksum:
  for +src: U32
  for +dst: U32
  for +seg: B.Octets
  for +h: T.TcpHeader
  for +c: U32
  for +e: {T.TcpHeader.parse(seg) == Done{h} : Result<&2, &2, N.NetError, T.TcpHeader>}
  for +ev: {T.TcpHeader.verify_ipv4(src, dst, seg) == True{} : Bool}
  for +hc: {B.Octets.be16_at(seg, 16n) == Some{c} : Maybe<&2, U32>}
  for +hk: {U32.is_eq(c, 65535) == False{} : Bool}
  {T.TcpHeader.build_ipv4(src, dst, h, B.Octets.drop(T.TcpHeader.length(h), seg)) == seg : B.Octets}

law tcp_ipv6_reverse_checksum:
  for +src: I6.Ipv6Addr
  for +dst: I6.Ipv6Addr
  for +seg: B.Octets
  for +h: T.TcpHeader
  for +c: U32
  for +e: {T.TcpHeader.parse(seg) == Done{h} : Result<&2, &2, N.NetError, T.TcpHeader>}
  for +ev: {T.TcpHeader.verify_ipv6(src, dst, seg) == True{} : Bool}
  for +hc: {B.Octets.be16_at(seg, 16n) == Some{c} : Maybe<&2, U32>}
  for +hk: {U32.is_eq(c, 65535) == False{} : Bool}
  {T.TcpHeader.build_ipv6(src, dst, h, B.Octets.drop(T.TcpHeader.length(h), seg)) == seg : B.Octets}
