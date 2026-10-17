# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input:
# * round trips: parsing a built header, followed by any bytes, gives back the
#   header with its fields masked to their widths (X.norm). For IPv4 and TCP
#   this covers every header length the parser accepts (IHL and data offset
#   5 to 15) with options of the matching length; for Ethernet, untagged
#   headers whose EtherType is not 0x8100 (it would read as a tag) and tagged
#   headers;
# * truncation: every input shorter than a header's fixed part fails with
#   NetTruncated;
# * the Internet checksum sum can be computed in pieces, split after an even
#   number of bytes (RFC 1071 section 2).
#
# Vectors: RFC 1071's worked example; checksums written by build_checksum and
# build_ipv4 / build_ipv6 verify; malformed headers fail with the right error.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ethernet.bend as E
import ./arp.bend as A
import ./ipv4.bend as I4
import ./ipv6.bend as I6
import ./icmp.bend as C
import ./udp.bend as U
import ./tcp.bend as T

# Round trips

law eth_round_trip:
  for +d: E.MacAddr
  for +s: E.MacAddr
  for +t: U32
  for e: {U32.is_eq(B.low16(t), 33024) == False{} : Bool}
  for +rest: B.Octets
  {E.EthHeader.parse(B.Octets.append(E.EthHeader.build(E.EthHeader{d, s, None{}, t}), rest)) == Done{E.EthHeader.norm(E.EthHeader{d, s, None{}, t})} : Result<&2, &2, N.NetError, E.EthHeader>}

law eth_round_trip_vlan:
  for +d: E.MacAddr
  for +s: E.MacAddr
  for +v: E.VlanTag
  for +t: U32
  for +rest: B.Octets
  {E.EthHeader.parse(B.Octets.append(E.EthHeader.build(E.EthHeader{d, s, Some{v}, t}), rest)) == Done{E.EthHeader.norm(E.EthHeader{d, s, Some{v}, t})} : Result<&2, &2, N.NetError, E.EthHeader>}

law arp_round_trip:
  for +p: A.ArpPacket
  for +rest: B.Octets
  {A.ArpPacket.parse(B.Octets.append(A.ArpPacket.build(p), rest)) == Done{A.ArpPacket.norm(p)} : Result<&2, &2, N.NetError, A.ArpPacket>}

# every IHL from 5 to 15, with IHL * 4 - 20 bytes of options
law ipv4_round_trip:
  for +ihl: U32
  for e1: {U32.is_ge(N.NetField.low(4n, ihl), 5) == True{} : Bool}
  for +dscp: U32
  for +ecn: U32
  for +total_length: U32
  for +ident: U32
  for +flags: U32
  for +frag_offset: U32
  for +ttl: U32
  for +protocol: U32
  for +checksum: U32
  for +src: U32
  for +dst: U32
  for +options: List<&2, U32>
  for e2: {B.len(options) == Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n) : Nat}
  for +rest: B.Octets
  {I4.Ipv4Header.parse(B.Octets.append(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, total_length, ident, flags, frag_offset, ttl, protocol, checksum, src, dst, B.Octets.of_list(options)}), rest)) == Done{I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, total_length, ident, flags, frag_offset, ttl, protocol, checksum, src, dst, B.Octets.of_list(options)})} : Result<&2, &2, N.NetError, I4.Ipv4Header>}

law ipv6_round_trip:
  for +traffic_class: U32
  for +flow_label: U32
  for +payload_length: U32
  for +next_header: U32
  for +hop_limit: U32
  for +src: I6.Ipv6Addr
  for +dst: I6.Ipv6Addr
  for +rest: B.Octets
  {I6.Ipv6Header.parse(B.Octets.append(I6.Ipv6Header.build(I6.Ipv6Header{6, traffic_class, flow_label, payload_length, next_header, hop_limit, src, dst}), rest)) == Done{I6.Ipv6Header.norm(I6.Ipv6Header{6, traffic_class, flow_label, payload_length, next_header, hop_limit, src, dst})} : Result<&2, &2, N.NetError, I6.Ipv6Header>}

law icmp_round_trip:
  for +h: C.IcmpHeader
  for +rest: B.Octets
  {C.IcmpHeader.parse(B.Octets.append(C.IcmpHeader.build(h), rest)) == Done{C.IcmpHeader.norm(h)} : Result<&2, &2, N.NetError, C.IcmpHeader>}

law udp_round_trip:
  for +h: U.UdpHeader
  for +rest: B.Octets
  {U.UdpHeader.parse(B.Octets.append(U.UdpHeader.build(h), rest)) == Done{U.UdpHeader.norm(h)} : Result<&2, &2, N.NetError, U.UdpHeader>}

# every data offset from 5 to 15, with data offset * 4 - 20 bytes of options
law tcp_round_trip:
  for +src_port: U32
  for +dst_port: U32
  for +seq: U32
  for +ack: U32
  for +data_offset: U32
  for e1: {U32.is_ge(N.NetField.low(4n, data_offset), 5) == True{} : Bool}
  for +reserved: U32
  for +flags: U32
  for +window: U32
  for +checksum: U32
  for +urgent: U32
  for +options: List<&2, U32>
  for e2: {B.len(options) == Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, data_offset))), 20n) : Nat}
  for +rest: B.Octets
  {T.TcpHeader.parse(B.Octets.append(T.TcpHeader.build(T.TcpHeader{src_port, dst_port, seq, ack, data_offset, reserved, flags, window, checksum, urgent, B.Octets.of_list(options)}), rest)) == Done{T.TcpHeader.norm(T.TcpHeader{src_port, dst_port, seq, ack, data_offset, reserved, flags, window, checksum, urgent, B.Octets.of_list(options)})} : Result<&2, &2, N.NetError, T.TcpHeader>}

# Truncation: fewer bytes than the fixed part of a header

law eth_truncated:
  for xs: List<&2, U32>
  for e: {Nat.is_lt(B.len(xs), 14n) == True{} : Bool}
  {E.EthHeader.parse(B.Octets.of_list(xs)) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, E.EthHeader>}

law arp_truncated:
  for xs: List<&2, U32>
  for e: {Nat.is_lt(B.len(xs), 28n) == True{} : Bool}
  {A.ArpPacket.parse(B.Octets.of_list(xs)) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, A.ArpPacket>}

law ipv4_truncated:
  for xs: List<&2, U32>
  for e: {Nat.is_lt(B.len(xs), 20n) == True{} : Bool}
  {I4.Ipv4Header.parse(B.Octets.of_list(xs)) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}

law ipv6_truncated:
  for xs: List<&2, U32>
  for e: {Nat.is_lt(B.len(xs), 40n) == True{} : Bool}
  {I6.Ipv6Header.parse(B.Octets.of_list(xs)) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, I6.Ipv6Header>}

law icmp_truncated:
  for xs: List<&2, U32>
  for e: {Nat.is_lt(B.len(xs), 8n) == True{} : Bool}
  {C.IcmpHeader.parse(B.Octets.of_list(xs)) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, C.IcmpHeader>}

law udp_truncated:
  for xs: List<&2, U32>
  for e: {Nat.is_lt(B.len(xs), 8n) == True{} : Bool}
  {U.UdpHeader.parse(B.Octets.of_list(xs)) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, U.UdpHeader>}

law tcp_truncated:
  for xs: List<&2, U32>
  for e: {Nat.is_lt(B.len(xs), 20n) == True{} : Bool}
  {T.TcpHeader.parse(B.Octets.of_list(xs)) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, T.TcpHeader>}

# The Internet checksum: the sum of a ++ b, a of even length, is the sum of b
# continued from the sum of a

law inet_update_split:
  for acc: U32
  for +a: B.Octets
  for +b: B.Octets
  for e: {K.inet_even(a) == True{} : Bool}
  {K.inet_update(acc, B.Octets.append(a, b)) == K.inet_update(K.inet_update(acc, a), b) : U32}

# Vectors

# RFC 1071 section 3: the bytes 00 01 f2 03 f4 f5 f6 f7 sum to 0xddf2
law rfc1071_sum:
  {K.inet_sum(B.Octets.of_list([0, 1, 242, 3, 244, 245, 246, 247])) == 56818 : U32}

# so their checksum is 0x220d
law rfc1071_checksum:
  {K.inet_checksum(B.Octets.of_list([0, 1, 242, 3, 244, 245, 246, 247])) == 8717 : U32}

# the same sum in two pieces, split after four bytes
law rfc1071_pieces:
  {K.inet_finish(K.inet_update(K.inet_update(K.inet_start(), B.Octets.of_list([0, 1, 242, 3])), B.Octets.of_list([244, 245, 246, 247]))) == 8717 : U32}

# an odd final byte is padded with zero: 0x0102 + 0x0300
law inet_odd_length:
  {K.inet_sum(B.Octets.of_list([1, 2, 3])) == 1026 : U32}

# carries fold back in: 0xffff + 0x0002 = 0x0002 (the end-around carry)
law inet_end_around_carry:
  {K.inet_sum(B.Octets.of_list([255, 255, 0, 2])) == 2 : U32}

# an IPv4 header, 192.168.0.1 to 192.168.0.199, UDP, total length 115, DF:
# checksum 0xb861
law ipv4_checksum:
  {B.Octets.to_list(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, 5, 0, 0, 115, 0, 2, 0, 64, 17, 0, 3232235521, 3232235719, B.Octets.empty()})) == [69, 0, 0, 115, 0, 0, 64, 0, 64, 17, 184, 97, 192, 168, 0, 1, 192, 168, 0, 199] : List<&2, U32>}

law ipv4_checksum_verifies:
  {I4.Ipv4Header.verify(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, 6, 46, 1, 60, 4660, 1, 100, 1, 6, 0, 167772161, 167772162, B.Octets.of_list([148, 4, 0, 0])})) == True{} : Bool}

law ipv4_bad_checksum:
  {I4.Ipv4Header.parse_verified(B.Octets.of_list([69, 0, 0, 115, 0, 0, 64, 0, 64, 17, 184, 98, 192, 168, 0, 1, 192, 168, 0, 199])) == Fail{N.NetBadChecksum{}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}

# UDP over IPv4 and IPv6, TCP over IPv4 and IPv6, ICMP and ICMPv6 echo
# requests: built with their checksums, they verify
law udp_ipv4_verifies:
  {U.UdpHeader.verify_ipv4(167772161, 167772162, U.UdpHeader.build_ipv4(167772161, 167772162, U.UdpHeader{1234, 53, 11, 0}, B.Octets.of_string("hi!"))) == True{} : Bool}

law udp_ipv6_verifies:
  {U.UdpHeader.verify_ipv6(I6.Ipv6Addr{536939960, 0, 0, 1}, I6.Ipv6Addr{536939960, 0, 0, 2}, U.UdpHeader.build_ipv6(I6.Ipv6Addr{536939960, 0, 0, 1}, I6.Ipv6Addr{536939960, 0, 0, 2}, U.UdpHeader{1234, 53, 11, 0}, B.Octets.of_string("hi!"))) == True{} : Bool}

# a UDP datagram without a checksum: accepted over IPv4 by default, refused
# when zero_ok is False, and always over IPv6
law udp_zero_checksum:
  {U.UdpHeader.verify_ipv4(167772161, 167772162, U.UdpHeader.build(U.UdpHeader{1234, 53, 8, 0})) == True{} : Bool}

law udp_zero_checksum_refused:
  {U.UdpHeader.verify_ipv4_with(False{}, 167772161, 167772162, U.UdpHeader.build(U.UdpHeader{1234, 53, 8, 0})) == False{} : Bool}

law udp_zero_checksum_ipv6:
  {U.UdpHeader.verify_ipv6(I6.Ipv6Addr{536939960, 0, 0, 1}, I6.Ipv6Addr{536939960, 0, 0, 2}, U.UdpHeader.build(U.UdpHeader{1234, 53, 8, 0})) == False{} : Bool}

law tcp_ipv4_verifies:
  {T.TcpHeader.verify_ipv4(167772161, 167772162, T.TcpHeader.build_ipv4(167772161, 167772162, T.TcpHeader{49152, 80, 1, 0, 6, 0, 2, 65535, 0, 0, B.Octets.of_list([2, 4, 5, 180])}, B.Octets.empty())) == True{} : Bool}

law tcp_ipv6_verifies:
  {T.TcpHeader.verify_ipv6(I6.Ipv6Addr{536939960, 0, 0, 1}, I6.Ipv6Addr{536939960, 0, 0, 2}, T.TcpHeader.build_ipv6(I6.Ipv6Addr{536939960, 0, 0, 1}, I6.Ipv6Addr{536939960, 0, 0, 2}, T.TcpHeader{49152, 443, 305419896, 2596069104, 5, 0, 24, 1024, 0, 0, B.Octets.empty()}, B.Octets.of_string("GET"))) == True{} : Bool}

# an echo request, identifier 1, sequence 1, data "abcd": checksum 0x3337
law icmp_checksum:
  {B.Octets.to_list(C.IcmpHeader.build_checksum(C.IcmpHeader{8, 0, 0, 65537}, B.Octets.of_string("abcd"))) == [8, 0, 51, 55, 0, 1, 0, 1, 97, 98, 99, 100] : List<&2, U32>}

law icmp_verifies:
  {C.IcmpHeader.verify(C.IcmpHeader.build_checksum(C.IcmpHeader{8, 0, 0, 65537}, B.Octets.of_string("abcd"))) == True{} : Bool}

law icmp6_verifies:
  {C.IcmpHeader.verify_ipv6(I6.Ipv6Addr{4269801472, 0, 0, 1}, I6.Ipv6Addr{4269801472, 0, 0, 2}, C.IcmpHeader.build_ipv6(I6.Ipv6Addr{4269801472, 0, 0, 1}, I6.Ipv6Addr{4269801472, 0, 0, 2}, C.IcmpHeader{128, 0, 0, 65537}, B.Octets.of_string("ab"))) == True{} : Bool}

# Malformed headers

law ipv4_bad_ihl:
  {I4.Ipv4Header.parse(B.Octets.of_list([68, 0, 0, 20, 0, 0, 0, 0, 64, 6, 0, 0, 10, 0, 0, 1, 10, 0, 0, 2])) == Fail{N.NetBadIhl{}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}

law ipv4_bad_version:
  {I4.Ipv4Header.parse(B.Octets.of_list([101, 0, 0, 20, 0, 0, 0, 0, 64, 6, 0, 0, 10, 0, 0, 1, 10, 0, 0, 2])) == Fail{N.NetBadVersion{}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}

# IHL 6 with only 20 bytes present
law ipv4_truncated_options:
  {I4.Ipv4Header.parse(B.Octets.of_list([70, 0, 0, 24, 0, 0, 0, 0, 64, 6, 0, 0, 10, 0, 0, 1, 10, 0, 0, 2])) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}

law ipv6_bad_version:
  {I6.Ipv6Header.parse(B.Octets.append(B.Octets.of_list([64, 0, 0, 0, 0, 0, 17, 64]), B.Octets.zeros(32n))) == Fail{N.NetBadVersion{}} : Result<&2, &2, N.NetError, I6.Ipv6Header>}

law tcp_bad_data_offset:
  {T.TcpHeader.parse(B.Octets.of_list([0, 80, 0, 80, 0, 0, 0, 1, 0, 0, 0, 0, 64, 2, 255, 255, 0, 0, 0, 0])) == Fail{N.NetBadDataOffset{}} : Result<&2, &2, N.NetError, T.TcpHeader>}

# hardware address length 8
law arp_bad_format:
  {A.ArpPacket.parse(B.Octets.of_list([0, 1, 8, 0, 8, 4, 0, 1, 1, 2, 3, 4, 5, 6, 10, 0, 0, 1, 0, 0, 0, 0, 0, 0, 10, 0, 0, 2])) == Fail{N.NetBadArpFormat{}} : Result<&2, &2, N.NetError, A.ArpPacket>}

# a frame cut inside its 802.1Q tag
law eth_truncated_tag:
  {E.EthHeader.parse(B.Octets.of_list([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 129, 0, 0, 5, 8])) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, E.EthHeader>}

# The payload behind a header

# total length 24, IHL 5: four bytes of payload, the fifth byte left out
law ipv4_payload:
  {I4.Ipv4Header.payload(I4.Ipv4Header{4, 5, 0, 0, 24, 0, 0, 0, 64, 17, 0, 1, 2, B.Octets.empty()}, B.Octets.append(B.Octets.zeros(20n), B.Octets.of_list([1, 2, 3, 4, 5]))) == Done{B.Octets.of_list([1, 2, 3, 4])} : Result<&2, &2, N.NetError, B.Octets>}

# UDP length 12, only three bytes after the header
law udp_payload_truncated:
  {U.UdpHeader.payload(U.UdpHeader{1, 2, 12, 0}, B.Octets.append(B.Octets.zeros(8n), B.Octets.of_list([1, 2, 3]))) == Fail{N.NetTruncated{}} : Result<&2, &2, N.NetError, B.Octets>}

# UDP length 7: shorter than its own header
law udp_payload_bad_length:
  {U.UdpHeader.payload(U.UdpHeader{1, 2, 7, 0}, B.Octets.zeros(8n)) == Fail{N.NetBadLength{}} : Result<&2, &2, N.NetError, B.Octets>}
