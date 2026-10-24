# The Internet checksum's one's complement arithmetic (RFC 1071), for every
# input, and what it gives the headers: a header or message built with its
# checksum verifies.
#
# A 16-bit value is a U32 of at most 65535. On such values:
# * inet_add is one's complement addition: the plain sum when it fits 16
#   bits, else the sum less 65535 (the end-around carry); it is commutative
#   and associative, 0 is its identity, it keeps values in 16 bits, and a
#   value plus its checksum (one's complement) is 0xffff;
# * the sum of data can be taken in any order: inet_update adds data, and
#   updates commute with each other and with inet_add; two pieces of even
#   length sum the same in either order (with inet_update_split in
#   LAWS.bend, which splits a sum into pieces);
# * data with its checksum written in (inet_fill, with a pseudo-header of
#   even length and the field at an even offset inside the data) verifies.
#
# The headers: ICMP and ICMPv6 messages, UDP datagrams and TCP segments over
# IPv4 and IPv6, built with their checksums, verify, for every header and
# payload (UDP's computed checksum 0 is sent as 0xffff, which verifies too).
#
# These are in a pair of their own (PROOF_sum.bend): their proofs rest on
# bend-osdev-u32's laws, not on the bit-level round trips of PROOF.bend.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ipv6.bend as I6
import ./icmp.bend as C
import ./udp.bend as U
import ./tcp.bend as T

# One's complement addition of 16-bit values

law inet_add_comm:
  for +a: U32
  for +b: U32
  {K.inet_add(a, b) == K.inet_add(b, a) : U32}

law inet_add_bound:
  for +a: U32
  for +b: U32
  for ha: {U32.is_le(a, 65535) == True{} : Bool}
  for hb: {U32.is_le(b, 65535) == True{} : Bool}
  {U32.is_le(K.inet_add(a, b), 65535) == True{} : Bool}

# a sum that fits 16 bits is the plain sum
law inet_add_no_carry:
  for +a: U32
  for +b: U32
  for ha: {U32.is_le(a, 65535) == True{} : Bool}
  for hb: {U32.is_le(b, 65535) == True{} : Bool}
  for h: {U32.is_le(U32.add(a, b), 65535) == True{} : Bool}
  {K.inet_add(a, b) == U32.add(a, b) : U32}

# the end-around carry: a sum past 16 bits loses 2^16 and gains 1
law inet_add_end_around:
  for +a: U32
  for +b: U32
  for ha: {U32.is_le(a, 65535) == True{} : Bool}
  for hb: {U32.is_le(b, 65535) == True{} : Bool}
  for h: {U32.is_le(U32.add(a, b), 65535) == False{} : Bool}
  {K.inet_add(a, b) == U32.sub(U32.add(a, b), 65535) : U32}

law inet_add_zero:
  for +a: U32
  for ha: {U32.is_le(a, 65535) == True{} : Bool}
  {K.inet_add(a, 0) == a : U32}

law inet_add_assoc:
  for +a: U32
  for +b: U32
  for +c: U32
  for ha: {U32.is_le(a, 65535) == True{} : Bool}
  for hb: {U32.is_le(b, 65535) == True{} : Bool}
  for hc: {U32.is_le(c, 65535) == True{} : Bool}
  {K.inet_add(K.inet_add(a, b), c) == K.inet_add(a, K.inet_add(b, c)) : U32}

# a value plus its one's complement is 0xffff
law inet_add_complement:
  for +a: U32
  for ha: {U32.is_le(a, 65535) == True{} : Bool}
  {K.inet_add(a, K.inet_finish(a)) == 65535 : U32}

law inet_finish_bound:
  for +a: U32
  {U32.is_le(K.inet_finish(a), 65535) == True{} : Bool}

# The sum of data, in any order

law inet_update_bound:
  for +acc: U32
  for +o: B.Octets
  for ha: {U32.is_le(acc, 65535) == True{} : Bool}
  {U32.is_le(K.inet_update(acc, o), 65535) == True{} : Bool}

law inet_update_add:
  for +acc: U32
  for +w: U32
  for +o: B.Octets
  for ha: {U32.is_le(acc, 65535) == True{} : Bool}
  for hw: {U32.is_le(w, 65535) == True{} : Bool}
  {K.inet_update(K.inet_add(acc, w), o) == K.inet_add(K.inet_update(acc, o), w) : U32}

law inet_update_comm:
  for +acc: U32
  for +x: B.Octets
  for +y: B.Octets
  for ha: {U32.is_le(acc, 65535) == True{} : Bool}
  {K.inet_update(K.inet_update(acc, x), y) == K.inet_update(K.inet_update(acc, y), x) : U32}

law inet_sum_swap:
  for +x: B.Octets
  for +y: B.Octets
  for ex: {K.inet_even(x) == True{} : Bool}
  for ey: {K.inet_even(y) == True{} : Bool}
  {K.inet_sum(B.Octets.append(x, y)) == K.inet_sum(B.Octets.append(y, x)) : U32}

# The checksum written in: pseudo-header of even length, field at the even
# offset 2k inside o
law inet_fill_verifies:
  for +pseudo: B.Octets
  for +o: B.Octets
  for +k: Nat
  for ep: {K.inet_even(pseudo) == True{} : Bool}
  for hl: {Nat.is_le(Nat.double(k), B.Octets.len(o)) == True{} : Bool}
  {K.inet_verify(B.Octets.append(pseudo, K.inet_fill(pseudo, o, Nat.double(k)))) == True{} : Bool}

# Headers built with their checksums verify

law icmp_build_verifies:
  for +h: C.IcmpHeader
  for +data: B.Octets
  {C.IcmpHeader.verify(C.IcmpHeader.build_checksum(h, data)) == True{} : Bool}

law icmp6_build_verifies:
  for +src: I6.Ipv6Addr
  for +dst: I6.Ipv6Addr
  for +h: C.IcmpHeader
  for +data: B.Octets
  {C.IcmpHeader.verify_ipv6(src, dst, C.IcmpHeader.build_ipv6(src, dst, h, data)) == True{} : Bool}

law udp_ipv4_build_verifies:
  for +src: U32
  for +dst: U32
  for +h: U.UdpHeader
  for +payload: B.Octets
  {U.UdpHeader.verify_ipv4(src, dst, U.UdpHeader.build_ipv4(src, dst, h, payload)) == True{} : Bool}

law udp_ipv6_build_verifies:
  for +src: I6.Ipv6Addr
  for +dst: I6.Ipv6Addr
  for +h: U.UdpHeader
  for +payload: B.Octets
  {U.UdpHeader.verify_ipv6(src, dst, U.UdpHeader.build_ipv6(src, dst, h, payload)) == True{} : Bool}

law tcp_ipv4_build_verifies:
  for +src: U32
  for +dst: U32
  for +h: T.TcpHeader
  for +payload: B.Octets
  {T.TcpHeader.verify_ipv4(src, dst, T.TcpHeader.build_ipv4(src, dst, h, payload)) == True{} : Bool}

law tcp_ipv6_build_verifies:
  for +src: I6.Ipv6Addr
  for +dst: I6.Ipv6Addr
  for +h: T.TcpHeader
  for +payload: B.Octets
  {T.TcpHeader.verify_ipv6(src, dst, T.TcpHeader.build_ipv6(src, dst, h, payload)) == True{} : Bool}

# The checksum field written (inet_put16, as inet_fill and UDP's fill write
# it): the length is kept, the bytes past the field are kept, and ICMP and
# UDP headers parse back with the field written

law inet_put16_len:
  for +o: B.Octets
  for +off: Nat
  for +v: U32
  for h: {Nat.is_le(Nat.add(off, 2n), B.Octets.len(o)) == True{} : Bool}
  {B.Octets.len(K.inet_put16(o, off, v)) == B.Octets.len(o) : Nat}

law inet_put16_drop:
  for +o: B.Octets
  for +off: Nat
  for +v: U32
  for +n: Nat
  for +h1: {Nat.is_le(Nat.add(off, 2n), n) == True{} : Bool}
  for h2: {Nat.is_le(Nat.add(off, 2n), B.Octets.len(o)) == True{} : Bool}
  {B.Octets.drop(n, K.inet_put16(o, off, v)) == B.Octets.drop(n, o) : B.Octets}

law icmp_put_parse:
  for +msg_type: U32
  for +code: U32
  for +checksum: U32
  for +rest: U32
  for +data: B.Octets
  for +c: U32
  {C.IcmpHeader.parse(K.inet_put16(B.Octets.append(C.IcmpHeader.build(C.IcmpHeader{msg_type, code, checksum, rest}), data), 2n, c)) == Done{C.IcmpHeader.norm(C.IcmpHeader{msg_type, code, c, rest})} : Result<&2, &2, N.NetError, C.IcmpHeader>}

law udp_put_parse:
  for +src_port: U32
  for +dst_port: U32
  for +length: U32
  for +checksum: U32
  for +payload: B.Octets
  for +c: U32
  {U.UdpHeader.parse(K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)) == Done{U.UdpHeader.norm(U.UdpHeader{src_port, dst_port, length, c})} : Result<&2, &2, N.NetError, U.UdpHeader>}

# with the length field the datagram's length, the payload reads back
law udp_put_payload:
  for +src_port: U32
  for +dst_port: U32
  for +length: U32
  for +checksum: U32
  for +payload: B.Octets
  for +c: U32
  for hl: {U32.to_nat(N.NetField.low(16n, length)) == Nat.add(8n, B.Octets.len(payload)) : Nat}
  {U.UdpHeader.payload(U.UdpHeader.norm(U.UdpHeader{src_port, dst_port, length, c}), K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)) == Done{payload} : Result<&2, &2, N.NetError, B.Octets>}

# Satisfiability: the hypotheses hold for some inputs (0xffff + 2 carries;
# a 2-byte payload under a length field of 10)
law inet_sum_sat:
  {(U32.is_le(65535, 65535), U32.is_le(2, 65535), U32.is_le(U32.add(65535, 2), 65535), U32.is_le(U32.add(1, 2), 65535), K.inet_even(B.Octets.of_list([1, 2])), Nat.is_le(Nat.double(1n), B.Octets.len(B.Octets.of_list([1, 2]))), Nat.is_eq(U32.to_nat(N.NetField.low(16n, 10)), Nat.add(8n, B.Octets.len(B.Octets.of_list([1, 2]))))) == (True{}, True{}, False{}, True{}, True{}, True{}, True{}) : Bool & Bool & Bool & Bool & Bool & Bool & Bool}

# The end-around carry as a vector: 0xffff + 2 = 0x0001 + 1 = 2
law inet_add_vector:
  {(K.inet_add(65535, 2), U32.sub(U32.add(65535, 2), 65535), K.inet_finish(4660)) == (2, 2, 60875) : U32 & U32 & U32}
