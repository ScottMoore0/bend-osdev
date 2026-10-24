# Packet-level answers of ICMP and UDP, for every input: the bytes a sender
# builds, checksum and all, are taken by the receiver for what was sent.
#
# * ICMP (icmp.bend): an echo request's or reply's bytes decode back to it
#   (identifier and sequence number being 16-bit fields); the bytes of an
#   echo request, received, are answered by the bytes of the echo reply
#   with the same identifier, sequence number and data; the bytes of an echo
#   reply are reported to the application.
# * UDP (udp.bend): a datagram built over IPv4 (checksum and all) with its
#   length field the datagram's length is passed on with its ports and data,
#   as Udp.receive delivers a datagram (udp_bound_delivers in LAWS.bend: to
#   the socket bound to its port).
#
# A pair of its own (PROOF_packet.bend): the proofs rest on
# bend-osdev-netheaders' checksum laws (its LAWS_sum.bend).
import Base
import ../bytes/bytes.bend as B
import ../netheaders/netheaders.bend as N
import ../netheaders/udp.bend as NU
import ./udp.bend as U
import ./icmp.bend as IC

law icmp_decode_request:
  for +id: U32
  for +seq: U32
  for +data: B.Octets
  {IC.Icmp.decode(IC.Icmp.encode(IC.IcmpEchoRequest{id, seq, data})) == Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}

law icmp_decode_reply:
  for +id: U32
  for +seq: U32
  for +data: B.Octets
  {IC.Icmp.decode(IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})) == Done{IC.IcmpEchoReply{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}

# RFC 792: an echo request's bytes are answered by an echo reply's bytes,
# to the sender, with the same identifier, sequence number and data
law icmp_echo_packet_answered:
  for +src: U32
  for +dst: U32
  for +id: U32
  for +seq: U32
  for +data: B.Octets
  {Pair.snd(IC.IcmpState, List<&2, IC.IcmpAction>, IC.Icmp.step(IC.IcmpState{IC.IcmpOptions{True{}}}, IC.IcmpRecv{src, dst, IC.Icmp.encode(IC.IcmpEchoRequest{id, seq, data})})) == [IC.IcmpOut{src, IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})}] : List<&2, IC.IcmpAction>}

# an echo reply's bytes (the answer to our ping) reach the application
law icmp_reply_packet_reported:
  for +st: IC.IcmpState
  for +src: U32
  for +dst: U32
  for +id: U32
  for +seq: U32
  for +data: B.Octets
  {Pair.snd(IC.IcmpState, List<&2, IC.IcmpAction>, IC.Icmp.step(st, IC.IcmpRecv{src, dst, IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})})) == [IC.IcmpEchoed{src, U32.and(id, 65535), U32.and(seq, 65535), data}] : List<&2, IC.IcmpAction>}

# a datagram built over IPv4 from src to dst, its length field the
# datagram's length, is received with its ports (16 bits) and data
law udp_packet_received:
  for +st: U.UdpState
  for +src: U32
  for +dst: U32
  for +sport: U32
  for +dport: U32
  for +length: U32
  for +checksum: U32
  for +data: B.Octets
  for hl: {U32.to_nat(N.NetField.low(16n, length)) == Nat.add(8n, B.Octets.len(data)) : Nat}
  {Pair.snd(U.UdpState, List<&2, U.UdpAction>, U.Udp.recv(st, src, dst, NU.UdpHeader.build_ipv4(src, dst, NU.UdpHeader{sport, dport, length, checksum}, data))) == U.Udp.receive(st, src, dst, N.NetField.low(16n, sport), N.NetField.low(16n, dport), data) : List<&2, U.UdpAction>}

# the hypothesis holds for the length field Udp.send writes (8 plus the
# data's length), here for three bytes of data
law udp_packet_received_sat:
  {U32.to_nat(N.NetField.low(16n, U32.add(8, U32.from_nat(B.Octets.len(B.Octets.of_string("hi!")))))) == Nat.add(8n, B.Octets.len(B.Octets.of_string("hi!"))) : Nat}
