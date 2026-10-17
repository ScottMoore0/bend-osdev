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

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def show_error(e: N.NetError) -> String:
  match e:
    case N.NetTruncated{}:
      "truncated"
    case N.NetBadVersion{}:
      "bad version"
    case N.NetBadIhl{}:
      "bad ihl"
    case N.NetBadDataOffset{}:
      "bad data offset"
    case N.NetBadArpFormat{}:
      "bad arp format"
    case N.NetBadLength{}:
      "bad length"
    case N.NetBadChecksum{}:
      "bad checksum"

def hex16(v: U32) -> String:
  B.Octets.hex(B.Octets.be16(v))

def hex32(v: U32) -> String:
  B.Octets.hex(B.Octets.be32(v))

def show_mac(m: E.MacAddr) -> String:
  B.Octets.hex(E.MacAddr.bytes(m))

def show_vlan(v: Maybe<&2, E.VlanTag>) -> String:
  match v:
    case None{}:
      "untagged"
    case Some{E.VlanTag{p, d, i}}:
      "vlan " ++ U32.show(i) ++ " pcp " ++ U32.show(p) ++ " dei " ++ U32.show(d)

def show_eth(r: Result<&2, &2, N.NetError, E.EthHeader>) -> String:
  match r:
    case Done{E.EthHeader{d, s, v, t}}:
      "eth " ++ show_mac(d) ++ " " ++ show_mac(s) ++ " " ++ show_vlan(v) ++ " type " ++ hex16(t)
    case Fail{e}:
      show_error(e)

def show_ipv4(r: Result<&2, &2, N.NetError, I4.Ipv4Header>) -> String:
  match r:
    case Done{I4.Ipv4Header{ver, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, s, d, o}}:
      "ipv4 v" ++ U32.show(ver) ++ " ihl " ++ U32.show(ihl) ++ " dscp " ++ U32.show(dscp) ++ " ecn " ++ U32.show(ecn) ++ " len " ++ U32.show(tl) ++ " id " ++ U32.show(id) ++ " flags " ++ U32.show(fl) ++ " frag " ++ U32.show(fo) ++ " ttl " ++ U32.show(ttl) ++ " proto " ++ U32.show(pr) ++ " sum " ++ hex16(ck) ++ " " ++ hex32(s) ++ " " ++ hex32(d) ++ " opts [" ++ B.Octets.hex(o) ++ "]"
    case Fail{e}:
      show_error(e)

def show_ipv6(r: Result<&2, &2, N.NetError, I6.Ipv6Header>) -> String:
  match r:
    case Done{I6.Ipv6Header{ver, tc, fl, pl, nh, hop, s, d}}:
      "ipv6 v" ++ U32.show(ver) ++ " tc " ++ U32.show(tc) ++ " flow " ++ U32.show(fl) ++ " len " ++ U32.show(pl) ++ " next " ++ U32.show(nh) ++ " hop " ++ U32.show(hop) ++ " " ++ B.Octets.hex(I6.Ipv6Addr.bytes(s)) ++ " " ++ B.Octets.hex(I6.Ipv6Addr.bytes(d))
    case Fail{e}:
      show_error(e)

def show_udp(r: Result<&2, &2, N.NetError, U.UdpHeader>) -> String:
  match r:
    case Done{U.UdpHeader{a, b, c, d}}:
      "udp " ++ U32.show(a) ++ " " ++ U32.show(b) ++ " len " ++ U32.show(c) ++ " sum " ++ hex16(d)
    case Fail{e}:
      show_error(e)

def show_tcp(r: Result<&2, &2, N.NetError, T.TcpHeader>) -> String:
  match r:
    case Done{T.TcpHeader{sp, dp, sq, ak, off, rs, fl, win, ck, ur, o}}:
      "tcp " ++ U32.show(sp) ++ " " ++ U32.show(dp) ++ " seq " ++ U32.show(sq) ++ " ack " ++ U32.show(ak) ++ " off " ++ U32.show(off) ++ " rsv " ++ U32.show(rs) ++ " flags " ++ U32.show(fl) ++ " win " ++ U32.show(win) ++ " sum " ++ hex16(ck) ++ " urg " ++ U32.show(ur) ++ " opts [" ++ B.Octets.hex(o) ++ "]"
    case Fail{e}:
      show_error(e)

def show_icmp(r: Result<&2, &2, N.NetError, C.IcmpHeader>) -> String:
  match r:
    case Done{C.IcmpHeader{t, c, k, x}}:
      "icmp " ++ U32.show(t) ++ " " ++ U32.show(c) ++ " sum " ++ hex16(k) ++ " " ++ hex32(x)
    case Fail{e}:
      show_error(e)

def show_arp(r: Result<&2, &2, N.NetError, A.ArpPacket>) -> String:
  match r:
    case Done{A.ArpPacket{o, sha, spa, tha, tpa}}:
      "arp " ++ U32.show(o) ++ " " ++ show_mac(sha) ++ " " ++ hex32(spa) ++ " " ++ show_mac(tha) ++ " " ++ hex32(tpa)
    case Fail{e}:
      show_error(e)

def show_bytes(r: Result<&2, &2, N.NetError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      show_error(e)

# 10.0.0.1, 10.0.0.2, 2001:db8::1, 2001:db8::2
def a4() -> U32:
  167772161

def b4() -> U32:
  167772162

def a6() -> I6.Ipv6Addr:
  I6.Ipv6Addr{536939960, 0, 0, 1}

def b6() -> I6.Ipv6Addr:
  I6.Ipv6Addr{536939960, 0, 0, 2}

def mac1() -> E.MacAddr:
  E.MacAddr{2, 0, 0, 0, 0, 1}

def mac2() -> E.MacAddr:
  E.MacAddr{2, 0, 0, 0, 0, 2}

# a UDP datagram "hi!" from port 1234 to 53, with its checksum
def udp4() -> B.Octets:
  U.UdpHeader.build_ipv4(a4(), b4(), U.UdpHeader{1234, 53, 11, 0}, B.Octets.of_string("hi!"))

# the IPv4 packet that carries it
def ip4() -> B.Octets:
  B.Octets.append(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, 5, 0, 0, 31, 1, 2, 0, 64, 17, 0, a4(), b4(), B.Octets.empty()}), udp4())

# the Ethernet frame, VLAN 100, priority 5, that carries that
def frame() -> B.Octets:
  B.Octets.append(E.EthHeader.build(E.EthHeader{mac2(), mac1(), Some{E.VlanTag{5, 0, 100}}, 2048}), ip4())

def tcp6() -> B.Octets:
  T.TcpHeader.build_ipv6(a6(), b6(), T.TcpHeader{49152, 443, 305419896, 2596069104, 6, 0, 24, 1024, 0, 0, B.Octets.of_list([1, 1, 4, 2])}, B.Octets.of_string("GET"))

def ping6() -> B.Octets:
  C.IcmpHeader.build_ipv6(a6(), b6(), C.IcmpHeader{128, 0, 0, 65537}, B.Octets.of_string("ab"))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(hex16(K.inet_sum(B.Octets.of_list([0, 1, 242, 3, 244, 245, 246, 247]))))
    IO.print(hex16(K.inet_checksum(B.Octets.of_list([0, 1, 242, 3, 244, 245, 246, 247]))))
    IO.print(B.Octets.hex(frame()))
    IO.print(show_eth(E.EthHeader.parse(frame())))
    IO.print(show_ipv4(I4.Ipv4Header.parse_verified(B.Octets.drop(18n, frame()))))
    IO.print(show_bytes(I4.Ipv4Header.payload(I4.Ipv4Header{4, 5, 0, 0, 31, 1, 2, 0, 64, 17, 0, a4(), b4(), B.Octets.empty()}, ip4())))
    IO.print(show_udp(U.UdpHeader.parse(udp4())))
    IO.print(show_bool(U.UdpHeader.verify_ipv4(a4(), b4(), udp4())))
    IO.print(show_bool(U.UdpHeader.verify_ipv4(b4(), b4(), udp4())))
    IO.print(B.Octets.hex(tcp6()))
    IO.print(show_tcp(T.TcpHeader.parse(tcp6())))
    IO.print(show_bool(T.TcpHeader.verify_ipv6(a6(), b6(), tcp6())))
    IO.print(B.Octets.hex(I6.Ipv6Header.build(I6.Ipv6Header{6, 184, 74565, 27, 6, 64, a6(), b6()})))
    IO.print(show_ipv6(I6.Ipv6Header.parse(I6.Ipv6Header.build(I6.Ipv6Header{6, 184, 74565, 27, 6, 64, a6(), b6()}))))
    IO.print(B.Octets.hex(A.ArpPacket.build(A.ArpPacket{1, mac1(), a4(), E.MacAddr{0, 0, 0, 0, 0, 0}, b4()})))
    IO.print(show_arp(A.ArpPacket.parse(A.ArpPacket.build(A.ArpPacket{2, mac2(), b4(), mac1(), a4()}))))
    IO.print(B.Octets.hex(C.IcmpHeader.build_checksum(C.IcmpHeader{8, 0, 0, 65537}, B.Octets.of_string("abcd"))))
    IO.print(show_icmp(C.IcmpHeader.parse(ping6())))
    IO.print(show_bool(C.IcmpHeader.verify_ipv6(a6(), b6(), ping6())))
    IO.print(show_udp(U.UdpHeader.parse(B.Octets.of_list([0, 1, 0, 2, 0, 8]))))
    IO.print(show_eth(E.EthHeader.parse(B.Octets.zeros(13n))))
    IO.print(show_tcp(T.TcpHeader.parse(B.Octets.of_list([0, 80, 0, 80, 0, 0, 0, 1, 0, 0, 0, 0, 64, 2, 255, 255, 0, 0, 0, 0]))))

#|ddf2
#|220d
#|0200000000020200000000018100a06408004500001f00014000401126cb0a0000010a00000204d20035000b5d65686921
#|eth 020000000002 020000000001 vlan 100 pcp 5 dei 0 type 0800
#|ipv4 v4 ihl 5 dscp 0 ecn 0 len 31 id 1 flags 2 frag 0 ttl 64 proto 17 sum 26cb 0a000001 0a000002 opts []
#|04d20035000b5d65686921
#|udp 1234 53 len 11 sum 5d65
#|true
#|false
#|c00001bb123456789abcdef060180400fbf2000001010402474554
#|tcp 49152 443 seq 305419896 ack 2596069104 off 6 rsv 0 flags 24 win 1024 sum fbf2 urg 0 opts [01010402]
#|true
#|6b812345001b064020010db800000000000000000000000120010db8000000000000000000000002
#|ipv6 v6 tc 184 flow 74565 len 27 next 6 hop 64 20010db8000000000000000000000001 20010db8000000000000000000000002
#|00010800060400010200000000010a0000010000000000000a000002
#|arp 2 020000000002 0a000002 020000000001 0a000001
#|080033370001000161626364
#|icmp 128 0 sum c2e1 00010001
#|true
#|truncated
#|truncated
#|bad data offset
