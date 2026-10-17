#!/usr/bin/env python3
"""Differential test cases for bend-osdev-netheaders.

Writes ref/cases.bend (a Bend program that builds, parses and checksums
headers) and ref/expected.txt (the same results from an independent Python
implementation: struct packing and unpacking written from the header layouts
in the RFCs and IEEE 802.3 / 802.1Q, socket.inet_pton for addresses, and an
Internet checksum written from RFC 1071).

Both directions are tested: Bend builds from random field values (some with
bits above a field's width, which both sides must drop) and Python packs the
same; Python packs random headers (followed by random bytes) and Bend parses
them; malformed and truncated inputs must fail with the same error.
"""
import os, random, socket, struct, sys

# ---- the independent implementation

def inet_sum(data):
    if len(data) % 2:
        data += b"\0"
    s = 0
    for i in range(0, len(data), 2):
        s += (data[i] << 8) | data[i + 1]
    while s >> 16:
        s = (s & 0xFFFF) + (s >> 16)
    return s

def inet_checksum(data):
    return ~inet_sum(data) & 0xFFFF

def pseudo4(src, dst, proto, n):
    return struct.pack("!IIBBH", src, dst, 0, proto, n)

def pseudo6(src, dst, n, nxt):
    return src + dst + struct.pack("!I3xB", n, nxt)

def put16(b, off, v):
    return b[:off] + struct.pack("!H", v) + b[off + 2:]

M = lambda k: (1 << k) - 1

def eth_pack(d, s, vlan, et):
    out = bytes(d) + bytes(s)
    if vlan is not None:
        p, de, v = vlan
        out += struct.pack("!HH", 0x8100, (p & 7) << 13 | (de & 1) << 12 | (v & 0xFFF))
    return out + struct.pack("!H", et & 0xFFFF)

def mac_hex(m):
    return bytes(m).hex()

def eth_show(b):
    if len(b) < 14:
        return "truncated"
    et = struct.unpack("!H", b[12:14])[0]
    if et == 0x8100:
        if len(b) < 18:
            return "truncated"
        tci, et2 = struct.unpack("!HH", b[14:18])
        v = "vlan %d pcp %d dei %d" % (tci & 0xFFF, tci >> 13, tci >> 12 & 1)
        return "eth %s %s %s type %04x" % (b[0:6].hex(), b[6:12].hex(), v, et2)
    return "eth %s %s untagged type %04x" % (b[0:6].hex(), b[6:12].hex(), et)

def arp_pack(op, sha, spa, tha, tpa, hlen=6):
    return struct.pack("!HHBBH", 1, 0x0800, hlen, 4, op & 0xFFFF) + bytes(sha) + struct.pack("!I", spa) + bytes(tha) + struct.pack("!I", tpa)

def arp_show(b):
    if len(b) < 28:
        return "truncated"
    ht, pt, hl, pl, op = struct.unpack("!HHBBH", b[:8])
    if (ht, pt, hl, pl) != (1, 0x0800, 6, 4):
        return "bad arp format"
    return "arp %d %s %s %s %s" % (op, b[8:14].hex(), b[14:18].hex(), b[18:24].hex(), b[24:28].hex())

def ipv4_pack(ver, ihl, dscp, ecn, tl, ident, fl, fo, ttl, pr, ck, src, dst, opts):
    return struct.pack("!BBHHHBBHII", (ver & 15) << 4 | (ihl & 15), (dscp & 63) << 2 | (ecn & 3), tl & 0xFFFF,
                       ident & 0xFFFF, (fl & 7) << 13 | (fo & 0x1FFF), ttl & 255, pr & 255, ck & 0xFFFF, src, dst) + bytes(opts)

def ipv4_show(b):
    if len(b) < 20:
        return "truncated"
    vi, tos, tl, ident, ff, ttl, pr, ck, src, dst = struct.unpack("!BBHHHBBHII", b[:20])
    ver, ihl = vi >> 4, vi & 15
    if ver != 4:
        return "bad version"
    if ihl < 5:
        return "bad ihl"
    if len(b) < ihl * 4:
        return "truncated"
    return ("ipv4 v%d ihl %d dscp %d ecn %d len %d id %d flags %d frag %d ttl %d proto %d sum %04x %08x %08x opts [%s]"
            % (ver, ihl, tos >> 2, tos & 3, tl, ident, ff >> 13, ff & 0x1FFF, ttl, pr, ck, src, dst, b[20:ihl * 4].hex()))

def ipv6_pack(ver, tc, fl, pl, nh, hop, src, dst):
    return struct.pack("!IHBB", (ver & 15) << 28 | (tc & 255) << 20 | (fl & 0xFFFFF), pl & 0xFFFF, nh & 255, hop & 255) + src + dst

def ipv6_show(b):
    if len(b) < 40:
        return "truncated"
    w0, pl, nh, hop = struct.unpack("!IHBB", b[:8])
    if w0 >> 28 != 6:
        return "bad version"
    return "ipv6 v6 tc %d flow %d len %d next %d hop %d %s %s" % (w0 >> 20 & 255, w0 & 0xFFFFF, pl, nh, hop, b[8:24].hex(), b[24:40].hex())

def icmp_pack(t, c, k, r):
    return struct.pack("!BBHI", t & 255, c & 255, k & 0xFFFF, r)

def icmp_show(b):
    if len(b) < 8:
        return "truncated"
    t, c, k, r = struct.unpack("!BBHI", b[:8])
    return "icmp %d %d sum %04x %08x" % (t, c, k, r)

def udp_pack(a, b_, n, k):
    return struct.pack("!HHHH", a & 0xFFFF, b_ & 0xFFFF, n & 0xFFFF, k & 0xFFFF)

def udp_show(b):
    if len(b) < 8:
        return "truncated"
    return "udp %d %d len %d sum %04x" % struct.unpack("!HHHH", b[:8])

def tcp_pack(sp, dp, sq, ak, off, rs, fl, win, ck, ur, opts):
    return struct.pack("!HHIIBBHHH", sp & 0xFFFF, dp & 0xFFFF, sq, ak, (off & 15) << 4 | (rs & 15), fl & 255,
                       win & 0xFFFF, ck & 0xFFFF, ur & 0xFFFF) + bytes(opts)

def tcp_show(b):
    if len(b) < 20:
        return "truncated"
    sp, dp, sq, ak, orr, fl, win, ck, ur = struct.unpack("!HHIIBBHHH", b[:20])
    off = orr >> 4
    if off < 5:
        return "bad data offset"
    if len(b) < off * 4:
        return "truncated"
    return ("tcp %d %d seq %d ack %d off %d rsv %d flags %d win %d sum %04x urg %d opts [%s]"
            % (sp, dp, sq, ak, off, orr & 15, fl, win, ck, ur, b[20:off * 4].hex()))

def udp_with_checksum(pseudo, dg):
    c = inet_checksum(pseudo + put16(dg, 6, 0))
    return put16(dg, 6, c or 0xFFFF)

def with_checksum(pseudo, b, off):
    return put16(b, off, inet_checksum(pseudo + put16(b, off, 0)))

# ---- the Bend side

PRELUDE = r'''import Base
import ../../bytes/bytes.bend as B
import ../netheaders.bend as N
import ../checksum.bend as K
import ../ethernet.bend as E
import ../arp.bend as A
import ../ipv4.bend as I4
import ../ipv6.bend as I6
import ../icmp.bend as C
import ../udp.bend as U
import ../tcp.bend as T

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

'''

def blist(b):
    return "B.Octets.of_list([" + ", ".join(str(x) for x in b) + "])"

def bmac(m):
    return "E.MacAddr{%s}" % ", ".join(str(x) for x in m)

def bv6(a):
    return "I6.Ipv6Addr{%s}" % ", ".join(str(w) for w in struct.unpack("!IIII", a))

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    R = rng.randrange
    lines, expect = [], []

    def case(label, bend_expr, want):
        lines.append('    IO.print("%s " ++ %s)' % (label, bend_expr))
        expect.append("%s %s" % (label, want))

    def junk(k, extra=8):
        """a k-bit field value, sometimes with junk above bit k"""
        return R(1 << (k + extra)) if R(4) == 0 else R(1 << k)

    def rbytes(n):
        return bytes(R(256) for _ in range(n))

    def v4addr():
        return struct.unpack("!I", socket.inet_pton(socket.AF_INET, "%d.%d.%d.%d" % tuple(R(256) for _ in range(4))))[0]

    def v6addr():
        return socket.inet_pton(socket.AF_INET6, ":".join("%x" % R(65536) for _ in range(8)))

    N_ = 24
    for k in range(N_):
        # Ethernet: build from fields, parse packed bytes
        d, s = [R(256) for _ in range(6)], [R(256) for _ in range(6)]
        vlan = (junk(3), junk(1), junk(12)) if R(2) else None
        et = junk(16)
        if vlan is None and et & 0xFFFF == 0x8100:
            et = 0x0800
        bv = "None{}" if vlan is None else "Some{E.VlanTag{%d, %d, %d}}" % vlan
        h = "E.EthHeader{%s, %s, %s, %d}" % (bmac(d), bmac(s), bv, et)
        case("eth_build %d" % k, "B.Octets.hex(E.EthHeader.build(%s))" % h, eth_pack(d, s, vlan, et).hex())
        raw = eth_pack(d, s, vlan, et) + rbytes(R(6))
        if R(5) == 0:
            raw = raw[:R(len(raw))]
        case("eth_parse %d" % k, "show_eth(E.EthHeader.parse(%s))" % blist(raw), eth_show(raw))

        # ARP
        op, sha, spa, tha, tpa = junk(16), [R(256) for _ in range(6)], v4addr(), [R(256) for _ in range(6)], v4addr()
        h = "A.ArpPacket{%d, %s, %d, %s, %d}" % (op, bmac(sha), spa, bmac(tha), tpa)
        case("arp_build %d" % k, "B.Octets.hex(A.ArpPacket.build(%s))" % h, arp_pack(op, sha, spa, tha, tpa).hex())
        raw = arp_pack(op, sha, spa, tha, tpa, 6 if R(4) else R(256)) + rbytes(R(4))
        if R(5) == 0:
            raw = raw[:R(len(raw))]
        case("arp_parse %d" % k, "show_arp(A.ArpPacket.parse(%s))" % blist(raw), arp_show(raw))

        # IPv4: every IHL, options of the matching length
        ihl = 5 + R(11)
        opts = rbytes(4 * (ihl - 5))
        f = [4, ihl, junk(6), junk(2), junk(16), junk(16), junk(3), junk(13), junk(8), junk(8), junk(16), v4addr(), v4addr()]
        h = "I4.Ipv4Header{%s, %s}" % (", ".join(str(x) for x in f), blist(opts))
        case("ipv4_build %d" % k, "B.Octets.hex(I4.Ipv4Header.build(%s))" % h, ipv4_pack(*f, opts).hex())
        hdr = ipv4_pack(*f, opts)
        case("ipv4_checksum %d" % k, "B.Octets.hex(I4.Ipv4Header.build_checksum(%s))" % h, with_checksum(b"", hdr, 10).hex())
        case("ipv4_verified %d" % k, "show_ipv4(I4.Ipv4Header.parse_verified(I4.Ipv4Header.build_checksum(%s)))" % h,
             ipv4_show(with_checksum(b"", hdr, 10)))
        g = list(f)
        r = R(8)
        if r == 0:
            g[0] = R(16)
        elif r == 1:
            g[1] = R(5)
        raw = ipv4_pack(*g, opts) + rbytes(R(6))
        if R(6) == 0:
            raw = raw[:R(len(raw))]
        case("ipv4_parse %d" % k, "show_ipv4(I4.Ipv4Header.parse(%s))" % blist(raw), ipv4_show(raw))
        bad = bytearray(with_checksum(b"", hdr, 10))
        bad[R(len(bad))] ^= 1 << R(8)
        bi = bad[0] & 15
        want = "true" if bad[0] >> 4 == 4 and bi >= 5 and len(bad) >= 4 * bi and inet_sum(bytes(bad[:4 * bi])) == 0xFFFF else "false"
        case("ipv4_verify_bad %d" % k, "show_bool(I4.Ipv4Header.verify(%s))" % blist(bad), want)

        # IPv6
        src, dst = v6addr(), v6addr()
        f6 = [6, junk(8), junk(20), junk(16), junk(8), junk(8)]
        h = "I6.Ipv6Header{%s, %s, %s}" % (", ".join(str(x) for x in f6), bv6(src), bv6(dst))
        case("ipv6_build %d" % k, "B.Octets.hex(I6.Ipv6Header.build(%s))" % h, ipv6_pack(*f6, src, dst).hex())
        g6 = list(f6)
        if R(6) == 0:
            g6[0] = R(16)
        raw = ipv6_pack(*g6, src, dst) + rbytes(R(4))
        if R(6) == 0:
            raw = raw[:R(len(raw))]
        case("ipv6_parse %d" % k, "show_ipv6(I6.Ipv6Header.parse(%s))" % blist(raw), ipv6_show(raw))

        # ICMP and ICMPv6
        t, c, rh, data = junk(8), junk(8), R(1 << 32), rbytes(R(24))
        h = "C.IcmpHeader{%d, %d, %d, %d}" % (t, c, R(1 << 16), rh)
        msg = icmp_pack(t, c, 0, rh) + data
        case("icmp_build %d" % k, "B.Octets.hex(C.IcmpHeader.build_checksum(%s, %s))" % (h, blist(data)), with_checksum(b"", msg, 2).hex())
        case("icmp6_build %d" % k, "B.Octets.hex(C.IcmpHeader.build_ipv6(%s, %s, %s, %s))" % (bv6(src), bv6(dst), h, blist(data)),
             with_checksum(pseudo6(src, dst, len(msg), 58), msg, 2).hex())
        raw = with_checksum(b"", msg, 2)
        cut = raw[:R(12)] if R(5) == 0 else raw
        case("icmp_parse %d" % k, "show_icmp(C.IcmpHeader.parse(%s))" % blist(cut), icmp_show(cut))
        case("icmp_verify %d" % k, "show_bool(C.IcmpHeader.verify(%s))" % blist(raw), "true")
        m6 = with_checksum(pseudo6(src, dst, len(msg), 58), msg, 2)
        case("icmp6_verify %d" % k, "show_bool(C.IcmpHeader.verify_ipv6(%s, %s, %s))" % (bv6(src), bv6(dst), blist(m6)), "true")

        # UDP over IPv4 and IPv6
        a4, b4 = v4addr(), v4addr()
        sp, dp, payload = junk(16), junk(16), rbytes(R(40))
        n = 8 + len(payload)
        h = "U.UdpHeader{%d, %d, %d, %d}" % (sp, dp, n, R(1 << 16))
        dg = udp_pack(sp, dp, n, 0) + payload
        w4 = udp_with_checksum(pseudo4(a4, b4, 17, n), dg)
        w6 = udp_with_checksum(pseudo6(src, dst, n, 17), dg)
        case("udp4_build %d" % k, "B.Octets.hex(U.UdpHeader.build_ipv4(%d, %d, %s, %s))" % (a4, b4, h, blist(payload)), w4.hex())
        case("udp6_build %d" % k, "B.Octets.hex(U.UdpHeader.build_ipv6(%s, %s, %s, %s))" % (bv6(src), bv6(dst), h, blist(payload)), w6.hex())
        case("udp_parse %d" % k, "show_udp(U.UdpHeader.parse(%s))" % blist(w4), udp_show(w4))
        case("udp4_verify %d" % k, "show_bool(U.UdpHeader.verify_ipv4(%d, %d, %s))" % (a4, b4, blist(w4)), "true")
        bad = bytearray(w6)
        bad[R(len(bad))] ^= 1 << R(8)
        ok = struct.unpack("!H", bad[6:8])[0] != 0 and inet_sum(pseudo6(src, dst, n, 17) + bytes(bad)) == 0xFFFF
        case("udp6_verify_bad %d" % k, "show_bool(U.UdpHeader.verify_ipv6(%s, %s, %s))" % (bv6(src), bv6(dst), blist(bad)), "true" if ok else "false")

        # TCP over IPv4 and IPv6
        off = 5 + R(11)
        topts = rbytes(4 * (off - 5))
        ft = [junk(16), junk(16), R(1 << 32), R(1 << 32), off, junk(4), junk(8), junk(16), R(1 << 16), junk(16)]
        h = "T.TcpHeader{%s, %s}" % (", ".join(str(x) for x in ft), blist(topts))
        payload = rbytes(R(30))
        seg = tcp_pack(*ft, topts) + payload
        case("tcp_build %d" % k, "B.Octets.hex(T.TcpHeader.build(%s))" % h, tcp_pack(*ft, topts).hex())
        t4 = with_checksum(pseudo4(a4, b4, 6, len(seg)), seg, 16)
        t6 = with_checksum(pseudo6(src, dst, len(seg), 6), seg, 16)
        case("tcp4_build %d" % k, "B.Octets.hex(T.TcpHeader.build_ipv4(%d, %d, %s, %s))" % (a4, b4, h, blist(payload)), t4.hex())
        case("tcp6_build %d" % k, "B.Octets.hex(T.TcpHeader.build_ipv6(%s, %s, %s, %s))" % (bv6(src), bv6(dst), h, blist(payload)), t6.hex())
        gt = list(ft)
        if R(6) == 0:
            gt[4] = R(5)
        raw = tcp_pack(*gt, topts) + payload
        if R(6) == 0:
            raw = raw[:R(len(raw))]
        case("tcp_parse %d" % k, "show_tcp(T.TcpHeader.parse(%s))" % blist(raw), tcp_show(raw))
        case("tcp4_verify %d" % k, "show_bool(T.TcpHeader.verify_ipv4(%d, %d, %s))" % (a4, b4, blist(t4)), "true")
        bad = bytearray(t4)
        bad[R(len(bad))] ^= 1 << R(8)
        ok = inet_sum(pseudo4(a4, b4, 6, len(seg)) + bytes(bad)) == 0xFFFF
        case("tcp4_verify_bad %d" % k, "show_bool(T.TcpHeader.verify_ipv4(%d, %d, %s))" % (a4, b4, blist(bad)), "true" if ok else "false")

        # the checksum alone, and in two pieces split at an even length
        data = rbytes(R(80))
        case("inet %d" % k, "hex16(K.inet_checksum(%s))" % blist(data), "%04x" % inet_checksum(data))
        cut = 2 * R(len(data) // 2 + 1)
        case("inet_pieces %d" % k, "hex16(K.inet_finish(K.inet_update(K.inet_update(K.inet_start(), %s), %s)))" % (blist(data[:cut]), blist(data[cut:])),
             "%04x" % inet_checksum(data))

    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PRELUDE)
        # a long do block nests deeply: 40 steps to a part
        parts = [lines[i:i + 40] for i in range(0, len(lines), 40)]
        for i, part in enumerate(parts):
            f.write("def part%d() -> IO(Unit):\n  do IO<Unit>:\n" % i + "\n".join(part) + "\n\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    part%d()" % i for i in range(len(parts))) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
