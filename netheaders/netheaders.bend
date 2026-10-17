# bend-osdev-netheaders: the binary headers of Ethernet II with an optional
# 802.1Q tag (ethernet.bend), ARP (arp.bend), IPv4 (ipv4.bend), IPv6
# (ipv6.bend), ICMP and ICMPv6 (icmp.bend), UDP (udp.bend) and TCP (tcp.bend),
# and the Internet checksum (checksum.bend).
#
# This file is what they share: the error type every parser answers, and the
# bit fields of a 32-bit word that the headers are packed from.
#
# Every header has a record type X, and:
#   X.parse(o)   the header at the start of the Octets o: Done{header}, or
#                Fail{error} if o is too short or the header is malformed;
#   X.length(h)  the header's length in bytes, where the payload starts
#                (UdpHeader.header_length, UDP's length being a field);
#   X.build(h)   the header's bytes, each field masked to its width;
#   X.norm(h)    h with every field masked to its width: what parse gives back
#                for build(h).
#
# The field readers and writers work by bit slicing, so that the round trips
# can be proved for every value.
import Base
import ../bytes/bytes.bend as B

# Why a parse fails
type NetError is Data:
  # fewer bytes than the header needs
  NetTruncated{}
  # IPv4 not version 4, IPv6 not version 6
  NetBadVersion{}
  # an IPv4 IHL below 5
  NetBadIhl{}
  # a TCP data offset below 5
  NetBadDataOffset{}
  # an ARP packet that is not for IPv4 over Ethernet
  NetBadArpFormat{}
  # a length field shorter than its own header (IPv4 total length, UDP length)
  NetBadLength{}
  # a checksum that does not verify
  NetBadChecksum{}

# Bit fields of a 32-bit word (bit 0 is the least significant)

# the low k bits of an n-bit word; the others zero
def NetField.keep(n: Nat, k: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+m:
      match k:
        case 0n:
          Word.zero(1n+m)
        case 1n+j:
          match w:
            case WCon{b, t}:
              WCon{b, NetField.keep(m, j, t)}

# the low k bits of v
def NetField.low(k: Nat, v: U32) -> U32:
  match v:
    case U32{w}:
      U32{NetField.keep(32n, k, w)}

# the k bits of v from bit p up, as a number
def NetField.get(v: U32, p: Nat, k: Nat) -> U32:
  NetField.low(k, U32.shrn(v, p))

# w with bits p .. p+k-1 taken from x (x already shifted to bit p)
def NetField.put.go(n: Nat, p: Nat, k: Nat, w: Word(n), x: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+m:
      match p:
        case 1n+q:
          match w x:
            case WCon{a, wt} WCon{b, xt}:
              WCon{a, NetField.put.go(m, q, k, wt, xt)}
        case 0n:
          match k:
            case 0n:
              match w x:
                case WCon{a, wt} WCon{b, xt}:
                  WCon{a, NetField.put.go(m, 0n, 0n, wt, xt)}
            case 1n+j:
              match w x:
                case WCon{a, wt} WCon{b, xt}:
                  WCon{b, NetField.put.go(m, 0n, j, wt, xt)}

def NetField.put.word(p: Nat, k: Nat, v: U32, x: U32) -> U32:
  match v x:
    case U32{w} U32{y}:
      U32{NetField.put.go(32n, p, k, w, y)}

# v with its k bits from bit p up replaced by the low k bits of x
def NetField.put(+p: Nat, +k: Nat, x: U32, v: U32) -> U32:
  NetField.put.word(p, k, v, U32.shln(NetField.low(k, x), p))

# Internal helpers shared by the header files

# whether xs has at least n bytes
def net.has(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      match xs:
        case Nil{}:
          False{}
        case Con{h, t}:
          net.has(m, t)

# the number of bytes of o, as a U32
def net.len32(o: B.Octets) -> U32:
  U32.from_nat(B.Octets.len(o))

# Done{x} if ok, else Fail{e}
def net.check(-A: Data, ok: Bool, e: NetError, x: A) -> Result<&2, &2, NetError, A>:
  match ok:
    case True{}:
      Done{x}
    case False{}:
      Fail{e}

# n bytes of o from offset i, if o has them
def net.slice(+i: Nat, +n: Nat, +o: B.Octets) -> Result<&2, &2, NetError, B.Octets>:
  net.check(B.Octets, Nat.is_le(Nat.add(i, n), B.Octets.len(o)), NetTruncated{}, B.Octets.slice(i, n, o))
