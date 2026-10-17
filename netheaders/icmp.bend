# ICMP (RFC 792) and ICMPv6 (RFC 4443): the same 8-byte header. The ICMP
# checksum covers the message; the ICMPv6 checksum also covers the IPv6
# pseudo-header, with next header 58.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ipv6.bend as I6

# type, code, checksum, and the four bytes after them as one 32-bit word
# (their meaning depends on the type: identifier and sequence number for an
# echo, a pointer, an MTU, or unused)
type IcmpHeader is Data:
  IcmpHeader{msg_type: U32, code: U32, checksum: U32, rest_of_header: U32}

def IcmpHeader.norm(h: IcmpHeader) -> IcmpHeader:
  match h:
    case IcmpHeader{t, c, k, r}:
      IcmpHeader{N.NetField.low(8n, t), N.NetField.low(8n, c), N.NetField.low(16n, k), r}

def IcmpHeader.build.list(h: IcmpHeader) -> List<&2, U32>:
  match h:
    case IcmpHeader{t, c, k, r}:
      B.append(B.be32(N.NetField.put(24n, 8n, t, N.NetField.put(16n, 8n, c, N.NetField.low(16n, k)))), B.be32(r))

def IcmpHeader.build(h: IcmpHeader) -> B.Octets:
  B.Octets.of_list(IcmpHeader.build.list(h))

def IcmpHeader.make(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>) -> Result<&2, &2, N.NetError, IcmpHeader>:
  match m0 m1:
    case Some{+w0} Some{r}:
      Done{IcmpHeader{N.NetField.get(w0, 24n, 8n), N.NetField.get(w0, 16n, 8n), N.NetField.get(w0, 0n, 16n), r}}
    case _ _:
      Fail{N.NetTruncated{}}

def IcmpHeader.parse.list(+xs: List<&2, U32>) -> Result<&2, &2, N.NetError, IcmpHeader>:
  IcmpHeader.make(B.be32_at(xs, 0n), B.be32_at(xs, 4n))

# the header at the start of o; NetTruncated if o is shorter than 8 bytes
def IcmpHeader.parse(o: B.Octets) -> Result<&2, &2, N.NetError, IcmpHeader>:
  IcmpHeader.parse.list(B.Octets.to_list(o))

def IcmpHeader.length(h: IcmpHeader) -> Nat:
  8n

# ICMP: the message (header and data) with its checksum
def IcmpHeader.build_checksum(h: IcmpHeader, data: B.Octets) -> B.Octets:
  K.inet_fill(B.Octets.empty(), B.Octets.append(IcmpHeader.build(h), data), 2n)

# whether an ICMP message's checksum verifies
def IcmpHeader.verify(msg: B.Octets) -> Bool:
  K.inet_verify(msg)

# ICMPv6: the message with its checksum over the pseudo-header from src to dst
def IcmpHeader.build_ipv6(src: I6.Ipv6Addr, dst: I6.Ipv6Addr, h: IcmpHeader, data: B.Octets) -> B.Octets:
  +msg = B.Octets.append(IcmpHeader.build(h), data)
  K.inet_fill(I6.ipv6_pseudo(src, dst, N.net.len32(msg), 58), msg, 2n)

def IcmpHeader.verify_ipv6(src: I6.Ipv6Addr, dst: I6.Ipv6Addr, +msg: B.Octets) -> Bool:
  K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, N.net.len32(msg), 58), msg))

# Common types
def IcmpHeader.ECHO_REPLY() -> U32:
  0

def IcmpHeader.ECHO_REQUEST() -> U32:
  8

def IcmpHeader.ECHO6_REQUEST() -> U32:
  128

def IcmpHeader.ECHO6_REPLY() -> U32:
  129
