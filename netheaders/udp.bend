# UDP (RFC 768): the 8-byte header, and its checksum over the IPv4
# pseudo-header (RFC 768) or the IPv6 pseudo-header (RFC 8200 section 8.1),
# protocol / next header 17.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ipv4.bend as I4
import ./ipv6.bend as I6

type UdpHeader is Data:
  UdpHeader{src_port: U32, dst_port: U32, length: U32, checksum: U32}

def UdpHeader.norm(h: UdpHeader) -> UdpHeader:
  match h:
    case UdpHeader{a, b, c, d}:
      UdpHeader{N.NetField.low(16n, a), N.NetField.low(16n, b), N.NetField.low(16n, c), N.NetField.low(16n, d)}

def UdpHeader.build.list(h: UdpHeader) -> List<&2, U32>:
  match h:
    case UdpHeader{a, b, c, d}:
      B.append(B.be16(a), B.append(B.be16(b), B.append(B.be16(c), B.be16(d))))

def UdpHeader.build(h: UdpHeader) -> B.Octets:
  B.Octets.of_list(UdpHeader.build.list(h))

def UdpHeader.make(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, m3: Maybe<&2, U32>) -> Result<&2, &2, N.NetError, UdpHeader>:
  match m0 m1 m2 m3:
    case Some{a} Some{b} Some{c} Some{d}:
      Done{UdpHeader{a, b, c, d}}
    case _ _ _ _:
      Fail{N.NetTruncated{}}

def UdpHeader.parse.list(+xs: List<&2, U32>) -> Result<&2, &2, N.NetError, UdpHeader>:
  UdpHeader.make(B.be16_at(xs, 0n), B.be16_at(xs, 2n), B.be16_at(xs, 4n), B.be16_at(xs, 6n))

# the header at the start of o; NetTruncated if o is shorter than 8 bytes
def UdpHeader.parse(o: B.Octets) -> Result<&2, &2, N.NetError, UdpHeader>:
  UdpHeader.parse.list(B.Octets.to_list(o))

# the header's length in bytes (the length field is the datagram's)
def UdpHeader.header_length(h: UdpHeader) -> Nat:
  8n

def UdpHeader.payload.go(ok: Bool, +n: Nat, +dg: B.Octets) -> Result<&2, &2, N.NetError, B.Octets>:
  match ok:
    case True{}:
      N.net.slice(8n, n, dg)
    case False{}:
      Fail{N.NetBadLength{}}

# the payload of the datagram (header first) whose header is h: length - 8
# bytes after the header. NetBadLength if the length is below 8,
# NetTruncated if the datagram is shorter than it.
def UdpHeader.payload(h: UdpHeader, dg: B.Octets) -> Result<&2, &2, N.NetError, B.Octets>:
  match h:
    case UdpHeader{a, b, c, d}:
      +n = U32.to_nat(N.NetField.low(16n, c))
      UdpHeader.payload.go(Nat.is_ge(n, 8n), Nat.sub(n, 8n), dg)

# The checksum

# a computed checksum of zero is sent as all ones (RFC 768)
def UdpHeader.nonzero.go(z: Bool, c: U32) -> U32:
  match z:
    case True{}:
      65535
    case False{}:
      c

def UdpHeader.nonzero(+c: U32) -> U32:
  UdpHeader.nonzero.go(U32.is_eq(c, 0), c)

def UdpHeader.fill(pseudo: B.Octets, +dg: B.Octets) -> B.Octets:
  K.inet_put16(dg, 6n, UdpHeader.nonzero(K.inet_checksum(B.Octets.append(pseudo, K.inet_put16(dg, 6n, 0)))))

# the datagram (header, then payload) with its checksum over the IPv4
# pseudo-header from src to dst. The pseudo-header's length is the number of
# bytes in the datagram, which the length field should match.
def UdpHeader.build_ipv4(src: U32, dst: U32, h: UdpHeader, payload: B.Octets) -> B.Octets:
  +dg = B.Octets.append(UdpHeader.build(h), payload)
  UdpHeader.fill(I4.ipv4_pseudo(src, dst, 17, N.net.len32(dg)), dg)

def UdpHeader.build_ipv6(src: I6.Ipv6Addr, dst: I6.Ipv6Addr, h: UdpHeader, payload: B.Octets) -> B.Octets:
  +dg = B.Octets.append(UdpHeader.build(h), payload)
  UdpHeader.fill(I6.ipv6_pseudo(src, dst, N.net.len32(dg), 17), dg)

def UdpHeader.verify.go(zero: Bool, if_zero: Bool, sum_ok: Bool) -> Bool:
  match zero:
    case True{}:
      if_zero
    case False{}:
      sum_ok

def UdpHeader.zero_field(m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{c}:
      U32.is_eq(c, 0)
    case None{}:
      False{}

# whether the datagram's checksum verifies over IPv4. A zero checksum field
# means the sender computed none (RFC 768); zero_ok says whether to accept
# such a datagram.
def UdpHeader.verify_ipv4_with(zero_ok: Bool, src: U32, dst: U32, +dg: B.Octets) -> Bool:
  UdpHeader.verify.go(UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), zero_ok, K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, N.net.len32(dg)), dg)))

# the default: accept a datagram without a checksum, as RFC 768 allows
def UdpHeader.verify_ipv4(src: U32, dst: U32, dg: B.Octets) -> Bool:
  UdpHeader.verify_ipv4_with(True{}, src, dst, dg)

# over IPv6 the checksum is mandatory (RFC 8200 section 8.1): zero fails
def UdpHeader.verify_ipv6(src: I6.Ipv6Addr, dst: I6.Ipv6Addr, +dg: B.Octets) -> Bool:
  UdpHeader.verify.go(UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), False{}, K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, N.net.len32(dg), 17), dg)))
