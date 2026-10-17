# IPv6 (RFC 8200): the fixed 40-byte header, and the pseudo-header that
# upper-layer checksums cover (section 8.1). Extension headers are not parsed:
# next_header names the first, and the payload starts after the 40 bytes.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N

# A 128-bit address, as four 32-bit words, most significant first
type Ipv6Addr is Data:
  Ipv6Addr{w0: U32, w1: U32, w2: U32, w3: U32}

def Ipv6Addr.list(a: Ipv6Addr) -> List<&2, U32>:
  match a:
    case Ipv6Addr{w0, w1, w2, w3}:
      B.append(B.be32(w0), B.append(B.be32(w1), B.append(B.be32(w2), B.be32(w3))))

# the sixteen bytes
def Ipv6Addr.bytes(a: Ipv6Addr) -> B.Octets:
  B.Octets.of_list(Ipv6Addr.list(a))

def Ipv6Addr.of(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, m3: Maybe<&2, U32>) -> Maybe<&2, Ipv6Addr>:
  match m0 m1 m2 m3:
    case Some{w0} Some{w1} Some{w2} Some{w3}:
      Some{Ipv6Addr{w0, w1, w2, w3}}
    case _ _ _ _:
      None{}

def Ipv6Addr.at(+xs: List<&2, U32>, +off: Nat) -> Maybe<&2, Ipv6Addr>:
  Ipv6Addr.of(B.be32_at(xs, off), B.be32_at(xs, Nat.add(off, 4n)), B.be32_at(xs, Nat.add(off, 8n)), B.be32_at(xs, Nat.add(off, 12n)))

# version, traffic class (8 bits), flow label (20), payload length, next
# header, hop limit, source, destination
type Ipv6Header is Data:
  Ipv6Header{version: U32, traffic_class: U32, flow_label: U32, payload_length: U32, next_header: U32, hop_limit: U32, src: Ipv6Addr, dst: Ipv6Addr}

def Ipv6Header.norm(h: Ipv6Header) -> Ipv6Header:
  match h:
    case Ipv6Header{ver, tc, fl, pl, nh, hop, s, d}:
      Ipv6Header{N.NetField.low(4n, ver), N.NetField.low(8n, tc), N.NetField.low(20n, fl), N.NetField.low(16n, pl), N.NetField.low(8n, nh), N.NetField.low(8n, hop), s, d}

def Ipv6Header.build.list(h: Ipv6Header) -> List<&2, U32>:
  match h:
    case Ipv6Header{ver, tc, fl, pl, nh, hop, s, d}:
      +w0 = N.NetField.put(28n, 4n, ver, N.NetField.put(20n, 8n, tc, N.NetField.low(20n, fl)))
      +w1 = N.NetField.put(16n, 16n, pl, N.NetField.put(8n, 8n, nh, N.NetField.low(8n, hop)))
      B.append(B.be32(w0), B.append(B.be32(w1), B.append(Ipv6Addr.list(s), Ipv6Addr.list(d))))

def Ipv6Header.build(h: Ipv6Header) -> B.Octets:
  B.Octets.of_list(Ipv6Header.build.list(h))

def Ipv6Header.make(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>, ms: Maybe<&2, Ipv6Addr>, md: Maybe<&2, Ipv6Addr>) -> Result<&2, &2, N.NetError, Ipv6Header>:
  match m0 m1 ms md:
    case Some{+w0} Some{+w1} Some{s} Some{d}:
      +ver = N.NetField.get(w0, 28n, 4n)
      N.net.check(Ipv6Header, U32.is_eq(ver, 6), N.NetBadVersion{}, Ipv6Header{ver, N.NetField.get(w0, 20n, 8n), N.NetField.get(w0, 0n, 20n), N.NetField.get(w1, 16n, 16n), N.NetField.get(w1, 8n, 8n), N.NetField.get(w1, 0n, 8n), s, d})
    case _ _ _ _:
      Fail{N.NetTruncated{}}

def Ipv6Header.parse.list(+xs: List<&2, U32>) -> Result<&2, &2, N.NetError, Ipv6Header>:
  Ipv6Header.make(B.be32_at(xs, 0n), B.be32_at(xs, 4n), Ipv6Addr.at(xs, 8n), Ipv6Addr.at(xs, 24n))

# the header at the start of o: NetTruncated if o is shorter than 40 bytes,
# NetBadVersion if the version is not 6
def Ipv6Header.parse(o: B.Octets) -> Result<&2, &2, N.NetError, Ipv6Header>:
  Ipv6Header.parse.list(B.Octets.to_list(o))

def Ipv6Header.length(h: Ipv6Header) -> Nat:
  40n

# the payload of the packet (header first) whose header is h: the
# payload_length bytes after the header; NetTruncated if there are fewer
def Ipv6Header.payload(h: Ipv6Header, packet: B.Octets) -> Result<&2, &2, N.NetError, B.Octets>:
  match h:
    case Ipv6Header{ver, tc, fl, pl, nh, hop, s, d}:
      N.net.slice(40n, U32.to_nat(N.NetField.low(16n, pl)), packet)

# The pseudo-header (RFC 8200 section 8.1): source, destination, the
# upper-layer length (32 bits), three zero bytes, next header
def ipv6_pseudo(src: Ipv6Addr, dst: Ipv6Addr, len: U32, next: U32) -> B.Octets:
  B.Octets.of_list(B.append(Ipv6Addr.list(src), B.append(Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(next)]))))
