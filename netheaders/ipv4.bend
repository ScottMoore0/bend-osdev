# IPv4 (RFC 791): the header, its checksum, and the pseudo-header that UDP
# and TCP checksums cover (RFC 768, RFC 9293).
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./checksum.bend as K

# version, IHL (the header length in 32-bit words), DSCP (6 bits), ECN (2),
# total length, identification, flags (3 bits: reserved, DF, MF), fragment
# offset (13), TTL, protocol, header checksum, source, destination, and the
# options, raw (IHL * 4 - 20 bytes)
type Ipv4Header is Data:
  Ipv4Header{version: U32, ihl: U32, dscp: U32, ecn: U32, total_length: U32, ident: U32, flags: U32, frag_offset: U32, ttl: U32, protocol: U32, checksum: U32, src: U32, dst: U32, options: B.Octets}

def Ipv4Header.norm(h: Ipv4Header) -> Ipv4Header:
  match h:
    case Ipv4Header{ver, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, s, d, o}:
      Ipv4Header{N.NetField.low(4n, ver), N.NetField.low(4n, ihl), N.NetField.low(6n, dscp), N.NetField.low(2n, ecn), N.NetField.low(16n, tl), N.NetField.low(16n, id), N.NetField.low(3n, fl), N.NetField.low(13n, fo), N.NetField.low(8n, ttl), N.NetField.low(8n, pr), N.NetField.low(16n, ck), s, d, o}

def Ipv4Header.build.list(h: Ipv4Header) -> List<&2, U32>:
  match h:
    case Ipv4Header{ver, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, s, d, o}:
      +w0 = N.NetField.put(28n, 4n, ver, N.NetField.put(24n, 4n, ihl, N.NetField.put(18n, 6n, dscp, N.NetField.put(16n, 2n, ecn, N.NetField.low(16n, tl)))))
      +w1 = N.NetField.put(16n, 16n, id, N.NetField.put(13n, 3n, fl, N.NetField.low(13n, fo)))
      +w2 = N.NetField.put(24n, 8n, ttl, N.NetField.put(16n, 8n, pr, N.NetField.low(16n, ck)))
      B.append(B.be32(w0), B.append(B.be32(w1), B.append(B.be32(w2), B.append(B.be32(s), B.append(B.be32(d), B.Octets.to_list(o))))))

# the header's bytes, every field as given: the options must be IHL * 4 - 20
# bytes for the header to parse back
def Ipv4Header.build(h: Ipv4Header) -> B.Octets:
  B.Octets.of_list(Ipv4Header.build.list(h))

def Ipv4Header.check(version_ok: Bool, ihl_ok: Bool, present: Bool, h: Ipv4Header) -> Result<&2, &2, N.NetError, Ipv4Header>:
  match version_ok:
    case False{}:
      Fail{N.NetBadVersion{}}
    case True{}:
      match ihl_ok:
        case False{}:
          Fail{N.NetBadIhl{}}
        case True{}:
          N.net.check(Ipv4Header, present, N.NetTruncated{}, h)

def Ipv4Header.make(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, m3: Maybe<&2, U32>, m4: Maybe<&2, U32>, +xs: List<&2, U32>) -> Result<&2, &2, N.NetError, Ipv4Header>:
  match m0 m1 m2 m3 m4:
    case Some{+w0} Some{+w1} Some{+w2} Some{s} Some{d}:
      +ver = N.NetField.get(w0, 28n, 4n)
      +ihl = N.NetField.get(w0, 24n, 4n)
      +hl = Nat.mul(4n, U32.to_nat(ihl))
      Ipv4Header.check(U32.is_eq(ver, 4), U32.is_ge(ihl, 5), N.net.has(hl, xs), Ipv4Header{ver, ihl, N.NetField.get(w0, 18n, 6n), N.NetField.get(w0, 16n, 2n), N.NetField.get(w0, 0n, 16n), N.NetField.get(w1, 16n, 16n), N.NetField.get(w1, 13n, 3n), N.NetField.get(w1, 0n, 13n), N.NetField.get(w2, 24n, 8n), N.NetField.get(w2, 16n, 8n), N.NetField.get(w2, 0n, 16n), s, d, B.Octets.of_list(B.take(Nat.sub(hl, 20n), B.drop(20n, xs)))})
    case _ _ _ _ _:
      Fail{N.NetTruncated{}}

def Ipv4Header.parse.list(+xs: List<&2, U32>) -> Result<&2, &2, N.NetError, Ipv4Header>:
  Ipv4Header.make(B.be32_at(xs, 0n), B.be32_at(xs, 4n), B.be32_at(xs, 8n), B.be32_at(xs, 12n), B.be32_at(xs, 16n), xs)

# the header at the start of o: NetTruncated if o is shorter than 20 bytes or
# than IHL * 4, NetBadVersion if the version is not 4, NetBadIhl if IHL is
# below 5. The checksum is not checked (see parse_verified).
def Ipv4Header.parse(o: B.Octets) -> Result<&2, &2, N.NetError, Ipv4Header>:
  Ipv4Header.parse.list(B.Octets.to_list(o))

# the header's length in bytes, IHL * 4
def Ipv4Header.length(h: Ipv4Header) -> Nat:
  match h:
    case Ipv4Header{ver, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, s, d, o}:
      Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl)))

# The checksum

# the header's bytes with its checksum computed (the checksum field ignored)
def Ipv4Header.build_checksum(h: Ipv4Header) -> B.Octets:
  K.inet_fill(B.Octets.empty(), Ipv4Header.build(h), 10n)

def Ipv4Header.verify.go(r: Result<&2, &2, N.NetError, Ipv4Header>, o: B.Octets) -> Bool:
  match r:
    case Done{h}:
      K.inet_verify(B.Octets.take(Ipv4Header.length(h), o))
    case Fail{e}:
      False{}

# whether o starts with a well-formed IPv4 header whose checksum verifies
def Ipv4Header.verify(+o: B.Octets) -> Bool:
  Ipv4Header.verify.go(Ipv4Header.parse(o), o)

def Ipv4Header.parse_verified.go(r: Result<&2, &2, N.NetError, Ipv4Header>, o: B.Octets) -> Result<&2, &2, N.NetError, Ipv4Header>:
  match r:
    case Done{+h}:
      N.net.check(Ipv4Header, K.inet_verify(B.Octets.take(Ipv4Header.length(h), o)), N.NetBadChecksum{}, h)
    case Fail{e}:
      Fail{e}

# parse, and NetBadChecksum if the header checksum does not verify
def Ipv4Header.parse_verified(+o: B.Octets) -> Result<&2, &2, N.NetError, Ipv4Header>:
  Ipv4Header.parse_verified.go(Ipv4Header.parse(o), o)

# The payload

def Ipv4Header.payload.go(ok: Bool, +hl: Nat, +n: Nat, +packet: B.Octets) -> Result<&2, &2, N.NetError, B.Octets>:
  match ok:
    case True{}:
      N.net.slice(hl, n, packet)
    case False{}:
      Fail{N.NetBadLength{}}

# the payload of the packet (header first) whose header is h: total length
# minus IHL * 4 bytes after the header. NetBadLength if the total length is
# shorter than the header, NetTruncated if the packet is shorter than it.
def Ipv4Header.payload(h: Ipv4Header, packet: B.Octets) -> Result<&2, &2, N.NetError, B.Octets>:
  match h:
    case Ipv4Header{ver, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, s, d, o}:
      +hl = Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl)))
      +total = U32.to_nat(N.NetField.low(16n, tl))
      Ipv4Header.payload.go(Nat.is_ge(total, hl), hl, Nat.sub(total, hl), packet)

# The pseudo-header (RFC 768, RFC 9293): source, destination, a zero byte,
# protocol, and the upper-layer length (16 bits)
def ipv4_pseudo(src: U32, dst: U32, proto: U32, len: U32) -> B.Octets:
  B.Octets.of_list(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(proto)], B.be16(len)))))

# Protocol numbers
def Ipv4Header.PROTO_ICMP() -> U32:
  1

def Ipv4Header.PROTO_TCP() -> U32:
  6

def Ipv4Header.PROTO_UDP() -> U32:
  17
