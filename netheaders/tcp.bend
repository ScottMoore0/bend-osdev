# TCP (RFC 9293): the header, options as raw bytes, and the checksum over the
# IPv4 pseudo-header (RFC 9293 section 3.1) or the IPv6 pseudo-header
# (RFC 8200 section 8.1), protocol / next header 6.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ipv4.bend as I4
import ./ipv6.bend as I6

# ports, sequence and acknowledgment numbers, data offset (the header length
# in 32-bit words), the 4 reserved bits, the 8 control bits (CWR ECE URG ACK
# PSH RST SYN FIN, most significant first), window, checksum, urgent pointer,
# and the options, raw (data offset * 4 - 20 bytes)
type TcpHeader is Data:
  TcpHeader{src_port: U32, dst_port: U32, seq: U32, ack: U32, data_offset: U32, reserved: U32, flags: U32, window: U32, checksum: U32, urgent: U32, options: B.Octets}

# The control bits, as masks of the flags field
def TcpHeader.FIN() -> U32:
  1

def TcpHeader.SYN() -> U32:
  2

def TcpHeader.RST() -> U32:
  4

def TcpHeader.PSH() -> U32:
  8

def TcpHeader.ACK() -> U32:
  16

def TcpHeader.URG() -> U32:
  32

def TcpHeader.ECE() -> U32:
  64

def TcpHeader.CWR() -> U32:
  128

def TcpHeader.norm(h: TcpHeader) -> TcpHeader:
  match h:
    case TcpHeader{sp, dp, sq, ak, off, rs, fl, win, ck, ur, o}:
      TcpHeader{N.NetField.low(16n, sp), N.NetField.low(16n, dp), sq, ak, N.NetField.low(4n, off), N.NetField.low(4n, rs), N.NetField.low(8n, fl), N.NetField.low(16n, win), N.NetField.low(16n, ck), N.NetField.low(16n, ur), o}

def TcpHeader.build.list(h: TcpHeader) -> List<&2, U32>:
  match h:
    case TcpHeader{sp, dp, sq, ak, off, rs, fl, win, ck, ur, o}:
      +w0 = N.NetField.put(16n, 16n, sp, N.NetField.low(16n, dp))
      +w3 = N.NetField.put(28n, 4n, off, N.NetField.put(24n, 4n, rs, N.NetField.put(16n, 8n, fl, N.NetField.low(16n, win))))
      +w4 = N.NetField.put(16n, 16n, ck, N.NetField.low(16n, ur))
      B.append(B.be32(w0), B.append(B.be32(sq), B.append(B.be32(ak), B.append(B.be32(w3), B.append(B.be32(w4), B.Octets.to_list(o))))))

# the header's bytes, every field as given: the options must be data offset
# * 4 - 20 bytes for the header to parse back
def TcpHeader.build(h: TcpHeader) -> B.Octets:
  B.Octets.of_list(TcpHeader.build.list(h))

def TcpHeader.check(offset_ok: Bool, present: Bool, h: TcpHeader) -> Result<&2, &2, N.NetError, TcpHeader>:
  match offset_ok:
    case False{}:
      Fail{N.NetBadDataOffset{}}
    case True{}:
      N.net.check(TcpHeader, present, N.NetTruncated{}, h)

def TcpHeader.make(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, m3: Maybe<&2, U32>, m4: Maybe<&2, U32>, +xs: List<&2, U32>) -> Result<&2, &2, N.NetError, TcpHeader>:
  match m0 m1 m2 m3 m4:
    case Some{+w0} Some{sq} Some{ak} Some{+w3} Some{+w4}:
      +off = N.NetField.get(w3, 28n, 4n)
      +hl = Nat.mul(4n, U32.to_nat(off))
      TcpHeader.check(U32.is_ge(off, 5), N.net.has(hl, xs), TcpHeader{N.NetField.get(w0, 16n, 16n), N.NetField.get(w0, 0n, 16n), sq, ak, off, N.NetField.get(w3, 24n, 4n), N.NetField.get(w3, 16n, 8n), N.NetField.get(w3, 0n, 16n), N.NetField.get(w4, 16n, 16n), N.NetField.get(w4, 0n, 16n), B.Octets.of_list(B.take(Nat.sub(hl, 20n), B.drop(20n, xs)))})
    case _ _ _ _ _:
      Fail{N.NetTruncated{}}

def TcpHeader.parse.list(+xs: List<&2, U32>) -> Result<&2, &2, N.NetError, TcpHeader>:
  TcpHeader.make(B.be32_at(xs, 0n), B.be32_at(xs, 4n), B.be32_at(xs, 8n), B.be32_at(xs, 12n), B.be32_at(xs, 16n), xs)

# the header at the start of o: NetTruncated if o is shorter than 20 bytes or
# than data offset * 4, NetBadDataOffset if the data offset is below 5
def TcpHeader.parse(o: B.Octets) -> Result<&2, &2, N.NetError, TcpHeader>:
  TcpHeader.parse.list(B.Octets.to_list(o))

# the header's length in bytes, data offset * 4
def TcpHeader.length(h: TcpHeader) -> Nat:
  match h:
    case TcpHeader{sp, dp, sq, ak, off, rs, fl, win, ck, ur, o}:
      Nat.mul(4n, U32.to_nat(N.NetField.low(4n, off)))

# The checksum: the TCP length in the pseudo-header is the number of bytes in
# the segment (header and payload)

def TcpHeader.build_ipv4(src: U32, dst: U32, h: TcpHeader, payload: B.Octets) -> B.Octets:
  +seg = B.Octets.append(TcpHeader.build(h), payload)
  K.inet_fill(I4.ipv4_pseudo(src, dst, 6, N.net.len32(seg)), seg, 16n)

def TcpHeader.build_ipv6(src: I6.Ipv6Addr, dst: I6.Ipv6Addr, h: TcpHeader, payload: B.Octets) -> B.Octets:
  +seg = B.Octets.append(TcpHeader.build(h), payload)
  K.inet_fill(I6.ipv6_pseudo(src, dst, N.net.len32(seg), 6), seg, 16n)

def TcpHeader.verify_ipv4(src: U32, dst: U32, +seg: B.Octets) -> Bool:
  K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 6, N.net.len32(seg)), seg))

def TcpHeader.verify_ipv6(src: I6.Ipv6Addr, dst: I6.Ipv6Addr, +seg: B.Octets) -> Bool:
  K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, N.net.len32(seg), 6), seg))
