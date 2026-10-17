# ARP (RFC 826) for IPv4 over Ethernet: hardware type 1, protocol type
# 0x0800, hardware address length 6, protocol address length 4. The packet is
# 28 bytes.
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./ethernet.bend as E

# operation (1 request, 2 reply), sender hardware and protocol addresses,
# target hardware and protocol addresses
type ArpPacket is Data:
  ArpPacket{oper: U32, sha: E.MacAddr, spa: U32, tha: E.MacAddr, tpa: U32}

def ArpPacket.REQUEST() -> U32:
  1

def ArpPacket.REPLY() -> U32:
  2

def ArpPacket.norm(p: ArpPacket) -> ArpPacket:
  match p:
    case ArpPacket{o, sha, spa, tha, tpa}:
      ArpPacket{N.NetField.low(16n, o), E.MacAddr.norm(sha), spa, E.MacAddr.norm(tha), tpa}

def ArpPacket.build.list(p: ArpPacket) -> List<&2, U32>:
  match p:
    case ArpPacket{o, sha, spa, tha, tpa}:
      B.append([0, 1, 8, 0, 6, 4], B.append(B.be16(o), B.append(E.MacAddr.list(sha), B.append(B.be32(spa), B.append(E.MacAddr.list(tha), B.be32(tpa))))))

def ArpPacket.build(p: ArpPacket) -> B.Octets:
  B.Octets.of_list(ArpPacket.build.list(p))

def ArpPacket.make(mf: Maybe<&2, U32>, ml: Maybe<&2, U32>, mo: Maybe<&2, U32>, msha: Maybe<&2, E.MacAddr>, mspa: Maybe<&2, U32>, mtha: Maybe<&2, E.MacAddr>, mtpa: Maybe<&2, U32>) -> Result<&2, &2, N.NetError, ArpPacket>:
  match mf ml mo msha mspa mtha mtpa:
    case Some{f} Some{l} Some{o} Some{sha} Some{spa} Some{tha} Some{tpa}:
      N.net.check(ArpPacket, Bool.and(U32.is_eq(f, 67584), U32.is_eq(l, 1540)), N.NetBadArpFormat{}, ArpPacket{o, sha, spa, tha, tpa})
    case _ _ _ _ _ _ _:
      Fail{N.NetTruncated{}}

# hardware and protocol type are one 32-bit word, 0x00010800 (67584); the
# address lengths one 16-bit word, 0x0604 (1540)
def ArpPacket.parse.list(+xs: List<&2, U32>) -> Result<&2, &2, N.NetError, ArpPacket>:
  ArpPacket.make(B.be32_at(xs, 0n), B.be16_at(xs, 4n), B.be16_at(xs, 6n), E.MacAddr.at(xs, 8n), B.be32_at(xs, 14n), E.MacAddr.at(xs, 18n), B.be32_at(xs, 24n))

# the packet at the start of o; NetTruncated if o is shorter than 28 bytes,
# NetBadArpFormat if it is not for IPv4 over Ethernet
def ArpPacket.parse(o: B.Octets) -> Result<&2, &2, N.NetError, ArpPacket>:
  ArpPacket.parse.list(B.Octets.to_list(o))

def ArpPacket.length(p: ArpPacket) -> Nat:
  28n
