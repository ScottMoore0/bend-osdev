# Ethernet II framing (IEEE 802.3) with an optional 802.1Q tag (IEEE 802.1Q):
# destination and source MAC addresses, the tag if any, and the EtherType.
# The frame check sequence is not part of the header (bend-osdev-crc's crc32
# computes it).
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N

# A 48-bit MAC address, as its six bytes in transmission order
type MacAddr is Data:
  MacAddr{a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32}

def MacAddr.norm(m: MacAddr) -> MacAddr:
  match m:
    case MacAddr{a0, a1, a2, a3, a4, a5}:
      MacAddr{B.byte(a0), B.byte(a1), B.byte(a2), B.byte(a3), B.byte(a4), B.byte(a5)}

def MacAddr.list(m: MacAddr) -> List<&2, U32>:
  match m:
    case MacAddr{a0, a1, a2, a3, a4, a5}:
      [B.byte(a0), B.byte(a1), B.byte(a2), B.byte(a3), B.byte(a4), B.byte(a5)]

# the six bytes
def MacAddr.bytes(m: MacAddr) -> B.Octets:
  B.Octets.of_list(MacAddr.list(m))

def MacAddr.of(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, m3: Maybe<&2, U32>, m4: Maybe<&2, U32>, m5: Maybe<&2, U32>) -> Maybe<&2, MacAddr>:
  match m0 m1 m2 m3 m4 m5:
    case Some{a0} Some{a1} Some{a2} Some{a3} Some{a4} Some{a5}:
      Some{MacAddr{a0, a1, a2, a3, a4, a5}}
    case _ _ _ _ _ _:
      None{}

# the MAC address at offset off of a byte list
def MacAddr.at(+xs: List<&2, U32>, +off: Nat) -> Maybe<&2, MacAddr>:
  MacAddr.of(B.at(xs, off), B.at(xs, Nat.add(off, 1n)), B.at(xs, Nat.add(off, 2n)), B.at(xs, Nat.add(off, 3n)), B.at(xs, Nat.add(off, 4n)), B.at(xs, Nat.add(off, 5n)))

# the broadcast address ff:ff:ff:ff:ff:ff
def MacAddr.broadcast() -> MacAddr:
  MacAddr{255, 255, 255, 255, 255, 255}

# The 802.1Q tag control information: priority code point (3 bits), drop
# eligible indicator (1), VLAN identifier (12)
type VlanTag is Data:
  VlanTag{pcp: U32, dei: U32, vid: U32}

# dst, src, the 802.1Q tag if any, and the EtherType (a value below 0x0600 is
# an IEEE 802.3 length instead; it is reported as it is)
type EthHeader is Data:
  EthHeader{dst: MacAddr, src: MacAddr, vlan: Maybe<&2, VlanTag>, ethertype: U32}

def VlanTag.norm(v: VlanTag) -> VlanTag:
  match v:
    case VlanTag{p, d, i}:
      VlanTag{N.NetField.low(3n, p), N.NetField.low(1n, d), N.NetField.low(12n, i)}

def VlanTag.tci(v: VlanTag) -> U32:
  match v:
    case VlanTag{p, d, i}:
      N.NetField.put(13n, 3n, p, N.NetField.put(12n, 1n, d, N.NetField.low(12n, i)))

def VlanTag.of_tci(+t: U32) -> VlanTag:
  VlanTag{N.NetField.get(t, 13n, 3n), N.NetField.get(t, 12n, 1n), N.NetField.get(t, 0n, 12n)}

def EthHeader.norm.vlan(v: Maybe<&2, VlanTag>) -> Maybe<&2, VlanTag>:
  match v:
    case None{}:
      None{}
    case Some{t}:
      Some{VlanTag.norm(t)}

def EthHeader.norm(h: EthHeader) -> EthHeader:
  match h:
    case EthHeader{d, s, v, t}:
      EthHeader{MacAddr.norm(d), MacAddr.norm(s), EthHeader.norm.vlan(v), N.NetField.low(16n, t)}

# The tag protocol identifier: 0x8100 for an 802.1Q tag, the default. A
# caller may pass another (0x88a8, an 802.1ad service tag) to parse_with and
# build_with; one tag is read, and an inner tag is reported as the EtherType.
def EthHeader.TPID_8021Q() -> U32:
  33024

def EthHeader.build.tag(+tpid: U32, v: Maybe<&2, VlanTag>, t: U32) -> List<&2, U32>:
  match v:
    case None{}:
      B.be16(t)
    case Some{g}:
      B.append(B.be16(tpid), B.append(B.be16(VlanTag.tci(g)), B.be16(t)))

def EthHeader.build.list(+tpid: U32, h: EthHeader) -> List<&2, U32>:
  match h:
    case EthHeader{d, s, v, t}:
      B.append(MacAddr.list(d), B.append(MacAddr.list(s), EthHeader.build.tag(tpid, v, t)))

# the header's bytes; a tag is written with the identifier tpid
def EthHeader.build_with(+tpid: U32, h: EthHeader) -> B.Octets:
  B.Octets.of_list(EthHeader.build.list(tpid, h))

def EthHeader.build(h: EthHeader) -> B.Octets:
  EthHeader.build_with(EthHeader.TPID_8021Q(), h)

# whether a 16-bit field read is tpid
def EthHeader.is_tpid(+tpid: U32, m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{t}:
      U32.is_eq(t, tpid)
    case None{}:
      False{}

# whether the frame xs carries a tag
def EthHeader.tagged(+tpid: U32, xs: List<&2, U32>) -> Bool:
  EthHeader.is_tpid(tpid, B.be16_at(xs, 12n))

def EthHeader.make(md: Maybe<&2, MacAddr>, ms: Maybe<&2, MacAddr>, mv: Maybe<&2, Maybe<&2, VlanTag>>, mt: Maybe<&2, U32>) -> Result<&2, &2, N.NetError, EthHeader>:
  match md ms mv mt:
    case Some{d} Some{s} Some{v} Some{t}:
      Done{EthHeader{d, s, v, t}}
    case _ _ _ _:
      Fail{N.NetTruncated{}}

def EthHeader.parse.tci(m: Maybe<&2, U32>) -> Maybe<&2, Maybe<&2, VlanTag>>:
  match m:
    case Some{+t}:
      Some{Some{VlanTag.of_tci(t)}}
    case None{}:
      None{}

def EthHeader.parse.go(tagged: Bool, +xs: List<&2, U32>) -> Result<&2, &2, N.NetError, EthHeader>:
  match tagged:
    case True{}:
      EthHeader.make(MacAddr.at(xs, 0n), MacAddr.at(xs, 6n), EthHeader.parse.tci(B.be16_at(xs, 14n)), B.be16_at(xs, 16n))
    case False{}:
      EthHeader.make(MacAddr.at(xs, 0n), MacAddr.at(xs, 6n), Some{None{}}, B.be16_at(xs, 12n))

def EthHeader.parse.list(+tpid: U32, +xs: List<&2, U32>) -> Result<&2, &2, N.NetError, EthHeader>:
  EthHeader.parse.go(EthHeader.tagged(tpid, xs), xs)

# the header at the start of o, a tag recognised by its identifier tpid;
# NetTruncated if o is too short
def EthHeader.parse_with(+tpid: U32, o: B.Octets) -> Result<&2, &2, N.NetError, EthHeader>:
  EthHeader.parse.list(tpid, B.Octets.to_list(o))

def EthHeader.parse(o: B.Octets) -> Result<&2, &2, N.NetError, EthHeader>:
  EthHeader.parse_with(EthHeader.TPID_8021Q(), o)

# the header's length in bytes: 14, or 18 with a tag
def EthHeader.length(h: EthHeader) -> Nat:
  match h:
    case EthHeader{d, s, None{}, t}:
      14n
    case EthHeader{d, s, Some{v}, t}:
      18n

# Common EtherTypes
def EthHeader.TYPE_IPV4() -> U32:
  2048

def EthHeader.TYPE_ARP() -> U32:
  2054

def EthHeader.TYPE_IPV6() -> U32:
  34525
