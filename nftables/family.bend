# bend-osdev-nftables: address families, hooks and priorities (nft(8),
# "ADDRESS FAMILIES", "CHAINS"), and the package's error type, which every
# other file shares.
#
# A table belongs to one family. A packet reaches a hook in one netfilter
# protocol family (NftProto): an ip table sees IPv4 packets, ip6 IPv6, inet
# both, arp ARP, bridge bridged frames, netdev frames at a device.
import Base

# Why building a ruleset fails
type NftError is Data:
  # an interval set element overlaps one already in the set
  NftErrSetOverlap{}
  # an interval whose low end is above its high end
  NftErrBadInterval{}
  # no table of that name
  NftErrNoTable{}
  # no chain of that name in the table
  NftErrNoChain{}
  # no set or map of that name in the table
  NftErrNoSet{}
  # a table, chain or set of that name exists already
  NftErrExists{}
  # the hook is not available in the table's family
  NftErrBadHook{}
  # a packet whose headers do not parse
  NftErrBadPacket{}

# The families of a table
type NftFamily is Data:
  NftIp{}
  NftIp6{}
  NftInet{}
  NftArp{}
  NftBridge{}
  NftNetdev{}

# The protocol family a hook runs in, for one packet
type NftProto is Data:
  NftProtoIpv4{}
  NftProtoIpv6{}
  NftProtoArp{}
  NftProtoBridge{}
  NftProtoNetdev{}

# The hooks
type NftHook is Data:
  NftPrerouting{}
  NftInput{}
  NftForward{}
  NftOutput{}
  NftPostrouting{}
  NftIngress{}
  NftEgress{}

def NftFamily.index(f: NftFamily) -> U32:
  match f:
    case NftIp{}:
      0
    case NftIp6{}:
      1
    case NftInet{}:
      2
    case NftArp{}:
      3
    case NftBridge{}:
      4
    case NftNetdev{}:
      5

def NftFamily.is_eq(a: NftFamily, b: NftFamily) -> Bool:
  U32.is_eq(NftFamily.index(a), NftFamily.index(b))

# whether a table of family f sees packets of protocol family p
def NftFamily.sees(f: NftFamily, p: NftProto) -> Bool:
  match f p:
    case NftIp{} NftProtoIpv4{}:
      True{}
    case NftIp6{} NftProtoIpv6{}:
      True{}
    case NftInet{} NftProtoIpv4{}:
      True{}
    case NftInet{} NftProtoIpv6{}:
      True{}
    case NftArp{} NftProtoArp{}:
      True{}
    case NftBridge{} NftProtoBridge{}:
      True{}
    case NftNetdev{} NftProtoNetdev{}:
      True{}
    case _ _:
      False{}

# whether a base chain of family f may attach to hook h (nft(8), "CHAINS":
# ip, ip6 and inet have the five Netfilter hooks, inet also ingress; arp has
# input and output; bridge the five; netdev ingress and egress)
def NftFamily.has_hook(f: NftFamily, h: NftHook) -> Bool:
  match f h:
    case NftArp{} NftInput{}:
      True{}
    case NftArp{} NftOutput{}:
      True{}
    case NftArp{} _:
      False{}
    case NftNetdev{} NftIngress{}:
      True{}
    case NftNetdev{} NftEgress{}:
      True{}
    case NftNetdev{} _:
      False{}
    case NftInet{} NftIngress{}:
      True{}
    case _ NftIngress{}:
      False{}
    case _ NftEgress{}:
      False{}
    case _ _:
      True{}

def NftHook.index(h: NftHook) -> U32:
  match h:
    case NftPrerouting{}:
      0
    case NftInput{}:
      1
    case NftForward{}:
      2
    case NftOutput{}:
      3
    case NftPostrouting{}:
      4
    case NftIngress{}:
      5
    case NftEgress{}:
      6

def NftHook.is_eq(a: NftHook, b: NftHook) -> Bool:
  U32.is_eq(NftHook.index(a), NftHook.index(b))

# the value of `meta nfproto` for a packet of protocol family p (the
# NFPROTO_* numbers: ipv4 2, arp 3, netdev 5, bridge 7, ipv6 10)
def NftProto.nfproto(p: NftProto) -> U32:
  match p:
    case NftProtoIpv4{}:
      2
    case NftProtoIpv6{}:
      10
    case NftProtoArp{}:
      3
    case NftProtoBridge{}:
      7
    case NftProtoNetdev{}:
      5

# Priorities: signed 32-bit numbers, held as their two's complement bits in a
# U32; a lower priority runs first

# the priority -n (n, if neg is False)
def NftPrio.of(neg: Bool, n: U32) -> U32:
  match neg:
    case False{}:
      n
    case True{}:
      U32.sub(0, n)

# whether priority a runs before priority b: a < b as signed numbers
def NftPrio.lt(a: U32, b: U32) -> Bool:
  U32.is_lt(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

# The standard priority names (nft(8), "CHAINS", the priority table), for
# ip, ip6, inet, arp and netdev
def NftPrio.raw() -> U32:
  NftPrio.of(True{}, 300)

def NftPrio.mangle() -> U32:
  NftPrio.of(True{}, 150)

def NftPrio.dstnat() -> U32:
  NftPrio.of(True{}, 100)

def NftPrio.filter() -> U32:
  0

def NftPrio.security() -> U32:
  50

def NftPrio.srcnat() -> U32:
  100

# and for bridge
def NftPrio.bridge_dstnat() -> U32:
  NftPrio.of(True{}, 300)

def NftPrio.bridge_filter() -> U32:
  NftPrio.of(True{}, 200)

def NftPrio.bridge_out() -> U32:
  100

def NftPrio.bridge_srcnat() -> U32:
  300
