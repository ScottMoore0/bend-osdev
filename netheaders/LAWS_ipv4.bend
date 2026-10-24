# IPv4's header checksum: a header built with build_checksum verifies, for
# every header the parser accepts (version 4, IHL 5 to 15 with options of
# the matching length: ipv4_round_trip's hypotheses), whatever its
# checksum field held.
#
# A pair of its own (PROOF_ipv4.bend): the proof rests on both the round
# trip (LAWS.bend) and inet_fill_verifies (LAWS_sum.bend).
import Base
import ../bytes/bytes.bend as B
import ./netheaders.bend as N
import ./ipv4.bend as I4

law ipv4_build_verifies:
  for +ihl: U32
  for +e1: {U32.is_ge(N.NetField.low(4n, ihl), 5) == True{} : Bool}
  for +dscp: U32
  for +ecn: U32
  for +total_length: U32
  for +ident: U32
  for +flags: U32
  for +frag_offset: U32
  for +ttl: U32
  for +protocol: U32
  for +checksum: U32
  for +src: U32
  for +dst: U32
  for +options: List<&2, U32>
  for +e2: {B.len(options) == Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n) : Nat}
  {I4.Ipv4Header.verify(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, total_length, ident, flags, frag_offset, ttl, protocol, checksum, src, dst, B.Octets.of_list(options)})) == True{} : Bool}

# the hypotheses hold: IHL 5 and no options
law ipv4_build_verifies_sat:
  {(U32.is_ge(N.NetField.low(4n, 5), 5), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, 5))), 20n)) == (True{}, 0n) : Bool & Nat}
