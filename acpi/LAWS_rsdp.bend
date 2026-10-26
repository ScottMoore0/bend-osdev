# The RSDP's whole round trip (5.2.5.3), for every input: what
# AcpiRsdp.build writes, AcpiRsdp.parse reads back, both checksums passing
# (LAWS_checksum.bend). A revision 0 or 1 RSDP is the first 20 bytes; a
# revision 2 or later one adds the extended fields, its Length being the 36
# that build writes. The OEMID must be 6 bytes (build fits it to 6) and the
# revision a byte.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./rsdp.bend as P

law rsdp_v1_round_trip:
  for +oem: B.Octets
  for +oem6: {B.Octets.len(oem) == 6n : Nat}
  for +rev: U32
  for +rev8: {B.byte(rev) == rev : U32}
  for +rev2: {U32.is_lt(rev, 2) == True{} : Bool}
  for +rsdt: U32
  {P.AcpiRsdp.parse(P.AcpiRsdp.build(P.AcpiRsdp{oem, rev, rsdt, None{}})) == Done{P.AcpiRsdp{oem, rev, rsdt, None{}}} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}

law rsdp_v2_round_trip:
  for +oem: B.Octets
  for +oem6: {B.Octets.len(oem) == 6n : Nat}
  for +rev: U32
  for +rev8: {B.byte(rev) == rev : U32}
  for +rev2: {U32.is_lt(rev, 2) == False{} : Bool}
  for +rsdt: U32
  for +l: U32
  for +x: W.W64
  {P.AcpiRsdp.parse(P.AcpiRsdp.build(P.AcpiRsdp{oem, rev, rsdt, Some{P.AcpiRsdpExt{l, x}}})) == Done{P.AcpiRsdp{oem, rev, rsdt, Some{P.AcpiRsdpExt{36, x}}}} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}

# the hypotheses hold at an example: a 6-byte OEMID, revisions 1 and 2
law rsdp_round_trip_example:
  {(B.Octets.len(B.Octets.of_string("BENDOS")), B.byte(2), U32.is_lt(1, 2), U32.is_lt(2, 2)) == (6n, 2, True{}, False{}) : Nat & U32 & Bool & Bool}
