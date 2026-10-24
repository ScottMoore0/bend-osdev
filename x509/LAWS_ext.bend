# Laws of bend-osdev-x509's extension readers (extval.bend), for every
# input: an extension whose value is the DER that bend-osdev-asn1's writer
# writes for a value reads back as that value, under any rules.
#
# * key_usage_round_trip: keyUsage (RFC 5280 4.2.1.3), a well-formed BIT
#   STRING whose unused bits are zero (asn1's LAWS_typed.bend,
#   asn1law.bits_clear: DER's form of a named bit list);
# * subject_key_id_round_trip: subjectKeyIdentifier (4.2.1.2), an OCTET
#   STRING.
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/encode.bend as AEn
import ../asn1/prim.bend as AP
import ../asn1/bits.bend as ABi
import ../asn1/LAWS_typed.bend as ALT
import ../oid/oid.bend as O
import ./error.bend as XE
import ./rules.bend as XR
import ./ext.bend as XX
import ./extval.bend as XV

law key_usage_round_trip:
  for +r: XR.X509Rules
  for +id: O.Oid
  for +crit: Bool
  for +raw: B.Octets
  for +u: Nat
  for +o: B.Octets
  for +hok: {ABi.Asn1Bits.ok(ABi.Asn1Bits{u, o}) == True{} : Bool}
  for +hc: {ALT.asn1law.bits_clear(u, o) == True{} : Bool}
  for +v: B.Octets
  for +he: {AEn.Asn1.encode(ABi.Asn1.bits(ABi.Asn1Bits{u, o})) == Done{v} : Result<&2, &2, AE.Asn1Error, B.Octets>}
  {XV.X509.key_usage_of(r, XX.X509Ext{id, crit, v, raw}) == Done{ABi.Asn1Bits{u, o}} : Result<&2, &2, XE.X509Error, ABi.Asn1Bits>}

law subject_key_id_round_trip:
  for +r: XR.X509Rules
  for +id: O.Oid
  for +crit: Bool
  for +raw: B.Octets
  for +o: B.Octets
  for +v: B.Octets
  for +he: {AEn.Asn1.encode(AP.Asn1.octets(o)) == Done{v} : Result<&2, &2, AE.Asn1Error, B.Octets>}
  {XV.X509.subject_key_id_of(r, XX.X509Ext{id, crit, v, raw}) == Done{o} : Result<&2, &2, XE.X509Error, B.Octets>}
