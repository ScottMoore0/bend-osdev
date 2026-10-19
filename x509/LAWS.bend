# Laws of bend-osdev-x509, for every input:
#
# * parsed_conforms: a certificate X509.parse answers passes every check its
#   rules ask for (X509Cert.conforms): with X509.rules(), its version agrees
#   with its fields, its two signature algorithms are the same octets, its
#   issuer is not empty, its times follow the profile, no extension appears
#   twice and every extension read here is well formed;
# * verify_signed_if: for every signature scheme (crypto's interface, with
#   its laws as hypotheses), a certificate whose signature is the issuer's
#   signature of its tbsCertificate octets verifies under the issuer's
#   public-key bytes: X509.verify_with checks exactly those octets;
# * name_match_refl: every name matches itself, under any name rules;
# * name_match_binary: under binary comparison, names match exactly when
#   their DER octets are the same;
# * find_ext_id: the extension X509.find_ext finds has the identifier asked
#   for.
#
# Vectors: RFC 5280 7.1's comparison (case folding, insignificant spaces,
# PrintableString against UTF8String) on two names that only it matches.
import Base
import ../bytes/bytes.bend as B
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ../oid/oid.bend as O
import ./error.bend as XE
import ./rules.bend as XR
import ./name.bend as XN
import ./namecmp.bend as XC
import ./ext.bend as XX
import ./x509.bend as X
import ./verify.bend as XV

law parsed_conforms:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  {X.X509Cert.conforms(r, c) == True{} : Bool}

law verify_signed_if:
  for ~SK: Data
  for ~PK: Data
  for ~public: SK -> PK
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~pk_to: PK -> B.Octets
  for ~sign: SK -> B.Octets -> B.Octets
  for ~verify: PK -> B.Octets -> B.Octets -> Bool
  for +sk: SK
  for +c: X.X509Cert
  for hf: {pk_of(pk_to(public(sk))) == Done{public(sk)} : Result<&2, &2, Cr.CrError, PK>}
  for ha: {verify(public(sk), X.X509Cert.tbs_raw(c), sign(sk, X.X509Cert.tbs_raw(c))) == True{} : Bool}
  for hs: {X.X509Cert.signature_octets(c) == sign(sk, X.X509Cert.tbs_raw(c)) : B.Octets}
  {XV.X509.verify_with(~PK, ~pk_of, ~verify, pk_to(public(sk)), c) == True{} : Bool}

law name_match_refl:
  for +r: XC.X509NameRules
  for +n: XN.X509Name
  {XC.X509Name.matches(r, n, n) == True{} : Bool}

law name_match_binary:
  for +a: XN.X509Name
  for +b: XN.X509Name
  {XC.X509Name.matches(XC.X509.name_rules_binary(), a, b) == B.Octets.is_eq(XN.X509Name.raw(a), XN.X509Name.raw(b)) : Bool}

law find_ext_id:
  for +es: List<&2, XX.X509Ext>
  for +id: O.Oid
  for +x: XX.X509Ext
  for +e: {XX.X509.find_ext(es, id) == Some{x} : Maybe<&2, XX.X509Ext>}
  {O.Oid.is_eq(XX.X509Ext.id(x), id) == True{} : Bool}

# Vectors: CN "Example  Org" as a PrintableString and CN "example org" as a
# UTF8String (RFC 5280 A.1: id-at-commonName is 2.5.4.3)

def x5l.cn(+t: Nat, +s: String) -> XN.X509Name:
  XN.X509Name{[[XN.X509Atv{O.Oid{[2n, 5n, 4n, 3n]}, AN.Asn1Prim{AT.Asn1Tag.universal(t), B.Octets.of_string(s)}}]], B.Octets.of_string(s)}

law vec_name_rfc5280:
  {(XC.X509Name.matches(XC.X509.name_rules(), x5l.cn(19n, "Example  Org"), x5l.cn(12n, "example org")), XC.X509Name.matches(XC.X509.name_rules_binary(), x5l.cn(19n, "Example  Org"), x5l.cn(12n, "example org"))) == (True{}, False{}) : Bool & Bool}
