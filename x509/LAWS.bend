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
#   for;
# * cert_split, cert_whole: a certificate's octets are the input's first
#   octets (all of them when the rules refuse octets after it);
#   tbs_within, tbs_slice: the tbsCertificate's octets, which the signature
#   is over, are a slice of the certificate's octets, so of the input;
#   sig_alg_within: so are the outer signature algorithm's; issuer_within,
#   subject_within, spki_within, tbs_alg_within, ext_within: the names',
#   the key's, the inner signature algorithm's and each extension's octets
#   are slices of the tbsCertificate's.
#
# Vectors: RFC 5280 7.1's comparison (case folding, insignificant spaces,
# PrintableString against UTF8String) on two names that only it matches.
import Base
import ../bytes/bytes.bend as B
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/rules.bend as AR
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ../oid/oid.bend as O
import ./error.bend as XE
import ./rules.bend as XR
import ./alg.bend as XA
import ./spki.bend as XK
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

# The octets kept are the input's

law cert_split:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, rest => {B.Octets.append(X.X509Cert.raw(c), rest) == b : B.Octets}>

law cert_whole:
  for +r: XR.X509Rules
  for +ht: {AR.Asn1Rules.trailing(XR.X509Rules.asn1(r)) == False{} : Bool}
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  {X.X509Cert.raw(c) == b : B.Octets}

law tbs_slice:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {b == B.Octets.append(u, B.Octets.append(X.X509Cert.tbs_raw(c), v)) : B.Octets}>>

law tbs_within:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {X.X509Cert.raw(c) == B.Octets.append(u, B.Octets.append(X.X509Cert.tbs_raw(c), v)) : B.Octets}>>

law sig_alg_within:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {X.X509Cert.raw(c) == B.Octets.append(u, B.Octets.append(XA.X509AlgId.raw(X.X509Cert.sig_alg(c)), v)) : B.Octets}>>

law issuer_within:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {X.X509Cert.tbs_raw(c) == B.Octets.append(u, B.Octets.append(XN.X509Name.raw(X.X509Cert.issuer(c)), v)) : B.Octets}>>

law subject_within:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {X.X509Cert.tbs_raw(c) == B.Octets.append(u, B.Octets.append(XN.X509Name.raw(X.X509Cert.subject(c)), v)) : B.Octets}>>

law spki_within:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {X.X509Cert.tbs_raw(c) == B.Octets.append(u, B.Octets.append(XK.X509Spki.raw(X.X509Cert.spki(c)), v)) : B.Octets}>>

law tbs_alg_within:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {X.X509Cert.tbs_raw(c) == B.Octets.append(u, B.Octets.append(XA.X509AlgId.raw(X.X509Tbs.signature(X.X509Cert.tbs(c))), v)) : B.Octets}>>

law ext_within:
  for +r: XR.X509Rules
  for +b: B.Octets
  for +c: X.X509Cert
  for +pre: List<&2, XX.X509Ext>
  for +x: XX.X509Ext
  for +post: List<&2, XX.X509Ext>
  for +h: {X.X509Cert.extensions(c) == List.append(&2, XX.X509Ext, pre, Con{x, post}) : List<&2, XX.X509Ext>}
  for +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {X.X509Cert.tbs_raw(c) == B.Octets.append(u, B.Octets.append(XX.X509Ext.raw(x), v)) : B.Octets}>>

# Vectors: CN "Example  Org" as a PrintableString and CN "example org" as a
# UTF8String (RFC 5280 A.1: id-at-commonName is 2.5.4.3)

def x5l.cn(+t: Nat, +s: String) -> XN.X509Name:
  XN.X509Name{[[XN.X509Atv{O.Oid{[2n, 5n, 4n, 3n]}, AN.Asn1Prim{AT.Asn1Tag.universal(t), B.Octets.of_string(s)}}]], B.Octets.of_string(s)}

law vec_name_rfc5280:
  {(XC.X509Name.matches(XC.X509.name_rules(), x5l.cn(19n, "Example  Org"), x5l.cn(12n, "example org")), XC.X509Name.matches(XC.X509.name_rules_binary(), x5l.cn(19n, "Example  Org"), x5l.cn(12n, "example org"))) == (True{}, False{}) : Bool & Bool}
