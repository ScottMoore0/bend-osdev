# Laws of bend-osdev-pkcs, for every input:
#
# * cms_parsed_conforms: a SignedData Cms.parse answers passes every check
#   its rules ask for (CmsSignedData.conforms): with Pkcs.rules(), its
#   versions are RFC 5652's, its signed attributes are DER and hold the
#   content-type and message-digest attributes;
# * p8_parsed_conforms: likewise for PKCS #8 keys (Pkcs8Key.conforms);
# * signed_without_attrs: a signer without signed attributes signed the
#   content itself (RFC 5652 5.4);
# * verify_signed_if: for every signature scheme (crypto's interface, with
#   its laws as hypotheses), a signer whose signature is the scheme's
#   signature of Cms.signed_message verifies under the signer's public-key
#   bytes: Cms.verify_with checks exactly the octets 5.4 says were signed;
# * find_attr_type: the attribute Cms.find_attr finds has the type asked
#   for.
#
# Vector: signed attributes' octets retagged with SET's tag (RFC 5652 5.4:
# A0 becomes 31, the rest unchanged).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../oid/oid.bend as O
import ./error.bend as PE
import ./rules.bend as PR
import ./attr.bend as PA
import ./signer.bend as PG
import ./pkcs.bend as P
import ./signed.bend as PS
import ./p8.bend as P8

law cms_parsed_conforms:
  for +r: PR.PkcsRules
  for +b: B.Octets
  for +s: P.CmsSignedData
  for +e: {P.Cms.parse(r, b) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}
  {P.CmsSignedData.conforms(r, s) == True{} : Bool}

law p8_parsed_conforms:
  for +r: PR.PkcsRules
  for +b: B.Octets
  for +k: P8.Pkcs8Key
  for +e: {P8.Pkcs8.parse(r, b) == Done{k} : Result<&2, &2, PE.PkcsError, P8.Pkcs8Key>}
  {P8.Pkcs8Key.conforms(r, k) == True{} : Bool}

law signed_without_attrs:
  for +g: PG.CmsSigner
  for +c: B.Octets
  for +h: {PG.CmsSigner.signed_attrs(g) == None{} : Maybe<&2, PG.CmsAttrs>}
  {PS.Cms.signed_message(g, c) == c : B.Octets}

law verify_signed_if:
  for ~SK: Data
  for ~PK: Data
  for ~public: SK -> PK
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~pk_to: PK -> B.Octets
  for ~sign: SK -> B.Octets -> B.Octets
  for ~verify: PK -> B.Octets -> B.Octets -> Bool
  for +sk: SK
  for +g: PG.CmsSigner
  for +c: B.Octets
  for hf: {pk_of(pk_to(public(sk))) == Done{public(sk)} : Result<&2, &2, Cr.CrError, PK>}
  for ha: {verify(public(sk), PS.Cms.signed_message(g, c), sign(sk, PS.Cms.signed_message(g, c))) == True{} : Bool}
  for hs: {PG.CmsSigner.signature(g) == sign(sk, PS.Cms.signed_message(g, c)) : B.Octets}
  {PS.Cms.verify_with(~PK, ~pk_of, ~verify, pk_to(public(sk)), g, c) == True{} : Bool}

law find_attr_type:
  for +xs: List<&2, PA.CmsAttr>
  for +id: O.Oid
  for +a: PA.CmsAttr
  for +e: {PA.Cms.find_attr(xs, id) == Some{a} : Maybe<&2, PA.CmsAttr>}
  {O.Oid.is_eq(PA.CmsAttr.attr_type(a), id) == True{} : Bool}

law vec_set_tagged:
  {PS.Cms.set_tagged(B.Octets.of_list([160, 3, 2, 1, 5])) == B.Octets.of_list([49, 3, 2, 1, 5]) : B.Octets}
