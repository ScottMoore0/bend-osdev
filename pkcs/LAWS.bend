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
#   for;
# * signed_data_slice, signed_attrs_slice, certificate_slice: the
#   SignedData's octets, each signer's signed attributes' octets and each
#   certificate's octets are slices of the input;
#   signed_attrs_der: under the attrs_der rule, the octets a signer with
#   signed attributes signed (Cms.signed_message, RFC 5652 5.4) are the DER
#   of a SET OF elements (the attributes' elements, with SET's tag in place
#   of the IMPLICIT [0]).
#
# Vector: signed attributes' octets retagged with SET's tag (RFC 5652 5.4:
# A0 becomes 31, the rest unchanged).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/error.bend as AE
import ../asn1/encode.bend as AEn
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

# The octets kept are the input's

law signed_data_slice:
  for +r: PR.PkcsRules
  for +b: B.Octets
  for +s: P.CmsSignedData
  for +e: {P.Cms.parse(r, b) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {b == B.Octets.append(u, B.Octets.append(P.CmsSignedData.raw(s), v)) : B.Octets}>>

law signed_attrs_slice:
  for +r: PR.PkcsRules
  for +b: B.Octets
  for +s: P.CmsSignedData
  for +pre: List<&2, PG.CmsSigner>
  for +g: PG.CmsSigner
  for +post: List<&2, PG.CmsSigner>
  for +a: PG.CmsAttrs
  for +e: {P.Cms.parse(r, b) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}
  for +hg: {P.CmsSignedData.signers(s) == List.append(&2, PG.CmsSigner, pre, Con{g, post}) : List<&2, PG.CmsSigner>}
  for +ha: {PG.CmsSigner.signed_attrs(g) == Some{a} : Maybe<&2, PG.CmsAttrs>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {b == B.Octets.append(u, B.Octets.append(PG.CmsAttrs.raw(a), v)) : B.Octets}>>

law certificate_slice:
  for +r: PR.PkcsRules
  for +b: B.Octets
  for +s: P.CmsSignedData
  for +pre: List<&2, B.Octets>
  for +o: B.Octets
  for +post: List<&2, B.Octets>
  for +e: {P.Cms.parse(r, b) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}
  for +hc: {P.CmsSignedData.certificates(s) == List.append(&2, B.Octets, pre, Con{o, post}) : List<&2, B.Octets>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {b == B.Octets.append(u, B.Octets.append(o, v)) : B.Octets}>>

law signed_attrs_der:
  for +r: PR.PkcsRules
  for +b: B.Octets
  for +s: P.CmsSignedData
  for +pre: List<&2, PG.CmsSigner>
  for +g: PG.CmsSigner
  for +post: List<&2, PG.CmsSigner>
  for +a: PG.CmsAttrs
  for +c: B.Octets
  for +e: {P.Cms.parse(r, b) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}
  for +hg: {P.CmsSignedData.signers(s) == List.append(&2, PG.CmsSigner, pre, Con{g, post}) : List<&2, PG.CmsSigner>}
  for +ha: {PG.CmsSigner.signed_attrs(g) == Some{a} : Maybe<&2, PG.CmsAttrs>}
  for +hd: {PR.PkcsRules.attrs_der(r) == True{} : Bool}
  Sigma<&1, &1, List<&2, AN.Asn1Node>, ns => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), ns}) == Done{PS.Cms.signed_message(g, c)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>

law vec_set_tagged:
  {PS.Cms.set_tagged(B.Octets.of_list([160, 3, 2, 1, 5])) == B.Octets.of_list([49, 3, 2, 1, 5]) : B.Octets}
