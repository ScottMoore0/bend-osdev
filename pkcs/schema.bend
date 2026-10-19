# bend-osdev-pkcs, the ASN.1 types as bend-osdev-asn1 schemas (RFC 5652
# section 12.1's module, IMPLICIT TAGS; RFC 2315's SignedData has the same
# shape; RFC 5958 section 2 for keys):
#
#   ContentInfo ::= SEQUENCE { contentType OBJECT IDENTIFIER,
#                              content [0] EXPLICIT ANY }
#   SignedData ::= SEQUENCE { version CMSVersion,
#     digestAlgorithms SET OF DigestAlgorithmIdentifier,
#     encapContentInfo EncapsulatedContentInfo,
#     certificates [0] IMPLICIT CertificateSet OPTIONAL,
#     crls [1] IMPLICIT RevocationInfoChoices OPTIONAL,
#     signerInfos SET OF SignerInfo }
#   EncapsulatedContentInfo ::= SEQUENCE { eContentType OBJECT IDENTIFIER,
#     eContent [0] EXPLICIT OCTET STRING OPTIONAL }
#   SignerInfo ::= SEQUENCE { version CMSVersion, sid SignerIdentifier,
#     digestAlgorithm, signedAttrs [0] IMPLICIT SignedAttributes OPTIONAL,
#     signatureAlgorithm, signature OCTET STRING,
#     unsignedAttrs [1] IMPLICIT UnsignedAttributes OPTIONAL }
#   SignerIdentifier ::= CHOICE { issuerAndSerialNumber SEQUENCE {
#     issuer Name, serialNumber INTEGER },
#     subjectKeyIdentifier [0] SubjectKeyIdentifier }
#   Attribute ::= SEQUENCE { attrType OBJECT IDENTIFIER,
#                            attrValues SET OF AttributeValue }
#   OneAsymmetricKey ::= SEQUENCE { version, privateKeyAlgorithm,
#     privateKey OCTET STRING, attributes [0] IMPLICIT Attributes OPTIONAL,
#     publicKey [1] IMPLICIT BIT STRING OPTIONAL }
#
# OCTET STRINGs are matched as any element, so BER's constructed form is
# read too; certificates and CRLs are kept as their octets.
import Base
import ../asn1/tag.bend as AT
import ../asn1/schema.bend as ASc
import ../x509/schema.bend as XS

def pk.s.content_info() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.oid()), ASc.Asn1S.opt(ASc.Asn1S.explicit(0n, ASc.Asn1S.any()))])

def pk.s.attr() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.oid()), ASc.Asn1S.set_of(ASc.Asn1S.any())])

def pk.s.attrs(+n: Nat) -> ASc.Asn1Schema:
  ASc.Asn1SOf{AT.Asn1Tag.context(n), pk.s.attr(), True{}}

def pk.s.sid() -> ASc.Asn1Schema:
  ASc.Asn1SChoice{[ASc.Asn1S.seq([XS.X509.schema_name(), ASc.Asn1S.elem(AT.Asn1Tag.integer())]), ASc.Asn1S.ctx(0n)]}

def pk.s.signer() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.integer()), pk.s.sid(), XS.X509.schema_alg(), ASc.Asn1S.opt(pk.s.attrs(0n)), XS.X509.schema_alg(), ASc.Asn1S.any(), ASc.Asn1S.opt(pk.s.attrs(1n))])

def pk.s.encap() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.oid()), ASc.Asn1S.opt(ASc.Asn1S.explicit(0n, ASc.Asn1S.any()))])

def pk.s.signed_data() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.integer()), ASc.Asn1S.set_of(XS.X509.schema_alg()), pk.s.encap(), ASc.Asn1S.opt(ASc.Asn1SOf{AT.Asn1Tag.context(0n), ASc.Asn1S.any(), True{}}), ASc.Asn1S.opt(ASc.Asn1SOf{AT.Asn1Tag.context(1n), ASc.Asn1S.any(), True{}}), ASc.Asn1S.set_of(pk.s.signer())])

def pk.s.key() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.integer()), XS.X509.schema_alg(), ASc.Asn1S.any(), ASc.Asn1S.opt(pk.s.attrs(0n)), ASc.Asn1S.opt(ASc.Asn1S.ctx(1n))])
