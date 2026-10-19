# bend-osdev-x509, the certificate's ASN.1 types (RFC 5280 4.1, and
# Appendix A.1, whose module uses EXPLICIT TAGS) as bend-osdev-asn1
# schemas. The fields' contents are read from the match by the other files.
#
#   Certificate ::= SEQUENCE { tbsCertificate, signatureAlgorithm,
#                              signatureValue BIT STRING }
#   TBSCertificate ::= SEQUENCE {
#     version [0] EXPLICIT Version DEFAULT v1, serialNumber INTEGER,
#     signature AlgorithmIdentifier, issuer Name, validity Validity,
#     subject Name, subjectPublicKeyInfo SubjectPublicKeyInfo,
#     issuerUniqueID [1] IMPLICIT UniqueIdentifier OPTIONAL,
#     subjectUniqueID [2] IMPLICIT UniqueIdentifier OPTIONAL,
#     extensions [3] EXPLICIT Extensions OPTIONAL }
#   AlgorithmIdentifier ::= SEQUENCE { algorithm OBJECT IDENTIFIER,
#                                      parameters ANY OPTIONAL }
#   Name ::= SEQUENCE OF SET OF SEQUENCE { type OBJECT IDENTIFIER,
#                                          value ANY }
#   Validity ::= SEQUENCE { notBefore Time, notAfter Time }
#   SubjectPublicKeyInfo ::= SEQUENCE { algorithm AlgorithmIdentifier,
#                                       subjectPublicKey BIT STRING }
#   Extension ::= SEQUENCE { extnID OBJECT IDENTIFIER,
#                            critical BOOLEAN DEFAULT FALSE,
#                            extnValue OCTET STRING }
import Base
import ../asn1/tag.bend as AT
import ../asn1/prim.bend as AP
import ../asn1/build.bend as ABu
import ../asn1/schema.bend as ASc

def x5.s.alg() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.oid()), ASc.Asn1S.opt(ASc.Asn1S.any())])

def x5.s.atv() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.oid()), ASc.Asn1S.any()])

def x5.s.name() -> ASc.Asn1Schema:
  ASc.Asn1S.seq_of(ASc.Asn1S.set_of(x5.s.atv()))

def x5.s.validity() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.any(), ASc.Asn1S.any()])

def x5.s.spki() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([x5.s.alg(), ASc.Asn1S.elem(AT.Asn1Tag.bit_string())])

def x5.s.ext() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.elem(AT.Asn1Tag.oid()), ASc.Asn1SDefault{ASc.Asn1S.elem(AT.Asn1Tag.boolean()), AP.Asn1.bool(False{})}, ASc.Asn1S.elem(AT.Asn1Tag.octet_string())])

def x5.s.exts() -> ASc.Asn1Schema:
  ASc.Asn1S.seq_of(x5.s.ext())

# version v1 (0), the default
def x5.s.v1() -> ASc.Asn1Schema:
  ASc.Asn1SDefault{ASc.Asn1S.explicit(0n, ASc.Asn1S.elem(AT.Asn1Tag.integer())), ABu.Asn1.explicit(0n, AP.Asn1.int_nat(0n))}

def x5.s.tbs() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([x5.s.v1(), ASc.Asn1S.elem(AT.Asn1Tag.integer()), x5.s.alg(), x5.s.name(), x5.s.validity(), x5.s.name(), x5.s.spki(), ASc.Asn1S.opt(ASc.Asn1S.ctx(1n)), ASc.Asn1S.opt(ASc.Asn1S.ctx(2n)), ASc.Asn1S.opt(ASc.Asn1S.explicit(3n, x5.s.exts()))])

def x5.s.cert() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([x5.s.tbs(), x5.s.alg(), ASc.Asn1S.elem(AT.Asn1Tag.bit_string())])

# AlgorithmIdentifier and Name, for structures that hold them (PKCS, CMS)
def X509.schema_alg() -> ASc.Asn1Schema:
  x5.s.alg()

def X509.schema_name() -> ASc.Asn1Schema:
  x5.s.name()
