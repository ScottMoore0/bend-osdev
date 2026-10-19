# bend-osdev-pkcs, what a parse accepts: each choice as a field.
#
#   asn1            the encoding rules: CMS values are BER (RFC 5652
#                   section 1), and streaming signers write indefinite
#                   lengths
#   attrs_der       signed attributes in DER (RFC 5652 5.3), as the
#                   signature is over their DER (5.4)
#   attrs_required  signed attributes present when the content type is not
#                   id-data, and when present holding one content-type
#                   attribute equal to the content type and one
#                   message-digest attribute, each with one value (5.3,
#                   11.1, 11.2)
#   versions        SignedData's version as 5.1 sets it, each SignerInfo's
#                   as 5.3 does (1 with issuerAndSerialNumber, 3 with
#                   subjectKeyIdentifier); a PKCS #8 key's v1 or v2, v2
#                   when it carries its public key (RFC 5958 section 2)
#   digests_listed  each signer's digest algorithm among digestAlgorithms
#                   (5.1: SHOULD)
import Base
import ../asn1/rules.bend as AR

type PkcsRules is Data:
  PkcsRules{asn1: AR.Asn1Rules, attrs_der: Bool, attrs_required: Bool, versions: Bool, digests_listed: Bool}

# RFC 5652's requirements (MUST), on BER
def Pkcs.rules() -> PkcsRules:
  PkcsRules{AR.Asn1Rules.ber(), True{}, True{}, True{}, False{}}

# and its recommendation (SHOULD)
def Pkcs.rules_strict() -> PkcsRules:
  PkcsRules{AR.Asn1Rules.ber(), True{}, True{}, True{}, True{}}

# BER, and no checks
def Pkcs.rules_lenient() -> PkcsRules:
  PkcsRules{AR.Asn1Rules.ber(), False{}, False{}, False{}, False{}}

def PkcsRules.asn1(r: PkcsRules) -> AR.Asn1Rules:
  match r:
    case PkcsRules{a, d, q, v, l}:
      a

def PkcsRules.attrs_der(r: PkcsRules) -> Bool:
  match r:
    case PkcsRules{a, d, q, v, l}:
      d

def PkcsRules.attrs_required(r: PkcsRules) -> Bool:
  match r:
    case PkcsRules{a, d, q, v, l}:
      q

def PkcsRules.versions(r: PkcsRules) -> Bool:
  match r:
    case PkcsRules{a, d, q, v, l}:
      v

def PkcsRules.digests_listed(r: PkcsRules) -> Bool:
  match r:
    case PkcsRules{a, d, q, v, l}:
      l
