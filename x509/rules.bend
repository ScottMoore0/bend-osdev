# bend-osdev-x509, what a parse accepts: every choice RFC 5280 leaves to the
# reader, or that a reader may want to relax, as a field.
#
#   asn1              the encoding rules (RFC 5280 4.1: certificates are DER)
#   pivot             the UTCTime century: YY at or above it is 19YY
#                     (4.1.2.5.1: 50)
#   time_profile      UTCTime for years through 2049, GeneralizedTime from
#                     2050, both in Zulu time with seconds, without
#                     fractions (4.1.2.5, 4.1.2.5.1, 4.1.2.5.2)
#   alg_match         the outer signatureAlgorithm is the tbsCertificate's
#                     signature field (4.1.1.2)
#   versions          version v1, v2 or v3; unique identifiers only in v2
#                     and v3 (4.1.2.8); extensions only in v3, and one or
#                     more when present (4.1.2.9)
#   distinct_ext      no extension twice (4.2)
#   known_ext         the extensions read here (basicConstraints, keyUsage,
#                     subjectKeyIdentifier, authorityKeyIdentifier,
#                     subjectAltName, extKeyUsage) must be well formed
#   unknown_critical  refuse a critical extension not read here (4.2 asks
#                     this of a certificate-using system)
#   serial            the serial number positive and at most 20 octets
#                     (4.1.2.2; certificate users SHOULD handle others)
#   issuer_nonempty   the issuer a non-empty name (4.1.2.4)
import Base
import ../asn1/rules.bend as AR

type X509Rules is Data:
  X509Rules{asn1: AR.Asn1Rules, pivot: Nat, time_profile: Bool, alg_match: Bool, versions: Bool, distinct_ext: Bool, known_ext: Bool, unknown_critical: Bool, serial: Bool, issuer_nonempty: Bool}

# RFC 5280's profile as a certificate user reads it: DER, every check but
# unknown critical extensions (left to the validator, as 4.2 places it) and
# the serial number's (4.1.2.2: users SHOULD handle non-conforming ones)
def X509.rules() -> X509Rules:
  X509Rules{AR.Asn1Rules.der(), 50n, True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}}

# every check
def X509.rules_strict() -> X509Rules:
  X509Rules{AR.Asn1Rules.der(), 50n, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}}

# BER, and none of the profile's checks
def X509.rules_lenient() -> X509Rules:
  X509Rules{AR.Asn1Rules.ber(), 50n, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}}

def X509Rules.asn1(r: X509Rules) -> AR.Asn1Rules:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      a

def X509Rules.pivot(r: X509Rules) -> Nat:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      p

def X509Rules.time_profile(r: X509Rules) -> Bool:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      t

def X509Rules.alg_match(r: X509Rules) -> Bool:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      am

def X509Rules.versions(r: X509Rules) -> Bool:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      v

def X509Rules.distinct_ext(r: X509Rules) -> Bool:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      d

def X509Rules.known_ext(r: X509Rules) -> Bool:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      k

def X509Rules.unknown_critical(r: X509Rules) -> Bool:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      u

def X509Rules.serial(r: X509Rules) -> Bool:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      s

def X509Rules.issuer_nonempty(r: X509Rules) -> Bool:
  match r:
    case X509Rules{a, p, t, am, v, d, k, u, s, i}:
      i
