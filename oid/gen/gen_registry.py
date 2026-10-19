#!/usr/bin/env python3
"""Writes oid/registry.bend, the table of object identifiers and their names.
Run from the package directory:  python3 gen/gen_registry.py > registry.bend

Each entry: the name as the registering document's ASN.1 module writes it,
the kind, the arcs, and the source. Sources:

  RFC5280  RFC 5280 (May 2008), Appendix A.1 (attribute types, id-pe, id-qt,
           id-ad, id-kp) and A.2 (id-ce extensions); 4.2.1.12 (key purposes)
  RFC8017  RFC 8017, PKCS #1 v2.2 (November 2016), Appendix C (RSA and the
           hash functions)
  RFC3279  RFC 3279 (April 2002) (DSA, DH, ECDSA with SHA-1)
  RFC5480  RFC 5480 (March 2009) (EC public keys and the named curves)
  RFC5758  RFC 5758 (January 2010) (ECDSA and DSA with SHA-2)
  RFC8410  RFC 8410 (August 2018) (Ed25519, Ed448, X25519, X448)
  RFC5652  RFC 5652, CMS (September 2009) (content types and attributes)
  RFC2315  RFC 2315, PKCS #7 v1.5 (March 1998) (signedAndEnvelopedData)
  CSOR     NIST Computer Security Objects Register, algorithm registration
           (SHA-3 and SHAKE, ECDSA and RSA with SHA-3)
"""
E = []
def add(kind, src, base, items):
    for name, tail in items:
        arcs = [int(x) for x in base.split(".")] + ([tail] if isinstance(tail, int) else list(tail))
        E.append((name, kind, arcs, src))

PKCS1 = "1.2.840.113549.1.1"
add("Hash", "RFC8017", "1.2.840.113549.2", [("id-md2", 2), ("id-md5", 5)])
add("Hash", "RFC8017", "1.3.14.3.2", [("id-sha1", 26)])
add("Hash", "RFC8017", "2.16.840.1.101.3.4.2", [("id-sha256", 1), ("id-sha384", 2), ("id-sha512", 3), ("id-sha224", 4), ("id-sha512-224", 5), ("id-sha512-256", 6)])
add("Hash", "CSOR", "2.16.840.1.101.3.4.2", [("id-sha3-224", 7), ("id-sha3-256", 8), ("id-sha3-384", 9), ("id-sha3-512", 10), ("id-shake128", 11), ("id-shake256", 12)])
add("KeyAlg", "RFC8017", PKCS1, [("rsaEncryption", 1), ("id-RSAES-OAEP", 7), ("id-mgf1", 8), ("id-pSpecified", 9)])
add("SigAlg", "RFC8017", PKCS1, [("md2WithRSAEncryption", 2), ("md5WithRSAEncryption", 4), ("sha1WithRSAEncryption", 5), ("id-RSASSA-PSS", 10), ("sha256WithRSAEncryption", 11), ("sha384WithRSAEncryption", 12), ("sha512WithRSAEncryption", 13), ("sha224WithRSAEncryption", 14), ("sha512-224WithRSAEncryption", 15), ("sha512-256WithRSAEncryption", 16)])
add("KeyAlg", "RFC3279", "1.2.840.10040.4", [("id-dsa", 1)])
add("SigAlg", "RFC3279", "1.2.840.10040.4", [("id-dsa-with-sha1", 3)])
add("KeyAlg", "RFC3279", "1.2.840.10046.2", [("dhpublicnumber", 1)])
add("SigAlg", "RFC3279", "1.2.840.10045.4", [("ecdsa-with-SHA1", 1)])
add("SigAlg", "RFC5758", "1.2.840.10045.4.3", [("ecdsa-with-SHA224", 1), ("ecdsa-with-SHA256", 2), ("ecdsa-with-SHA384", 3), ("ecdsa-with-SHA512", 4)])
add("SigAlg", "RFC5758", "2.16.840.1.101.3.4.3", [("id-dsa-with-sha224", 1), ("id-dsa-with-sha256", 2)])
add("SigAlg", "CSOR", "2.16.840.1.101.3.4.3", [("id-ecdsa-with-sha3-224", 9), ("id-ecdsa-with-sha3-256", 10), ("id-ecdsa-with-sha3-384", 11), ("id-ecdsa-with-sha3-512", 12), ("id-rsassa-pkcs1-v1-5-with-sha3-224", 13), ("id-rsassa-pkcs1-v1-5-with-sha3-256", 14), ("id-rsassa-pkcs1-v1-5-with-sha3-384", 15), ("id-rsassa-pkcs1-v1-5-with-sha3-512", 16)])
add("KeyAlg", "RFC5480", "1.2.840.10045.2", [("id-ecPublicKey", 1)])
add("KeyAlg", "RFC5480", "1.3.132.1", [("id-ecDH", 12), ("id-ecMQV", 13)])
add("Curve", "RFC5480", "1.2.840.10045.3.1", [("secp192r1", 1), ("secp256r1", 7)])
add("Curve", "RFC5480", "1.3.132.0", [("sect163k1", 1), ("sect163r2", 15), ("sect283k1", 16), ("sect283r1", 17), ("sect233k1", 26), ("sect233r1", 27), ("secp224r1", 33), ("secp384r1", 34), ("secp521r1", 35), ("sect409k1", 36), ("sect409r1", 37), ("sect571k1", 38), ("sect571r1", 39)])
add("KeyAlg", "RFC8410", "1.3.101", [("id-X25519", 110), ("id-X448", 111)])
add("SigAlg", "RFC8410", "1.3.101", [("id-Ed25519", 112), ("id-Ed448", 113)])
add("Attribute", "RFC5280", "2.5.4", [("id-at-commonName", 3), ("id-at-surname", 4), ("id-at-serialNumber", 5), ("id-at-countryName", 6), ("id-at-localityName", 7), ("id-at-stateOrProvinceName", 8), ("id-at-organizationName", 10), ("id-at-organizationalUnitName", 11), ("id-at-title", 12), ("id-at-name", 41), ("id-at-givenName", 42), ("id-at-initials", 43), ("id-at-generationQualifier", 44), ("id-at-dnQualifier", 46), ("id-at-pseudonym", 65)])
add("Attribute", "RFC5280", "0.9.2342.19200300.100.1", [("id-domainComponent", 25)])
add("Attribute", "RFC5280", "1.2.840.113549.1.9", [("id-emailAddress", 1)])
add("Extension", "RFC5280", "2.5.29", [("id-ce-subjectDirectoryAttributes", 9), ("id-ce-subjectKeyIdentifier", 14), ("id-ce-keyUsage", 15), ("id-ce-privateKeyUsagePeriod", 16), ("id-ce-subjectAltName", 17), ("id-ce-issuerAltName", 18), ("id-ce-basicConstraints", 19), ("id-ce-cRLNumber", 20), ("id-ce-nameConstraints", 30), ("id-ce-cRLDistributionPoints", 31), ("id-ce-certificatePolicies", 32), ("id-ce-policyMappings", 33), ("id-ce-authorityKeyIdentifier", 35), ("id-ce-policyConstraints", 36), ("id-ce-extKeyUsage", 37), ("id-ce-freshestCRL", 46), ("id-ce-inhibitAnyPolicy", 54)])
add("Extension", "RFC5280", "1.3.6.1.5.5.7.1", [("id-pe-authorityInfoAccess", 1), ("id-pe-subjectInfoAccess", 11)])
add("KeyPurpose", "RFC5280", "1.3.6.1.5.5.7.3", [("id-kp-serverAuth", 1), ("id-kp-clientAuth", 2), ("id-kp-codeSigning", 3), ("id-kp-emailProtection", 4), ("id-kp-timeStamping", 8), ("id-kp-OCSPSigning", 9)])
add("Other", "RFC5280", "1.3.6.1.5.5.7.2", [("id-qt-cps", 1), ("id-qt-unotice", 2)])
add("Other", "RFC5280", "1.3.6.1.5.5.7.48", [("id-ad-ocsp", 1), ("id-ad-caIssuers", 2)])
add("ContentType", "RFC5652", "1.2.840.113549.1.7", [("id-data", 1), ("id-signedData", 2), ("id-envelopedData", 3), ("id-digestedData", 5), ("id-encryptedData", 6)])
add("ContentType", "RFC2315", "1.2.840.113549.1.7", [("signedAndEnvelopedData", 4)])
add("ContentType", "RFC5652", "1.2.840.113549.1.9.16.1", [("id-ct-authData", 2), ("id-ct-contentInfo", 6)])
add("CmsAttribute", "RFC5652", "1.2.840.113549.1.9", [("id-contentType", 3), ("id-messageDigest", 4), ("id-signingTime", 5), ("id-countersignature", 6)])

KINDS = ["Hash", "SigAlg", "KeyAlg", "Curve", "Attribute", "Extension", "KeyPurpose", "ContentType", "CmsAttribute", "Other"]
SRCS = sorted({e[3] for e in E})
names = [e[0] for e in E]
assert len(names) == len(set(names)), "duplicate names"
arcss = [tuple(e[2]) for e in E]
assert len(arcss) == len(set(arcss)), "duplicate arcs"

out = []
p = out.append
p("""# Generated by gen/gen_registry.py: do not edit.
#
# bend-osdev-oid, the registry: object identifiers X.509 and PKCS use, with
# the names their registering documents' ASN.1 modules give them, their
# kinds and their sources (README.md, "Registry", cites each source).
import Base
import ./oid.bend as O

type OidKind is Data:""")
for k in KINDS:
    p("  OidKind%s{}" % k)
p("""
type OidSource is Data:""")
for s in SRCS:
    p("  OidSrc%s{}" % s)
p("""
type OidEntry is Data:
  OidEntry{name: String, kind: OidKind, arcs: List<&2, Nat>, source: OidSource}

def OidEntry.name(e: OidEntry) -> String:
  match e:
    case OidEntry{n, k, a, s}:
      n

def OidEntry.kind(e: OidEntry) -> OidKind:
  match e:
    case OidEntry{n, k, a, s}:
      k

def OidEntry.arcs(e: OidEntry) -> List<&2, Nat>:
  match e:
    case OidEntry{n, k, a, s}:
      a

def OidEntry.source(e: OidEntry) -> OidSource:
  match e:
    case OidEntry{n, k, a, s}:
      s

def OidSource.name(s: OidSource) -> String:
  match s:""")
for s in SRCS:
    p('    case OidSrc%s{}:\n      "%s"' % (s, s))
p("""
def OidKind.name(k: OidKind) -> String:
  match k:""")
for k in KINDS:
    p('    case OidKind%s{}:\n      "%s"' % (k, k))
# the table, in pieces of 20 entries (list literals stay small)
chunks = [E[i:i + 20] for i in range(0, len(E), 20)]
for ci, ch in enumerate(chunks):
    p("\ndef oid.reg%d() -> List<&2, OidEntry>:\n  [" % ci + ", ".join('OidEntry{"%s", OidKind%s{}, [%s], OidSrc%s{}}' % (n, k, ", ".join("%dn" % a for a in arcs), s) for (n, k, arcs, s) in ch) + "]")
p("""
# every entry
def Oid.registry() -> List<&2, OidEntry>:
  """ + "".join("List.append(&2, OidEntry, oid.reg%d(), " % ci for ci in range(len(chunks) - 1)) + "oid.reg%d()" % (len(chunks) - 1) + ")" * (len(chunks) - 1) + """

def oid.find_arcs.pick(hit: Bool, e: OidEntry, r: Maybe<&2, OidEntry>) -> Maybe<&2, OidEntry>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      r

def oid.find_arcs(es: List<&2, OidEntry>, +arcs: List<&2, Nat>) -> Maybe<&2, OidEntry>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, t}:
      oid.find_arcs.pick(O.oid.eq(OidEntry.arcs(e), arcs), e, oid.find_arcs(t, arcs))

def oid.find_name(es: List<&2, OidEntry>, +name: String) -> Maybe<&2, OidEntry>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, t}:
      oid.find_arcs.pick(String.eq(OidEntry.name(e), name), e, oid.find_name(t, name))

# o's entry in the registry
def Oid.lookup(o: O.Oid) -> Maybe<&2, OidEntry>:
  oid.find_arcs(Oid.registry(), O.Oid.arcs(o))

# o's registered name
def Oid.name(o: O.Oid) -> Maybe<&2, String>:
  Maybe.map(&2, OidEntry, String, e => OidEntry.name(e), Oid.lookup(o))

# the entry registered under a name
def oid.entry(name: String) -> Maybe<&2, OidEntry>:
  oid.find_name(Oid.registry(), name)

# the Oid registered under a name
def Oid.named(name: String) -> Maybe<&2, O.Oid>:
  Maybe.map(&2, OidEntry, O.Oid, e => O.Oid{OidEntry.arcs(e)}, oid.entry(name))

# the arcs registered under a name (none if it is not registered)
def Oid.arcs_of(name: String) -> List<&2, Nat>:
  Maybe.default(&2, List<&2, Nat>, Maybe.map(&2, OidEntry, List<&2, Nat>, e => OidEntry.arcs(e), oid.entry(name)), Nil{})

# whether o is the Oid registered under a name
def Oid.is_named(o: O.Oid, name: String) -> Bool:
  O.oid.eq(O.Oid.arcs(o), Oid.arcs_of(name))""")
print("\n".join(out))
