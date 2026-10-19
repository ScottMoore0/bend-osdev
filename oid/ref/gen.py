#!/usr/bin/env python3
"""Differential test cases for bend-osdev-oid.

Two references, the system's tools:

* OpenSSL: `openssl asn1parse -genstr OID:<text>` writes the DER element of
  dotted text (or of a name OpenSSL knows), and `openssl asn1parse -inform
  DER` reads one back, refusing octets that are not a well-formed element
  (an error) or not an object identifier's contents ("BAD OBJECT");
* Python's `cryptography` package: `x509.ObjectIdentifier(text)` reads
  dotted text and refuses text that is not an object identifier, and its
  constants (NameOID, ExtensionOID, SignatureAlgorithmOID, ...) give the
  object identifiers of the names it knows.

Cases:

* random object identifiers as dotted text: the package's DER must be
  OpenSSL's, the package must read OpenSSL's DER back to the text, and
  `cryptography` must read the text to itself (when every arc is below
  2^32, the arcs it holds);
* text with leading zeros after the first arc, which both tools take
  (OpenSSL refuses them on the first): refused under the
  package's default rules, OpenSSL's DER under the lenient rules;
* text both tools refuse: the package must refuse it under both rules;
* DER both tools' reader refuses (OpenSSL): a subidentifier led by 80 hex
  (not in the fewest octets), a last subidentifier cut short, an octet after
  the element, the element cut short, a length past the end, no contents:
  the package must refuse each;
* the registry: each name that `cryptography` or OpenSSL knows must name
  the same object identifier there.

Writes ref/cases.bend and ref/expected.txt; prints how many cases.
"""
import os, random, subprocess, sys, tempfile
sys.dont_write_bytecode = True

from cryptography import x509
import cryptography.x509.oid as XO
from cryptography.hazmat.primitives.asymmetric import ec

MAX_SUBID = 1 << 42  # the package's bound: six base-128 octets

# registry names as `cryptography` constants
CRYPTO = {
    "id-at-commonName": XO.NameOID.COMMON_NAME,
    "id-at-surname": XO.NameOID.SURNAME,
    "id-at-serialNumber": XO.NameOID.SERIAL_NUMBER,
    "id-at-countryName": XO.NameOID.COUNTRY_NAME,
    "id-at-localityName": XO.NameOID.LOCALITY_NAME,
    "id-at-stateOrProvinceName": XO.NameOID.STATE_OR_PROVINCE_NAME,
    "id-at-organizationName": XO.NameOID.ORGANIZATION_NAME,
    "id-at-organizationalUnitName": XO.NameOID.ORGANIZATIONAL_UNIT_NAME,
    "id-at-title": XO.NameOID.TITLE,
    "id-at-givenName": XO.NameOID.GIVEN_NAME,
    "id-at-initials": XO.NameOID.INITIALS,
    "id-at-generationQualifier": XO.NameOID.GENERATION_QUALIFIER,
    "id-at-dnQualifier": XO.NameOID.DN_QUALIFIER,
    "id-at-pseudonym": XO.NameOID.PSEUDONYM,
    "id-domainComponent": XO.NameOID.DOMAIN_COMPONENT,
    "id-emailAddress": XO.NameOID.EMAIL_ADDRESS,
    "id-ce-subjectDirectoryAttributes": XO.ExtensionOID.SUBJECT_DIRECTORY_ATTRIBUTES,
    "id-ce-subjectKeyIdentifier": XO.ExtensionOID.SUBJECT_KEY_IDENTIFIER,
    "id-ce-keyUsage": XO.ExtensionOID.KEY_USAGE,
    "id-ce-subjectAltName": XO.ExtensionOID.SUBJECT_ALTERNATIVE_NAME,
    "id-ce-issuerAltName": XO.ExtensionOID.ISSUER_ALTERNATIVE_NAME,
    "id-ce-basicConstraints": XO.ExtensionOID.BASIC_CONSTRAINTS,
    "id-ce-cRLNumber": XO.ExtensionOID.CRL_NUMBER,
    "id-ce-nameConstraints": XO.ExtensionOID.NAME_CONSTRAINTS,
    "id-ce-cRLDistributionPoints": XO.ExtensionOID.CRL_DISTRIBUTION_POINTS,
    "id-ce-certificatePolicies": XO.ExtensionOID.CERTIFICATE_POLICIES,
    "id-ce-policyMappings": XO.ExtensionOID.POLICY_MAPPINGS,
    "id-ce-authorityKeyIdentifier": XO.ExtensionOID.AUTHORITY_KEY_IDENTIFIER,
    "id-ce-policyConstraints": XO.ExtensionOID.POLICY_CONSTRAINTS,
    "id-ce-extKeyUsage": XO.ExtensionOID.EXTENDED_KEY_USAGE,
    "id-ce-freshestCRL": XO.ExtensionOID.FRESHEST_CRL,
    "id-ce-inhibitAnyPolicy": XO.ExtensionOID.INHIBIT_ANY_POLICY,
    "id-pe-authorityInfoAccess": XO.ExtensionOID.AUTHORITY_INFORMATION_ACCESS,
    "id-pe-subjectInfoAccess": XO.ExtensionOID.SUBJECT_INFORMATION_ACCESS,
    "id-kp-serverAuth": XO.ExtendedKeyUsageOID.SERVER_AUTH,
    "id-kp-clientAuth": XO.ExtendedKeyUsageOID.CLIENT_AUTH,
    "id-kp-codeSigning": XO.ExtendedKeyUsageOID.CODE_SIGNING,
    "id-kp-emailProtection": XO.ExtendedKeyUsageOID.EMAIL_PROTECTION,
    "id-kp-timeStamping": XO.ExtendedKeyUsageOID.TIME_STAMPING,
    "id-kp-OCSPSigning": XO.ExtendedKeyUsageOID.OCSP_SIGNING,
    "id-qt-cps": XO.CertificatePoliciesOID.CPS_QUALIFIER,
    "id-qt-unotice": XO.CertificatePoliciesOID.CPS_USER_NOTICE,
    "id-ad-ocsp": XO.AuthorityInformationAccessOID.OCSP,
    "id-ad-caIssuers": XO.AuthorityInformationAccessOID.CA_ISSUERS,
    "md5WithRSAEncryption": XO.SignatureAlgorithmOID.RSA_WITH_MD5,
    "sha1WithRSAEncryption": XO.SignatureAlgorithmOID.RSA_WITH_SHA1,
    "sha224WithRSAEncryption": XO.SignatureAlgorithmOID.RSA_WITH_SHA224,
    "sha256WithRSAEncryption": XO.SignatureAlgorithmOID.RSA_WITH_SHA256,
    "sha384WithRSAEncryption": XO.SignatureAlgorithmOID.RSA_WITH_SHA384,
    "sha512WithRSAEncryption": XO.SignatureAlgorithmOID.RSA_WITH_SHA512,
    "id-RSASSA-PSS": XO.SignatureAlgorithmOID.RSASSA_PSS,
    "ecdsa-with-SHA1": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA1,
    "ecdsa-with-SHA224": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA224,
    "ecdsa-with-SHA256": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA256,
    "ecdsa-with-SHA384": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA384,
    "ecdsa-with-SHA512": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA512,
    "id-dsa-with-sha1": XO.SignatureAlgorithmOID.DSA_WITH_SHA1,
    "id-dsa-with-sha224": XO.SignatureAlgorithmOID.DSA_WITH_SHA224,
    "id-dsa-with-sha256": XO.SignatureAlgorithmOID.DSA_WITH_SHA256,
    "id-ecdsa-with-sha3-224": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA3_224,
    "id-ecdsa-with-sha3-256": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA3_256,
    "id-ecdsa-with-sha3-384": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA3_384,
    "id-ecdsa-with-sha3-512": XO.SignatureAlgorithmOID.ECDSA_WITH_SHA3_512,
    "id-rsassa-pkcs1-v1-5-with-sha3-224": XO.SignatureAlgorithmOID.RSA_WITH_SHA3_224,
    "id-rsassa-pkcs1-v1-5-with-sha3-256": XO.SignatureAlgorithmOID.RSA_WITH_SHA3_256,
    "id-rsassa-pkcs1-v1-5-with-sha3-384": XO.SignatureAlgorithmOID.RSA_WITH_SHA3_384,
    "id-rsassa-pkcs1-v1-5-with-sha3-512": XO.SignatureAlgorithmOID.RSA_WITH_SHA3_512,
    "id-Ed25519": XO.SignatureAlgorithmOID.ED25519,
    "id-Ed448": XO.SignatureAlgorithmOID.ED448,
    "secp192r1": ec.EllipticCurveOID.SECP192R1,
    "secp224r1": ec.EllipticCurveOID.SECP224R1,
    "secp256r1": ec.EllipticCurveOID.SECP256R1,
    "secp384r1": ec.EllipticCurveOID.SECP384R1,
    "secp521r1": ec.EllipticCurveOID.SECP521R1,
    "sect163k1": ec.EllipticCurveOID.SECT163K1,
    "sect163r2": ec.EllipticCurveOID.SECT163R2,
    "sect233k1": ec.EllipticCurveOID.SECT233K1,
    "sect233r1": ec.EllipticCurveOID.SECT233R1,
    "sect283k1": ec.EllipticCurveOID.SECT283K1,
    "sect283r1": ec.EllipticCurveOID.SECT283R1,
    "sect409k1": ec.EllipticCurveOID.SECT409K1,
    "sect409r1": ec.EllipticCurveOID.SECT409R1,
    "sect571k1": ec.EllipticCurveOID.SECT571K1,
    "sect571r1": ec.EllipticCurveOID.SECT571R1,
}

# registry names as OpenSSL's object names
OPENSSL = {
    "id-md2": "MD2", "id-md5": "MD5", "id-sha1": "SHA1", "id-sha224": "SHA224",
    "id-sha256": "SHA256", "id-sha384": "SHA384", "id-sha512": "SHA512",
    "id-sha512-224": "SHA512-224", "id-sha512-256": "SHA512-256",
    "id-sha3-224": "SHA3-224", "id-sha3-256": "SHA3-256", "id-sha3-384": "SHA3-384",
    "id-sha3-512": "SHA3-512", "id-shake128": "SHAKE128", "id-shake256": "SHAKE256",
    "rsaEncryption": "rsaEncryption", "id-RSAES-OAEP": "RSAES-OAEP", "id-mgf1": "mgf1",
    "id-pSpecified": "pSpecified", "id-RSASSA-PSS": "RSASSA-PSS",
    "md2WithRSAEncryption": "md2WithRSAEncryption", "md5WithRSAEncryption": "md5WithRSAEncryption",
    "sha1WithRSAEncryption": "sha1WithRSAEncryption", "sha224WithRSAEncryption": "sha224WithRSAEncryption",
    "sha256WithRSAEncryption": "sha256WithRSAEncryption", "sha384WithRSAEncryption": "sha384WithRSAEncryption",
    "sha512WithRSAEncryption": "sha512WithRSAEncryption",
    "sha512-224WithRSAEncryption": "sha512-224WithRSAEncryption",
    "sha512-256WithRSAEncryption": "sha512-256WithRSAEncryption",
    "id-dsa": "DSA", "id-dsa-with-sha1": "dsaWithSHA1", "id-dsa-with-sha224": "dsa_with_SHA224",
    "id-dsa-with-sha256": "dsa_with_SHA256", "dhpublicnumber": "dhpublicnumber",
    "ecdsa-with-SHA1": "ecdsa-with-SHA1", "ecdsa-with-SHA224": "ecdsa-with-SHA224",
    "ecdsa-with-SHA256": "ecdsa-with-SHA256", "ecdsa-with-SHA384": "ecdsa-with-SHA384",
    "ecdsa-with-SHA512": "ecdsa-with-SHA512",
    "id-ecdsa-with-sha3-224": "id-ecdsa-with-sha3-224", "id-ecdsa-with-sha3-256": "id-ecdsa-with-sha3-256",
    "id-ecdsa-with-sha3-384": "id-ecdsa-with-sha3-384", "id-ecdsa-with-sha3-512": "id-ecdsa-with-sha3-512",
    "id-rsassa-pkcs1-v1-5-with-sha3-224": "id-rsassa-pkcs1-v1_5-with-sha3-224",
    "id-rsassa-pkcs1-v1-5-with-sha3-256": "id-rsassa-pkcs1-v1_5-with-sha3-256",
    "id-rsassa-pkcs1-v1-5-with-sha3-384": "id-rsassa-pkcs1-v1_5-with-sha3-384",
    "id-rsassa-pkcs1-v1-5-with-sha3-512": "id-rsassa-pkcs1-v1_5-with-sha3-512",
    "id-ecPublicKey": "id-ecPublicKey", "secp192r1": "prime192v1", "secp256r1": "prime256v1",
    "secp224r1": "secp224r1", "secp384r1": "secp384r1", "secp521r1": "secp521r1",
    "sect163k1": "sect163k1", "sect163r2": "sect163r2", "sect233k1": "sect233k1",
    "sect233r1": "sect233r1", "sect283k1": "sect283k1", "sect283r1": "sect283r1",
    "sect409k1": "sect409k1", "sect409r1": "sect409r1", "sect571k1": "sect571k1",
    "sect571r1": "sect571r1", "id-X25519": "X25519", "id-X448": "X448",
    "id-Ed25519": "ED25519", "id-Ed448": "ED448",
    "id-at-name": "name", "id-ce-privateKeyUsagePeriod": "privateKeyUsagePeriod",
    "id-data": "pkcs7-data", "id-signedData": "pkcs7-signedData",
    "id-envelopedData": "pkcs7-envelopedData", "id-digestedData": "pkcs7-digestData",
    "id-encryptedData": "pkcs7-encryptedData", "signedAndEnvelopedData": "pkcs7-signedAndEnvelopedData",
    "id-ct-authData": "id-smime-ct-authData", "id-ct-contentInfo": "id-smime-ct-contentInfo",
    "id-contentType": "contentType", "id-messageDigest": "messageDigest",
    "id-signingTime": "signingTime", "id-countersignature": "countersignature",
    "id-emailAddress": "emailAddress", "id-domainComponent": "domainComponent",
    "id-at-commonName": "commonName", "id-ce-basicConstraints": "basicConstraints",
    "id-kp-serverAuth": "serverAuth", "id-qt-cps": "id-qt-cps", "id-qt-unotice": "id-qt-unotice",
    "id-ad-ocsp": "OCSP", "id-ad-caIssuers": "caIssuers",
}

HEADER = '''# Generated by gen.py: do not edit.
import Base
import ../../bytes/bytes.bend as B
import ../oid.bend as O
import ../text.bend as T
import ../registry.bend as R

def hexd(+c: Char) -> U32:
  +x = Char.to_u32(c)
  Bool.pick(U32, U32.is_lt(x, 58), U32.sub(x, 48), U32.sub(x, 87))

def unhex(s: String) -> List<&2, U32>:
  match s:
    case SCon{a, SCon{b, t}}:
      Con{U32.add(U32.mul(hexd(a), 16), hexd(b)), unhex(t)}
    case _:
      Nil{}

def hx(s: String) -> B.Octets:
  B.Octets.of_list(unhex(s))

def rb(r: Result<&2, &2, O.OidError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "ERR"
    case Done{b}:
      B.Octets.hex(b)

def ro(r: Result<&2, &2, O.OidError, O.Oid>) -> String:
  match r:
    case Fail{e}:
      "ERR"
    case Done{o}:
      T.Oid.to_text(o)

def td(+lz: Bool, s: String) -> String:
  rb(Result.bind(&2, &2, O.OidError, O.Oid, B.Octets, T.Oid.of_text(T.OidTextRules{lz}, s), o => O.Oid.to_der(o)))

def dt(h: String) -> String:
  ro(O.Oid.of_der(hx(h)))

def mt(m: Maybe<&2, O.Oid>) -> String:
  match m:
    case None{}:
      "none"
    case Some{o}:
      T.Oid.to_text(o)

def md(m: Maybe<&2, O.Oid>) -> String:
  match m:
    case None{}:
      "none"
    case Some{o}:
      rb(O.Oid.to_der(o))

def nt(name: String) -> String:
  mt(R.Oid.named(name))

def nd(name: String) -> String:
  md(R.Oid.named(name))

'''


def run(args, data=None):
    return subprocess.run(args, capture_output=True, text=True, errors="replace", input=data)


def genstr(text):
    """OpenSSL's DER element of an OID's text or name, or None"""
    with tempfile.NamedTemporaryFile(delete=False) as f:
        name = f.name
    try:
        p = run(["openssl", "asn1parse", "-genstr", "OID:" + text, "-out", name, "-noout"])
        data = open(name, "rb").read()
    finally:
        os.unlink(name)
    if p.returncode != 0 or "rror" in p.stderr or not data:
        return None
    return data


def openssl_reads(data):
    """whether `openssl asn1parse` reads data as one OBJECT IDENTIFIER"""
    with tempfile.NamedTemporaryFile(delete=False) as f:
        f.write(data)
        name = f.name
    try:
        p = run(["openssl", "asn1parse", "-inform", "DER", "-in", name])
    finally:
        os.unlink(name)
    out = p.stdout + p.stderr
    return p.returncode == 0 and "rror" not in out and "BAD OBJECT" not in out and "OBJECT" in p.stdout


def crypto_text(text):
    try:
        return x509.ObjectIdentifier(text).dotted_string
    except Exception:
        return None


def rand_arc(rng):
    bits = rng.choice([3, 7, 8, 14, 15, 21, 28, 32, 35, 41])
    return rng.randrange(0, 1 << bits)


def rand_arcs(rng):
    x = rng.randrange(0, 3)
    y = rng.randrange(0, 40) if x < 2 else rng.choice([rng.randrange(0, 48), rand_arc(rng) % (MAX_SUBID - 80)])
    return [x, y] + [rand_arc(rng) for _ in range(rng.randrange(0, 8))]


def text(arcs):
    return ".".join(str(a) for a in arcs)


def subid_starts(c):
    """where each subidentifier of contents c starts"""
    out, start = [], 0
    for i, b in enumerate(c):
        if b & 0x80 == 0:
            out.append(start)
            start = i + 1
    return out


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, lines, expect = [], [], []
    tally = {"openssl": 0, "cryptography": 0}

    def case(name, expr, want):
        defs.append("def c_%s() -> String:\n  %s\n" % (name, expr))
        lines.append('IO.print("%s " ++ c_%s())' % (name, name))
        expect.append("%s %s" % (name, want))

    bad_der = []
    for k in range(50):
        arcs = rand_arcs(rng)
        t = text(arcs)
        d = genstr(t)
        if d is None or not openssl_reads(d):
            raise SystemExit("openssl refuses %s" % t)
        tally["openssl"] += 1
        ct = crypto_text(t)
        if all(a < (1 << 32) for a in arcs):
            if ct != t:
                raise SystemExit("cryptography reads %s as %s" % (t, ct))
            tally["cryptography"] += 1
        case("t%d" % k, 'td(False{}, "%s") ++ " " ++ dt("%s")' % (t, d.hex()), "%s %s" % (d.hex(), t))
        c = d[2:]
        if len(c) > 1:
            bad_der.append(("lead%d" % k, d[:1] + bytes([d[1] + 1]) + c[:subid_starts(c)[-1]] + b"\x80" + c[subid_starts(c)[-1]:]))
        bad_der.append(("open%d" % k, d[:-1] + bytes([d[-1] | 0x80])))
        bad_der.append(("trail%d" % k, d + bytes([rng.randrange(0, 256)])))
        bad_der.append(("cut%d" % k, d[:rng.randrange(1, len(d))]))
        bad_der.append(("past%d" % k, d[:1] + bytes([d[1] + 1]) + c))
    bad_der.append(("empty", bytes.fromhex("0600")))
    bad_der.append(("x690_lead", bytes.fromhex("060480883703")))
    for name, data in bad_der:
        if openssl_reads(data):
            raise SystemExit("openssl reads %s (%s)" % (data.hex(), name))
        case(name, 'dt("%s")' % data.hex(), "ERR")

    # leading zeros: both tools take them
    for k in range(10):
        arcs = rand_arcs(rng)
        i = rng.randrange(1, len(arcs))  # OpenSSL reads the first arc as one digit
        parts = [str(a) for a in arcs]
        parts[i] = "0" * rng.randrange(1, 3) + parts[i]
        t = ".".join(parts)
        d = genstr(t)
        if d is None or d != genstr(text(arcs)):
            raise SystemExit("openssl reads %s otherwise" % t)
        if crypto_text(t) != text(arcs) and all(a < (1 << 32) for a in arcs):
            raise SystemExit("cryptography reads %s otherwise" % t)
        case("zero%d" % k, 'td(False{}, "%s") ++ " " ++ td(True{}, "%s")' % (t, t), "ERR %s" % d.hex())

    # text both tools refuse
    # (OpenSSL reads "1..2" and "1.2." as other arcs and `cryptography` reads
    # "+1.2"; the package refuses those too, as check.bend shows)
    bad_text = ["", "1", "3.1", "1.40", "0.40", "1.", ".1.2", "1.2a", "-1.2", "1.-2", "x",
                "2.5.x", "1.2.3a.4", "9.1"]
    for k, t in enumerate(bad_text):
        if genstr(t) is not None or crypto_text(t) is not None:
            raise SystemExit("a tool reads %r" % t)
        case("badtext%d" % k, 'td(False{}, "%s") ++ " " ++ td(True{}, "%s")' % (t, t), "ERR ERR")

    # the registry against the tools' names
    for name, oid in sorted(CRYPTO.items()):
        case("cr_%s" % name.replace("-", "_"), 'nt("%s")' % name, oid.dotted_string)
    for name, sn in sorted(OPENSSL.items()):
        d = genstr(sn)
        if d is None:
            raise SystemExit("openssl does not know %s" % sn)
        case("os_%s" % name.replace("-", "_"), 'nd("%s")' % name, d.hex())

    chunks = [lines[i:i + 80] for i in range(0, len(lines), 80)]
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(HEADER)
        f.write("\n".join(defs))
        for i, ch in enumerate(chunks):
            f.write("\ndef part%d() -> IO(Unit):\n  do IO<Unit>:\n" % i + "".join("    %s\n" % ln for ln in ch))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "".join("    part%d()\n" % i for i in range(len(chunks))))
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d texts against openssl, %d against cryptography, %d registry names)" %
          (len(expect), tally["openssl"], tally["cryptography"], len(CRYPTO) + len(OPENSSL)))


main()
