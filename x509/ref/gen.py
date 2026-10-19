#!/usr/bin/env python3
"""Differential test cases for bend-osdev-x509.

Certificates are made by Python's `cryptography` package (keys RSA with
PKCS #1 v1.5 and PSS signatures, ECDSA on P-256 and P-384, Ed25519, Ed448;
random names with PrintableString, UTF8String and IA5String values,
multi-valued RDNs and non-ASCII text; UTCTime and GeneralizedTime; random
serial numbers; every extension the package reads, with random contents,
and unknown ones, critical or not; CA and end-entity certificates) and by
OpenSSL (`openssl req -x509`, and `openssl x509 -req`, which writes a v1
certificate). Each certificate is read back by both tools:

* `cryptography`'s parsed objects give every field the package must answer:
  version, serial number, signature algorithm, issuer and subject (each
  attribute's object identifier and text), validity, the
  SubjectPublicKeyInfo's octets, each extension (identifier, critical flag,
  value octets, and the decoded basicConstraints, keyUsage,
  subjectKeyIdentifier, authorityKeyIdentifier, subjectAltName and
  extKeyUsage), the outer signature algorithm, the tbsCertificate's octets
  and the signature's octets;
* OpenSSL must agree with `cryptography` on the serial number and the
  validity (`openssl x509 -serial -startdate -enddate`), on the version and
  the basicConstraints and keyUsage text (`openssl x509 -text`), and on the
  tbsCertificate's and signature's lengths (`openssl asn1parse`).

Then inputs that are not DER, made from each certificate by a model of
X.690 written here: cut short, a length past its element's end, a serial
number with a leading zero octet (both tools refuse these); an octet after
it, a length in more octets than needed (outer, or an inner element's),
the indefinite form, a critical flag of 01 or an encoded FALSE (DER
requires FF and omits the DEFAULT), which `cryptography` refuses and
OpenSSL, reading BER and ignoring what follows, accepts. Every one must be
refused by `cryptography` (else the generator stops). The package must
refuse each under its default rules, and under
lenient (BER) rules read the BER forms of the whole certificate (outer
length) as the original. Each certificate is also read under the strict
rules (unknown critical extensions refused), and leaves are checked against
their issuer's subject (X509.issued_by, under RFC 5280 7.1's comparison and
binary).

Keys are fresh on each run; the seed fixes everything else. Writes
ref/cases.bend and ref/expected.txt; prints how many cases.
"""
import datetime, ipaddress, os, random, re, subprocess, sys, tempfile
sys.dont_write_bytecode = True

from cryptography import x509
from cryptography.x509.oid import NameOID, ExtendedKeyUsageOID, ObjectIdentifier
from cryptography.x509.name import _ASN1Type
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import rsa, ec, ed25519, ed448, padding

here = os.path.dirname(os.path.abspath(__file__))
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)

# DER, written from ITU-T X.690 8.1 (tags below 31 here)

def der_len(n, extra=0):
    if n < 128 and extra == 0:
        return bytes([n])
    bs = n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")
    bs = bytes(extra) + bs
    return bytes([0x80 | len(bs)]) + bs


def parse(b, i=0, end=None):
    end = len(b) if end is None else end
    out = []
    while i < end:
        t = b[i]
        l = b[i + 1]
        j = i + 2
        if l & 0x80:
            k = l & 0x7F
            l = int.from_bytes(b[j:j + k], "big")
            j += k
        body = b[j:j + l]
        node = [t, parse(b, j, j + l) if t & 0x20 else body]
        out.append(node)
        i = j + l
    return out


def enc(node, extra=None):
    """DER, with the lengths of the nodes in extra (by identity) in one
    more octet than needed"""
    t, v = node
    body = b"".join(enc(k, extra) for k in v) if isinstance(v, list) else v
    return bytes([t]) + der_len(len(body), 1 if extra and id(node) in extra else 0) + body


def walk(node, acc):
    acc.append(node)
    if isinstance(node[1], list):
        for k in node[1]:
            walk(k, acc)
    return acc

# Making certificates

WORDS = ["Example", "Test", "Acme", "Widgets", "North", "Lab", "Unit", "Root", "Leaf", "Ops", "Zone", "Q4"]
UTF = ["café", "München", "日本", "São Paulo", "Łódź"]


def words(k):
    return " ".join(rng.choice(WORDS) for _ in range(k))


def rand_attr():
    kind = rng.randrange(9)
    if kind == 0:
        return x509.NameAttribute(NameOID.COUNTRY_NAME, rng.choice(["US", "DE", "JP", "BR"]))
    if kind == 1:
        return x509.NameAttribute(NameOID.EMAIL_ADDRESS, "user%d@example.com" % rng.randrange(100))
    if kind == 2:
        return x509.NameAttribute(NameOID.DOMAIN_COMPONENT, rng.choice(["example", "com", "test"]))
    if kind == 3:
        return x509.NameAttribute(NameOID.SERIAL_NUMBER, str(rng.randrange(10 ** 6)), _type=_ASN1Type.PrintableString)
    oid = [NameOID.COMMON_NAME, NameOID.ORGANIZATION_NAME, NameOID.ORGANIZATIONAL_UNIT_NAME, NameOID.LOCALITY_NAME, NameOID.STATE_OR_PROVINCE_NAME][kind - 4]
    if rng.random() < 0.3:
        return x509.NameAttribute(oid, rng.choice(UTF) + " " + words(1))
    t = rng.choice([_ASN1Type.PrintableString, _ASN1Type.UTF8String])
    return x509.NameAttribute(oid, words(rng.randrange(1, 4)), _type=t)


def rand_name():
    rdns = []
    for _ in range(rng.randrange(1, 5)):
        k = 2 if rng.random() < 0.15 else 1
        attrs = []
        while len(attrs) < k:
            a = rand_attr()
            if all(b.oid != a.oid for b in attrs):
                attrs.append(a)
        rdns.append(x509.RelativeDistinguishedName(attrs))
    return x509.Name(rdns)


def rand_time():
    y = rng.choice([rng.randrange(1950, 2050), rng.randrange(2050, 2100), rng.randrange(2020, 2040)])
    return datetime.datetime(y, rng.randrange(1, 13), rng.randrange(1, 29), rng.randrange(24), rng.randrange(60), rng.randrange(60))


def rand_key():
    k = rng.randrange(6)
    if k == 0:
        return rsa.generate_private_key(65537, 2048), "rsa"
    if k == 1:
        return rsa.generate_private_key(65537, 2048), "pss"
    if k == 2:
        return ec.generate_private_key(ec.SECP256R1()), "p256"
    if k == 3:
        return ec.generate_private_key(ec.SECP384R1()), "p384"
    if k == 4:
        return ed25519.Ed25519PrivateKey.generate(), "ed25519"
    return ed448.Ed448PrivateKey.generate(), "ed448"


def sign_args(kind):
    if kind in ("rsa", "p256"):
        return dict(algorithm=hashes.SHA256())
    if kind == "p384":
        return dict(algorithm=hashes.SHA384())
    if kind == "pss":
        return dict(algorithm=hashes.SHA256(), rsa_padding=padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32))
    return dict(algorithm=None)


def rand_gn():
    k = rng.randrange(7)
    if k == 0:
        return x509.DNSName("host%d.example.com" % rng.randrange(1000))
    if k == 1:
        return x509.RFC822Name("a%d@example.org" % rng.randrange(1000))
    if k == 2:
        return x509.IPAddress(ipaddress.ip_address(rng.choice(["192.0.2.%d" % rng.randrange(256), "2001:db8::%x" % rng.randrange(65536)])))
    if k == 3:
        return x509.UniformResourceIdentifier("https://example.com/%d" % rng.randrange(1000))
    if k == 4:
        return x509.DirectoryName(rand_name())
    if k == 5:
        return x509.RegisteredID(ObjectIdentifier("1.3.6.1.4.1.55555.%d" % rng.randrange(100)))
    return x509.OtherName(ObjectIdentifier("1.3.6.1.4.1.55555.9.%d" % rng.randrange(100)), b"\x0c\x03abc")


def rand_exts(issuer_key, subject_pub, ca):
    out = []
    if ca or rng.random() < 0.6:
        out.append((x509.BasicConstraints(ca=ca, path_length=rng.choice([None, 0, 1, 5]) if ca else None), rng.random() < 0.7))
    if rng.random() < 0.7:
        ka = rng.random() < 0.3
        out.append((x509.KeyUsage(digital_signature=rng.random() < 0.6, content_commitment=rng.random() < 0.2, key_encipherment=rng.random() < 0.3, data_encipherment=rng.random() < 0.2, key_agreement=ka, key_cert_sign=ca, crl_sign=ca and rng.random() < 0.7, encipher_only=ka and rng.random() < 0.5, decipher_only=ka and rng.random() < 0.5), rng.random() < 0.6))
    if rng.random() < 0.7:
        out.append((x509.SubjectKeyIdentifier(rng.randbytes(20)), False))
    if rng.random() < 0.6:
        if rng.random() < 0.3:
            out.append((x509.AuthorityKeyIdentifier(rng.randbytes(20), [x509.DirectoryName(rand_name())], rng.randrange(1, 1 << 64)), False))
        else:
            out.append((x509.AuthorityKeyIdentifier(rng.randbytes(20), None, None), False))
    if rng.random() < 0.6:
        out.append((x509.SubjectAlternativeName([rand_gn() for _ in range(rng.randrange(1, 5))]), rng.random() < 0.2))
    if rng.random() < 0.5:
        eku = [ExtendedKeyUsageOID.SERVER_AUTH, ExtendedKeyUsageOID.CLIENT_AUTH, ExtendedKeyUsageOID.CODE_SIGNING, ExtendedKeyUsageOID.EMAIL_PROTECTION, ExtendedKeyUsageOID.TIME_STAMPING, ExtendedKeyUsageOID.OCSP_SIGNING]
        out.append((x509.ExtendedKeyUsage(rng.sample(eku, rng.randrange(1, 4))), False))
    if rng.random() < 0.4:
        out.append((x509.UnrecognizedExtension(ObjectIdentifier("1.3.6.1.4.1.55555.1.%d" % rng.randrange(100)), b"\x0c\x05hello"), rng.random() < 0.5))
    rng.shuffle(out)
    return out


def make_cert(subject, issuer, pub, issuer_key, issuer_kind, ca):
    a, b = sorted([rand_time(), rand_time()])
    bld = (x509.CertificateBuilder().subject_name(subject).issuer_name(issuer).public_key(pub)
           .serial_number(rng.randrange(1, 1 << rng.choice([8, 32, 64, 120, 159]))).not_valid_before(a).not_valid_after(b))
    for ext, crit in rand_exts(issuer_key, pub, ca):
        bld = bld.add_extension(ext, crit)
    return bld.sign(issuer_key, **sign_args(issuer_kind)).public_bytes(serialization.Encoding.DER)


def run(args, data=None):
    return subprocess.run(args, capture_output=True, input=data)


def openssl_certs():
    """an RSA certificate from openssl req -x509 and a v1 one from openssl
    x509 -req"""
    d = tempfile.mkdtemp()
    k = os.path.join(d, "k.pem")
    out = []
    run(["openssl", "genpkey", "-algorithm", "EC", "-pkeyopt", "ec_paramgen_curve:P-256", "-out", k])
    c = os.path.join(d, "c.der")
    if run(["openssl", "req", "-x509", "-key", k, "-subj", "/C=US/O=Example/CN=openssl req", "-days", "10", "-outform", "DER", "-out", c]).returncode == 0:
        out.append(open(c, "rb").read())
    csr = os.path.join(d, "r.csr")
    run(["openssl", "req", "-new", "-key", k, "-subj", "/CN=v1 cert/O=Example", "-out", csr])
    if run(["openssl", "x509", "-req", "-in", csr, "-key", k, "-days", "5", "-outform", "DER", "-out", c]).returncode == 0:
        out.append(open(c, "rb").read())
    for f in os.listdir(d):
        os.unlink(os.path.join(d, f))
    os.rmdir(d)
    return out

# What the tools read

def twos(n):
    """an INTEGER's contents octets (X.690 8.3)"""
    k = 1
    while True:
        try:
            return n.to_bytes(k, "big", signed=True)
        except OverflowError:
            k += 1


def name_text(n):
    return ", ".join(" + ".join("%s=%s" % (a.oid.dotted_string, a.value) for a in rdn) for rdn in n.rdns)


def gn_text(g):
    if isinstance(g, x509.DNSName):
        return "DNS:" + g.value
    if isinstance(g, x509.RFC822Name):
        return "email:" + g.value
    if isinstance(g, x509.IPAddress):
        return "IP:" + g.value.packed.hex()
    if isinstance(g, x509.UniformResourceIdentifier):
        return "URI:" + g.value
    if isinstance(g, x509.DirectoryName):
        return "dir:" + name_text(g.value)
    if isinstance(g, x509.RegisteredID):
        return "RID:" + g.value.dotted_string
    if isinstance(g, x509.OtherName):
        return "othername:" + g.type_id.dotted_string
    raise SystemExit("general name %r" % g)


KU = ["digital_signature", "content_commitment", "key_encipherment", "data_encipherment", "key_agreement", "key_cert_sign", "crl_sign", "encipher_only", "decipher_only"]


def ext_text(e):
    v = e.value
    head = e.oid.dotted_string + ("!" if e.critical else "") + " " + v.public_bytes().hex() + " "
    if isinstance(v, x509.BasicConstraints):
        return head + "ca=%s pathlen=%s" % (v.ca, "-" if v.path_length is None else v.path_length)
    if isinstance(v, x509.KeyUsage):
        bits = []
        for i, n in enumerate(KU):
            if n in ("encipher_only", "decipher_only") and not v.key_agreement:
                continue
            if getattr(v, n):
                bits.append(str(i))
        return head + "ku=" + ",".join(bits)
    if isinstance(v, x509.SubjectKeyIdentifier):
        return head + "ski=" + v.digest.hex()
    if isinstance(v, x509.AuthorityKeyIdentifier):
        iss = "-" if v.authority_cert_issuer is None else ";".join(gn_text(g) for g in v.authority_cert_issuer)
        ser = "-" if v.authority_cert_serial_number is None else twos(v.authority_cert_serial_number).hex()
        kid = "-" if v.key_identifier is None else v.key_identifier.hex()
        return head + "keyid=%s issuer=%s serial=%s" % (kid, iss, ser)
    if isinstance(v, x509.SubjectAlternativeName):
        return head + "san=" + ",".join(gn_text(g) for g in v)
    if isinstance(v, x509.ExtendedKeyUsage):
        return head + "eku=" + ",".join(o.dotted_string for o in v)
    return head + "other"


def fmt_time(t):
    return t.strftime("%Y-%m-%dT%H:%M:%SZ")


def crypto_line(c):
    pub = c.public_key().public_bytes(serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo)
    return " | ".join([
        "v%d" % c.version.value, "serial=" + twos(c.serial_number).hex(),
        "sig=" + c.signature_algorithm_oid.dotted_string, "issuer=" + name_text(c.issuer),
        "from=" + fmt_time(c.not_valid_before), "to=" + fmt_time(c.not_valid_after),
        "subject=" + name_text(c.subject), "spki=" + pub.hex(),
        "exts=" + "; ".join(ext_text(e) for e in c.extensions),
        "outer=" + c.signature_algorithm_oid.dotted_string,
        "tbs=" + c.tbs_certificate_bytes.hex(), "sig=" + c.signature.hex()])


def openssl(args, data):
    with tempfile.NamedTemporaryFile(delete=False) as f:
        f.write(data)
        name = f.name
    try:
        p = run(["openssl"] + args + ["-in", name])
    finally:
        os.unlink(name)
    return p.returncode, p.stdout.decode("utf-8", "replace")


def openssl_agrees(d, c):
    """OpenSSL reads the same serial, validity, version, basicConstraints,
    keyUsage and element lengths as cryptography"""
    code, out = openssl(["x509", "-inform", "DER", "-noout", "-serial", "-startdate", "-enddate"], d)
    if code != 0:
        raise SystemExit("openssl refuses a certificate")
    ser = re.search(r"serial=([0-9A-F]+)", out).group(1)
    if int(ser, 16) != c.serial_number:
        raise SystemExit("serial: openssl %s" % ser)
    for key, t in (("notBefore", c.not_valid_before), ("notAfter", c.not_valid_after)):
        s = re.search(key + r"=(.*)", out).group(1).strip()
        if datetime.datetime.strptime(s, "%b %d %H:%M:%S %Y GMT") != t:
            raise SystemExit("%s: openssl %s" % (key, s))
    code, text = openssl(["x509", "-inform", "DER", "-noout", "-text"], d)
    m = re.search(r"Version: (\d+)", text)
    if int(m.group(1)) != c.version.value + 1:
        raise SystemExit("version: openssl %s" % m.group(1))
    try:
        bc = c.extensions.get_extension_for_class(x509.BasicConstraints).value
        want = "CA:TRUE" if bc.ca else "CA:FALSE"
        if bc.path_length is not None:
            want += ", pathlen:%d" % bc.path_length
        if want not in text:
            raise SystemExit("basicConstraints: openssl text lacks %s" % want)
    except x509.ExtensionNotFound:
        pass
    try:
        ku = c.extensions.get_extension_for_class(x509.KeyUsage).value
        names = {"digital_signature": "Digital Signature", "content_commitment": "Non Repudiation", "key_encipherment": "Key Encipherment", "data_encipherment": "Data Encipherment", "key_agreement": "Key Agreement", "key_cert_sign": "Certificate Sign", "crl_sign": "CRL Sign"}
        for n, label in names.items():
            if getattr(ku, n) != (label in re.search(r"X509v3 Key Usage:.*\n(.*)", text).group(1)):
                raise SystemExit("keyUsage %s: openssl disagrees" % n)
    except x509.ExtensionNotFound:
        pass
    code, out = openssl(["asn1parse", "-inform", "DER"], d)
    rows = [re.match(r"\s*(\d+):d=\s*(\d+)\s+hl=\s*(\d+)\s+l=\s*(\d+)", ln) for ln in out.splitlines()]
    rows = [(int(m.group(1)), int(m.group(2)), int(m.group(3)) + int(m.group(4))) for m in rows if m]
    top = [r for r in rows if r[1] == 1]
    if top[0][2] != len(c.tbs_certificate_bytes) or top[2][2] != len(c.signature) + 3 + (1 if len(c.signature) + 1 >= 128 else 0) + (1 if len(c.signature) + 1 >= 256 else 0):
        raise SystemExit("asn1parse lengths disagree")


def tools_refuse(d):
    """whether OpenSSL and cryptography refuse d"""
    code, _ = openssl(["x509", "-inform", "DER", "-noout", "-text"], d)
    try:
        c = x509.load_der_x509_certificate(d)
        c.extensions
        c.issuer
        c.subject
        c.public_key()
        crypto = False
    except Exception:
        crypto = True
    return code != 0, crypto


# Mutations, by the model above

def mutations(d):
    out = []
    out.append(("cut", d[:rng.randrange(1, len(d))]))
    out.append(("trail", d + bytes([rng.randrange(256)])))
    top = parse(d)[0]
    out.append(("longtop", enc(top, {id(top)})))
    nodes = walk(top, [])[1:]
    n = rng.choice(nodes)
    out.append(("longin", enc(top, {id(n)})))
    tbs = top[1][0]
    v = tbs[1]
    # an inner length one past its element's end: the tbsCertificate's
    t0 = 2 + (d[1] & 0x7F if d[1] & 0x80 else 0)
    if d[t0 + 1] & 0x80:
        k = d[t0 + 1] & 0x7F
        n = int.from_bytes(d[t0 + 2:t0 + 2 + k], "big") + 1
        out.append(("past", d[:t0 + 2] + n.to_bytes(k, "big") + d[t0 + 2 + k:]))
    else:
        out.append(("past", d[:t0 + 1] + bytes([d[t0 + 1] + 1]) + d[t0 + 2:]))
    # the indefinite form
    inner = b"".join(enc(k) for k in top[1])
    out.append(("indef", bytes([0x30, 0x80]) + inner + b"\x00\x00"))
    # a serial number with a leading zero octet
    si = 1 if v[0][0] == 0xA0 else 0
    if v[si][1][0] < 0x80:
        v2 = list(v)
        v2[si] = [0x02, b"\x00" + v[si][1]]
        out.append(("serial0", enc([0x30, [[0x30, v2]] + top[1][1:]])))
    # critical flags not in DER
    if v[-1][0] == 0xA3:
        exts = v[-1][1][0][1]
        for i, e in enumerate(exts):
            if len(e[1]) == 3:
                e2 = [0x30, [e[1][0], [0x01, b"\x01"], e[1][2]]]
                tag = "crit01"
            else:
                e2 = [0x30, [e[1][0], [0x01, b"\x00"], e[1][1]]]
                tag = "critfalse"
            exts2 = exts[:i] + [e2] + exts[i + 1:]
            v2 = v[:-1] + [[0xA3, [[0x30, exts2]]]]
            out.append((tag, enc([0x30, [[0x30, v2]] + top[1][1:]])))
            break
    return out


def main():
    defs, lines, expect = [], [], []
    tally = {"certs": 0, "both": 0, "crypto": 0}

    def case(name, expr, want):
        defs.append("def c_%s() -> String:\n  %s\n" % (name, expr))
        lines.append('IO.print("%s " ++ c_%s())' % (name, name))
        expect.append("%s %s" % (name, want))

    def add_cert(name, d, issuer_der=None):
        c = x509.load_der_x509_certificate(d)
        openssl_agrees(d, c)
        tally["certs"] += 1
        line = crypto_line(c)
        case(name, 'run(XR.X509.rules(), hx("%s"))' % d.hex(), line)
        unknown_crit = [e.oid.dotted_string for e in c.extensions if e.critical and e.oid.dotted_string not in ("2.5.29.19", "2.5.29.15", "2.5.29.14", "2.5.29.35", "2.5.29.17", "2.5.29.37")]
        case(name + "_strict", 'strict(hx("%s"))' % d.hex(), "X509UnknownCritical " + unknown_crit[0] if unknown_crit else "ok")
        if issuer_der is not None:
            p = x509.load_der_x509_certificate(issuer_der)
            same = c.issuer.public_bytes() == p.subject.public_bytes()
            case(name + "_issued", 'issued(hx("%s"), hx("%s"))' % (d.hex(), issuer_der.hex()), "%s %s" % (same, same))
        for tag, m in mutations(d):
            by_openssl, by_crypto = tools_refuse(m)
            if not by_crypto:
                raise SystemExit("cryptography reads %s of %s" % (tag, name))
            tally["both" if by_openssl else "crypto"] += 1
            case("%s_%s" % (name, tag), 'run(XR.X509.rules(), hx("%s"))' % m.hex(), "ERR")
            if tag in ("longtop", "indef"):
                case("%s_%s_ber" % (name, tag), 'run(XR.X509.rules_lenient(), hx("%s"))' % m.hex(), line)

    for k in range(12):
        ca_key, ca_kind = rand_key()
        ca_name = rand_name()
        ca = make_cert(ca_name, ca_name, ca_key.public_key(), ca_key, ca_kind, True)
        add_cert("ca%d" % k, ca)
        leaf_key, _ = rand_key()
        leaf = make_cert(rand_name(), ca_name, leaf_key.public_key(), ca_key, ca_kind, False)
        add_cert("leaf%d" % k, leaf, ca)
    for k, d in enumerate(openssl_certs()):
        add_cert("openssl%d" % k, d)

    chunks = [lines[i:i + 60] for i in range(0, len(lines), 60)]
    with open(os.path.join(here, "cases.bend"), "w", newline="\n", encoding="utf-8") as f:
        f.write(open(os.path.join(here, "show.bend.in"), encoding="utf-8").read())
        f.write("\n".join(defs))
        for i, ch in enumerate(chunks):
            f.write("\ndef part%d() -> IO(Unit):\n  do IO<Unit>:\n" % i + "".join("    %s\n" % ln for ln in ch))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "".join("    part%d()\n" % i for i in range(len(chunks))))
    with open(os.path.join(here, "expected.txt"), "w", newline="\n", encoding="utf-8") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d certificates against cryptography and openssl; %d inputs refused by both, %d by cryptography only)" % (len(expect), tally["certs"], tally["both"], tally["crypto"]))


main()
