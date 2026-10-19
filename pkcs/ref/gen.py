#!/usr/bin/env python3
"""Differential test cases for bend-osdev-pkcs.

CMS SignedData messages are made by OpenSSL (`openssl cms -sign`: DER and
streamed BER with indefinite lengths; attached and detached; with and
without signed attributes; signers named by issuer and serial number or by
subject key identifier; one or two signers; extra certificates or none;
SHA-256 and SHA-384; a content type other than id-data;
`openssl smime -sign` for PKCS #7) and by Python's `cryptography`
(PKCS7SignatureBuilder), with RSA and ECDSA (P-256, P-384) signer keys
(OpenSSL 3.0 does not sign CMS with Ed25519). The expected fields come from a model of X.690 (BER, with
indefinite lengths) and RFC 5652 written here, and the model is held to
both tools:

* `openssl cms -verify` must accept each message (with its content for a
  detached one), and `openssl cms -cmsout -print` must show the model's
  SignedData version and content type;
* `cryptography` must verify each signer's signature over the octets the
  model says it signed (RFC 5652 5.4: the content, or the signed
  attributes' DER under the SET OF tag) with the signer certificate's key,
  its digest of the content must be the message-digest attribute, and
  `load_der_pkcs7_certificates` must give the model's certificates.

The package must answer every field of the model: versions, digest
algorithms, content type, content, each certificate's octets, the number
of CRLs, and for each signer its version, identifier, digest algorithm,
signed attribute types and value counts, message digest, signature
algorithm, signature, signed octets, unsigned attribute count, and the
certificate it names. Inputs both tools refuse (cut short) must be
refused. So must two that OpenSSL 3.0 accepts: a content-type attribute
that does not match the content type (RFC 5652 11.1; OpenSSL does not
compare them), and a signed attribute not in DER (5.3; OpenSSL encodes
the attributes in DER again before checking the signature).

PKCS #8 keys: RSA, EC (P-256, P-384), Ed25519, Ed448, X25519 and X448 from
`cryptography` (PrivateKeyInfo, v1), and the same Ed25519 key as a v2
OneAsymmetricKey with its public key (RFC 5958), made by the model here
(OpenSSL 3.0 reads only PrivateKeyInfo and refuses it). The
privateKey octets must be RSAPrivateKey as `cryptography` writes it, the
ECPrivateKey's key the private value, and for the RFC 8410 curves the
CurvePrivateKey the raw key; OpenSSL (`openssl pkey`) and `cryptography`
must read each key. Cut keys must be refused.

Keys are fresh on each run. Writes ref/cases.bend and ref/expected.txt;
prints how many cases.
"""
import hashlib, os, random, re, subprocess, sys, tempfile
sys.dont_write_bytecode = True

from cryptography import x509
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import rsa, ec, ed25519, ed448, x25519, x448, padding
from cryptography.hazmat.primitives.serialization import pkcs7

here = os.path.dirname(os.path.abspath(__file__))
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
work = tempfile.mkdtemp()

# BER, written from ITU-T X.690 8.1 (indefinite lengths, 8.1.3.6)

def read(b, i):
    """the element at i: (tag, constructed, contents or elements, start, end)"""
    t = b[i]
    j = i + 1
    l = b[j]
    j += 1
    if l == 0x80:
        kids = []
        while b[j] != 0 or b[j + 1] != 0:
            k = read(b, j)
            kids.append(k)
            j = k[4]
        return (t, True, kids, i, j + 2)
    if l & 0x80:
        n = l & 0x7F
        l = int.from_bytes(b[j:j + n], "big")
        j += n
    if t & 0x20:
        kids, k = [], j
        while k < j + l:
            e = read(b, k)
            kids.append(e)
            k = e[4]
        return (t, True, kids, i, j + l)
    return (t, False, b[j:j + l], i, j + l)


def octets(e):
    """an OCTET STRING's octets, joined from BER's segments (8.7.3)"""
    return e[2] if not e[1] else b"".join(octets(k) for k in e[2])


def oid_text(c):
    """an OBJECT IDENTIFIER's contents as dotted text (8.19)"""
    ss, v = [], 0
    for x in c:
        v = (v << 7) | (x & 0x7F)
        if not x & 0x80:
            ss.append(v)
            v = 0
    f = ss[0]
    a, b = (0, f) if f < 40 else ((1, f - 40) if f < 80 else (2, f - 80))
    return ".".join(str(x) for x in [a, b] + ss[1:])


def raw(b, e):
    return b[e[3]:e[4]]

# The tools

def run(args, data=None):
    return subprocess.run(args, capture_output=True, input=data)


def tmp(name, data):
    p = os.path.join(work, name)
    with open(p, "wb") as f:
        f.write(data)
    return p


def mkcert(kind, cn):
    k = {"rsa": lambda: rsa.generate_private_key(65537, 2048), "p256": lambda: ec.generate_private_key(ec.SECP256R1()),
         "p384": lambda: ec.generate_private_key(ec.SECP384R1()), "ed25519": lambda: ed25519.Ed25519PrivateKey.generate()}[kind]()
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, cn), x509.NameAttribute(NameOID.ORGANIZATION_NAME, "Example")])
    import datetime
    now = datetime.datetime(2026, 1, 1)
    b = (x509.CertificateBuilder().subject_name(name).issuer_name(name).public_key(k.public_key())
         .serial_number(rng.randrange(1, 1 << 64)).not_valid_before(now).not_valid_after(now + datetime.timedelta(days=3650))
         .add_extension(x509.SubjectKeyIdentifier.from_public_key(k.public_key()), False))
    c = b.sign(k, None if kind == "ed25519" else hashes.SHA256())
    return k, c


def pem_files(k, c, tag):
    kp = tmp(tag + "k.pem", k.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()))
    cp = tmp(tag + "c.pem", c.public_bytes(serialization.Encoding.PEM))
    return kp, cp


HASH = {"2.16.840.1.101.3.4.2.1": hashes.SHA256, "2.16.840.1.101.3.4.2.2": hashes.SHA384, "2.16.840.1.101.3.4.2.3": hashes.SHA512}
HLIB = {"2.16.840.1.101.3.4.2.1": hashlib.sha256, "2.16.840.1.101.3.4.2.2": hashlib.sha384, "2.16.840.1.101.3.4.2.3": hashlib.sha512}


def twos(c):
    return c.hex()


def name_text(n):
    return ", ".join(" + ".join("%s=%s" % (a.oid.dotted_string, a.value) for a in rdn) for rdn in n.rdns)

# The model of a SignedData (RFC 5652 5.1 to 5.4)

def model(d, content_ext, certs_by_serial):
    ci = read(d, 0)
    sd = ci[2][1][2][0]
    f = sd[2]
    ver = int.from_bytes(f[0][2], "big")
    digests = [oid_text(a[2][0][2]) for a in f[1][2]]
    encap = f[2][2]
    ctype = oid_text(encap[0][2])
    content = octets(encap[1][2][0]) if len(encap) > 1 else None
    i = 3
    certs, crls = [], 0
    if i < len(f) and f[i][0] in (0xA0,):
        certs = [raw(d, e) for e in f[i][2]]
        i += 1
    if i < len(f) and f[i][0] == 0xA1:
        crls = len(f[i][2])
        i += 1
    signers = []
    for s in f[i][2]:
        g = s[2]
        sv = int.from_bytes(g[0][2], "big")
        sidn = g[1]
        if sidn[0] == 0x80:
            sid = "ski:" + sidn[2].hex()
            cert = [c for c in certs_by_serial.values() if c.extensions.get_extension_for_class(x509.SubjectKeyIdentifier).value.digest == sidn[2]]
        else:
            ser = sidn[2][1][2]
            cert = [c for c in certs_by_serial.values() if c.serial_number == int.from_bytes(ser, "big", signed=True)]
            if raw(d, sidn[2][0]) != cert[0].issuer.public_bytes():
                raise SystemExit("sid issuer is not the certificate's")
            sid = "iss:" + name_text(cert[0].issuer) + "/" + ser.hex()
        dig = oid_text(g[2][2][0][2])
        j = 3
        attrs = None
        md = None
        if g[j][0] == 0xA0:
            attrs = g[j]
            j += 1
        sigalg = oid_text(g[j][2][0][2])
        sig = octets(g[j + 1])
        unsigned = len(g[j + 2][2]) if len(g) > j + 2 else 0
        if attrs is None:
            alist = "-"
            signed = content if content is not None else content_ext
        else:
            alist = ",".join("%s=%d" % (oid_text(a[2][0][2]), len(a[2][1][2])) for a in attrs[2])
            ar = raw(d, attrs)
            signed = b"\x31" + ar[1:]
            for a in attrs[2]:
                if oid_text(a[2][0][2]) == "1.2.840.113549.1.9.4":
                    md = a[2][1][2][0][2]
        c = cert[0]
        # cryptography: the signature over the model's signed octets, and
        # the digest of the content
        pub = c.public_key()
        h = HASH.get(dig)
        if isinstance(pub, rsa.RSAPublicKey):
            pub.verify(sig, signed, padding.PKCS1v15(), h())
        elif isinstance(pub, ec.EllipticCurvePublicKey):
            pub.verify(sig, signed, ec.ECDSA(h()))
        else:
            pub.verify(sig, signed)
        if md is not None and HLIB[dig](content if content is not None else content_ext).digest() != md:
            raise SystemExit("message digest is not the content's")
        signers.append(" ".join(["v%d" % sv, "sid=" + sid, "dig=" + dig, "attrs=" + alist, "md=" + ("-" if md is None else md.hex()),
                                 "sigalg=" + sigalg, "sig=" + sig.hex(), "signed=" + signed.hex(), "unsigned=%d" % unsigned,
                                 "cert=" + (twos(c.serial_number.to_bytes((c.serial_number.bit_length() + 8) // 8, "big")) if c.public_bytes(serialization.Encoding.DER) in certs else "-")]))
    line = " | ".join(["v%d" % ver, "digests=" + ",".join(digests), "type=" + ctype, "content=" + ("-" if content is None else content.hex()),
                       "certs=" + ";".join(c.hex() for c in certs), "crls=%d" % crls, "signers=" + " || ".join(signers)])
    return line, ver, ctype, certs

# Making messages

def main():
    defs, lines, expect = [], [], []
    tally = {"cms": 0, "refused": 0, "keys": 0, "certs": 0}

    def case(name, expr, want):
        defs.append("def c_%s() -> String:\n  %s\n" % (name, expr))
        lines.append('IO.print("%s " ++ c_%s())' % (name, name))
        expect.append("%s %s" % (name, want))

    signers = {}
    for kind in ("rsa", "p256", "p384"):
        signers[kind] = mkcert(kind, "Signer " + kind)
    by_serial = {c.serial_number: c for k, c in signers.values()}
    files = {kind: pem_files(k, c, kind) for kind, (k, c) in signers.items()}
    allcerts = tmp("all.pem", b"".join(c.public_bytes(serialization.Encoding.PEM) for k, c in signers.values()))

    def add_cms(name, d, content, detached):
        ext = content if detached else b""
        cp = tmp("m.bin", content)
        args = ["openssl", "cms", "-verify", "-inform", "DER", "-in", tmp("s.der", d), "-noverify", "-binary", "-out", os.devnull, "-certfile", allcerts]
        if detached:
            args += ["-content", cp]
        if run(args).returncode != 0:
            raise SystemExit("openssl cms -verify refuses %s" % name)
        line, ver, ctype, certs = model(d, ext, by_serial)
        out = run(["openssl", "cms", "-cmsout", "-print", "-inform", "DER", "-in", tmp("s.der", d)]).stdout.decode("utf-8", "replace")
        if int(re.search(r"version: (\d+)", out).group(1)) != ver or "(%s)" % ctype not in out.split("eContentType:")[1].split("\n")[0]:
            raise SystemExit("openssl prints another version or content type for %s" % name)
        # (cryptography reads PKCS #7, whose signers have no subject key
        # identifier form, so it is asked only of the others)
        if certs and "sid=ski:" not in line:
            got = [c.public_bytes(serialization.Encoding.DER) for c in pkcs7.load_der_pkcs7_certificates(d)]
            if got != certs:
                raise SystemExit("cryptography reads other certificates in %s" % name)
            tally["certs"] += 1
        tally["cms"] += 1
        case(name, 'cms(PR.Pkcs.rules(), hx("%s"), hx("%s"))' % (d.hex(), ext.hex()), line)
        case(name + "_strict", 'cms_ok(PR.Pkcs.rules_strict(), hx("%s"))' % d.hex(), "ok")
        cut = d[:rng.randrange(1, len(d) - 1)]
        if run(["openssl", "cms", "-cmsout", "-inform", "DER", "-in", tmp("c.der", cut), "-out", os.devnull]).returncode == 0:
            raise SystemExit("openssl reads a cut message")
        try:
            pkcs7.load_der_pkcs7_certificates(cut)
            raise SystemExit("cryptography reads a cut message")
        except ValueError:
            pass
        tally["refused"] += 1
        case(name + "_cut", 'cms(PR.Pkcs.rules(), hx("%s"), hx(""))' % cut.hex(), "ERR")
        return d

    k = 0
    for kind in ("rsa", "p256", "p384"):
        kp, cp = files[kind]
        for opts in (["-nodetach"], ["-nodetach", "-stream"], [], ["-nodetach", "-noattr"], ["-nodetach", "-keyid"], ["-nodetach", "-md", "sha384"], ["-nodetach", "-nocerts"], ["-nodetach", "-econtent_type", "1.2.840.113549.1.9.16.1.4"]):
            content = ("message %d " % k).encode() + rng.randbytes(rng.randrange(0, 200))
            out = tmp("o.der", b"")
            p = run(["openssl", "cms", "-sign", "-binary", "-in", tmp("in.bin", content), "-signer", cp, "-inkey", kp, "-outform", "DER", "-out", out] + opts)
            if p.returncode != 0:
                raise SystemExit("openssl cms -sign %s %s: %s" % (kind, opts, p.stderr))
            d = open(out, "rb").read()
            add_cms("cms%d" % k, d, content, "-nodetach" not in opts)
            k += 1
    # two signers and an extra certificate
    content = b"two signers"
    out = tmp("o.der", b"")
    run(["openssl", "cms", "-sign", "-binary", "-nodetach", "-in", tmp("in.bin", content), "-signer", files["rsa"][1], "-inkey", files["rsa"][0],
         "-signer", files["p256"][1], "-inkey", files["p256"][0], "-certfile", files["p384"][1], "-outform", "DER", "-out", out])
    add_cms("cms%d" % k, open(out, "rb").read(), content, False)
    k += 1
    # PKCS #7 from openssl smime
    out = tmp("o.der", b"")
    run(["openssl", "smime", "-sign", "-binary", "-nodetach", "-in", tmp("in.bin", b"pkcs7 v1.5"), "-signer", files["rsa"][1], "-inkey", files["rsa"][0], "-outform", "DER", "-out", out])
    add_cms("cms%d" % k, open(out, "rb").read(), b"pkcs7 v1.5", False)
    k += 1
    # cryptography's PKCS7SignatureBuilder
    for kind in ("rsa", "p256"):
        key, cert = signers[kind]
        for opt in ([pkcs7.PKCS7Options.Binary], [pkcs7.PKCS7Options.Binary, pkcs7.PKCS7Options.NoAttributes], [pkcs7.PKCS7Options.Binary, pkcs7.PKCS7Options.DetachedSignature]):
            content = b"cryptography %d" % k
            d = pkcs7.PKCS7SignatureBuilder().set_data(content).add_signer(cert, key, hashes.SHA256()).sign(serialization.Encoding.DER, opt)
            add_cms("cms%d" % k, d, content, pkcs7.PKCS7Options.DetachedSignature in opt)
            k += 1

    # signed attributes not in DER, and a content-type attribute that does
    # not match: OpenSSL refuses the signature, the package the message
    kp, cp = files["rsa"]
    out = tmp("o.der", b"")
    run(["openssl", "cms", "-sign", "-binary", "-nodetach", "-in", tmp("in.bin", b"attrs"), "-signer", cp, "-inkey", kp, "-outform", "DER", "-out", out])
    d = open(out, "rb").read()
    ci = read(d, 0)
    sd = ci[2][1][2][0]
    si = sd[2][-1][2][0]
    attrs = si[2][3]
    first = attrs[2][0]
    # the first attribute's length in two octets (81 xx), BER but not DER;
    # the lengths around it grow by one
    a0 = raw(d, first)
    a1 = a0[:1] + b"\x81" + a0[1:]
    def grow(b, e, delta):
        """b with element e's definite length grown by delta (one length
        octet, or 81/82 long forms, here)"""
        s = e[3]
        l = b[s + 1]
        if l < 0x80:
            n = l + delta
            hdr = bytes([b[s], n]) if n < 128 else bytes([b[s], 0x81, n])
            return b[:s] + hdr + b[s + 2:], len(hdr) - 2
        k = l & 0x7F
        n = int.from_bytes(b[s + 2:s + 2 + k], "big") + delta
        return b[:s + 2] + n.to_bytes(k, "big") + b[s + 2 + k:], 0
    m = d[:first[3]] + a1 + d[first[4]:]
    delta = 1
    for e in (attrs, si, sd[2][-1], sd, ci[2][1], ci):
        m, extra = grow(m, e, delta)
        delta += extra
    # (OpenSSL accepts it: it encodes the attributes in DER again before
    # checking the signature)
    if run(["openssl", "cms", "-verify", "-inform", "DER", "-in", tmp("m.der", m), "-noverify", "-binary", "-out", os.devnull, "-certfile", allcerts]).returncode != 0:
        raise SystemExit("openssl refuses BER signed attributes")
    case("attrs_ber", 'cms_ok(PR.Pkcs.rules(), hx("%s"))' % m.hex(), "PkcsAttrsNotDer")
    case("attrs_ber_lenient", 'cms_ok(PR.Pkcs.rules_lenient(), hx("%s"))' % m.hex(), "ok")
    # eContentType changed (the content-type attribute no longer matches)
    pos = d.index(bytes.fromhex("06092a864886f70d010701"), sd[3] + 10)
    m2 = d[:pos] + bytes.fromhex("06092a864886f70d010703") + d[pos + 11:]
    # (OpenSSL 3.0 verifies it: it does not compare the attribute with the
    # content type)
    if oid_text(read(m2, 0)[2][1][2][0][2][2][2][0][2]) != "1.2.840.113549.1.7.3":
        raise SystemExit("the content type was not changed")
    case("ctype", 'cms_ok(PR.PkcsRules{AR.Asn1Rules.ber(), True{}, True{}, False{}, False{}}, hx("%s"))' % m2.hex(), "PkcsContentTypeMismatch")
    case("ctype_versions", 'cms_ok(PR.Pkcs.rules(), hx("%s"))' % m2.hex(), "PkcsBadVersion")

    # PKCS #8
    keys = [("rsa", rsa.generate_private_key(65537, 2048)), ("p256", ec.generate_private_key(ec.SECP256R1())), ("p384", ec.generate_private_key(ec.SECP384R1())),
            ("ed25519", ed25519.Ed25519PrivateKey.generate()), ("ed448", ed448.Ed448PrivateKey.generate()), ("x25519", x25519.X25519PrivateKey.generate()), ("x448", x448.X448PrivateKey.generate())]
    for name, key in keys:
        d = key.private_bytes(serialization.Encoding.DER, serialization.PrivateFormat.PKCS8, serialization.NoEncryption())
        e = read(d, 0)[2]
        ver = int.from_bytes(e[0][2], "big")
        alg = oid_text(e[1][2][0][2])
        params = "p" if len(e[1][2]) > 1 else "-"
        pk = e[2][2]
        curve = "-"
        if name == "rsa":
            if pk != key.private_bytes(serialization.Encoding.DER, serialization.PrivateFormat.TraditionalOpenSSL, serialization.NoEncryption()):
                raise SystemExit("RSAPrivateKey differs")
        elif name.startswith("p"):
            inner = read(pk, 0)[2]
            n = key.private_numbers().private_value
            if int.from_bytes(inner[1][2], "big") != n:
                raise SystemExit("ECPrivateKey differs")
        else:
            curve = read(pk, 0)[2].hex()
            if curve != key.private_bytes(serialization.Encoding.Raw, serialization.PrivateFormat.Raw, serialization.NoEncryption()).hex():
                raise SystemExit("CurvePrivateKey differs")
        if run(["openssl", "pkey", "-inform", "DER", "-in", tmp("k.der", d), "-noout"]).returncode != 0:
            raise SystemExit("openssl refuses a key")
        serialization.load_der_private_key(d, None)
        tally["keys"] += 1
        want = "v%d alg=%s params=%s key=%s curve=%s pub=- attrs=0" % (ver, alg, params, pk.hex(), curve)
        case("p8_" + name, 'p8(PR.Pkcs.rules(), hx("%s"))' % d.hex(), want)
        cut = d[:rng.randrange(1, len(d) - 1)]
        if run(["openssl", "pkey", "-inform", "DER", "-in", tmp("k.der", cut), "-noout"]).returncode == 0:
            raise SystemExit("openssl reads a cut key")
        try:
            serialization.load_der_private_key(cut, None)
            raise SystemExit("cryptography reads a cut key")
        except ValueError:
            pass
        tally["refused"] += 1
        case("p8_%s_cut" % name, 'p8(PR.Pkcs.rules(), hx("%s"))' % cut.hex(), "ERR")
        if name == "ed25519":
            # v2 with the public key (RFC 5958 section 2: [1] IMPLICIT BIT
            # STRING), version 1
            pub = key.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
            body = bytes([0x02, 0x01, 0x01]) + raw(d, e[1]) + raw(d, e[2]) + bytes([0x81, len(pub) + 1, 0]) + pub
            v2 = bytes([0x30, len(body)]) + body
            # (OpenSSL 3.0 reads PrivateKeyInfo only, and refuses it)
            if run(["openssl", "pkey", "-inform", "DER", "-in", tmp("k.der", v2), "-noout"]).returncode == 0:
                raise SystemExit("openssl reads a v2 key: compare it")
            case("p8_ed25519_v2", 'p8(PR.Pkcs.rules(), hx("%s"))' % v2.hex(), "v1 alg=%s params=- key=%s curve=%s pub=%s attrs=0" % (alg, pk.hex(), curve, pub.hex()))
            # the public key in a v1 key: refused under the versions rule
            v1 = bytes([0x30, len(body), 0x02, 0x01, 0x00]) + body[3:]
            case("p8_ed25519_v1pub", 'p8(PR.Pkcs.rules(), hx("%s"))' % v1.hex(), "ERR")
            case("p8_ed25519_v1pub_lenient", 'p8(PR.Pkcs.rules_lenient(), hx("%s"))' % v1.hex(), "v0 alg=%s params=- key=%s curve=%s pub=%s attrs=0" % (alg, pk.hex(), curve, pub.hex()))

    chunks = [lines[i:i + 60] for i in range(0, len(lines), 60)]
    with open(os.path.join(here, "cases.bend"), "w", newline="\n", encoding="utf-8") as f:
        f.write(open(os.path.join(here, "show.bend.in"), encoding="utf-8").read())
        f.write("\n".join(defs))
        for i, ch in enumerate(chunks):
            f.write("\ndef part%d() -> IO(Unit):\n  do IO<Unit>:\n" % i + "".join("    %s\n" % ln for ln in ch))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "".join("    part%d()\n" % i for i in range(len(chunks))))
    with open(os.path.join(here, "expected.txt"), "w", newline="\n", encoding="utf-8") as f:
        f.write("\n".join(expect) + "\n")
    for n in os.listdir(work):
        os.unlink(os.path.join(work, n))
    os.rmdir(work)
    print("%d cases (%d messages, %d with certificates read by cryptography, and %d keys against openssl and cryptography; %d refusals)" % (len(expect), tally["cms"], tally["certs"], tally["keys"], tally["refused"]))


main()
