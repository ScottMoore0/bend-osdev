# bend-osdev-pkcs, what a signer signed and the extension points for
# checking it (RFC 5652 5.4, 5.6). The message digest is computed over the
# content's octets; without signed attributes the signature is over the
# same octets, and with them over the DER of the signed attributes with
# the EXPLICIT SET OF tag (31 hex) in place of the IMPLICIT [0] (5.4).
# Digest and signature schemes are the caller's: a digest is a function
# from octets to octets, a signature scheme bend-osdev-crypto's signature
# interface (crypto/sign.bend).
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/rules.bend as AR
import ../asn1/node.bend as AN
import ../asn1/prim.bend as AP
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ../x509/error.bend as XE
import ../x509/rules.bend as XR
import ../x509/namecmp.bend as XC
import ../x509/name.bend as XN
import ../x509/ext.bend as XX
import ../x509/extval.bend as XEV
import ../x509/x509.bend as X
import ./attr.bend as PA
import ./signer.bend as PG
import ./pkcs.bend as P

def pk.retag.l(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{49, t}

# octets with their first octet (an identifier) made SET's, 31 hex
def Cms.set_tagged(o: B.Octets) -> B.Octets:
  B.Octets.of_list(pk.retag.l(B.Octets.to_list(o)))

def pk.signed.msg(a: Maybe<&2, PG.CmsAttrs>, content: B.Octets) -> B.Octets:
  match a:
    case None{}:
      content
    case Some{x}:
      Cms.set_tagged(PG.CmsAttrs.raw(x))

# the octets a signer's signature is over, given the content's octets (the
# SignedData's own, or a detached signature's external content)
def Cms.signed_message(s: PG.CmsSigner, content: B.Octets) -> B.Octets:
  pk.signed.msg(PG.CmsSigner.signed_attrs(s), content)

# whether a signer's signature is valid under the public key with these
# bytes (False for a malformed key)
def Cms.verify_with(~PK: Data, ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>, ~verify: PK -> B.Octets -> B.Octets -> Bool, key: B.Octets, +s: PG.CmsSigner, content: B.Octets) -> Bool:
  Sg.CrSign.verify_bytes(~PK, ~pk_of, ~verify, key, Cms.signed_message(s, content), PG.CmsSigner.signature(s))

def pk.md.res(r: Result<&2, &2, AE.Asn1Error, B.Octets>) -> Maybe<&2, B.Octets>:
  match r:
    case Fail{e}:
      None{}
    case Done{o}:
      Some{o}

def pk.md.value(m: Maybe<&2, AN.Asn1Node>) -> Maybe<&2, B.Octets>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      pk.md.res(AP.Asn1.get_octets(AR.Asn1Rules.der(), n))

def pk.md.attr(m: Maybe<&2, PA.CmsAttr>) -> Maybe<&2, B.Octets>:
  match m:
    case None{}:
      None{}
    case Some{at}:
      pk.md.value(PA.CmsAttr.single(at))

def pk.md.of(a: Maybe<&2, PG.CmsAttrs>) -> Maybe<&2, B.Octets>:
  match a:
    case None{}:
      None{}
    case Some{x}:
      pk.md.attr(PA.Cms.find_attr(PG.CmsAttrs.attrs(x), P.Cms.id_message_digest()))

# the message-digest attribute's value (RFC 5652 11.2)
def Cms.message_digest(s: PG.CmsSigner) -> Maybe<&2, B.Octets>:
  pk.md.of(PG.CmsSigner.signed_attrs(s))

def pk.md.is(m: Maybe<&2, B.Octets>, d: B.Octets) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      B.Octets.is_eq(x, d)

# whether the message-digest attribute is digest's value of the content
def Cms.digest_matches(~digest: B.Octets -> B.Octets, s: PG.CmsSigner, content: B.Octets) -> Bool:
  pk.md.is(Cms.message_digest(s), digest(content))

# The signer's certificate

def pk.ski.res(r: Result<&2, &2, XE.X509Error, B.Octets>, +k: B.Octets) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{o}:
      B.Octets.is_eq(o, k)

def pk.ski.is(+k: B.Octets, m: Maybe<&2, XX.X509Ext>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{e}:
      pk.ski.res(XEV.X509.subject_key_id_of(XR.X509.rules_lenient(), e), k)

def pk.cert.is(+nr: XC.X509NameRules, +sid: PG.CmsSid, +c: X.X509Cert) -> Bool:
  match sid:
    case PG.CmsSidIssuer{i, n}:
      Bool.and(XC.X509Name.matches(nr, i, X.X509Cert.issuer(c)), B.Octets.is_eq(n, X.X509Cert.serial(c)))
    case PG.CmsSidKeyId{k}:
      pk.ski.is(k, X.X509Cert.extension(c, XEV.X509.id_subject_key_id()))

def pk.cert.pick(+nr: XC.X509NameRules, +sid: PG.CmsSid, r: Result<&2, &2, XE.X509Error, X.X509Cert>, rest: Maybe<&2, X.X509Cert>) -> Maybe<&2, X.X509Cert>:
  match r:
    case Fail{e}:
      rest
    case Done{+c}:
      Bool.pick(Maybe<&2, X.X509Cert>, pk.cert.is(nr, sid, c), Some{c}, rest)

def pk.cert.find(+xr: XR.X509Rules, +nr: XC.X509NameRules, +sid: PG.CmsSid, os: List<&2, B.Octets>) -> Maybe<&2, X.X509Cert>:
  match os:
    case Nil{}:
      None{}
    case Con{o, t}:
      pk.cert.pick(nr, sid, X.X509.parse(xr, o), pk.cert.find(xr, nr, sid, t))

# the certificate among the SignedData's that the signer names (by issuer
# compared under nr, and serial number; or by subject key identifier),
# read under xr
def Cms.signer_certificate(+xr: XR.X509Rules, +nr: XC.X509NameRules, s: P.CmsSignedData, g: PG.CmsSigner) -> Maybe<&2, X.X509Cert>:
  pk.cert.find(xr, nr, PG.CmsSigner.sid(g), P.CmsSignedData.certificates(s))
