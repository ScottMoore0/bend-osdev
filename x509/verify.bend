# bend-osdev-x509, the extension points for checking certificates: the
# signature check, through bend-osdev-crypto's signature interface (a
# scheme is its template arguments, crypto/sign.bend), and the name links
# of a chain. Choosing the scheme from the signature algorithm, and
# validating a path (RFC 5280 section 6: times, constraints, policies,
# revocation), are the caller's; these are the pieces it builds on.
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ./name.bend as XN
import ./namecmp.bend as XC
import ./spki.bend as XK
import ./x509.bend as X

# whether c's signature is valid for its tbsCertificate under the public
# key with these bytes (False for a malformed key)
def X509.verify_with(~PK: Data, ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>, ~verify: PK -> B.Octets -> B.Octets -> Bool, key: B.Octets, +c: X.X509Cert) -> Bool:
  Sg.CrSign.verify_bytes(~PK, ~pk_of, ~verify, key, X.X509Cert.tbs_raw(c), X.X509Cert.signature_octets(c))

def x5.key_or_empty(m: Maybe<&2, B.Octets>) -> B.Octets:
  Maybe.default(&2, B.Octets, m, B.Octets.empty())

# whether c's signature is valid under issuer's public key (its
# subjectPublicKey's octets, the bytes pk_of reads)
def X509.verify_by(~PK: Data, ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>, ~verify: PK -> B.Octets -> B.Octets -> Bool, issuer: X.X509Cert, c: X.X509Cert) -> Bool:
  X509.verify_with(~PK, ~pk_of, ~verify, x5.key_or_empty(XK.X509Spki.key_octets(X.X509Cert.spki(issuer))), c)

# whether parent's subject is child's issuer, under name rules r
def X509.issued_by(+r: XC.X509NameRules, child: X.X509Cert, parent: X.X509Cert) -> Bool:
  XC.X509Name.matches(r, X.X509Cert.issuer(child), X.X509Cert.subject(parent))

# whether each certificate of a path (from the end entity up) was issued by
# the next, by name
def X509.names_chain(+r: XC.X509NameRules, cs: List<&2, X.X509Cert>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+a, t}:
      match t:
        case Nil{}:
          True{}
        case Con{+b, +u}:
          Bool.and(X509.issued_by(r, a, b), X509.names_chain(r, Con{b, u}))

# whether a certificate names itself as its issuer (self-issued, RFC 5280
# 6.1)
def X509.self_issued(+r: XC.X509NameRules, +c: X.X509Cert) -> Bool:
  X509.issued_by(r, c, c)
