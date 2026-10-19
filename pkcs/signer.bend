# bend-osdev-pkcs, SignerInfo (RFC 5652 5.3; RFC 2315 9.2): who signed (by
# issuer and serial number, or by subject key identifier), the digest and
# signature algorithms, the signed attributes with their exact octets (the
# signature is over their DER, 5.4), the signature, and the unsigned
# attributes.
import Base
import ../bytes/bytes.bend as B
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/prim.bend as AP
import ../asn1/schema.bend as ASc
import ../x509/alg.bend as XA
import ../x509/name.bend as XN
import ./error.bend as PE
import ./rules.bend as PR
import ./attr.bend as PA

type CmsSid is Data:
  CmsSidIssuer{issuer: XN.X509Name, serial: B.Octets}
  CmsSidKeyId{key_id: B.Octets}

type CmsAttrs is Data:
  CmsAttrs{attrs: List<&2, PA.CmsAttr>, raw: B.Octets}

type CmsSigner is Data:
  CmsSigner{version: Nat, sid: CmsSid, digest_alg: XA.X509AlgId, signed_attrs: Maybe<&2, CmsAttrs>, sig_alg: XA.X509AlgId, signature: B.Octets, unsigned_attrs: List<&2, PA.CmsAttr>}

def CmsAttrs.attrs(a: CmsAttrs) -> List<&2, PA.CmsAttr>:
  match a:
    case CmsAttrs{x, r}:
      x

# the signed attributes' exact octets, with their [0] IMPLICIT tag
def CmsAttrs.raw(a: CmsAttrs) -> B.Octets:
  match a:
    case CmsAttrs{x, r}:
      r

def CmsSigner.version(s: CmsSigner) -> Nat:
  match s:
    case CmsSigner{v, i, d, a, g, x, u}:
      v

def CmsSigner.sid(s: CmsSigner) -> CmsSid:
  match s:
    case CmsSigner{v, i, d, a, g, x, u}:
      i

def CmsSigner.digest_alg(s: CmsSigner) -> XA.X509AlgId:
  match s:
    case CmsSigner{v, i, d, a, g, x, u}:
      d

def CmsSigner.signed_attrs(s: CmsSigner) -> Maybe<&2, CmsAttrs>:
  match s:
    case CmsSigner{v, i, d, a, g, x, u}:
      a

def CmsSigner.sig_alg(s: CmsSigner) -> XA.X509AlgId:
  match s:
    case CmsSigner{v, i, d, a, g, x, u}:
      g

def CmsSigner.signature(s: CmsSigner) -> B.Octets:
  match s:
    case CmsSigner{v, i, d, a, g, x, u}:
      x

def CmsSigner.unsigned_attrs(s: CmsSigner) -> List<&2, PA.CmsAttr>:
  match s:
    case CmsSigner{v, i, d, a, g, x, u}:
      u

# Reading

def pk.nat(m: Maybe<&2, AN.Asn1Node>, e: PE.PkcsError) -> Result<&2, &2, PE.PkcsError, Nat>:
  match m:
    case None{}:
      Fail{e}
    case Some{n}:
      PE.pk.or(Nat, AP.Asn1.get_nat(n), e)

def pk.octets(+r: PR.PkcsRules, m: Maybe<&2, AN.Asn1Node>, e: PE.PkcsError) -> Result<&2, &2, PE.PkcsError, B.Octets>:
  match m:
    case None{}:
      Fail{e}
    case Some{n}:
      PE.pk.or(B.Octets, AP.Asn1.get_octets(PR.PkcsRules.asn1(r), n), e)

def pk.sid.issuer(n: Result<&2, &2, PE.PkcsError, XN.X509Name>, s: Result<&2, &2, PE.PkcsError, B.Octets>) -> Result<&2, &2, PE.PkcsError, CmsSid>:
  match n s:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{y}:
      Done{CmsSidIssuer{x, y}}

def pk.int_bytes(m: Maybe<&2, AN.Asn1Node>, e: PE.PkcsError) -> Result<&2, &2, PE.PkcsError, B.Octets>:
  match m:
    case None{}:
      Fail{e}
    case Some{n}:
      PE.pk.or(B.Octets, AP.Asn1.get_int_bytes(n), e)

def pk.sid.pick(ski: Bool, n: AN.Asn1Node, +m: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, CmsSid>:
  match ski:
    case True{}:
      Done{CmsSidKeyId{AN.Asn1Node.content(n)}}
    case False{}:
      pk.sid.issuer(PE.pk.x509(XN.X509Name, XN.X509Name.of_match(ASc.Asn1Match.at(m, 0n))), pk.int_bytes(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), PE.PkcsBadSigner{}))

def pk.sid.node(mn: Maybe<&2, AN.Asn1Node>, +m: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, CmsSid>:
  match mn:
    case None{}:
      Fail{PE.PkcsBadSigner{}}
    case Some{+n}:
      pk.sid.pick(AT.Asn1Tag.is_eq(AN.Asn1Node.tag(n), AT.Asn1Tag.context(0n)), n, m)

# a SignerIdentifier's match (the CHOICE)
def pk.sid.of(+m: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, CmsSid>:
  +x = ASc.Asn1Match.inner(m)
  pk.sid.node(ASc.Asn1Match.node(x), x)

def pk.signed.of(+m: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, Maybe<&2, CmsAttrs>>:
  Bool.pick(Result<&2, &2, PE.PkcsError, Maybe<&2, CmsAttrs>>, ASc.Asn1Match.present(m), Result.map(&2, &2, PE.PkcsError, List<&2, PA.CmsAttr>, Maybe<&2, CmsAttrs>, xs => Some{CmsAttrs{xs, ASc.Asn1Match.raw(m)}}, PA.pk.attrs.of(ASc.Asn1Match.items(m))), Done{None{}})

# a SignerInfo matched against its schema
def pk.signer.of(+r: PR.PkcsRules, +m: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, CmsSigner>:
  +v = pk.nat(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)), PE.PkcsBadVersion{})
  +i = pk.sid.of(ASc.Asn1Match.at(m, 1n))
  +d = PE.pk.x509(XA.X509AlgId, XA.X509AlgId.of_match(ASc.Asn1Match.at(m, 2n)))
  +a = pk.signed.of(ASc.Asn1Match.at(m, 3n))
  +g = PE.pk.x509(XA.X509AlgId, XA.X509AlgId.of_match(ASc.Asn1Match.at(m, 4n)))
  +x = pk.octets(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 5n)), PE.PkcsBadSigner{})
  +u = PA.pk.attrs.of(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 6n)))
  PE.pk.then(Nat, CmsSigner, v, v1 => PE.pk.then(CmsSid, CmsSigner, i, i1 => PE.pk.then(XA.X509AlgId, CmsSigner, d, d1 => PE.pk.then(Maybe<&2, CmsAttrs>, CmsSigner, a, a1 => PE.pk.then(XA.X509AlgId, CmsSigner, g, g1 => PE.pk.then(B.Octets, CmsSigner, x, x1 => PE.pk.then(List<&2, PA.CmsAttr>, CmsSigner, u, u1 => Done{CmsSigner{v1, i1, d1, a1, g1, x1, u1}})))))))

def pk.signers.of(+r: PR.PkcsRules, ms: List<&2, ASc.Asn1Match>) -> Result<&2, &2, PE.PkcsError, List<&2, CmsSigner>>:
  match ms:
    case Nil{}:
      Done{Nil{}}
    case Con{m, t}:
      PE.pk.cons(CmsSigner, pk.signer.of(r, m), pk.signers.of(r, t))
