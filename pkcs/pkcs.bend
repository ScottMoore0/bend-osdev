# bend-osdev-pkcs: CMS SignedData (RFC 5652, which PKCS #7 v1.5's, RFC 2315,
# is a version of), the entry file. Cms.parse reads a ContentInfo holding a
# SignedData into its fields: the digest algorithms, the encapsulated
# content (absent for a detached signature, 5.2), the certificates and
# CRLs as their octets, and each SignerInfo (signer.bend). It checks what
# its rules ask (rules.bend). PKCS #8 keys are p8.bend; the signed octets
# and the signature check are signed.bend.
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/node.bend as AN
import ../asn1/tag.bend as AT
import ../asn1/rules.bend as AR
import ../asn1/prim.bend as AP
import ../asn1/schema.bend as ASc
import ../oid/oid.bend as O
import ../x509/alg.bend as XA
import ./error.bend as PE
import ./rules.bend as PR
import ./schema.bend as PS
import ./attr.bend as PA
import ./signer.bend as PG

type CmsSignedData is Data:
  CmsSignedData{version: Nat, digest_algs: List<&2, XA.X509AlgId>, content_type: O.Oid, content: Maybe<&2, B.Octets>, certificates: List<&2, B.Octets>, crls: List<&2, B.Octets>, signers: List<&2, PG.CmsSigner>, raw: B.Octets}

def CmsSignedData.version(s: CmsSignedData) -> Nat:
  match s:
    case CmsSignedData{v, d, t, c, x, l, g, r}:
      v

def CmsSignedData.digest_algs(s: CmsSignedData) -> List<&2, XA.X509AlgId>:
  match s:
    case CmsSignedData{v, d, t, c, x, l, g, r}:
      d

# eContentType
def CmsSignedData.content_type(s: CmsSignedData) -> O.Oid:
  match s:
    case CmsSignedData{v, d, t, c, x, l, g, r}:
      t

# eContent's octets (None for a detached signature)
def CmsSignedData.content(s: CmsSignedData) -> Maybe<&2, B.Octets>:
  match s:
    case CmsSignedData{v, d, t, c, x, l, g, r}:
      c

# each CertificateChoices element's octets
def CmsSignedData.certificates(s: CmsSignedData) -> List<&2, B.Octets>:
  match s:
    case CmsSignedData{v, d, t, c, x, l, g, r}:
      x

# each RevocationInfoChoice element's octets
def CmsSignedData.crls(s: CmsSignedData) -> List<&2, B.Octets>:
  match s:
    case CmsSignedData{v, d, t, c, x, l, g, r}:
      l

def CmsSignedData.signers(s: CmsSignedData) -> List<&2, PG.CmsSigner>:
  match s:
    case CmsSignedData{v, d, t, c, x, l, g, r}:
      g

# the SignedData's exact octets
def CmsSignedData.raw(s: CmsSignedData) -> B.Octets:
  match s:
    case CmsSignedData{v, d, t, c, x, l, g, r}:
      r

# The object identifiers used here (RFC 5652 sections 4, 5.1, 11.1, 11.2)

def Cms.id_data() -> O.Oid:
  O.Oid{[1n, 2n, 840n, 113549n, 1n, 7n, 1n]}

def Cms.id_signed_data() -> O.Oid:
  O.Oid{[1n, 2n, 840n, 113549n, 1n, 7n, 2n]}

def Cms.id_content_type() -> O.Oid:
  O.Oid{[1n, 2n, 840n, 113549n, 1n, 9n, 3n]}

def Cms.id_message_digest() -> O.Oid:
  O.Oid{[1n, 2n, 840n, 113549n, 1n, 9n, 4n]}

# Reading

def pk.raws(ms: List<&2, ASc.Asn1Match>) -> List<&2, B.Octets>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      Con{ASc.Asn1Match.raw(m), pk.raws(t)}

def pk.algs(ms: List<&2, ASc.Asn1Match>) -> Result<&2, &2, PE.PkcsError, List<&2, XA.X509AlgId>>:
  match ms:
    case Nil{}:
      Done{Nil{}}
    case Con{m, t}:
      PE.pk.cons(XA.X509AlgId, PE.pk.x509(XA.X509AlgId, XA.X509AlgId.of_match(m)), pk.algs(t))

def pk.oid(m: Maybe<&2, AN.Asn1Node>, e: PE.PkcsError) -> Result<&2, &2, PE.PkcsError, O.Oid>:
  match m:
    case None{}:
      Fail{e}
    case Some{n}:
      PE.pk.oid_or(O.Oid.of_node(n), e)

def pk.econtent(+r: PR.PkcsRules, m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, PE.PkcsError, Maybe<&2, B.Octets>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{n}:
      Result.map(&2, &2, PE.PkcsError, B.Octets, Maybe<&2, B.Octets>, o => Some{o}, PE.pk.or(B.Octets, AP.Asn1.get_octets(PR.PkcsRules.asn1(r), n), PE.PkcsBadContent{}))

def pk.sd.of(+r: PR.PkcsRules, +m: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, CmsSignedData>:
  +v = PG.pk.nat(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)), PE.PkcsBadVersion{})
  +d = pk.algs(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 1n)))
  +em = ASc.Asn1Match.at(m, 2n)
  +t = pk.oid(ASc.Asn1Match.node(ASc.Asn1Match.at(em, 0n)), PE.PkcsBadContent{})
  +c = pk.econtent(r, ASc.Asn1Match.node(ASc.Asn1Match.inner(ASc.Asn1Match.at(em, 1n))))
  +x = pk.raws(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 3n)))
  +l = pk.raws(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 4n)))
  +g = PG.pk.signers.of(r, ASc.Asn1Match.items(ASc.Asn1Match.at(m, 5n)))
  +raw = ASc.Asn1Match.raw(m)
  PE.pk.then(Nat, CmsSignedData, v, v1 => PE.pk.then(List<&2, XA.X509AlgId>, CmsSignedData, d, d1 => PE.pk.then(O.Oid, CmsSignedData, t, t1 => PE.pk.then(Maybe<&2, B.Octets>, CmsSignedData, c, c1 => PE.pk.then(List<&2, PG.CmsSigner>, CmsSignedData, g, g1 => Done{CmsSignedData{v1, d1, t1, c1, x, l, g1, raw}})))))

def pk.sd.inner(+r: PR.PkcsRules, ok: Bool, +ci: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, CmsSignedData>:
  match ok:
    case False{}:
      Fail{PE.PkcsNotSignedData{}}
    case True{}:
      PE.pk.then(ASc.Asn1Match, CmsSignedData, PE.pk.lift(ASc.Asn1Match, ASc.Asn1.match(PR.PkcsRules.asn1(r), PS.pk.s.signed_data(), ASc.Asn1Match.raw(ASc.Asn1Match.inner(ASc.Asn1Match.at(ci, 1n))))), m => pk.sd.of(r, m))

def pk.ci.of(+r: PR.PkcsRules, +ci: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, CmsSignedData>:
  PE.pk.then(O.Oid, CmsSignedData, pk.oid(ASc.Asn1Match.node(ASc.Asn1Match.at(ci, 0n)), PE.PkcsNotSignedData{}), +t => pk.sd.inner(r, O.Oid.is_eq(t, Cms.id_signed_data()), ci))

def pk.parse0(+r: PR.PkcsRules, b: B.Octets) -> Result<&2, &2, PE.PkcsError, CmsSignedData>:
  PE.pk.then(ASc.Asn1Match, CmsSignedData, PE.pk.lift(ASc.Asn1Match, ASc.Asn1.match(PR.PkcsRules.asn1(r), PS.pk.s.content_info(), b)), m => pk.ci.of(r, m))

# What the rules ask (rules.bend)

def pk.is_ski(s: PG.CmsSid) -> Bool:
  match s:
    case PG.CmsSidKeyId{k}:
      True{}
    case PG.CmsSidIssuer{i, n}:
      False{}

def pk.any_ski(gs: List<&2, PG.CmsSigner>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{g, t}:
      Bool.or(pk.is_ski(PG.CmsSigner.sid(g)), pk.any_ski(t))

def pk.head.l(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      x

def pk.head(o: B.Octets) -> U32:
  pk.head.l(B.Octets.to_list(o))

def pk.any_tag(os: List<&2, B.Octets>, +t: U32) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{o, r}:
      Bool.or(U32.is_eq(pk.head(o), t), pk.any_tag(r, t))

# SignedData's version as RFC 5652 5.1 sets it: 5 with an other
# certificate ([3]) or revocation format ([1]); 4 with a v2 attribute
# certificate ([2]); 3 with a v1 attribute certificate ([1]), a version 3
# SignerInfo, or content other than id-data; else 1
def Cms.expected_version(+s: CmsSignedData) -> Nat:
  +xs = CmsSignedData.certificates(s)
  +five = Bool.or(pk.any_tag(xs, 163), pk.any_tag(CmsSignedData.crls(s), 161))
  +four = pk.any_tag(xs, 162)
  +three = Bool.or(pk.any_tag(xs, 161), Bool.or(pk.any_ski(CmsSignedData.signers(s)), Bool.not(O.Oid.is_eq(CmsSignedData.content_type(s), Cms.id_data()))))
  Bool.pick(Nat, five, 5n, Bool.pick(Nat, four, 4n, Bool.pick(Nat, three, 3n, 1n)))

def pk.signer_version(+g: PG.CmsSigner) -> Bool:
  Nat.is_eq(PG.CmsSigner.version(g), Bool.pick(Nat, pk.is_ski(PG.CmsSigner.sid(g)), 3n, 1n))

def pk.attrs_der(a: Maybe<&2, PG.CmsAttrs>) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{x}:
      Result.is_done(&2, &2, AE.Asn1Error, ASc.Asn1Match, ASc.Asn1.match(AR.Asn1Rules.der(), PS.pk.s.attrs(0n), PG.CmsAttrs.raw(x)))

def pk.oid_is(r: Result<&2, &2, O.OidError, O.Oid>, +t: O.Oid) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{o}:
      O.Oid.is_eq(o, t)

def pk.ct_ok(+t: O.Oid, m: Maybe<&2, AN.Asn1Node>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      pk.oid_is(O.Oid.of_node(n), t)

def pk.md_ok(m: Maybe<&2, AN.Asn1Node>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      Result.is_done(&2, &2, AE.Asn1Error, B.Octets, AP.Asn1.get_octets(AR.Asn1Rules.der(), n))

def pk.single_of(m: Maybe<&2, PA.CmsAttr>) -> Maybe<&2, AN.Asn1Node>:
  match m:
    case None{}:
      None{}
    case Some{a}:
      PA.CmsAttr.single(a)

def pk.one_attr(+xs: List<&2, PA.CmsAttr>, +id: O.Oid) -> Maybe<&2, AN.Asn1Node>:
  Bool.pick(Maybe<&2, AN.Asn1Node>, Nat.is_eq(PA.Cms.count_attr(xs, id), 1n), pk.single_of(PA.Cms.find_attr(xs, id)), None{})

def pk.required.attrs(+t: O.Oid, a: Maybe<&2, PG.CmsAttrs>) -> Result<&2, &2, PE.PkcsError, Unit>:
  match a:
    case None{}:
      PE.pk.check(O.Oid.is_eq(t, Cms.id_data()), PE.PkcsMissingAttrs{})
    case Some{x}:
      +xs = PG.CmsAttrs.attrs(x)
      PE.pk.first([PE.pk.check(Nat.is_eq(PA.Cms.count_attr(xs, Cms.id_content_type()), 1n), PE.PkcsBadAttribute{Cms.id_content_type()}), PE.pk.check(pk.ct_ok(t, pk.one_attr(xs, Cms.id_content_type())), PE.PkcsContentTypeMismatch{}), PE.pk.check(pk.md_ok(pk.one_attr(xs, Cms.id_message_digest())), PE.PkcsBadAttribute{Cms.id_message_digest()})])

def pk.listed(ds: List<&2, XA.X509AlgId>, +a: XA.X509AlgId) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      Bool.or(O.Oid.is_eq(XA.X509AlgId.oid(d), XA.X509AlgId.oid(a)), pk.listed(t, a))

def pk.signer_ok(+r: PR.PkcsRules, +s: CmsSignedData, +g: PG.CmsSigner) -> Result<&2, &2, PE.PkcsError, Unit>:
  PE.pk.first([PE.pk.gate(PR.PkcsRules.versions(r), PE.pk.check(pk.signer_version(g), PE.PkcsBadVersion{})), PE.pk.gate(PR.PkcsRules.attrs_der(r), PE.pk.check(pk.attrs_der(PG.CmsSigner.signed_attrs(g)), PE.PkcsAttrsNotDer{})), PE.pk.gate(PR.PkcsRules.attrs_required(r), pk.required.attrs(CmsSignedData.content_type(s), PG.CmsSigner.signed_attrs(g))), PE.pk.gate(PR.PkcsRules.digests_listed(r), PE.pk.check(pk.listed(CmsSignedData.digest_algs(s), PG.CmsSigner.digest_alg(g)), PE.PkcsDigestNotListed{}))])

def pk.signers_ok(+r: PR.PkcsRules, +s: CmsSignedData, gs: List<&2, PG.CmsSigner>) -> Result<&2, &2, PE.PkcsError, Unit>:
  match gs:
    case Nil{}:
      Done{Unit{}}
    case Con{g, t}:
      PE.pk.first([pk.signer_ok(r, s, g), pk.signers_ok(r, s, t)])

def pk.conform(+r: PR.PkcsRules, +s: CmsSignedData) -> Result<&2, &2, PE.PkcsError, Unit>:
  PE.pk.first([PE.pk.gate(PR.PkcsRules.versions(r), PE.pk.check(Nat.is_eq(CmsSignedData.version(s), Cms.expected_version(s)), PE.PkcsBadVersion{})), pk.signers_ok(r, s, CmsSignedData.signers(s))])

# whether a SignedData passes every check its rules ask for
def CmsSignedData.conforms(+r: PR.PkcsRules, s: CmsSignedData) -> Bool:
  Result.is_done(&2, &2, PE.PkcsError, Unit, pk.conform(r, s))

# Parsing

def pk.fin(q: Result<&2, &2, PE.PkcsError, Unit>, s: CmsSignedData) -> Result<&2, &2, PE.PkcsError, CmsSignedData>:
  match q:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{s}

def pk.finish(+r: PR.PkcsRules, res: Result<&2, &2, PE.PkcsError, CmsSignedData>) -> Result<&2, &2, PE.PkcsError, CmsSignedData>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{+s}:
      pk.fin(pk.conform(r, s), s)

# the SignedData of a ContentInfo's octets, under rules r
def Cms.parse(+r: PR.PkcsRules, b: B.Octets) -> Result<&2, &2, PE.PkcsError, CmsSignedData>:
  pk.finish(r, pk.parse0(r, b))
