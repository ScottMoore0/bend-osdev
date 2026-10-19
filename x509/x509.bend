# bend-osdev-x509: X.509 v3 certificates (RFC 5280), the entry file.
# X509.parse reads a certificate's DER octets into its fields, keeping the
# exact octets of the tbsCertificate (what the issuer signed), of each
# name, algorithm identifier, key and extension; it checks what its rules
# ask (rules.bend), and X509Cert.conforms says the same of a parsed
# certificate. Chains are not validated here: verify.bend holds the
# signature check and the name links a validator builds on.
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/node.bend as AN
import ../asn1/tag.bend as AT
import ../asn1/prim.bend as AP
import ../asn1/bits.bend as ABi
import ../asn1/schema.bend as ASc
import ../oid/oid.bend as O
import ./error.bend as XE
import ./rules.bend as XR
import ./schema.bend as XS
import ./alg.bend as XA
import ./name.bend as XN
import ./validity.bend as XV
import ./spki.bend as XK
import ./ext.bend as XX
import ./extval.bend as XEV

type X509Tbs is Data:
  X509Tbs{version: Nat, serial: B.Octets, signature: XA.X509AlgId, issuer: XN.X509Name, validity: XV.X509Validity, subject: XN.X509Name, spki: XK.X509Spki, issuer_uid: Maybe<&2, ABi.Asn1Bits>, subject_uid: Maybe<&2, ABi.Asn1Bits>, exts: List<&2, XX.X509Ext>, exts_present: Bool, raw: B.Octets}

type X509Cert is Data:
  X509Cert{tbs: X509Tbs, sig_alg: XA.X509AlgId, sig: ABi.Asn1Bits, raw: B.Octets}

# The tbsCertificate's fields

# the version field's value: 0 for v1, 1 for v2, 2 for v3
def X509Tbs.version(t: X509Tbs) -> Nat:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      v

# the serial number's contents octets (two's complement, big-endian)
def X509Tbs.serial(t: X509Tbs) -> B.Octets:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      s

def X509Tbs.signature(t: X509Tbs) -> XA.X509AlgId:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      a

def X509Tbs.issuer(t: X509Tbs) -> XN.X509Name:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      i

def X509Tbs.validity(t: X509Tbs) -> XV.X509Validity:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      va

def X509Tbs.subject(t: X509Tbs) -> XN.X509Name:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      su

def X509Tbs.spki(t: X509Tbs) -> XK.X509Spki:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      k

def X509Tbs.issuer_uid(t: X509Tbs) -> Maybe<&2, ABi.Asn1Bits>:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      iu

def X509Tbs.subject_uid(t: X509Tbs) -> Maybe<&2, ABi.Asn1Bits>:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      su2

def X509Tbs.extensions(t: X509Tbs) -> List<&2, XX.X509Ext>:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      x

# whether the extensions field was present (even if empty)
def X509Tbs.has_extensions(t: X509Tbs) -> Bool:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      xp

# the tbsCertificate's exact octets: what the signature is over
def X509Tbs.raw(t: X509Tbs) -> B.Octets:
  match t:
    case X509Tbs{v, s, a, i, va, su, k, iu, su2, x, xp, r}:
      r

# The certificate's fields

def X509Cert.tbs(c: X509Cert) -> X509Tbs:
  match c:
    case X509Cert{t, a, s, r}:
      t

def X509Cert.sig_alg(c: X509Cert) -> XA.X509AlgId:
  match c:
    case X509Cert{t, a, s, r}:
      a

def X509Cert.signature(c: X509Cert) -> ABi.Asn1Bits:
  match c:
    case X509Cert{t, a, s, r}:
      s

# the certificate's exact octets
def X509Cert.raw(c: X509Cert) -> B.Octets:
  match c:
    case X509Cert{t, a, s, r}:
      r

# the signed octets (the tbsCertificate's) and the signature's octets
def X509Cert.tbs_raw(c: X509Cert) -> B.Octets:
  X509Tbs.raw(X509Cert.tbs(c))

def X509Cert.signature_octets(c: X509Cert) -> B.Octets:
  ABi.Asn1Bits.octets(X509Cert.signature(c))

def X509Cert.issuer(c: X509Cert) -> XN.X509Name:
  X509Tbs.issuer(X509Cert.tbs(c))

def X509Cert.subject(c: X509Cert) -> XN.X509Name:
  X509Tbs.subject(X509Cert.tbs(c))

def X509Cert.serial(c: X509Cert) -> B.Octets:
  X509Tbs.serial(X509Cert.tbs(c))

def X509Cert.validity(c: X509Cert) -> XV.X509Validity:
  X509Tbs.validity(X509Cert.tbs(c))

def X509Cert.spki(c: X509Cert) -> XK.X509Spki:
  X509Tbs.spki(X509Cert.tbs(c))

def X509Cert.extensions(c: X509Cert) -> List<&2, XX.X509Ext>:
  X509Tbs.extensions(X509Cert.tbs(c))

# the extension with this identifier, if the certificate has it
def X509Cert.extension(c: X509Cert, +id: O.Oid) -> Maybe<&2, XX.X509Ext>:
  XX.X509.find_ext(X509Cert.extensions(c), id)

# Reading the tbsCertificate

def x5.version.items(ns: List<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, Nat>:
  match ns:
    case Con{n, Nil{}}:
      XE.x5.or(Nat, AP.Asn1.get_nat(n), XE.X509BadVersion{})
    case _:
      Fail{XE.X509BadVersion{}}

def x5.version(m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, Nat>:
  match m:
    case None{}:
      Fail{XE.X509BadVersion{}}
    case Some{n}:
      x5.version.items(AN.Asn1Node.items(n))

def x5.serial(m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, B.Octets>:
  match m:
    case None{}:
      Fail{XE.X509BadSerial{}}
    case Some{n}:
      XE.x5.or(B.Octets, AP.Asn1.get_int_bytes(n), XE.X509BadSerial{})

def x5.uid(+r: XR.X509Rules, +k: Nat, m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, Maybe<&2, ABi.Asn1Bits>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{n}:
      Result.map(&2, &2, XE.X509Error, ABi.Asn1Bits, Maybe<&2, ABi.Asn1Bits>, x => Some{x}, XE.x5.or(ABi.Asn1Bits, ABi.Asn1.get_bits_as(XR.X509Rules.asn1(r), AT.Asn1Tag.context(k), n), XE.X509BadUniqueId{}))

def x5.tbs.of(+r: XR.X509Rules, +m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Tbs>:
  +v = x5.version(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)))
  +s = x5.serial(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)))
  +a = XA.x5.alg.of(ASc.Asn1Match.at(m, 2n))
  +i = XN.x5.name.of(ASc.Asn1Match.at(m, 3n))
  +va = XV.x5.validity.of(r, ASc.Asn1Match.at(m, 4n))
  +su = XN.x5.name.of(ASc.Asn1Match.at(m, 5n))
  +k = XK.x5.spki.of(r, ASc.Asn1Match.at(m, 6n))
  +iu = x5.uid(r, 1n, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 7n)))
  +su2 = x5.uid(r, 2n, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 8n)))
  +xm = ASc.Asn1Match.at(m, 9n)
  +x = XX.x5.exts.of(r, ASc.Asn1Match.items(ASc.Asn1Match.inner(xm)))
  +xp = ASc.Asn1Match.present(xm)
  +raw = ASc.Asn1Match.raw(m)
  XE.x5.then(Nat, X509Tbs, v, v1 => XE.x5.then(B.Octets, X509Tbs, s, s1 => XE.x5.then(XA.X509AlgId, X509Tbs, a, a1 => XE.x5.then(XN.X509Name, X509Tbs, i, i1 => XE.x5.then(XV.X509Validity, X509Tbs, va, va1 => XE.x5.then(XN.X509Name, X509Tbs, su, su1 => XE.x5.then(XK.X509Spki, X509Tbs, k, k1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X509Tbs, x, x1 => Done{X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}}))))))))))

def x5.cert.mk(t: Result<&2, &2, XE.X509Error, X509Tbs>, a: Result<&2, &2, XE.X509Error, XA.X509AlgId>, s: Result<&2, &2, XE.X509Error, ABi.Asn1Bits>, raw: B.Octets) -> Result<&2, &2, XE.X509Error, X509Cert>:
  match t a s:
    case Done{x} Done{y} Done{z}:
      Done{X509Cert{x, y, z, raw}}
    case Fail{e} _ _:
      Fail{e}
    case Done{x} Fail{e} _:
      Fail{e}
    case Done{x} Done{y} Fail{e}:
      Fail{e}

# a Certificate matched against x5.s.cert()
def x5.cert.of(+r: XR.X509Rules, +m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Cert>:
  x5.cert.mk(x5.tbs.of(r, ASc.Asn1Match.at(m, 0n)), XA.x5.alg.of(ASc.Asn1Match.at(m, 1n)), XK.x5.bits.of(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 2n)), XE.X509Asn1{AE.Asn1BadBits{}}), ASc.Asn1Match.raw(m))

# What the rules ask of a certificate (rules.bend)

def x5.gate(on: Bool, c: Result<&2, &2, XE.X509Error, Unit>) -> Result<&2, &2, XE.X509Error, Unit>:
  match on:
    case True{}:
      c
    case False{}:
      Done{Unit{}}

def x5.first(rs: List<&2, Result<&2, &2, XE.X509Error, Unit>>) -> Result<&2, &2, XE.X509Error, Unit>:
  match rs:
    case Nil{}:
      Done{Unit{}}
    case Con{Fail{e}, t}:
      Fail{e}
    case Con{Done{u}, t}:
      x5.first(t)

def x5.is_some_bits(m: Maybe<&2, ABi.Asn1Bits>) -> Bool:
  Maybe.is_some(&2, ABi.Asn1Bits, m)

def x5.nonempty(xs: List<&2, XX.X509Ext>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{a, t}:
      True{}

# RFC 5280 4.1.2.1, 4.1.2.8, 4.1.2.9
def x5.versions_ok(+t: X509Tbs) -> Result<&2, &2, XE.X509Error, Unit>:
  +v = X509Tbs.version(t)
  +uids = Bool.or(x5.is_some_bits(X509Tbs.issuer_uid(t)), x5.is_some_bits(X509Tbs.subject_uid(t)))
  +xp = X509Tbs.has_extensions(t)
  x5.first([XE.x5.check(Nat.is_le(v, 2n), XE.X509BadVersion{}), XE.x5.check(Bool.or(Bool.not(uids), Nat.is_le(1n, v)), XE.X509BadUniqueId{}), XE.x5.check(Bool.or(Bool.not(xp), Nat.is_eq(v, 2n)), XE.X509BadVersion{}), XE.x5.check(Bool.or(Bool.not(xp), x5.nonempty(X509Tbs.extensions(t))), XE.X509EmptyExtensions{})])

def x5.any_nonzero(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{a, t}:
      Bool.or(Bool.not(U32.is_eq(a, 0)), x5.any_nonzero(t))

def x5.serial_ok.go(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{a, t}:
      Bool.and(U32.is_lt(a, 128), Bool.and(x5.any_nonzero(Con{a, t}), Nat.is_le(List.length(&2, U32, Con{a, t}), 20n)))

# RFC 5280 4.1.2.2: positive, at most 20 octets
def X509.serial_ok(o: B.Octets) -> Bool:
  x5.serial_ok.go(B.Octets.to_list(o))

def x5.dup_check(m: Maybe<&2, O.Oid>) -> Result<&2, &2, XE.X509Error, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{o}:
      Fail{XE.X509DuplicateExtension{o}}

def x5.known_all(+r: XR.X509Rules, es: List<&2, XX.X509Ext>) -> Result<&2, &2, XE.X509Error, Unit>:
  match es:
    case Nil{}:
      Done{Unit{}}
    case Con{e, t}:
      x5.first([XEV.x5.known(r, e), x5.known_all(r, t)])

def x5.critical_all(es: List<&2, XX.X509Ext>) -> Result<&2, &2, XE.X509Error, Unit>:
  match es:
    case Nil{}:
      Done{Unit{}}
    case Con{+e, t}:
      x5.first([XE.x5.check(Bool.or(Bool.not(XX.X509Ext.critical(e)), XEV.X509.is_known_ext(XX.X509Ext.id(e))), XE.X509UnknownCritical{XX.X509Ext.id(e)}), x5.critical_all(t)])

def x5.conform(+r: XR.X509Rules, c: X509Cert) -> Result<&2, &2, XE.X509Error, Unit>:
  match c:
    case X509Cert{+t, +a, s, raw}:
      +es = X509Tbs.extensions(t)
      x5.first([x5.gate(XR.X509Rules.versions(r), x5.versions_ok(t)), x5.gate(XR.X509Rules.serial(r), XE.x5.check(X509.serial_ok(X509Tbs.serial(t)), XE.X509BadSerial{})), x5.gate(XR.X509Rules.alg_match(r), XE.x5.check(XA.X509AlgId.is_eq(X509Tbs.signature(t), a), XE.X509AlgMismatch{})), x5.gate(XR.X509Rules.issuer_nonempty(r), XE.x5.check(Bool.not(XN.X509Name.is_empty(X509Tbs.issuer(t))), XE.X509EmptyIssuer{})), x5.gate(XR.X509Rules.time_profile(r), XE.x5.check(XV.X509Validity.profile_ok(X509Tbs.validity(t)), XE.X509BadTime{})), x5.gate(XR.X509Rules.distinct_ext(r), x5.dup_check(XX.X509.duplicate_ext(es))), x5.gate(XR.X509Rules.known_ext(r), x5.known_all(r, es)), x5.gate(XR.X509Rules.unknown_critical(r), x5.critical_all(es))])

# whether a certificate passes every check its rules ask for
def X509Cert.conforms(+r: XR.X509Rules, c: X509Cert) -> Bool:
  Result.is_done(&2, &2, XE.X509Error, Unit, x5.conform(r, c))

# Parsing

def x5.fin(q: Result<&2, &2, XE.X509Error, Unit>, c: X509Cert) -> Result<&2, &2, XE.X509Error, X509Cert>:
  match q:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{c}

def x5.finish(+r: XR.X509Rules, res: Result<&2, &2, XE.X509Error, X509Cert>) -> Result<&2, &2, XE.X509Error, X509Cert>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{+c}:
      x5.fin(x5.conform(r, c), c)

def x5.parse0(+r: XR.X509Rules, b: B.Octets) -> Result<&2, &2, XE.X509Error, X509Cert>:
  XE.x5.then(ASc.Asn1Match, X509Cert, XE.x5.lift(ASc.Asn1Match, ASc.Asn1.match(XR.X509Rules.asn1(r), XS.x5.s.cert(), b)), m => x5.cert.of(r, m))

# the certificate whose octets b are, under rules r
def X509.parse(+r: XR.X509Rules, b: B.Octets) -> Result<&2, &2, XE.X509Error, X509Cert>:
  x5.finish(r, x5.parse0(r, b))
