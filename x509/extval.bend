# bend-osdev-x509, the extensions read here (RFC 5280 4.2.1, and Appendix
# A.2, whose module uses IMPLICIT TAGS), each from an extension's value:
#
#   basicConstraints (4.2.1.9)   SEQUENCE { cA BOOLEAN DEFAULT FALSE,
#                                  pathLenConstraint INTEGER (0..MAX)
#                                  OPTIONAL }
#   keyUsage (4.2.1.3)           BIT STRING: digitalSignature (0),
#                                  nonRepudiation (1), keyEncipherment (2),
#                                  dataEncipherment (3), keyAgreement (4),
#                                  keyCertSign (5), cRLSign (6),
#                                  encipherOnly (7), decipherOnly (8)
#   subjectKeyIdentifier         KeyIdentifier ::= OCTET STRING
#     (4.2.1.2)
#   authorityKeyIdentifier       SEQUENCE { keyIdentifier [0]
#     (4.2.1.1)                    KeyIdentifier OPTIONAL,
#                                  authorityCertIssuer [1] GeneralNames
#                                  OPTIONAL, authorityCertSerialNumber [2]
#                                  CertificateSerialNumber OPTIONAL }
#   subjectAltName (4.2.1.6)     GeneralNames ::= SEQUENCE SIZE (1..MAX) OF
#                                  GeneralName
#   extKeyUsage (4.2.1.12)       SEQUENCE SIZE (1..MAX) OF KeyPurposeId
#                                  (OBJECT IDENTIFIER)
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/asn1.bend as A
import ../asn1/prim.bend as AP
import ../asn1/bits.bend as ABi
import ../asn1/build.bend as ABu
import ../asn1/schema.bend as ASc
import ../oid/oid.bend as O
import ./error.bend as XE
import ./rules.bend as XR
import ./ext.bend as XX
import ./gname.bend as XG

type X509BasicConstraints is Data:
  X509BasicConstraints{ca: Bool, path_len: Maybe<&2, Nat>}

type X509Aki is Data:
  X509Aki{key_id: Maybe<&2, B.Octets>, issuer: Maybe<&2, List<&2, XG.X509GeneralName>>, serial: Maybe<&2, B.Octets>}

def X509BasicConstraints.ca(b: X509BasicConstraints) -> Bool:
  match b:
    case X509BasicConstraints{c, p}:
      c

def X509BasicConstraints.path_len(b: X509BasicConstraints) -> Maybe<&2, Nat>:
  match b:
    case X509BasicConstraints{c, p}:
      p

def X509Aki.key_id(a: X509Aki) -> Maybe<&2, B.Octets>:
  match a:
    case X509Aki{k, i, s}:
      k

def X509Aki.issuer(a: X509Aki) -> Maybe<&2, List<&2, XG.X509GeneralName>>:
  match a:
    case X509Aki{k, i, s}:
      i

def X509Aki.serial(a: X509Aki) -> Maybe<&2, B.Octets>:
  match a:
    case X509Aki{k, i, s}:
      s

# The extensions' identifiers (RFC 5280 A.2: id-ce is 2.5.29)

def X509.id_basic_constraints() -> O.Oid:
  O.Oid{[2n, 5n, 29n, 19n]}

def X509.id_key_usage() -> O.Oid:
  O.Oid{[2n, 5n, 29n, 15n]}

def X509.id_subject_key_id() -> O.Oid:
  O.Oid{[2n, 5n, 29n, 14n]}

def X509.id_authority_key_id() -> O.Oid:
  O.Oid{[2n, 5n, 29n, 35n]}

def X509.id_subject_alt_name() -> O.Oid:
  O.Oid{[2n, 5n, 29n, 17n]}

def X509.id_ext_key_usage() -> O.Oid:
  O.Oid{[2n, 5n, 29n, 37n]}

# Reading values

def x5.v.bad(e: XX.X509Ext) -> XE.X509Error:
  XE.X509BadExtension{XX.X509Ext.id(e)}

def x5.v.match(+r: XR.X509Rules, s: ASc.Asn1Schema, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, ASc.Asn1Match>:
  XE.x5.or(ASc.Asn1Match, ASc.Asn1.match(XR.X509Rules.asn1(r), s, XX.X509Ext.value(e)), x5.v.bad(e))

def x5.v.node(+r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, AN.Asn1Node>:
  XE.x5.or(AN.Asn1Node, A.Asn1.decode(XR.X509Rules.asn1(r), XX.X509Ext.value(e)), x5.v.bad(e))

def x5.v.then(-X: Data, -Y: Data, r: Result<&2, &2, XE.X509Error, X>, f: X -> Result<&2, &2, XE.X509Error, Y>) -> Result<&2, &2, XE.X509Error, Y>:
  Result.bind(&2, &2, XE.X509Error, X, Y, r, f)

def x5.v.opt(-X: Data, m: Maybe<&2, AN.Asn1Node>, f: AN.Asn1Node -> Result<&2, &2, AE.Asn1Error, X>, e: XE.X509Error) -> Result<&2, &2, XE.X509Error, Maybe<&2, X>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{n}:
      Result.map(&2, &2, XE.X509Error, X, Maybe<&2, X>, x => Some{x}, XE.x5.or(X, f(n), e))

def x5.v.need(-X: Data, m: Maybe<&2, AN.Asn1Node>, f: AN.Asn1Node -> Result<&2, &2, AE.Asn1Error, X>, e: XE.X509Error) -> Result<&2, &2, XE.X509Error, X>:
  match m:
    case None{}:
      Fail{e}
    case Some{n}:
      XE.x5.or(X, f(n), e)

def x5.s.bc() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1SDefault{ASc.Asn1S.elem(AT.Asn1Tag.boolean()), AP.Asn1.bool(False{})}, ASc.Asn1S.opt(ASc.Asn1S.elem(AT.Asn1Tag.integer()))])

def x5.bc.mk(a: Result<&2, &2, XE.X509Error, Bool>, b: Result<&2, &2, XE.X509Error, Maybe<&2, Nat>>) -> Result<&2, &2, XE.X509Error, X509BasicConstraints>:
  match a b:
    case Fail{x} _:
      Fail{x}
    case Done{c} Fail{x}:
      Fail{x}
    case Done{c} Done{p}:
      Done{X509BasicConstraints{c, p}}

def x5.bc.of(+r: XR.X509Rules, +e: XX.X509Ext, +m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509BasicConstraints>:
  x5.bc.mk(x5.v.need(Bool, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)), n => AP.Asn1.get_bool(XR.X509Rules.asn1(r), n), x5.v.bad(e)), x5.v.opt(Nat, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), n => AP.Asn1.get_nat(n), x5.v.bad(e)))

# basicConstraints from its extension
def X509.basic_constraints_of(+r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, X509BasicConstraints>:
  x5.v.then(ASc.Asn1Match, X509BasicConstraints, x5.v.match(r, x5.s.bc(), e), m => x5.bc.of(r, e, m))

# keyUsage from its extension
def X509.key_usage_of(+r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, ABi.Asn1Bits>:
  x5.v.then(AN.Asn1Node, ABi.Asn1Bits, x5.v.node(r, e), n => XE.x5.or(ABi.Asn1Bits, ABi.Asn1.get_bits(XR.X509Rules.asn1(r), n), x5.v.bad(e)))

def x5.ku.pick(set: Bool, +i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match set:
    case True{}:
      Con{i, rest}
    case False{}:
      rest

def x5.ku.go(k: Nat, +b: ABi.Asn1Bits, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      x5.ku.pick(ABi.Asn1Bits.bit(b, i), i, x5.ku.go(j, b, 1n+i))

# the key usage bits set, of the nine RFC 5280 names
def X509.key_usage_bits(+b: ABi.Asn1Bits) -> List<&2, Nat>:
  x5.ku.go(9n, b, 0n)

# subjectKeyIdentifier from its extension
def X509.subject_key_id_of(+r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, B.Octets>:
  x5.v.then(AN.Asn1Node, B.Octets, x5.v.node(r, e), n => XE.x5.or(B.Octets, AP.Asn1.get_octets(XR.X509Rules.asn1(r), n), x5.v.bad(e)))

def x5.s.aki() -> ASc.Asn1Schema:
  ASc.Asn1S.seq([ASc.Asn1S.opt(ASc.Asn1S.ctx(0n)), ASc.Asn1S.opt(ASc.Asn1SOf{AT.Asn1Tag.context(1n), ASc.Asn1S.any(), False{}}), ASc.Asn1S.opt(ASc.Asn1S.ctx(2n))])

def x5.v.names(+r: XR.X509Rules, m: Maybe<&2, AN.Asn1Node>, e: XE.X509Error) -> Result<&2, &2, XE.X509Error, Maybe<&2, List<&2, XG.X509GeneralName>>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{n}:
      Result.map(&2, &2, XE.X509Error, List<&2, XG.X509GeneralName>, Maybe<&2, List<&2, XG.X509GeneralName>>, x => Some{x}, XE.x5.or_x(List<&2, XG.X509GeneralName>, XG.X509.general_names(r, AN.Asn1Node.items(n)), e))

def x5.aki.mk(a: Result<&2, &2, XE.X509Error, Maybe<&2, B.Octets>>, b: Result<&2, &2, XE.X509Error, Maybe<&2, List<&2, XG.X509GeneralName>>>, c: Result<&2, &2, XE.X509Error, Maybe<&2, B.Octets>>) -> Result<&2, &2, XE.X509Error, X509Aki>:
  match a b c:
    case Done{x} Done{y} Done{z}:
      Done{X509Aki{x, y, z}}
    case Fail{x} _ _:
      Fail{x}
    case Done{x} Fail{y} _:
      Fail{y}
    case Done{x} Done{y} Fail{z}:
      Fail{z}

def x5.aki.of(+r: XR.X509Rules, +e: XX.X509Ext, +m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Aki>:
  +k = x5.v.opt(B.Octets, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)), n => AP.Asn1.get_octets_as(XR.X509Rules.asn1(r), AT.Asn1Tag.context(0n), n), x5.v.bad(e))
  +s = x5.v.opt(B.Octets, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 2n)), n => AP.Asn1.get_int_bytes_as(AT.Asn1Tag.context(2n), n), x5.v.bad(e))
  x5.aki.mk(k, x5.v.names(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), x5.v.bad(e)), s)

# authorityKeyIdentifier from its extension
def X509.authority_key_id_of(+r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, X509Aki>:
  x5.v.then(ASc.Asn1Match, X509Aki, x5.v.match(r, x5.s.aki(), e), m => x5.aki.of(r, e, m))

def x5.v.nonempty(-X: Data, xs: List<&2, X>, e: XE.X509Error) -> Result<&2, &2, XE.X509Error, List<&2, X>>:
  match xs:
    case Nil{}:
      Fail{e}
    case Con{a, t}:
      Done{Con{a, t}}

# subjectAltName from its extension (one name or more)
def X509.subject_alt_name_of(+r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, List<&2, XG.X509GeneralName>>:
  x5.v.then(AN.Asn1Node, List<&2, XG.X509GeneralName>, x5.v.node(r, e), n => x5.v.then(List<&2, AN.Asn1Node>, List<&2, XG.X509GeneralName>, XE.x5.or(List<&2, AN.Asn1Node>, ABu.Asn1.get_seq(n), x5.v.bad(e)), xs => x5.v.then(List<&2, XG.X509GeneralName>, List<&2, XG.X509GeneralName>, XE.x5.or_x(List<&2, XG.X509GeneralName>, XG.X509.general_names(r, xs), x5.v.bad(e)), gs => x5.v.nonempty(XG.X509GeneralName, gs, x5.v.bad(e)))))

def x5.v.oids(ns: List<&2, AN.Asn1Node>, +e: XE.X509Error) -> Result<&2, &2, XE.X509Error, List<&2, O.Oid>>:
  match ns:
    case Nil{}:
      Done{Nil{}}
    case Con{n, t}:
      XE.x5.cons(O.Oid, XE.x5.oid_or(O.Oid.of_node(n), e), x5.v.oids(t, e))

# extKeyUsage from its extension (one purpose or more)
def X509.ext_key_usage_of(+r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, List<&2, O.Oid>>:
  x5.v.then(AN.Asn1Node, List<&2, O.Oid>, x5.v.node(r, e), n => x5.v.then(List<&2, AN.Asn1Node>, List<&2, O.Oid>, XE.x5.or(List<&2, AN.Asn1Node>, ABu.Asn1.get_seq(n), x5.v.bad(e)), xs => x5.v.then(List<&2, O.Oid>, List<&2, O.Oid>, x5.v.oids(xs, x5.v.bad(e)), os => x5.v.nonempty(O.Oid, os, x5.v.bad(e)))))

# Which extensions are read here

def x5.kind.go(ids: List<&2, O.Oid>, +id: O.Oid, +i: Nat) -> Nat:
  match ids:
    case Nil{}:
      0n
    case Con{x, t}:
      Bool.pick(Nat, O.Oid.is_eq(x, id), i, x5.kind.go(t, id, 1n+i))

# 1 to 6 for the extensions read here, in the order below; 0 for others
def x5.kind(+id: O.Oid) -> Nat:
  x5.kind.go([X509.id_basic_constraints(), X509.id_key_usage(), X509.id_subject_key_id(), X509.id_authority_key_id(), X509.id_subject_alt_name(), X509.id_ext_key_usage()], id, 1n)

# whether an extension is one read here
def X509.is_known_ext(+id: O.Oid) -> Bool:
  Bool.not(Nat.is_eq(x5.kind(id), 0n))

def x5.drop(-X: Data, r: Result<&2, &2, XE.X509Error, X>) -> Result<&2, &2, XE.X509Error, Unit>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{Unit{}}

def x5.known.go(k: Nat, +r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, Unit>:
  match k:
    case 1n:
      x5.drop(X509BasicConstraints, X509.basic_constraints_of(r, e))
    case 2n:
      x5.drop(ABi.Asn1Bits, X509.key_usage_of(r, e))
    case 3n:
      x5.drop(B.Octets, X509.subject_key_id_of(r, e))
    case 4n:
      x5.drop(X509Aki, X509.authority_key_id_of(r, e))
    case 5n:
      x5.drop(List<&2, XG.X509GeneralName>, X509.subject_alt_name_of(r, e))
    case 6n:
      x5.drop(List<&2, O.Oid>, X509.ext_key_usage_of(r, e))
    case _:
      Done{Unit{}}

# whether an extension read here is well formed (others pass)
def x5.known(+r: XR.X509Rules, +e: XX.X509Ext) -> Result<&2, &2, XE.X509Error, Unit>:
  x5.known.go(x5.kind(XX.X509Ext.id(e)), r, e)
