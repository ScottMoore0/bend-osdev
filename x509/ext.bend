# bend-osdev-x509, Extension (RFC 5280 4.1.2.9, 4.2): an extension's
# object identifier, whether it is critical (DEFAULT FALSE), and its value:
# the contents of extnValue's OCTET STRING, the DER of the extension's own
# type. Every extension is kept, known or not, with its exact octets.
import Base
import ../bytes/bytes.bend as B
import ../asn1/node.bend as AN
import ../asn1/prim.bend as AP
import ../asn1/schema.bend as ASc
import ../oid/oid.bend as O
import ./error.bend as XE
import ./rules.bend as XR

type X509Ext is Data:
  X509Ext{id: O.Oid, critical: Bool, value: B.Octets, raw: B.Octets}

def X509Ext.id(e: X509Ext) -> O.Oid:
  match e:
    case X509Ext{i, c, v, r}:
      i

def X509Ext.critical(e: X509Ext) -> Bool:
  match e:
    case X509Ext{i, c, v, r}:
      c

def X509Ext.value(e: X509Ext) -> B.Octets:
  match e:
    case X509Ext{i, c, v, r}:
      v

def X509Ext.raw(e: X509Ext) -> B.Octets:
  match e:
    case X509Ext{i, c, v, r}:
      r

# Reading

def x5.ext.id(m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, O.Oid>:
  match m:
    case None{}:
      Fail{XE.X509BadExtension{O.Oid{Nil{}}}}
    case Some{n}:
      XE.x5.oid_or(O.Oid.of_node(n), XE.X509BadExtension{O.Oid{Nil{}}})

def x5.ext.bool(+r: XR.X509Rules, m: Maybe<&2, AN.Asn1Node>, +id: O.Oid) -> Result<&2, &2, XE.X509Error, Bool>:
  match m:
    case None{}:
      Fail{XE.X509BadExtension{id}}
    case Some{n}:
      XE.x5.or(Bool, AP.Asn1.get_bool(XR.X509Rules.asn1(r), n), XE.X509BadExtension{id})

def x5.ext.octets(+r: XR.X509Rules, m: Maybe<&2, AN.Asn1Node>, +id: O.Oid) -> Result<&2, &2, XE.X509Error, B.Octets>:
  match m:
    case None{}:
      Fail{XE.X509BadExtension{id}}
    case Some{n}:
      XE.x5.or(B.Octets, AP.Asn1.get_octets(XR.X509Rules.asn1(r), n), XE.X509BadExtension{id})

def x5.ext.mk(+id: O.Oid, c: Result<&2, &2, XE.X509Error, Bool>, v: Result<&2, &2, XE.X509Error, B.Octets>, raw: B.Octets) -> Result<&2, &2, XE.X509Error, X509Ext>:
  match c v:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{y}:
      Done{X509Ext{id, x, y, raw}}

def x5.ext.with(+r: XR.X509Rules, +m: ASc.Asn1Match, i: Result<&2, &2, XE.X509Error, O.Oid>) -> Result<&2, &2, XE.X509Error, X509Ext>:
  match i:
    case Fail{e}:
      Fail{e}
    case Done{+id}:
      x5.ext.mk(id, x5.ext.bool(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), id), x5.ext.octets(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 2n)), id), ASc.Asn1Match.raw(m))

# an Extension matched against x5.s.ext()
def x5.ext.of(+r: XR.X509Rules, +m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Ext>:
  x5.ext.with(r, m, x5.ext.id(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n))))

def x5.exts.of(+r: XR.X509Rules, ms: List<&2, ASc.Asn1Match>) -> Result<&2, &2, XE.X509Error, List<&2, X509Ext>>:
  match ms:
    case Nil{}:
      Done{Nil{}}
    case Con{m, t}:
      XE.x5.cons(X509Ext, x5.ext.of(r, m), x5.exts.of(r, t))

# Finding

def x5.find.pick(hit: Bool, e: X509Ext, rest: Maybe<&2, X509Ext>) -> Maybe<&2, X509Ext>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      rest

# the first extension with this identifier
def X509.find_ext(es: List<&2, X509Ext>, +id: O.Oid) -> Maybe<&2, X509Ext>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, t}:
      x5.find.pick(O.Oid.is_eq(X509Ext.id(e), id), e, X509.find_ext(t, id))

def x5.dup.pick(hit: Bool, +id: O.Oid, rest: Maybe<&2, O.Oid>) -> Maybe<&2, O.Oid>:
  match hit:
    case True{}:
      Some{id}
    case False{}:
      rest

# the first identifier that appears twice
def X509.duplicate_ext(es: List<&2, X509Ext>) -> Maybe<&2, O.Oid>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, +t}:
      x5.dup.pick(Maybe.is_some(&2, X509Ext, X509.find_ext(t, X509Ext.id(e))), X509Ext.id(e), X509.duplicate_ext(t))
