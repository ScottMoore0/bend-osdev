# bend-osdev-pkcs, attributes (RFC 5652 5.3: Attribute ::= SEQUENCE {
# attrType OBJECT IDENTIFIER, attrValues SET OF AttributeValue }), as in
# SignerInfo's signed and unsigned attributes and PKCS #8's attributes.
# Values stay elements; the attribute's exact octets are kept.
import Base
import ../bytes/bytes.bend as B
import ../asn1/node.bend as AN
import ../asn1/schema.bend as ASc
import ../oid/oid.bend as O
import ./error.bend as PE

type CmsAttr is Data:
  CmsAttr{attr_type: O.Oid, values: List<&2, AN.Asn1Node>, raw: B.Octets}

def CmsAttr.attr_type(a: CmsAttr) -> O.Oid:
  match a:
    case CmsAttr{t, v, r}:
      t

def CmsAttr.values(a: CmsAttr) -> List<&2, AN.Asn1Node>:
  match a:
    case CmsAttr{t, v, r}:
      v

def CmsAttr.raw(a: CmsAttr) -> B.Octets:
  match a:
    case CmsAttr{t, v, r}:
      r

# the attribute's value when it has exactly one
def pk.one(vs: List<&2, AN.Asn1Node>) -> Maybe<&2, AN.Asn1Node>:
  match vs:
    case Con{v, Nil{}}:
      Some{v}
    case _:
      None{}

def CmsAttr.single(a: CmsAttr) -> Maybe<&2, AN.Asn1Node>:
  pk.one(CmsAttr.values(a))

def pk.nodes.put(m: Maybe<&2, AN.Asn1Node>, rest: List<&2, AN.Asn1Node>) -> List<&2, AN.Asn1Node>:
  match m:
    case None{}:
      rest
    case Some{n}:
      Con{n, rest}

def pk.nodes(ms: List<&2, ASc.Asn1Match>) -> List<&2, AN.Asn1Node>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      pk.nodes.put(ASc.Asn1Match.node(m), pk.nodes(t))

def pk.attr.type(m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, PE.PkcsError, O.Oid>:
  match m:
    case None{}:
      Fail{PE.PkcsBadAttribute{O.Oid{Nil{}}}}
    case Some{n}:
      PE.pk.oid_or(O.Oid.of_node(n), PE.PkcsBadAttribute{O.Oid{Nil{}}})

def pk.attr.mk(t: Result<&2, &2, PE.PkcsError, O.Oid>, vs: List<&2, AN.Asn1Node>, raw: B.Octets) -> Result<&2, &2, PE.PkcsError, CmsAttr>:
  match t:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Done{CmsAttr{o, vs, raw}}

# an Attribute matched against its schema
def pk.attr.of(+m: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, CmsAttr>:
  pk.attr.mk(pk.attr.type(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n))), pk.nodes(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 1n))), ASc.Asn1Match.raw(m))

def pk.attrs.of(ms: List<&2, ASc.Asn1Match>) -> Result<&2, &2, PE.PkcsError, List<&2, CmsAttr>>:
  match ms:
    case Nil{}:
      Done{Nil{}}
    case Con{m, t}:
      PE.pk.cons(CmsAttr, pk.attr.of(m), pk.attrs.of(t))

def pk.find.pick(hit: Bool, a: CmsAttr, rest: Maybe<&2, CmsAttr>) -> Maybe<&2, CmsAttr>:
  match hit:
    case True{}:
      Some{a}
    case False{}:
      rest

# the first attribute of this type
def Cms.find_attr(xs: List<&2, CmsAttr>, +id: O.Oid) -> Maybe<&2, CmsAttr>:
  match xs:
    case Nil{}:
      None{}
    case Con{+a, t}:
      pk.find.pick(O.Oid.is_eq(CmsAttr.attr_type(a), id), a, Cms.find_attr(t, id))

# how many attributes have this type
def Cms.count_attr(xs: List<&2, CmsAttr>, +id: O.Oid) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+a, t}:
      Nat.add(Bool.pick(Nat, O.Oid.is_eq(CmsAttr.attr_type(a), id), 1n, 0n), Cms.count_attr(t, id))
