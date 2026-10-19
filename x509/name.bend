# bend-osdev-x509, Name (RFC 5280 4.1.2.4): a sequence of relative
# distinguished names, each a set of attribute type and value pairs. The
# values are left as elements (their types are the attributes'; RFC 5280
# 4.1.2.4 lists the directory string choices) and the exact octets of the
# whole name are kept, for binary comparison (namecmp.bend).
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/node.bend as AN
import ../asn1/rules.bend as AR
import ../asn1/encode.bend as AEn
import ../asn1/string.bend as AS
import ../asn1/schema.bend as ASc
import ../oid/oid.bend as O
import ../oid/show.bend as OS
import ./error.bend as XE

type X509Atv is Data:
  X509Atv{attr: O.Oid, value: AN.Asn1Node}

type X509Name is Data:
  X509Name{rdns: List<&2, List<&2, X509Atv>>, raw: B.Octets}

def X509Atv.attr(a: X509Atv) -> O.Oid:
  match a:
    case X509Atv{t, v}:
      t

def X509Atv.value(a: X509Atv) -> AN.Asn1Node:
  match a:
    case X509Atv{t, v}:
      v

def X509Name.rdns(n: X509Name) -> List<&2, List<&2, X509Atv>>:
  match n:
    case X509Name{r, raw}:
      r

def X509Name.raw(n: X509Name) -> B.Octets:
  match n:
    case X509Name{r, raw}:
      raw

def X509Name.is_empty(n: X509Name) -> Bool:
  match n:
    case X509Name{r, raw}:
      match r:
        case Nil{}:
          True{}
        case Con{a, t}:
          False{}

# Reading

def x5.atv.mk(r: Result<&2, &2, XE.X509Error, O.Oid>, v: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, X509Atv>:
  match r v:
    case Done{o} Some{x}:
      Done{X509Atv{o, x}}
    case Fail{e} _:
      Fail{e}
    case Done{o} None{}:
      Fail{XE.X509BadName{}}

def x5.atv.oid(m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, O.Oid>:
  match m:
    case None{}:
      Fail{XE.X509BadName{}}
    case Some{n}:
      XE.x5.oid_or(O.Oid.of_node(n), XE.X509BadName{})

def x5.atv.of(+m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Atv>:
  x5.atv.mk(x5.atv.oid(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n))), ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)))

def x5.atvs(ms: List<&2, ASc.Asn1Match>) -> Result<&2, &2, XE.X509Error, List<&2, X509Atv>>:
  match ms:
    case Nil{}:
      Done{Nil{}}
    case Con{m, t}:
      XE.x5.cons(X509Atv, x5.atv.of(m), x5.atvs(t))

def x5.rdns(ms: List<&2, ASc.Asn1Match>) -> Result<&2, &2, XE.X509Error, List<&2, List<&2, X509Atv>>>:
  match ms:
    case Nil{}:
      Done{Nil{}}
    case Con{m, t}:
      XE.x5.cons(List<&2, X509Atv>, x5.atvs(ASc.Asn1Match.items(m)), x5.rdns(t))

def x5.name.mk(r: Result<&2, &2, XE.X509Error, List<&2, List<&2, X509Atv>>>, raw: B.Octets) -> Result<&2, &2, XE.X509Error, X509Name>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rs}:
      Done{X509Name{rs, raw}}

# a Name matched against x5.s.name()
def x5.name.of(+m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Name>:
  x5.name.mk(x5.rdns(ASc.Asn1Match.items(m)), ASc.Asn1Match.raw(m))

# Showing: RDNs in order, joined by ", ", each attribute "type=value",
# joined by " + "; the type its registered name or dotted text, the value
# its text when it is a character string, else "#" and its DER in hex

def x5.value.show(r: Result<&2, &2, AE.Asn1Error, AS.Asn1Str>, +n: AN.Asn1Node) -> String:
  match r:
    case Done{s}:
      AS.Asn1Str.text(s)
    case Fail{e}:
      "#" ++ B.Octets.hex(Result.default(&2, &2, AE.Asn1Error, B.Octets, AEn.Asn1.encode(n), B.Octets.empty()))

def X509Atv.show(a: X509Atv) -> String:
  match a:
    case X509Atv{t, +v}:
      OS.Oid.show(t) ++ "=" ++ x5.value.show(AS.Asn1.get_string(AR.Asn1Rules.ber(), v), v)

def x5.join(+sep: String, xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{a, t}:
      match t:
        case Nil{}:
          a
        case Con{b, u}:
          a ++ sep ++ x5.join(sep, Con{b, u})

def x5.rdn.show(xs: List<&2, X509Atv>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{X509Atv.show(a), x5.rdn.show(t)}

def x5.rdns.show(rs: List<&2, List<&2, X509Atv>>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{x5.join(" + ", x5.rdn.show(r)), x5.rdns.show(t)}

def X509Name.show(n: X509Name) -> String:
  x5.join(", ", x5.rdns.show(X509Name.rdns(n)))

# a Name matched against X509.schema_name()
def X509Name.of_match(+m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Name>:
  x5.name.of(m)
