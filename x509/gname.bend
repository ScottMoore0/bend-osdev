# bend-osdev-x509, GeneralName (RFC 5280 4.2.1.6, and Appendix A.2, whose
# module uses IMPLICIT TAGS):
#
#   GeneralName ::= CHOICE {
#     otherName [0] AnotherName,           -- SEQUENCE { type-id OBJECT
#                                          --   IDENTIFIER, value [0]
#                                          --   EXPLICIT ANY }
#     rfc822Name [1] IA5String, dNSName [2] IA5String,
#     x400Address [3] ORAddress, directoryName [4] Name,
#     ediPartyName [5] EDIPartyName,
#     uniformResourceIdentifier [6] IA5String,
#     iPAddress [7] OCTET STRING, registeredID [8] OBJECT IDENTIFIER }
#
# directoryName's tag is explicit (Name is a CHOICE, ITU-T X.680 (02/2021)
# 31.2.7). An iPAddress is four octets (IPv4) or sixteen (IPv6) (4.2.1.6).
# x400Address and ediPartyName are kept as elements.
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/encode.bend as AEn
import ../asn1/string.bend as AS
import ../asn1/schema.bend as ASc
import ../oid/oid.bend as O
import ../oid/text.bend as OT
import ./error.bend as XE
import ./rules.bend as XR
import ./schema.bend as XS
import ./name.bend as XN

type X509GeneralName is Data:
  X509GnOther{type_id: O.Oid, value: AN.Asn1Node}
  X509GnEmail{text: String}
  X509GnDns{text: String}
  X509GnX400{node: AN.Asn1Node}
  X509GnDir{name: XN.X509Name}
  X509GnEdi{node: AN.Asn1Node}
  X509GnUri{text: String}
  X509GnIp{addr: B.Octets}
  X509GnRid{id: O.Oid}

def x5.gn.bad() -> XE.X509Error:
  XE.X509BadName{}

def x5.gn.ia5(+r: XR.X509Rules, +k: Nat, n: AN.Asn1Node) -> Result<&2, &2, XE.X509Error, String>:
  Result.map(&2, &2, XE.X509Error, AS.Asn1Str, String, s => AS.Asn1Str.text(s), XE.x5.or(AS.Asn1Str, AS.Asn1.get_string_as(XR.X509Rules.asn1(r), AT.Asn1Tag.context(k), AS.Asn1Ia5{}, n), x5.gn.bad()))

def x5.gn.text(r: Result<&2, &2, XE.X509Error, String>, f: String -> X509GeneralName) -> Result<&2, &2, XE.X509Error, X509GeneralName>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      Done{f(s)}

def x5.gn.ip(+c: B.Octets) -> Result<&2, &2, XE.X509Error, X509GeneralName>:
  +l = B.Octets.len(c)
  Bool.pick(Result<&2, &2, XE.X509Error, X509GeneralName>, Bool.or(Nat.is_eq(l, 4n), Nat.is_eq(l, 16n)), Done{X509GnIp{c}}, Fail{x5.gn.bad()})

def x5.gn.rid(r: Result<&2, &2, XE.X509Error, O.Oid>) -> Result<&2, &2, XE.X509Error, X509GeneralName>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Done{X509GnRid{o}}

def x5.gn.prim(+r: XR.X509Rules, k: Nat, +n: AN.Asn1Node) -> Result<&2, &2, XE.X509Error, X509GeneralName>:
  match k:
    case 1n:
      x5.gn.text(x5.gn.ia5(r, 1n, n), s => X509GnEmail{s})
    case 2n:
      x5.gn.text(x5.gn.ia5(r, 2n, n), s => X509GnDns{s})
    case 6n:
      x5.gn.text(x5.gn.ia5(r, 6n, n), s => X509GnUri{s})
    case 7n:
      x5.gn.ip(AN.Asn1Node.content(n))
    case 8n:
      x5.gn.rid(XE.x5.oid_or(O.Oid.of_node(AN.Asn1Prim{AT.Asn1Tag.oid(), AN.Asn1Node.content(n)}), x5.gn.bad()))
    case _:
      Fail{x5.gn.bad()}

def x5.gn.other(r: Result<&2, &2, XE.X509Error, O.Oid>, v: AN.Asn1Node) -> Result<&2, &2, XE.X509Error, X509GeneralName>:
  match r v:
    case Fail{e} _:
      Fail{e}
    case Done{o} AN.Asn1Cons{AT.Asn1Tag{AT.Asn1Context{}, 0n}, Con{x, Nil{}}}:
      Done{X509GnOther{o, x}}
    case Done{o} _:
      Fail{x5.gn.bad()}

def x5.gn.dir(r: Result<&2, &2, XE.X509Error, XN.X509Name>) -> Result<&2, &2, XE.X509Error, X509GeneralName>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{X509GnDir{x}}

def x5.name.matched(m: Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>) -> Result<&2, &2, XE.X509Error, XN.X509Name>:
  match m:
    case Fail{e}:
      Fail{x5.gn.bad()}
    case Done{x}:
      XN.x5.name.of(x)

def x5.name.enc(+r: XR.X509Rules, b: Result<&2, &2, AE.Asn1Error, B.Octets>) -> Result<&2, &2, XE.X509Error, XN.X509Name>:
  match b:
    case Fail{e}:
      Fail{x5.gn.bad()}
    case Done{o}:
      x5.name.matched(ASc.Asn1.match(XR.X509Rules.asn1(r), XS.x5.s.name(), o))

# a Name held as an element, read through its DER octets (to keep them)
def x5.name.of_node(+r: XR.X509Rules, n: AN.Asn1Node) -> Result<&2, &2, XE.X509Error, XN.X509Name>:
  x5.name.enc(r, AEn.Asn1.encode(n))

def x5.gn.cons(+r: XR.X509Rules, k: Nat, +xs: List<&2, AN.Asn1Node>, +n: AN.Asn1Node) -> Result<&2, &2, XE.X509Error, X509GeneralName>:
  match k:
    case 0n:
      match xs:
        case Con{a, Con{b, Nil{}}}:
          x5.gn.other(XE.x5.oid_or(O.Oid.of_node(a), x5.gn.bad()), b)
        case _:
          Fail{x5.gn.bad()}
    case 3n:
      Done{X509GnX400{n}}
    case 4n:
      match xs:
        case Con{a, Nil{}}:
          x5.gn.dir(x5.name.of_node(r, a))
        case _:
          Fail{x5.gn.bad()}
    case 5n:
      Done{X509GnEdi{n}}
    case _:
      Fail{x5.gn.bad()}

# a GeneralName element
def X509.general_name(+r: XR.X509Rules, n: AN.Asn1Node) -> Result<&2, &2, XE.X509Error, X509GeneralName>:
  match n:
    case AN.Asn1Prim{AT.Asn1Tag{AT.Asn1Context{}, +k}, c}:
      x5.gn.prim(r, k, AN.Asn1Prim{AT.Asn1Tag.context(k), c})
    case AN.Asn1Cons{AT.Asn1Tag{AT.Asn1Context{}, +k}, +xs}:
      x5.gn.cons(r, k, xs, AN.Asn1Cons{AT.Asn1Tag.context(k), xs})
    case _:
      Fail{x5.gn.bad()}

def X509.general_names(+r: XR.X509Rules, ns: List<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, List<&2, X509GeneralName>>:
  match ns:
    case Nil{}:
      Done{Nil{}}
    case Con{n, t}:
      XE.x5.cons(X509GeneralName, X509.general_name(r, n), X509.general_names(r, t))

# Showing, as "kind:value"

def X509GeneralName.show(g: X509GeneralName) -> String:
  match g:
    case X509GnOther{o, v}:
      "othername:" ++ OT.Oid.to_text(o)
    case X509GnEmail{s}:
      "email:" ++ s
    case X509GnDns{s}:
      "DNS:" ++ s
    case X509GnX400{n}:
      "x400"
    case X509GnDir{x}:
      "dir:" ++ XN.X509Name.show(x)
    case X509GnEdi{n}:
      "edi"
    case X509GnUri{s}:
      "URI:" ++ s
    case X509GnIp{a}:
      "IP:" ++ B.Octets.hex(a)
    case X509GnRid{o}:
      "RID:" ++ OT.Oid.to_text(o)
