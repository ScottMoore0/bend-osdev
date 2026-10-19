# bend-osdev-x509, comparing names (RFC 5280 7.1): two names match when
# they have the same RDNs in the same order, two RDNs when they have the
# same attributes in any order, two attributes when their types are the
# same and their values match after string preparation (RFC 4518). Each
# step of preparation done here is a rule:
#
#   fold_case  case folding (RFC 4518 2.2, by RFC 3454 B.2); here for the
#              letters A to Z only
#   spaces     insignificant space handling (RFC 4518 2.6.1): a value with
#              no character other than spaces becomes two spaces; otherwise
#              leading and trailing runs of spaces become one space and
#              inner runs two
#   kinds      character string types compared by their characters, so a
#              PrintableString matches the same UTF8String (RFC 5280 7.1
#              applies the same matching to both)
#
# With every rule off, names match when their DER octets are the same:
# binary comparison, RFC 5280 section 8's minimum. Preparation applies to
# every character string value; other values compare by their octets.
# RFC 4518's other steps (mapping characters other than A to Z,
# normalization to Form KC, prohibited characters) are not done.
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/rules.bend as AR
import ../asn1/encode.bend as AEn
import ../asn1/prim.bend as AP
import ../asn1/string.bend as AS
import ../asn1/build.bend as ABu
import ../oid/oid.bend as O
import ./name.bend as XN

type X509NameRules is Data:
  X509NameRules{fold_case: Bool, spaces: Bool, kinds: Bool}

# RFC 5280 7.1's comparison, as far as it is done here
def X509.name_rules() -> X509NameRules:
  X509NameRules{True{}, True{}, True{}}

# binary comparison
def X509.name_rules_binary() -> X509NameRules:
  X509NameRules{False{}, False{}, False{}}

def X509NameRules.fold_case(r: X509NameRules) -> Bool:
  match r:
    case X509NameRules{f, s, k}:
      f

def X509NameRules.spaces(r: X509NameRules) -> Bool:
  match r:
    case X509NameRules{f, s, k}:
      s

def X509NameRules.kinds(r: X509NameRules) -> Bool:
  match r:
    case X509NameRules{f, s, k}:
      k

# Preparing a string's characters

def x5.fold1.pick(up: Bool, +c: U32) -> U32:
  match up:
    case True{}:
      U32.add(c, 32)
    case False{}:
      c

def x5.fold(cs: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Con{x5.fold1.pick(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), c), x5.fold(t)}

# the runs of characters other than spaces, from the end; open: the first
# run is still being read
type X5Words is Data:
  X5Words{ws: List<&2, List<&2, U32>>, open: Bool}

def x5.words.add(c: U32, w: X5Words) -> X5Words:
  match w:
    case X5Words{Con{x, rest}, True{}}:
      X5Words{Con{Con{c, x}, rest}, True{}}
    case X5Words{ws, o}:
      X5Words{Con{[c], ws}, True{}}

def x5.words.close(w: X5Words) -> X5Words:
  match w:
    case X5Words{ws, o}:
      X5Words{ws, False{}}

def x5.words.step(space: Bool, c: U32, w: X5Words) -> X5Words:
  match space:
    case True{}:
      x5.words.close(w)
    case False{}:
      x5.words.add(c, w)

def x5.words.go(cs: List<&2, U32>) -> X5Words:
  match cs:
    case Nil{}:
      X5Words{Nil{}, False{}}
    case Con{+c, t}:
      x5.words.step(U32.is_eq(c, 32), c, x5.words.go(t))

def x5.words.of(w: X5Words) -> List<&2, List<&2, U32>>:
  match w:
    case X5Words{ws, o}:
      ws

def x5.words(cs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  x5.words.of(x5.words.go(cs))

def x5.inner(ws: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      [32]
    case Con{w, t}:
      match t:
        case Nil{}:
          List.append(&2, U32, w, [32])
        case Con{v, u}:
          List.append(&2, U32, w, Con{32, Con{32, x5.inner(Con{v, u})}})

# RFC 4518 2.6.1
def x5.spaces.of(ws: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      [32, 32]
    case Con{w, t}:
      Con{32, x5.inner(Con{w, t})}

def x5.spaces(cs: List<&2, U32>) -> List<&2, U32>:
  x5.spaces.of(x5.words(cs))

def x5.when(go: Bool, cs: List<&2, U32>, f: List<&2, U32> -> List<&2, U32>) -> List<&2, U32>:
  match go:
    case True{}:
      f(cs)
    case False{}:
      cs

def x5.prep(+r: X509NameRules, cs: List<&2, U32>) -> List<&2, U32>:
  x5.when(X509NameRules.spaces(r), x5.when(X509NameRules.fold_case(r), cs, xs => x5.fold(xs)), xs => x5.spaces(xs))

# A value prepared: a character string's characters, in UTF-8, under its
# own tag or (kinds) as a UTF8String; any other value as it is

def x5.tag.pick(utf8: Bool, t: AT.Asn1Tag) -> AT.Asn1Tag:
  match utf8:
    case True{}:
      AS.Asn1StrKind.tag(AS.Asn1Utf8{})
    case False{}:
      t

def x5.value.str(+r: X509NameRules, +v: AN.Asn1Node, m: Maybe<&2, List<&2, U32>>) -> AN.Asn1Node:
  match m:
    case None{}:
      v
    case Some{cs}:
      AN.Asn1Prim{x5.tag.pick(X509NameRules.kinds(r), AN.Asn1Node.tag(v)), B.Octets.of_list(AS.Asn1.utf8_encode(x5.prep(r, cs)))}

def x5.value.prep(+r: X509NameRules, +v: AN.Asn1Node, s: Result<&2, &2, AE.Asn1Error, AS.Asn1Str>) -> AN.Asn1Node:
  match s:
    case Fail{e}:
      v
    case Done{x}:
      x5.value.str(r, v, AS.Asn1Str.chars(x))

def x5.atv.key(+r: X509NameRules, a: XN.X509Atv) -> AN.Asn1Node:
  match a:
    case XN.X509Atv{t, +v}:
      ABu.Asn1.seq([Result.default(&2, &2, O.OidError, AN.Asn1Node, O.Oid.node(t), AP.Asn1.null()), x5.value.prep(r, v, AS.Asn1.get_string(AR.Asn1Rules.ber(), v))])

def x5.rdn.key(+r: X509NameRules, xs: List<&2, XN.X509Atv>) -> List<&2, AN.Asn1Node>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{x5.atv.key(r, a), x5.rdn.key(r, t)}

def x5.rdns.key(+r: X509NameRules, rs: List<&2, List<&2, XN.X509Atv>>) -> List<&2, AN.Asn1Node>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{ABu.Asn1.set_of(x5.rdn.key(r, x)), x5.rdns.key(r, t)}

def x5.key.pick(prep: Bool, +r: X509NameRules, +n: XN.X509Name) -> B.Octets:
  match prep:
    case False{}:
      XN.X509Name.raw(n)
    case True{}:
      Result.default(&2, &2, AE.Asn1Error, B.Octets, AEn.Asn1.encode(ABu.Asn1.seq(x5.rdns.key(r, XN.X509Name.rdns(n)))), XN.X509Name.raw(n))

# the octets two names are compared by under r: the name's own DER under
# binary comparison, else the DER of the name with every value prepared and
# every RDN's attributes in DER's SET OF order
def X509Name.key(+r: X509NameRules, +n: XN.X509Name) -> B.Octets:
  x5.key.pick(Bool.or(X509NameRules.fold_case(r), Bool.or(X509NameRules.spaces(r), X509NameRules.kinds(r))), r, n)

# whether two names match under r
def X509Name.matches(+r: X509NameRules, a: XN.X509Name, b: XN.X509Name) -> Bool:
  B.Octets.is_eq(X509Name.key(r, a), X509Name.key(r, b))
