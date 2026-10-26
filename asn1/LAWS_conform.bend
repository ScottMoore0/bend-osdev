# The laws of the schema matcher's answers, for every rules, schema and
# input: every match conforms to its schema.
#
# A match m conforms to a schema s when it has s's shape, all the way down:
#
#   Asn1SAny{}                 an element's match (Asn1MElem)
#   Asn1SElem{tag}             an element's match, of that tag
#   Asn1SSeq{tag, fields}      a sequence's match of a constructed element of
#                              that tag, with one match per field, in order,
#                              each conforming to its field
#   Asn1SOf{tag, item, set}    a sequence's match of a constructed element of
#                              that tag, each of its matches conforming to
#                              item
#   Asn1SChoice{alts}          a choice's match whose match conforms to one
#                              of the alternatives
#   Asn1SExplicit{num, inner}  an explicit match of a constructed element
#                              tagged [num], whose match conforms to inner
#   Asn1SOpt{inner}            absent (Asn1MAbsent), or conforming to inner
#   Asn1SDefault{inner, value} absent (Asn1MDefault), or conforming to inner
#
# What this does not state: that a choice's index is that of the first
# alternative whose tags admit the element, that a DEFAULT field's
# encoded value differs from its default under the values rule, and that
# a SET OF's elements are in DER's order (the matcher checks all three;
# README.md, "Laws").
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./asn1.bend as A
import ./schema.bend as Sc

# the element x has tag t, and is constructed if cons
def asn1law.tag_is(+t: T.Asn1Tag, cons: Bool, +x: A.Asn1Tlv) -> Bool:
  Bool.and(T.Asn1Tag.is_eq(t, N.Asn1Node.tag(A.Asn1Tlv.node(x))), Bool.or(Bool.not(cons), N.Asn1Node.is_cons(A.Asn1Tlv.node(x))))

def asn1law.is_absent(m: Sc.Asn1Match) -> Bool:
  match m:
    case Sc.Asn1MAbsent{}:
      True{}
    case _:
      False{}

def asn1law.is_default(m: Sc.Asn1Match) -> Bool:
  match m:
    case Sc.Asn1MDefault{v}:
      True{}
    case _:
      False{}

# What to check (asn1law.conf): with Asn1LawOne{}, the first match of ms
# against the first schema of ss; with Asn1LawFields{}, the matches against
# the schemas, one each, in order; with Asn1LawAll{}, every match against
# the first schema; with Asn1LawAny{}, the first match against one of the
# schemas. The fuel bounds the nesting (it is spent going into a match, not
# along a list), and conformance is true at some fuel: none means no.
type Asn1LawJob is Data:
  Asn1LawOne{}
  Asn1LawFields{}
  Asn1LawAll{}
  Asn1LawAny{}

def asn1law.conf(fuel: Nat, k: Asn1LawJob, +ss: List<&2, Sc.Asn1Schema>, +ms: List<&2, Sc.Asn1Match>) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+ +n:
      match k:
        case Asn1LawOne{}:
          match ss:
            case Nil{}:
              False{}
            case Con{s, st}:
              match s:
                case Sc.Asn1SAny{}:
                  match ms:
                    case Nil{}:
                      False{}
                    case Con{+m, mt}:
                      match m:
                        case Sc.Asn1MElem{e}:
                          True{}
                        case _:
                          False{}
                case Sc.Asn1SElem{t}:
                  match ms:
                    case Nil{}:
                      False{}
                    case Con{+m, mt}:
                      match m:
                        case Sc.Asn1MElem{e}:
                          asn1law.tag_is(t, False{}, e)
                        case _:
                          False{}
                case Sc.Asn1SSeq{t, fs}:
                  match ms:
                    case Nil{}:
                      False{}
                    case Con{+m, mt}:
                      match m:
                        case Sc.Asn1MSeq{e, xs}:
                          Bool.and(asn1law.tag_is(t, True{}, e), asn1law.conf(n, Asn1LawFields{}, fs, xs))
                        case _:
                          False{}
                case Sc.Asn1SOf{t, item, set}:
                  match ms:
                    case Nil{}:
                      False{}
                    case Con{+m, mt}:
                      match m:
                        case Sc.Asn1MSeq{e, xs}:
                          Bool.and(asn1law.tag_is(t, True{}, e), asn1law.conf(n, Asn1LawAll{}, [item], xs))
                        case _:
                          False{}
                case Sc.Asn1SChoice{alts}:
                  match ms:
                    case Nil{}:
                      False{}
                    case Con{+m, mt}:
                      match m:
                        case Sc.Asn1MChoice{i, x}:
                          asn1law.conf(n, Asn1LawAny{}, alts, [x])
                        case _:
                          False{}
                case Sc.Asn1SExplicit{num, inner}:
                  match ms:
                    case Nil{}:
                      False{}
                    case Con{+m, mt}:
                      match m:
                        case Sc.Asn1MExplicit{e, x}:
                          Bool.and(asn1law.tag_is(T.Asn1Tag.context(num), True{}, e), asn1law.conf(n, Asn1LawOne{}, [inner], [x]))
                        case _:
                          False{}
                case Sc.Asn1SOpt{inner}:
                  match ms:
                    case Nil{}:
                      False{}
                    case Con{+m, mt}:
                      Bool.or(asn1law.is_absent(m), asn1law.conf(n, Asn1LawOne{}, [inner], [m]))
                case Sc.Asn1SDefault{inner, v}:
                  match ms:
                    case Nil{}:
                      False{}
                    case Con{+m, mt}:
                      Bool.or(asn1law.is_default(m), asn1law.conf(n, Asn1LawOne{}, [inner], [m]))
        case Asn1LawFields{}:
          match ss ms:
            case Nil{} Nil{}:
              True{}
            case Con{f, ft} Con{x, xt}:
              Bool.and(asn1law.conf(n, Asn1LawOne{}, [f], [x]), asn1law.conf(1n+n, Asn1LawFields{}, ft, xt))
            case _ _:
              False{}
        case Asn1LawAll{}:
          match ms:
            case Nil{}:
              True{}
            case Con{x, xt}:
              Bool.and(asn1law.conf(n, Asn1LawOne{}, ss, [x]), asn1law.conf(1n+n, Asn1LawAll{}, ss, xt))
        case Asn1LawAny{}:
          match ss:
            case Nil{}:
              False{}
            case Con{a, rest}:
              Bool.or(asn1law.conf(n, Asn1LawOne{}, [a], ms), asn1law.conf(1n+n, Asn1LawAny{}, rest, ms))

law match_tlv_conforms:
  for +r: R.Asn1Rules
  for +s: Sc.Asn1Schema
  for +x: A.Asn1Tlv
  for +m: Sc.Asn1Match
  for +e: {Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  exs n: Nat
  {asn1law.conf(n, Asn1LawOne{}, [s], [m]) == True{} : Bool}

law match_conforms:
  for +r: R.Asn1Rules
  for +s: Sc.Asn1Schema
  for +b: B.Octets
  for +m: Sc.Asn1Match
  for +e: {Sc.Asn1.match(r, s, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  exs n: Nat
  {asn1law.conf(n, Asn1LawOne{}, [s], [m]) == True{} : Bool}

# a vector: X.690 8.9.3's SEQUENCE {name IA5String, ok BOOLEAN}
law vec_conforms:
  {Result.map(&2, &2, E.Asn1Error, Sc.Asn1Match, Bool, m => asn1law.conf(8n, Asn1LawOne{}, [Sc.Asn1S.seq([Sc.Asn1S.elem(T.Asn1Tag.ia5_string()), Sc.Asn1S.elem(T.Asn1Tag.boolean())])], [m]), Sc.Asn1.match(R.Asn1Rules.der(), Sc.Asn1S.seq([Sc.Asn1S.elem(T.Asn1Tag.ia5_string()), Sc.Asn1S.elem(T.Asn1Tag.boolean())]), B.Octets.of_list([48, 10, 22, 5, 83, 109, 105, 116, 104, 1, 1, 255]))) == Done{True{}} : Result<&2, &2, E.Asn1Error, Bool>}
