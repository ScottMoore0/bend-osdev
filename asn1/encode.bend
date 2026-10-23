# bend-osdev-asn1, the encoder: elements as identifier octets, definite
# length octets in the fewest octets, and contents octets (ITU-T X.690
# (02/2021) 8.1.1, 8.1.2, 8.1.3; 10.1), a constructed element's contents
# being its elements' encodings in order. The elements are written as given:
# a SET's order is the caller's (Asn1.set_of in build.bend sorts it).
#
# Some values have no encoding, and Asn1.encode refuses them: a tag
# [UNIVERSAL 0], which X.680 (02/2021) Table 1 reserves for the encoding
# rules (Asn1ReservedTag); and, as this implementation bounds the numbers
# it reads (number.bend), a tag number of more than six base-128 octets
# (Asn1BadTag) and contents of 2^48 octets or more (Asn1TooLong).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./length.bend as L
import ./node.bend as N

def a1.app(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

# an element's header, then its contents octets cs, then rest
def a1.tlv(c: T.Asn1Class, cons: Bool, +n: Nat, +cs: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  a1.app(T.a1.id_bytes(c, cons, n), a1.app(L.a1.len_bytes(List.length(&2, U32, cs)), a1.app(cs, rest)))

# the encodings of elements ns, then tail
def a1.enc_list(ns: List<&2, N.Asn1Node>, tail: List<&2, U32>) -> List<&2, U32>:
  match ns:
    case Nil{}:
      tail
    case Con{N.Asn1Prim{T.Asn1Tag{c, n}, o}, rest}:
      a1.tlv(c, False{}, n, B.Octets.to_list(o), a1.enc_list(rest, tail))
    case Con{N.Asn1Cons{T.Asn1Tag{c, n}, xs}, rest}:
      a1.tlv(c, True{}, n, a1.enc_list(xs, Nil{}), a1.enc_list(rest, tail))

# the identifier octets the encoder writes for a tag, primitive or
# constructed (8.1.2)
def Asn1.identifier(t: T.Asn1Tag, cons: Bool) -> B.Octets:
  match t:
    case T.Asn1Tag{c, +n}:
      B.Octets.of_list(T.a1.id_bytes(c, cons, n))

# Why elements cannot be encoded

def a1.is_univ0(c: T.Asn1Class, n: Nat) -> Bool:
  match c:
    case T.Asn1Universal{}:
      Nat.is_eq(n, 0n)
    case T.Asn1Application{}:
      False{}
    case T.Asn1Context{}:
      False{}
    case T.Asn1Private{}:
      False{}

def a1.node_err.pick(u0: Bool, idok: Bool, ok: Bool) -> Maybe<&2, E.Asn1Error>:
  match u0 idok ok:
    case True{} _ _:
      Some{E.Asn1ReservedTag{}}
    case False{} False{} _:
      Some{E.Asn1BadTag{}}
    case False{} True{} True{}:
      None{}
    case False{} True{} False{}:
      Some{E.Asn1TooLong{}}

def a1.node_err(+c: T.Asn1Class, +n: Nat, +len: Nat) -> Maybe<&2, E.Asn1Error>:
  a1.node_err.pick(a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(len))

def a1.first(a: Maybe<&2, E.Asn1Error>, b: Maybe<&2, E.Asn1Error>) -> Maybe<&2, E.Asn1Error>:
  match a:
    case Some{e}:
      Some{e}
    case None{}:
      b

# the first error of elements ns (None: they can be encoded)
def a1.enc_err(ns: List<&2, N.Asn1Node>) -> Maybe<&2, E.Asn1Error>:
  match ns:
    case Nil{}:
      None{}
    case Con{N.Asn1Prim{T.Asn1Tag{+c, +n}, o}, rest}:
      a1.first(a1.node_err(c, n, B.Octets.len(o)), a1.enc_err(rest))
    case Con{N.Asn1Cons{T.Asn1Tag{+c, +n}, +xs}, rest}:
      a1.first(a1.node_err(c, n, List.length(&2, U32, a1.enc_list(xs, Nil{}))), a1.first(a1.enc_err(xs), a1.enc_err(rest)))

def a1.encode.go(m: Maybe<&2, E.Asn1Error>, +ns: List<&2, N.Asn1Node>) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match m:
    case None{}:
      Done{B.Octets.of_list(a1.enc_list(ns, Nil{}))}
    case Some{e}:
      Fail{e}

# the DER encodings of elements, one after another
def Asn1.encode_all(+ns: List<&2, N.Asn1Node>) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  a1.encode.go(a1.enc_err(ns), ns)

# an element's encoding (DER when its SETs are in order, and its universal
# types in their forms: conform.bend)
def Asn1.encode(+n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  Asn1.encode_all([n])
