# bend-osdev-asn1, constructed values and tagging: SEQUENCE and SEQUENCE OF
# (ITU-T X.690 (02/2021) 8.9, 8.10), SET (8.11; DER: in tag order, 10.3) and
# SET OF (8.12; DER: encodings ascending, 11.6), and prefixed values
# (8.14): EXPLICIT tagging wraps the element in a constructed one with the
# new tag (8.14.3), IMPLICIT tagging replaces its tag (8.14.4).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./encode.bend as En
import ./conform.bend as C
import ./prim.bend as P

def Asn1.seq(xs: List<&2, N.Asn1Node>) -> N.Asn1Node:
  N.Asn1Cons{T.Asn1Tag.sequence(), xs}

def Asn1.set(xs: List<&2, N.Asn1Node>) -> N.Asn1Node:
  N.Asn1Cons{T.Asn1Tag.set(), xs}

def a1.set_le(a: N.Asn1Node, b: N.Asn1Node) -> Bool:
  C.a1.le_pad(En.a1.enc_list([a], Nil{}), En.a1.enc_list([b], Nil{}))

# a SET OF its elements in DER's order (their encodings ascending, 11.6)
def Asn1.set_of(xs: List<&2, N.Asn1Node>) -> N.Asn1Node:
  N.Asn1Cons{T.Asn1Tag.set(), List.sort(~N.Asn1Node, ~(a => b => a1.set_le(a, b)), xs)}

def a1.tag_lt(a: N.Asn1Node, b: N.Asn1Node) -> Bool:
  Bool.not(T.Asn1Tag.is_lt(N.Asn1Node.tag(b), N.Asn1Node.tag(a)))

# a SET its elements in DER's order (their tags ascending, 10.3)
def Asn1.set_sorted(xs: List<&2, N.Asn1Node>) -> N.Asn1Node:
  N.Asn1Cons{T.Asn1Tag.set(), List.sort(~N.Asn1Node, ~(a => b => a1.tag_lt(a, b)), xs)}

# [n] EXPLICIT x: a context-specific constructed element holding x
def Asn1.explicit(n: Nat, x: N.Asn1Node) -> N.Asn1Node:
  N.Asn1Cons{T.Asn1Tag.context(n), [x]}

# x with its tag replaced (IMPLICIT tagging)
def Asn1.implicit(t: T.Asn1Tag, x: N.Asn1Node) -> N.Asn1Node:
  match x:
    case N.Asn1Prim{u, o}:
      N.Asn1Prim{t, o}
    case N.Asn1Cons{u, xs}:
      N.Asn1Cons{t, xs}

def a1.cons_as.pick(ok: Bool, xs: List<&2, N.Asn1Node>) -> Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>:
  match ok:
    case True{}:
      Done{xs}
    case False{}:
      Fail{E.Asn1Unexpected{}}

# the elements of a constructed element with tag t
def Asn1.cons_as(+t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>:
  match n:
    case N.Asn1Cons{u, xs}:
      a1.cons_as.pick(T.Asn1Tag.is_eq(t, u), xs)
    case N.Asn1Prim{u, o}:
      Fail{E.Asn1Unexpected{}}

def Asn1.get_seq(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>:
  Asn1.cons_as(T.Asn1Tag.sequence(), n)

def Asn1.get_set(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>:
  Asn1.cons_as(T.Asn1Tag.set(), n)

def a1.one_of(r: Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{[x]}:
      Done{x}
    case Done{xs}:
      Fail{E.Asn1Unexpected{}}

# the element inside [n] EXPLICIT
def Asn1.get_explicit(+n: Nat, x: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  a1.one_of(Asn1.cons_as(T.Asn1Tag.context(n), x))

# whether an element has tag t
def Asn1.has_tag(t: T.Asn1Tag, x: N.Asn1Node) -> Bool:
  T.Asn1Tag.is_eq(t, N.Asn1Node.tag(x))

def a1.untag.pick(ok: Bool, +u: T.Asn1Tag, x: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match ok:
    case True{}:
      Done{Asn1.implicit(u, x)}
    case False{}:
      Fail{E.Asn1Unexpected{}}

# an IMPLICIT-tagged element (tag t) with the tag u of its type restored
def Asn1.untag(+t: T.Asn1Tag, +u: T.Asn1Tag, +x: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  a1.untag.pick(T.Asn1Tag.is_eq(t, N.Asn1Node.tag(x)), u, x)
