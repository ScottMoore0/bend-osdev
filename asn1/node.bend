# bend-osdev-asn1, elements: an ASN.1 value as its tag and either its
# contents octets (a primitive encoding, ITU-T X.690 (02/2021) 3.10) or the
# elements its contents octets hold (a constructed encoding, 3.2). The type
# is open: callers build and match its constructors.
import Base
import ../bytes/bytes.bend as B
import ./tag.bend as T

type Asn1Node is Data:
  Asn1Prim{tag: T.Asn1Tag, content: B.Octets}
  Asn1Cons{tag: T.Asn1Tag, items: List<&2, Asn1Node>}

def Asn1Node.tag(n: Asn1Node) -> T.Asn1Tag:
  match n:
    case Asn1Prim{t, c}:
      t
    case Asn1Cons{t, xs}:
      t

def Asn1Node.is_cons(n: Asn1Node) -> Bool:
  match n:
    case Asn1Prim{t, c}:
      False{}
    case Asn1Cons{t, xs}:
      True{}

# the contents octets of a primitive element (empty for a constructed one)
def Asn1Node.content(n: Asn1Node) -> B.Octets:
  match n:
    case Asn1Prim{t, c}:
      c
    case Asn1Cons{t, xs}:
      B.Octets.empty()

# the elements of a constructed element (none for a primitive one)
def Asn1Node.items(n: Asn1Node) -> List<&2, Asn1Node>:
  match n:
    case Asn1Prim{t, c}:
      Nil{}
    case Asn1Cons{t, xs}:
      xs

# The bytes a decoder must read for elements, at the least: two (an
# identifier octet and a length octet) for each element, and each primitive
# element's contents octets
def a1.span_list(ns: List<&2, Asn1Node>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Con{Asn1Prim{t, c}, rest}:
      Nat.add(2n, Nat.add(B.Octets.len(c), a1.span_list(rest)))
    case Con{Asn1Cons{t, xs}, rest}:
      Nat.add(2n, Nat.add(a1.span_list(xs), a1.span_list(rest)))

def Asn1.span(n: Asn1Node) -> Nat:
  a1.span_list([n])

def Asn1.spans(ns: List<&2, Asn1Node>) -> Nat:
  a1.span_list(ns)
