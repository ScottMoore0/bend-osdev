# bend-osdev-asn1, what rules accept of a value: each universal element in
# the form the rules require (rules.bend), and each SET's elements in the
# rules' order: for the SET OF order, the encodings ascending as octet
# strings, the shorter padded at its end with zero octets (ITU-T X.690
# (02/2021) 11.6, comparing as 6.3 does); for the SET order, the tags
# ascending in X.680 (02/2021) 8.6's canonical order (X.690 10.3).
#
# Asn1.conforms(r, n) is what the decoder checks of each element it builds,
# so a value the encoder writes is decoded back under rules r exactly when
# it conforms to r (LAWS.bend: decode_encode).
import Base
import ../bytes/bytes.bend as B
import ./tag.bend as T
import ./rules.bend as R
import ./node.bend as N
import ./encode.bend as En

def a1.zeros_only(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{a, s}:
      Bool.and(U32.is_eq(a, 0), a1.zeros_only(s))

def a1.lex(c: Cmp, rest: Bool) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      rest
    case GT{}:
      False{}

# xs <= ys as octet strings, the shorter padded with zero octets (11.6)
def a1.le_pad(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} _:
      True{}
    case Con{a, s} Nil{}:
      a1.zeros_only(Con{a, s})
    case Con{a, s} Con{b, t}:
      a1.lex(U32.cmp(a, b), a1.le_pad(s, t))

# whether a may come before b in a SET under order o
def a1.ordered(o: R.Asn1SetOrder, a: N.Asn1Node, b: N.Asn1Node) -> Bool:
  match o:
    case R.Asn1SetAny{}:
      True{}
    case R.Asn1SetOfOrder{}:
      a1.le_pad(En.a1.enc_list([a], Nil{}), En.a1.enc_list([b], Nil{}))
    case R.Asn1SetTagOrder{}:
      T.Asn1Tag.is_lt(N.Asn1Node.tag(a), N.Asn1Node.tag(b))

def a1.sorted.go(xs: List<&2, N.Asn1Node>, +o: R.Asn1SetOrder, prev: N.Asn1Node) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+b, t}:
      Bool.and(a1.ordered(o, prev, b), a1.sorted.go(t, o, b))

# elements in order o, each against the next
def a1.sorted(+o: R.Asn1SetOrder, xs: List<&2, N.Asn1Node>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{a, t}:
      a1.sorted.go(t, o, a)

def a1.set_ok.pick(is_set: Bool, +r: R.Asn1Rules, xs: List<&2, N.Asn1Node>) -> Bool:
  match is_set:
    case True{}:
      a1.sorted(R.Asn1Rules.set_order(r), xs)
    case False{}:
      True{}

# a constructed element's elements in the order its rules require (only
# [UNIVERSAL 17], SET and SET OF, has one)
def a1.set_ok(+r: R.Asn1Rules, t: T.Asn1Tag, xs: List<&2, N.Asn1Node>) -> Bool:
  match t:
    case T.Asn1Tag{T.Asn1Universal{}, +n}:
      a1.set_ok.pick(Nat.is_eq(n, 17n), r, xs)
    case T.Asn1Tag{c, n}:
      True{}

# whether rules r accept every element of ns (form and SET order)
def a1.conf_list(ns: List<&2, N.Asn1Node>, +r: R.Asn1Rules) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{N.Asn1Prim{+t, o}, rest}:
      Bool.and(R.a1.form_ok(r, t, False{}), a1.conf_list(rest, r))
    case Con{N.Asn1Cons{+t, +xs}, rest}:
      Bool.and(R.a1.form_ok(r, t, True{}), Bool.and(a1.set_ok(r, t, xs), Bool.and(a1.conf_list(xs, r), a1.conf_list(rest, r))))

def Asn1.conforms(+r: R.Asn1Rules, n: N.Asn1Node) -> Bool:
  a1.conf_list([n], r)
