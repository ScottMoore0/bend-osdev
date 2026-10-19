# bend-osdev-asn1, the simple universal types (ITU-T X.690 (02/2021)):
# BOOLEAN (8.2: one octet, FALSE 00, TRUE any other; DER: FF, 11.1), NULL
# (8.8: no contents), OCTET STRING (8.7: primitive, or in BER constructed
# from segments, 8.7.3), INTEGER and ENUMERATED (8.3, 8.4: two's
# complement, big-endian, in the fewest octets, 8.3.2).
#
# Each reader takes the tag it expects, so an IMPLICIT-tagged value is read
# with its own tag (Asn1.get_octets_as(t, n) and so on); the plain readers
# use the universal tag.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./number.bend as Nu
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R

# An integer held as a natural number: its sign and magnitude (value =
# -magnitude when negative). Bend's natural numbers are below 2^48 at run
# time, so the readers give one only for contents of six octets or fewer
# (Asn1TooLong otherwise); larger integers (serial numbers, RSA moduli) are
# read as octets (Asn1.get_int_bytes, Asn1.get_uint_bytes).
type Asn1Int is Data:
  Asn1Int{negative: Bool, magnitude: Nat}

def a1.tag_is(a: T.Asn1Tag, b: T.Asn1Tag) -> Bool:
  T.Asn1Tag.is_eq(a, b)

def a1.need(ok: Bool, e: E.Asn1Error) -> Result<&2, &2, E.Asn1Error, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# the contents of a primitive element with tag t
def a1.prim_as.pick(ok: Bool, o: B.Octets) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match ok:
    case True{}:
      Done{o}
    case False{}:
      Fail{E.Asn1Unexpected{}}

def Asn1.prim_as(+t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match n:
    case N.Asn1Prim{u, o}:
      a1.prim_as.pick(a1.tag_is(t, u), o)
    case N.Asn1Cons{u, xs}:
      Fail{E.Asn1Unexpected{}}

# BOOLEAN

def Asn1.bool(b: Bool) -> N.Asn1Node:
  N.Asn1Prim{T.Asn1Tag.boolean(), B.Octets.of_list([Bool.pick(U32, b, 255, 0)])}

def a1.bool.pick(zero: Bool, ff: Bool, der: Bool) -> Result<&2, &2, E.Asn1Error, Bool>:
  match zero ff der:
    case True{} _ _:
      Done{False{}}
    case False{} True{} _:
      Done{True{}}
    case False{} False{} True{}:
      Fail{E.Asn1BadValue{}}
    case False{} False{} False{}:
      Done{True{}}

def a1.bool.of(+v: U32, der: Bool) -> Result<&2, &2, E.Asn1Error, Bool>:
  a1.bool.pick(U32.is_eq(v, 0), U32.is_eq(v, 255), der)

def a1.bool.read(xs: List<&2, U32>, der: Bool) -> Result<&2, &2, E.Asn1Error, Bool>:
  match xs:
    case Con{v, Nil{}}:
      a1.bool.of(v, der)
    case _:
      Fail{E.Asn1BadValue{}}

def a1.bool.from(r: Result<&2, &2, E.Asn1Error, B.Octets>, der: Bool) -> Result<&2, &2, E.Asn1Error, Bool>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      a1.bool.read(B.Octets.to_list(o), der)

# a BOOLEAN element's value (under the values rule, TRUE must be FF)
def Asn1.get_bool_as(+r: R.Asn1Rules, +t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Bool>:
  a1.bool.from(Asn1.prim_as(t, n), R.Asn1Rules.values(r))

def Asn1.get_bool(+r: R.Asn1Rules, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Bool>:
  Asn1.get_bool_as(r, T.Asn1Tag.boolean(), n)

# NULL

def Asn1.null() -> N.Asn1Node:
  N.Asn1Prim{T.Asn1Tag.null(), B.Octets.empty()}

def a1.null.from(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> Result<&2, &2, E.Asn1Error, Unit>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      a1.need(Nat.is_eq(B.Octets.len(o), 0n), E.Asn1BadValue{})

def Asn1.get_null(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Unit>:
  a1.null.from(Asn1.prim_as(T.Asn1Tag.null(), n))

# whether an element is NULL
def Asn1.is_null(n: N.Asn1Node) -> Bool:
  Result.is_done(&2, &2, E.Asn1Error, Unit, Asn1.get_null(n))

# OCTET STRING

def Asn1.octets(o: B.Octets) -> N.Asn1Node:
  N.Asn1Prim{T.Asn1Tag.octet_string(), o}

def Asn1.octets_as(t: T.Asn1Tag, o: B.Octets) -> N.Asn1Node:
  N.Asn1Prim{t, o}

def a1.segs.cons(o: B.Octets, r: Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>) -> Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{os}:
      Done{Con{o, os}}

def a1.segs.app(a: Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>, b: Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>) -> Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>:
  match a b:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{y}:
      Done{List.append(&2, B.Octets, x, y)}

def a1.segs.pick(ok: Bool, o: B.Octets, r: Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>) -> Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>:
  match ok:
    case True{}:
      a1.segs.cons(o, r)
    case False{}:
      Fail{E.Asn1Unexpected{}}

def a1.segs.pick2(ok: Bool, a: Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>, r: Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>) -> Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>:
  match ok:
    case True{}:
      a1.segs.app(a, r)
    case False{}:
      Fail{E.Asn1Unexpected{}}

# the segments of a constructed string encoding (X.690 8.7.3, 8.23.6): each
# element of universal tag u, primitive or itself constructed
def a1.segs(ns: List<&2, N.Asn1Node>, +u: T.Asn1Tag) -> Result<&2, &2, E.Asn1Error, List<&2, B.Octets>>:
  match ns:
    case Nil{}:
      Done{Nil{}}
    case Con{N.Asn1Prim{t, o}, rest}:
      a1.segs.pick(a1.tag_is(u, t), o, a1.segs(rest, u))
    case Con{N.Asn1Cons{t, xs}, rest}:
      a1.segs.pick2(a1.tag_is(u, t), a1.segs(xs, u), a1.segs(rest, u))

def a1.str.cons(ok: Bool, +prim: Bool, ns: List<&2, N.Asn1Node>, +u: T.Asn1Tag) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match ok prim:
    case True{} False{}:
      Result.map(&2, &2, E.Asn1Error, List<&2, B.Octets>, B.Octets, os => B.Octets.concat(os), a1.segs(ns, u))
    case True{} True{}:
      Fail{E.Asn1BadForm{}}
    case False{} _:
      Fail{E.Asn1Unexpected{}}

# the value of a string-like element with tag t: its contents, or (in BER)
# its segments' contents joined (segments carry the universal tag u);
# prim: only the primitive form (DER, 10.2)
def a1.string_value(+prim: Bool, +t: T.Asn1Tag, +u: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match n:
    case N.Asn1Prim{v, o}:
      a1.prim_as.pick(a1.tag_is(t, v), o)
    case N.Asn1Cons{v, xs}:
      a1.str.cons(a1.tag_is(t, v), prim, xs, u)

# an OCTET STRING element's octets (constructed segments joined under BER)
def Asn1.get_octets_as(+r: R.Asn1Rules, +t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  a1.string_value(R.Asn1Rules.prim_strings(r), t, T.Asn1Tag.octet_string(), n)

def Asn1.get_octets(+r: R.Asn1Rules, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  Asn1.get_octets_as(r, T.Asn1Tag.octet_string(), n)

# INTEGER

def a1.int.pad(hi: Bool, +xs: List<&2, U32>) -> List<&2, U32>:
  match hi:
    case True{}:
      Con{0, xs}
    case False{}:
      xs

def a1.int.first(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      x

# a non-negative integer's contents: big-endian, a leading 00 when its top
# bit would read as a sign
def a1.int.nat(+n: Nat) -> List<&2, U32>:
  +xs = Nu.a1.be(n)
  a1.int.pad(U32.is_le(128, a1.int.first(xs)), xs)

def a1.int.comp(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.sub(255, x), a1.int.comp(t)}

def a1.int.npad(lo: Bool, +xs: List<&2, U32>) -> List<&2, U32>:
  match lo:
    case True{}:
      Con{255, xs}
    case False{}:
      xs

# a negative integer -m's contents: the complement of m - 1, with a leading
# FF when its top bit would read as positive
def a1.int.neg(+m: Nat) -> List<&2, U32>:
  +xs = a1.int.comp(Nu.a1.be(Nat.sub(m, 1n)))
  a1.int.npad(U32.is_lt(a1.int.first(xs), 128), xs)

def a1.int.content(i: Asn1Int) -> List<&2, U32>:
  match i:
    case Asn1Int{True{}, 0n}:
      [0]
    case Asn1Int{True{}, +m}:
      a1.int.neg(m)
    case Asn1Int{False{}, +m}:
      a1.int.nat(m)

def Asn1.int_as(t: T.Asn1Tag, i: Asn1Int) -> N.Asn1Node:
  N.Asn1Prim{t, B.Octets.of_list(a1.int.content(i))}

def Asn1.int(i: Asn1Int) -> N.Asn1Node:
  Asn1.int_as(T.Asn1Tag.integer(), i)

def Asn1.int_nat(+n: Nat) -> N.Asn1Node:
  N.Asn1Prim{T.Asn1Tag.integer(), B.Octets.of_list(a1.int.nat(n))}

def a1.int.min2(+a: U32, +b: U32) -> Bool:
  Bool.not(Bool.or(Bool.and(U32.is_eq(a, 0), U32.is_lt(b, 128)), Bool.and(U32.is_eq(a, 255), U32.is_le(128, b))))

# INTEGER contents are one octet or more, the first nine bits neither all
# zero nor all one (8.3.1, 8.3.2)
def Asn1.int_content_ok(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{a, Nil{}}:
      True{}
    case Con{a, Con{b, t}}:
      a1.int.min2(a, b)

def a1.int.value(neg: Bool, +xs: List<&2, U32>) -> Asn1Int:
  match neg:
    case True{}:
      Asn1Int{True{}, Nat.add(Nu.a1.fold256(a1.int.comp(xs), 0n), 1n)}
    case False{}:
      Asn1Int{False{}, Nu.a1.fold256(xs, 0n)}

def a1.int.of.small(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, E.Asn1Error, Asn1Int>:
  match ok:
    case True{}:
      Done{a1.int.value(U32.is_le(128, a1.int.first(xs)), xs)}
    case False{}:
      Fail{E.Asn1TooLong{}}

def a1.int.of.pick(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, E.Asn1Error, Asn1Int>:
  match ok:
    case True{}:
      a1.int.of.small(Nat.is_le(List.length(&2, U32, xs), Nu.a1.max_octets()), xs)
    case False{}:
      Fail{E.Asn1BadInteger{}}

# the integer of INTEGER contents (Asn1BadInteger if empty or not in the
# fewest octets; Asn1TooLong past six octets)
def Asn1.int_of_content(o: B.Octets) -> Result<&2, &2, E.Asn1Error, Asn1Int>:
  +xs = B.Octets.to_list(o)
  a1.int.of.pick(Asn1.int_content_ok(xs), xs)

def a1.int.from(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> Result<&2, &2, E.Asn1Error, Asn1Int>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Asn1.int_of_content(o)

def Asn1.get_int_as(+t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Int>:
  a1.int.from(Asn1.prim_as(t, n))

def Asn1.get_int(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Int>:
  Asn1.get_int_as(T.Asn1Tag.integer(), n)

def a1.int.nat_of(i: Asn1Int) -> Result<&2, &2, E.Asn1Error, Nat>:
  match i:
    case Asn1Int{True{}, m}:
      Fail{E.Asn1Negative{}}
    case Asn1Int{False{}, m}:
      Done{m}

def a1.int.nat_from(r: Result<&2, &2, E.Asn1Error, Asn1Int>) -> Result<&2, &2, E.Asn1Error, Nat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{i}:
      a1.int.nat_of(i)

# a non-negative INTEGER element's value (Asn1Negative for a negative one)
def Asn1.get_nat_as(+t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Nat>:
  a1.int.nat_from(Asn1.get_int_as(t, n))

def Asn1.get_nat(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Nat>:
  Asn1.get_nat_as(T.Asn1Tag.integer(), n)

def a1.int.bytes_pick(ok: Bool, o: B.Octets) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match ok:
    case True{}:
      Done{o}
    case False{}:
      Fail{E.Asn1BadInteger{}}

def a1.int.bytes_from(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+o}:
      a1.int.bytes_pick(Asn1.int_content_ok(B.Octets.to_list(o)), o)

# an INTEGER element's contents, checked (a certificate's serial number is
# kept as these octets: RFC 5280 4.1.2.2 allows 20 of them)
def Asn1.get_int_bytes_as(+t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  a1.int.bytes_from(Asn1.prim_as(t, n))

def Asn1.get_int_bytes(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  Asn1.get_int_bytes_as(T.Asn1Tag.integer(), n)

# ENUMERATED (8.4: as INTEGER)
def Asn1.get_enum(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Int>:
  Asn1.get_int_as(T.Asn1Tag.enumerated(), n)

def Asn1.enum(i: Asn1Int) -> N.Asn1Node:
  Asn1.int_as(T.Asn1Tag.enumerated(), i)

# Large integers as octets

def a1.int.zhead(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      U32.is_eq(x, 0)

# without leading zero octets
def a1.int.strip.go(xs: List<&2, U32>, z: Bool) -> List<&2, U32>:
  match xs z:
    case Nil{} _:
      Nil{}
    case Con{x, t} False{}:
      Con{x, t}
    case Con{x, +t} True{}:
      a1.int.strip.go(t, a1.int.zhead(t))

def a1.int.strip(+xs: List<&2, U32>) -> List<&2, U32>:
  a1.int.strip.go(xs, a1.int.zhead(xs))

def a1.int.unsigned(+xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [0]
    case Con{+x, +t}:
      a1.int.pad(U32.is_le(128, x), Con{x, t})

# the INTEGER whose value is the unsigned big-endian number o (a leading
# 00 added when its top bit is set; leading zeros dropped)
def Asn1.uint(o: B.Octets) -> N.Asn1Node:
  N.Asn1Prim{T.Asn1Tag.integer(), B.Octets.of_list(a1.int.unsigned(a1.int.strip(B.Octets.to_list(o))))}

def a1.int.mag.go(neg: Bool, o: B.Octets) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match neg:
    case True{}:
      Fail{E.Asn1Negative{}}
    case False{}:
      Done{B.Octets.of_list(a1.int.strip(B.Octets.to_list(o)))}

def a1.int.mag(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+o}:
      a1.int.mag.go(U32.is_le(128, a1.int.first(B.Octets.to_list(o))), o)

# a non-negative INTEGER element's value as unsigned big-endian octets, no
# leading zeros (empty for 0); Asn1Negative for a negative one
def Asn1.get_uint_bytes_as(+t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  a1.int.mag(Asn1.get_int_bytes_as(t, n))

def Asn1.get_uint_bytes(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  Asn1.get_uint_bytes_as(T.Asn1Tag.integer(), n)
