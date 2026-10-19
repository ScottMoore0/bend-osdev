# bend-osdev-asn1, OBJECT IDENTIFIER contents (ITU-T X.690 (02/2021) 8.19):
# subidentifiers in base-128 octets, bit 8 set on all but the last octet of
# each, each in the fewest octets (its leading octet not 80 hex, 8.19.2);
# the first subidentifier is 40 * X + Y for the first two arcs X and Y
# (8.19.4), the others the remaining arcs in order (8.19.5). An object
# identifier has at least two arcs, the first 0, 1 or 2, and the second
# below 40 when the first is 0 or 1 (8.19.4's note: 0 and 1 have at most 39
# arcs beneath them).
#
# Arcs are natural numbers of any size. The `oid` package builds the
# registry, the dotted text form and the DER form on these.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./number.bend as Nu
import ./tag.bend as T
import ./node.bend as N

def a1.oid.second_ok(+x: Nat, +y: Nat) -> Bool:
  Bool.or(Nat.is_eq(x, 2n), Nat.is_lt(y, 40n))

def a1.oid.valid2(+x: Nat, +y: Nat) -> Bool:
  Bool.and(Nat.is_le(x, 2n), a1.oid.second_ok(x, y))

# every subidentifier has at most six base-128 octets (number.bend's bound)
def a1.oid.small(ss: List<&2, Nat>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      Bool.and(Nat.is_le(List.length(&2, U32, Nu.a1.b128(s)), Nu.a1.max_octets()), a1.oid.small(t))

def a1.oid.valid(arcs: List<&2, Nat>) -> Bool:
  match arcs:
    case Con{+x, Con{+y, rest}}:
      a1.oid.valid2(x, y)
    case _:
      False{}

# the subidentifiers of arcs (the first two folded into one)
def a1.oid.to_subids(arcs: List<&2, Nat>) -> List<&2, Nat>:
  match arcs:
    case Con{x, Con{y, rest}}:
      Con{Nat.add(Nat.mul(x, 40n), y), rest}
    case _:
      Nil{}

# whether arcs name an object identifier (two arcs or more, the first two
# within X.690 8.19.4's bounds) that this implementation can hold (each
# subidentifier below 2^42)
def Asn1.oid_valid(+arcs: List<&2, Nat>) -> Bool:
  Bool.and(a1.oid.valid(arcs), a1.oid.small(a1.oid.to_subids(arcs)))

# the subidentifiers' octets
def a1.oid.subids(ss: List<&2, Nat>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      List.append(&2, U32, Nu.a1.b128(s), a1.oid.subids(rest))

def a1.oid.content.pick(ok: Bool, +arcs: List<&2, Nat>) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  match ok:
    case True{}:
      Done{B.Octets.of_list(a1.oid.subids(a1.oid.to_subids(arcs)))}
    case False{}:
      Fail{E.Asn1BadOid{}}

# the contents octets of an object identifier (Asn1BadOid for arcs that
# do not name one)
def Asn1.oid_content(+arcs: List<&2, Nat>) -> Result<&2, &2, E.Asn1Error, B.Octets>:
  a1.oid.content.pick(Asn1.oid_valid(arcs), arcs)

# Reading

def a1.oid.cons(s: Nat, r: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match r:
    case None{}:
      None{}
    case Some{ss}:
      Some{Con{s, ss}}

def a1.oid.one(ok: Bool, +s: Nat, rest: List<&2, U32>, more: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match ok rest:
    case False{} _:
      None{}
    case True{} Nil{}:
      Some{[s]}
    case True{} Con{y, t}:
      a1.oid.cons(s, more)

# the subidentifiers, from the first read on (each must be minimal); fuel
# bounds them, as each takes an octet or more
def a1.oid.read(fuel: Nat, m: Maybe<&2, Nu.A1Num>) -> Maybe<&2, List<&2, Nat>>:
  match fuel m:
    case _ None{}:
      None{}
    case 0n Some{x}:
      None{}
    case 1n+f Some{Nu.A1Num{+s, u, +rest}}:
      a1.oid.one(Nu.a1.leq(Nu.a1.b128(s), u), s, rest, a1.oid.read(f, Nu.a1.r128(rest, True{}, Nu.a1.max_octets(), 0n)))

# the first subidentifier as the first two arcs (8.19.4)
def a1.oid.split2(lt40: Bool, lt80: Bool, +s: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match lt40 lt80:
    case True{} _:
      Con{0n, Con{s, rest}}
    case False{} True{}:
      Con{1n, Con{Nat.sub(s, 40n), rest}}
    case False{} False{}:
      Con{2n, Con{Nat.sub(s, 80n), rest}}

def a1.oid.arcs(m: Maybe<&2, List<&2, Nat>>) -> Result<&2, &2, E.Asn1Error, List<&2, Nat>>:
  match m:
    case Some{Con{+s, rest}}:
      Done{a1.oid.split2(Nat.is_lt(s, 40n), Nat.is_lt(s, 80n), s, rest)}
    case _:
      Fail{E.Asn1BadOid{}}

# the arcs of an object identifier's contents octets (Asn1BadOid for none,
# a truncated subidentifier, or one not in the fewest octets)
def Asn1.oid_of_content(o: B.Octets) -> Result<&2, &2, E.Asn1Error, List<&2, Nat>>:
  +xs = B.Octets.to_list(o)
  a1.oid.arcs(a1.oid.read(List.length(&2, U32, xs), Nu.a1.r128(xs, True{}, Nu.a1.max_octets(), 0n)))

# Elements

# the OBJECT IDENTIFIER element of arcs
def Asn1.oid(+arcs: List<&2, Nat>) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  Result.map(&2, &2, E.Asn1Error, B.Octets, N.Asn1Node, o => N.Asn1Prim{T.Asn1Tag.oid(), o}, Asn1.oid_content(arcs))

# the arcs of an OBJECT IDENTIFIER element
def Asn1.get_oid(n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, List<&2, Nat>>:
  match n:
    case N.Asn1Prim{T.Asn1Tag{T.Asn1Universal{}, 6n}, o}:
      Asn1.oid_of_content(o)
    case _:
      Fail{E.Asn1Unexpected{}}
