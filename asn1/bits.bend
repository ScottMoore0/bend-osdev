# bend-osdev-asn1, BIT STRING (ITU-T X.690 (02/2021) 8.6): an initial
# octet giving the unused bits of the final octet (0 to 7; 0 when there are
# no subsequent octets, 8.6.2.2, 8.6.2.3), then the bits from bit 8 of the
# first subsequent octet on (8.6.2.1). In BER the value may be constructed
# from segments (8.6.3, 8.6.4), every segment but the last a whole number of
# octets. DER requires the unused bits be zero (11.2.1).
#
# A bit string is the octets holding its bits and the count of unused bits
# at the end of the last; bit i is bit 8 - (i mod 8) of octet i / 8.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./prim.bend as P

type Asn1Bits is Data:
  Asn1Bits{unused: Nat, octets: B.Octets}

def Asn1Bits.octets(b: Asn1Bits) -> B.Octets:
  match b:
    case Asn1Bits{u, o}:
      o

def Asn1Bits.unused(b: Asn1Bits) -> Nat:
  match b:
    case Asn1Bits{u, o}:
      u

# the number of bits
def Asn1Bits.len(b: Asn1Bits) -> Nat:
  match b:
    case Asn1Bits{u, o}:
      Nat.sub(Nat.mul(B.Octets.len(o), 8n), u)

# a whole number of octets as a bit string
def Asn1Bits.of_octets(o: B.Octets) -> Asn1Bits:
  Asn1Bits{0n, o}

def a1.bits.last(xs: List<&2, U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      a1.bits.last(t, x)

# the low u bits of the last octet are zero
def a1.bits.clear(+u: Nat, +o: B.Octets) -> Bool:
  U32.is_eq(U32.and(a1.bits.last(B.Octets.to_list(o), 0), U32.sub(U32.shln(1, u), 1)), 0)

# a bit string is well formed: at most 7 unused bits, none without octets
def Asn1Bits.ok(b: Asn1Bits) -> Bool:
  match b:
    case Asn1Bits{+u, +o}:
      Bool.and(Nat.is_le(u, 7n), Bool.or(Nat.is_lt(0n, B.Octets.len(o)), Nat.is_eq(u, 0n)))

def a1.bits.bit(inside: Bool, +o: B.Octets, +i: Nat) -> Bool:
  match inside:
    case True{}:
      U32.is_eq(U32.and(U32.shrn(Maybe.default(&2, U32, B.Octets.at(o, Nat.div(i, 8n)), 0), Nat.sub(7n, Nat.mod(i, 8n))), 1), 1)
    case False{}:
      False{}

# bit i (0 is the first), False past the end
def Asn1Bits.bit(b: Asn1Bits, +i: Nat) -> Bool:
  match b:
    case Asn1Bits{+u, +o}:
      a1.bits.bit(Nat.is_lt(i, Asn1Bits.len(Asn1Bits{u, o})), o, i)

def Asn1.bits_as(t: T.Asn1Tag, b: Asn1Bits) -> N.Asn1Node:
  match b:
    case Asn1Bits{u, o}:
      N.Asn1Prim{t, B.Octets.cons(U32.from_nat(u), o)}

def Asn1.bits(b: Asn1Bits) -> N.Asn1Node:
  Asn1.bits_as(T.Asn1Tag.bit_string(), b)

# Reading

def a1.bits.check(ok: Bool, b: Asn1Bits) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  match ok:
    case True{}:
      Done{b}
    case False{}:
      Fail{E.Asn1BadBits{}}

def a1.bits.of_prim(+der: Bool, xs: List<&2, U32>) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  match xs:
    case Nil{}:
      Fail{E.Asn1BadBits{}}
    case Con{x, t}:
      +u = U32.to_nat(x)
      +o = B.Octets.of_list(t)
      +b : Asn1Bits = Asn1Bits{u, o}
      a1.bits.check(Bool.and(Asn1Bits.ok(b), R.a1.when(der, a1.bits.clear(u, o))), b)

def a1.bits.seg(+der: Bool, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  match n:
    case N.Asn1Prim{t, o}:
      a1.bits.of_prim(der, B.Octets.to_list(o))
    case N.Asn1Cons{t, xs}:
      Fail{E.Asn1BadBits{}}

# BER segments: each primitive (nested constructed segments are not
# accepted here), all but the last a whole number of octets
def a1.bits.join(acc: Result<&2, &2, E.Asn1Error, Asn1Bits>, r: Result<&2, &2, E.Asn1Error, Asn1Bits>, last: Bool) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  match acc r:
    case Fail{e} _:
      Fail{e}
    case Done{a} Fail{e}:
      Fail{e}
    case Done{a} Done{Asn1Bits{+u, o}}:
      a1.bits.check(Bool.or(last, Nat.is_eq(u, 0n)), Asn1Bits{u, B.Octets.append(Asn1Bits.octets(a), o)})

def a1.bits.segs(ns: List<&2, N.Asn1Node>, +der: Bool, acc: Result<&2, &2, E.Asn1Error, Asn1Bits>) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  match ns:
    case Nil{}:
      acc
    case Con{x, +rest}:
      a1.bits.segs(rest, der, a1.bits.join(acc, a1.bits.seg(der, x), List.is_empty(&2, N.Asn1Node, rest)))

def a1.bits.cons(ok: Bool, +prim: Bool, ns: List<&2, N.Asn1Node>, +der: Bool) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  match ok prim:
    case True{} False{}:
      a1.bits.segs(ns, der, Done{Asn1Bits{0n, B.Octets.empty()}})
    case True{} True{}:
      Fail{E.Asn1BadForm{}}
    case False{} _:
      Fail{E.Asn1Unexpected{}}

def a1.bits.prim(ok: Bool, +der: Bool, o: B.Octets) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  match ok:
    case True{}:
      a1.bits.of_prim(der, B.Octets.to_list(o))
    case False{}:
      Fail{E.Asn1Unexpected{}}

# a BIT STRING element (tag t) as a bit string
def Asn1.get_bits_as(+r: R.Asn1Rules, +t: T.Asn1Tag, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  match n:
    case N.Asn1Prim{v, o}:
      a1.bits.prim(P.a1.tag_is(t, v), R.Asn1Rules.values(r), o)
    case N.Asn1Cons{v, xs}:
      a1.bits.cons(P.a1.tag_is(t, v), R.Asn1Rules.prim_strings(r), xs, R.Asn1Rules.values(r))

def Asn1.get_bits(+r: R.Asn1Rules, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Bits>:
  Asn1.get_bits_as(r, T.Asn1Tag.bit_string(), n)
