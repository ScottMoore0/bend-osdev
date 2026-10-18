# bend-osdev-acpi, aml_pkglength.bend: PkgLength, the length that opens every
# AML package (ACPI 6.5, section 20.2.4, Package Length Encoding):
#
#   PkgLength := PkgLeadByte |
#                <PkgLeadByte ByteData> |
#                <PkgLeadByte ByteData ByteData> |
#                <PkgLeadByte ByteData ByteData ByteData>
#
# Bits 7-6 of PkgLeadByte count the ByteData that follow. With none, bits
# 5-0 are the length (0 to 63). Otherwise bits 3-0 are its least
# significant four bits, each following byte the next eight, and bits 5-4
# must be zero. So a PkgLength holds up to 2^28 - 1. The value counts the
# PkgLength's own bytes and the package that follows.
#
# The decoder reads bits by pattern and builds the value by joining bits,
# so that its round trip with the encoder computes for a value whose bits
# are unknown (LAWS.bend: pkglength_round_trip).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E

# the value, its size in bytes (1 to 4) and what follows (list layer)
type AmlPkgL is Data:
  AmlPkgL{value: U32, size: Nat, rest: List<&2, U32>}

# the value and what follows
type AmlPkgLen is Data:
  AmlPkgLen{value: U32, rest: B.Octets}

# Encoding (list layer): the shortest form

def pk.enc.pick(s1: Bool, s2: Bool, s3: Bool, +v: U32) -> List<&2, U32>:
  match s1:
    case True{}:
      [U32.and(63, v)]
    case False{}:
      match s2:
        case True{}:
          [U32.or(64, U32.and(15, v)), U32.and(255, U32.shrn(v, 4n))]
        case False{}:
          match s3:
            case True{}:
              [U32.or(128, U32.and(15, v)), U32.and(255, U32.shrn(v, 4n)), U32.and(255, U32.shrn(v, 12n))]
            case False{}:
              [U32.or(192, U32.and(15, v)), U32.and(255, U32.shrn(v, 4n)), U32.and(255, U32.shrn(v, 12n)), U32.and(255, U32.shrn(v, 20n))]

def pk.enc(+v: U32) -> List<&2, U32>:
  pk.enc.pick(U32.is_eq(U32.shrn(v, 6n), 0), U32.is_eq(U32.shrn(v, 12n), 0), U32.is_eq(U32.shrn(v, 20n), 0), v)

# Decoding (list layer)

def pk.v2(l0: Bool, l1: Bool, l2: Bool, l3: Bool, a: U32) -> U32:
  match a:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}}:
      U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(20n)}}}}}}}}}}}}}

def pk.v3(l0: Bool, l1: Bool, l2: Bool, l3: Bool, a: U32, b: U32) -> U32:
  match a b:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}}:
      U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(12n)}}}}}}}}}}}}}}}}}}}}}

def pk.v4(l0: Bool, l1: Bool, l2: Bool, l3: Bool, a: U32, b: U32, c: U32) -> U32:
  match a b c:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, ch}}}}}}}}}:
      U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, Word.zero(4n)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def pk.d2(l0: Bool, l1: Bool, l2: Bool, l3: Bool, t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlPkgL>:
  match t:
    case Con{a, r}:
      Done{AmlPkgL{pk.v2(l0, l1, l2, l3, a), 2n, r}}
    case Nil{}:
      Fail{E.AcpiAmlTruncated{}}

def pk.d3(l0: Bool, l1: Bool, l2: Bool, l3: Bool, t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlPkgL>:
  match t:
    case Con{a, Con{b, r}}:
      Done{AmlPkgL{pk.v3(l0, l1, l2, l3, a, b), 3n, r}}
    case _:
      Fail{E.AcpiAmlTruncated{}}

def pk.d4(l0: Bool, l1: Bool, l2: Bool, l3: Bool, t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlPkgL>:
  match t:
    case Con{a, Con{b, Con{c, r}}}:
      Done{AmlPkgL{pk.v4(l0, l1, l2, l3, a, b, c), 4n, r}}
    case _:
      Fail{E.AcpiAmlTruncated{}}

# bits 5-4 must be zero in the multi-byte forms; n: how many bytes follow
def pk.multi(l4: Bool, l5: Bool, n: Nat, l0: Bool, l1: Bool, l2: Bool, l3: Bool, t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlPkgL>:
  match l4 l5:
    case False{} False{}:
      match n:
        case 1n:
          pk.d2(l0, l1, l2, l3, t)
        case 2n:
          pk.d3(l0, l1, l2, l3, t)
        case _:
          pk.d4(l0, l1, l2, l3, t)
    case _ _:
      Fail{E.AcpiAmlBadPkgLength{}}

def pk.lead(l7: Bool, l6: Bool, l0: Bool, l1: Bool, l2: Bool, l3: Bool, l4: Bool, l5: Bool, t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlPkgL>:
  match l7:
    case False{}:
      match l6:
        case False{}:
          Done{AmlPkgL{U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, Word.zero(26n)}}}}}}}, 1n, t}}
        case True{}:
          pk.multi(l4, l5, 1n, l0, l1, l2, l3, t)
    case True{}:
      match l6:
        case False{}:
          pk.multi(l4, l5, 2n, l0, l1, l2, l3, t)
        case True{}:
          pk.multi(l4, l5, 3n, l0, l1, l2, l3, t)

# the PkgLength at the front of a list of bytes
def pk.dec(xs: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlPkgL>:
  match xs:
    case Nil{}:
      Fail{E.AcpiAmlTruncated{}}
    case Con{U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, lh}}}}}}}}}, t}:
      pk.lead(l7, l6, l0, l1, l2, l3, l4, l5, t)

# The public interface, on Octets

# the values a PkgLength holds: below 2^28
def AmlPkgLength.fits(v: U32) -> Bool:
  U32.is_eq(U32.shrn(v, 28n), 0)

# v in the shortest form (the low 28 bits of v)
def AmlPkgLength.encode(+v: U32) -> B.Octets:
  B.Octets.of_list(pk.enc(v))

def pk.pub(r: Result<&2, &2, E.AcpiError, AmlPkgL>) -> Result<&2, &2, E.AcpiError, AmlPkgLen>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlPkgL{v, n, rest}}:
      Done{AmlPkgLen{v, B.Octets.of_list(rest)}}

# the PkgLength at the front of o, and what follows it; AcpiAmlTruncated if
# o ends inside it, AcpiAmlBadPkgLength if bits 5-4 are set in a
# multi-byte form
def AmlPkgLength.decode(o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlPkgLen>:
  pk.pub(pk.dec(B.Octets.to_list(o)))

def pk.size.pick(a: Bool, b: Bool, c: Bool) -> Nat:
  match a:
    case True{}:
      1n
    case False{}:
      match b:
        case True{}:
          2n
        case False{}:
          match c:
            case True{}:
              3n
            case False{}:
              4n

# the size of the PkgLength that covers a package whose contents (after
# the PkgLength) are n bytes
def AmlPkgLength.size_for(+n: Nat) -> Nat:
  pk.size.pick(Nat.is_lt(n, 63n), Nat.is_lt(n, 4094n), Nat.is_lt(n, 1048573n))

# a package: the PkgLength covering it, then its contents
def AmlPkgLength.wrap(+body: B.Octets) -> B.Octets:
  +n = B.Octets.len(body)
  B.Octets.append(AmlPkgLength.encode(U32.from_nat(Nat.add(n, AmlPkgLength.size_for(n)))), body)
