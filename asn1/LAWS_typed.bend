# Laws of bend-osdev-asn1's typed readers and writers, for every input.
#
# Reading what a writer writes gives the value back:
#
# * bool_round_trip, null_round_trip, octets_round_trip: BOOLEAN, NULL and
#   OCTET STRING (under any rules, with any tag for OCTET STRING);
# * int_round_trip, enum_round_trip, nat_round_trip: INTEGER and
#   ENUMERATED values of six contents octets or fewer (the reader's
#   bound), other than -0 (written as 0), with any tag;
# * bits_round_trip, bits_ber_round_trip, bits_octets_round_trip: a
#   well-formed BIT STRING (at most 7 unused bits, none without octets)
#   whose unused bits are zero, under any rules; any well-formed one under
#   rules without DER's value checks; a whole number of octets under any
#   rules;
# * string_round_trip, string_implicit_round_trip: a character string of
#   any type whose octets are valid for its type, with its universal tag
#   or an IMPLICIT one;
# * utc_round_trip, gen_round_trip, time_utc_round_trip,
#   time_gen_round_trip: a valid time in Zulu time with no fraction of a
#   second, written as UTCTime (its year one its two digits stand for under
#   the century rule) or GeneralizedTime (a year below 10000), read by its
#   own reader or by Asn1.get_time;
# * seq_round_trip, set_round_trip, cons_round_trip, explicit_round_trip,
#   implicit_round_trip, implicit_tag: SEQUENCE, SET, constructed elements
#   of any tag, EXPLICIT and IMPLICIT tagging.
#
# What the readers accept:
#
# * bool_canonical, null_canonical, int_canonical, enum_canonical,
#   nat_canonical, octets_canonical, bits_canonical, string_canonical,
#   string_implicit_canonical, cons_canonical, seq_canonical,
#   set_canonical, explicit_canonical, utc_canonical, gen_canonical: an
#   element read is the element the writer writes for the value read (under
#   DER's checks where the reader has them: BOOLEAN's FF, primitive
#   strings, the time forms; for GeneralizedTime, a time read with no
#   fraction of a second);
# * string_valid, string_implicit_valid: a string read is valid for its
#   type; utc_valid, gen_valid, time_valid: a time read is valid (a date
#   and time of day that exist); utc_zulu, gen_zulu, time_zulu: under DER,
#   in Zulu time;
# * numeric_chars, printable_chars, ia5_chars, visible_chars,
#   teletex_chars: the checks of the one-octet string types are X.680's
#   tables of their characters.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./prim.bend as P
import ./bits.bend as Bi
import ./string.bend as S
import ./time.bend as Ti
import ./build.bend as Bu

# the last of a list's elements (acc for none)
def asn1law.last(xs: List<&2, U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      asn1law.last(t, x)

# a bit string's unused bits, the low u bits of its last octet, are zero
# (X.690 11.2.1)
def asn1law.bits_clear(+u: Nat, +o: B.Octets) -> Bool:
  U32.is_eq(U32.and(asn1law.last(B.Octets.to_list(o), 0), U32.sub(U32.shln(1, u), 1)), 0)

# the year a UTCTime's two digits yy stand for: 20yy below pivot, 19yy
# from it (RFC 5280 4.1.2.5.1 with pivot 50)
def asn1law.utc_year(+yy: Nat, +pivot: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(yy, pivot), Nat.add(2000n, yy), Nat.add(1900n, yy))

# X.680 (02/2021)'s character tables of the one-octet string types, as
# octets: Table 9 (NumericString: digits and space), Table 10
# (PrintableString), IA5String (ISO 646's 128 characters, registrations 1
# and 6) and VisibleString (registration 6, the graphic characters, and
# space)

def asn1law.numeric_chars() -> List<&2, U32>:
  [32, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]

def asn1law.printable_chars() -> List<&2, U32>:
  [32, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 61, 63, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]

def asn1law.ia5_chars() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]

def asn1law.visible_chars() -> List<&2, U32>:
  [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]

# whether an octet is in a table
def asn1law.member(+x: U32, t: List<&2, U32>) -> Bool:
  match t:
    case Nil{}:
      False{}
    case Con{c, r}:
      Bool.or(U32.is_eq(x, c), asn1law.member(x, r))

# whether every octet is in a table
def asn1law.all_of(xs: List<&2, U32>, +t: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      Bool.and(asn1law.member(x, t), asn1law.all_of(r, t))

# BOOLEAN, NULL, OCTET STRING

law bool_round_trip:
  for +r: R.Asn1Rules
  for b: Bool
  {P.Asn1.get_bool(r, P.Asn1.bool(b)) == Done{b} : Result<&2, &2, E.Asn1Error, Bool>}

law null_round_trip:
  {P.Asn1.get_null(P.Asn1.null()) == Done{Unit{}} : Result<&2, &2, E.Asn1Error, Unit>}

law octets_round_trip:
  for +r: R.Asn1Rules
  for +t: T.Asn1Tag
  for +o: B.Octets
  {P.Asn1.get_octets_as(r, t, P.Asn1.octets_as(t, o)) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}

# INTEGER and ENUMERATED

law int_round_trip:
  for +t: T.Asn1Tag
  for neg: Bool
  for +m: Nat
  for +hz: {Bool.and(neg, Nat.is_eq(m, 0n)) == False{} : Bool}
  for +hl: {Nat.is_le(B.Octets.len(N.Asn1Node.content(P.Asn1.int_as(t, P.Asn1Int{neg, m}))), 6n) == True{} : Bool}
  {P.Asn1.get_int_as(t, P.Asn1.int_as(t, P.Asn1Int{neg, m})) == Done{P.Asn1Int{neg, m}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}

law enum_round_trip:
  for neg: Bool
  for +m: Nat
  for +hz: {Bool.and(neg, Nat.is_eq(m, 0n)) == False{} : Bool}
  for +hl: {Nat.is_le(B.Octets.len(N.Asn1Node.content(P.Asn1.enum(P.Asn1Int{neg, m}))), 6n) == True{} : Bool}
  {P.Asn1.get_enum(P.Asn1.enum(P.Asn1Int{neg, m})) == Done{P.Asn1Int{neg, m}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}

law nat_round_trip:
  for +n: Nat
  for +hl: {Nat.is_le(B.Octets.len(N.Asn1Node.content(P.Asn1.int_nat(n))), 6n) == True{} : Bool}
  {P.Asn1.get_nat(P.Asn1.int_nat(n)) == Done{n} : Result<&2, &2, E.Asn1Error, Nat>}

# BIT STRING

law bits_round_trip:
  for +r: R.Asn1Rules
  for +t: T.Asn1Tag
  for +u: Nat
  for +o: B.Octets
  for +hok: {Bi.Asn1Bits.ok(Bi.Asn1Bits{u, o}) == True{} : Bool}
  for +hc: {asn1law.bits_clear(u, o) == True{} : Bool}
  {Bi.Asn1.get_bits_as(r, t, Bi.Asn1.bits_as(t, Bi.Asn1Bits{u, o})) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}

law bits_ber_round_trip:
  for +r: R.Asn1Rules
  for +hv: {R.Asn1Rules.values(r) == False{} : Bool}
  for +t: T.Asn1Tag
  for +u: Nat
  for +o: B.Octets
  for +hok: {Bi.Asn1Bits.ok(Bi.Asn1Bits{u, o}) == True{} : Bool}
  {Bi.Asn1.get_bits_as(r, t, Bi.Asn1.bits_as(t, Bi.Asn1Bits{u, o})) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}

law bits_octets_round_trip:
  for +r: R.Asn1Rules
  for +t: T.Asn1Tag
  for +o: B.Octets
  {Bi.Asn1.get_bits_as(r, t, Bi.Asn1.bits_as(t, Bi.Asn1Bits.of_octets(o))) == Done{Bi.Asn1Bits.of_octets(o)} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}

# Character strings

law string_round_trip:
  for +r: R.Asn1Rules
  for +k: S.Asn1StrKind
  for +o: B.Octets
  for +hv: {S.Asn1Str.valid(S.Asn1Str{k, o}) == True{} : Bool}
  {S.Asn1.get_string(r, S.Asn1.string(S.Asn1Str{k, o})) == Done{S.Asn1Str{k, o}} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}

law string_implicit_round_trip:
  for +r: R.Asn1Rules
  for +t: T.Asn1Tag
  for +k: S.Asn1StrKind
  for +o: B.Octets
  for +hv: {S.Asn1Str.valid(S.Asn1Str{k, o}) == True{} : Bool}
  {S.Asn1.get_string_as(r, t, k, Bu.Asn1.implicit(t, S.Asn1.string(S.Asn1Str{k, o}))) == Done{S.Asn1Str{k, o}} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}

# Times

law utc_round_trip:
  for +r: R.Asn1Rules
  for +pivot: Nat
  for +yy: Nat
  for +mo: Nat
  for +d: Nat
  for +h: Nat
  for +mi: Nat
  for +s: Nat
  for +hyy: {Nat.is_lt(yy, 100n) == True{} : Bool}
  for +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{asn1law.utc_year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}) == True{} : Bool}
  {Ti.Asn1.get_utc_time(r, pivot, Ti.Asn1.utc_time(Ti.Asn1Time{asn1law.utc_year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}})) == Done{Ti.Asn1Time{asn1law.utc_year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}

law gen_round_trip:
  for +r: R.Asn1Rules
  for +cc: Nat
  for +yy: Nat
  for +mo: Nat
  for +d: Nat
  for +h: Nat
  for +mi: Nat
  for +s: Nat
  for +hcc: {Nat.is_lt(cc, 100n) == True{} : Bool}
  for +hyy: {Nat.is_lt(yy, 100n) == True{} : Bool}
  for +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}) == True{} : Bool}
  {Ti.Asn1.get_gen_time(r, Ti.Asn1.gen_time(Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}})) == Done{Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}

law time_utc_round_trip:
  for +r: R.Asn1Rules
  for +pivot: Nat
  for +yy: Nat
  for +mo: Nat
  for +d: Nat
  for +h: Nat
  for +mi: Nat
  for +s: Nat
  for +hyy: {Nat.is_lt(yy, 100n) == True{} : Bool}
  for +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{asn1law.utc_year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}) == True{} : Bool}
  {Ti.Asn1.get_time(r, pivot, Ti.Asn1.utc_time(Ti.Asn1Time{asn1law.utc_year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}})) == Done{Ti.Asn1Time{asn1law.utc_year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}

law time_gen_round_trip:
  for +r: R.Asn1Rules
  for +pivot: Nat
  for +cc: Nat
  for +yy: Nat
  for +mo: Nat
  for +d: Nat
  for +h: Nat
  for +mi: Nat
  for +s: Nat
  for +hcc: {Nat.is_lt(cc, 100n) == True{} : Bool}
  for +hyy: {Nat.is_lt(yy, 100n) == True{} : Bool}
  for +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}) == True{} : Bool}
  {Ti.Asn1.get_time(r, pivot, Ti.Asn1.gen_time(Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}})) == Done{Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}

# Constructed values and tags

law seq_round_trip:
  for +xs: List<&2, N.Asn1Node>
  {Bu.Asn1.get_seq(Bu.Asn1.seq(xs)) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}

law set_round_trip:
  for +xs: List<&2, N.Asn1Node>
  {Bu.Asn1.get_set(Bu.Asn1.set(xs)) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}

law cons_round_trip:
  for +t: T.Asn1Tag
  for +xs: List<&2, N.Asn1Node>
  {Bu.Asn1.cons_as(t, N.Asn1Cons{t, xs}) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}

law explicit_round_trip:
  for +n: Nat
  for +x: N.Asn1Node
  {Bu.Asn1.get_explicit(n, Bu.Asn1.explicit(n, x)) == Done{x} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}

law implicit_round_trip:
  for +t: T.Asn1Tag
  for +u: T.Asn1Tag
  for x: N.Asn1Node
  {Bu.Asn1.untag(t, u, Bu.Asn1.implicit(t, x)) == Done{Bu.Asn1.implicit(u, x)} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}

law implicit_tag:
  for +t: T.Asn1Tag
  for x: N.Asn1Node
  {Bu.Asn1.has_tag(t, Bu.Asn1.implicit(t, x)) == True{} : Bool}

# What the readers accept: under DER's checks, only what the writers
# write; and only values their checks pass

law bool_canonical:
  for +r: R.Asn1Rules
  for +hv: {R.Asn1Rules.values(r) == True{} : Bool}
  for n: N.Asn1Node
  for b: Bool
  for +e: {P.Asn1.get_bool(r, n) == Done{b} : Result<&2, &2, E.Asn1Error, Bool>}
  {P.Asn1.bool(b) == n : N.Asn1Node}

law null_canonical:
  for n: N.Asn1Node
  for u: Unit
  for +e: {P.Asn1.get_null(n) == Done{u} : Result<&2, &2, E.Asn1Error, Unit>}
  {P.Asn1.null() == n : N.Asn1Node}

law octets_canonical:
  for +r: R.Asn1Rules
  for +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}
  for +t: T.Asn1Tag
  for +n: N.Asn1Node
  for o: B.Octets
  for +e: {P.Asn1.get_octets_as(r, t, n) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}
  {P.Asn1.octets_as(t, o) == n : N.Asn1Node}

law bits_canonical:
  for +r: R.Asn1Rules
  for +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}
  for +t: T.Asn1Tag
  for n: N.Asn1Node
  for b: Bi.Asn1Bits
  for +e: {Bi.Asn1.get_bits_as(r, t, n) == Done{b} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  {Bi.Asn1.bits_as(t, b) == n : N.Asn1Node}

law string_canonical:
  for +r: R.Asn1Rules
  for +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}
  for +n: N.Asn1Node
  for s: S.Asn1Str
  for +e: {S.Asn1.get_string(r, n) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}
  {S.Asn1.string(s) == n : N.Asn1Node}

law string_implicit_canonical:
  for +r: R.Asn1Rules
  for +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}
  for +t: T.Asn1Tag
  for +k: S.Asn1StrKind
  for +n: N.Asn1Node
  for s: S.Asn1Str
  for +e: {S.Asn1.get_string_as(r, t, k, n) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}
  {Bu.Asn1.implicit(t, S.Asn1.string(s)) == n : N.Asn1Node}

law string_valid:
  for +r: R.Asn1Rules
  for +n: N.Asn1Node
  for s: S.Asn1Str
  for +e: {S.Asn1.get_string(r, n) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}
  {S.Asn1Str.valid(s) == True{} : Bool}

law string_implicit_valid:
  for +r: R.Asn1Rules
  for +t: T.Asn1Tag
  for +k: S.Asn1StrKind
  for +n: N.Asn1Node
  for s: S.Asn1Str
  for +e: {S.Asn1.get_string_as(r, t, k, n) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}
  {S.Asn1Str.valid(s) == True{} : Bool}

law cons_canonical:
  for +t: T.Asn1Tag
  for n: N.Asn1Node
  for xs: List<&2, N.Asn1Node>
  for +e: {Bu.Asn1.cons_as(t, n) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}
  {N.Asn1Cons{t, xs} == n : N.Asn1Node}

law seq_canonical:
  for n: N.Asn1Node
  for xs: List<&2, N.Asn1Node>
  for +e: {Bu.Asn1.get_seq(n) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}
  {Bu.Asn1.seq(xs) == n : N.Asn1Node}

law set_canonical:
  for n: N.Asn1Node
  for xs: List<&2, N.Asn1Node>
  for +e: {Bu.Asn1.get_set(n) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}
  {Bu.Asn1.set(xs) == n : N.Asn1Node}

law explicit_canonical:
  for +k: Nat
  for +n: N.Asn1Node
  for x: N.Asn1Node
  for +e: {Bu.Asn1.get_explicit(k, n) == Done{x} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
  {Bu.Asn1.explicit(k, x) == n : N.Asn1Node}

law utc_valid:
  for +r: R.Asn1Rules
  for +pivot: Nat
  for +n: N.Asn1Node
  for +t: Ti.Asn1Time
  for +e: {Ti.Asn1.get_utc_time(r, pivot, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {Ti.Asn1Time.valid(t) == True{} : Bool}

law gen_valid:
  for +r: R.Asn1Rules
  for +n: N.Asn1Node
  for +t: Ti.Asn1Time
  for +e: {Ti.Asn1.get_gen_time(r, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {Ti.Asn1Time.valid(t) == True{} : Bool}

law time_valid:
  for +r: R.Asn1Rules
  for +pivot: Nat
  for +n: N.Asn1Node
  for +t: Ti.Asn1Time
  for +e: {Ti.Asn1.get_time(r, pivot, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {Ti.Asn1Time.valid(t) == True{} : Bool}

law utc_zulu:
  for +r: R.Asn1Rules
  for +hv: {R.Asn1Rules.values(r) == True{} : Bool}
  for +pivot: Nat
  for +n: N.Asn1Node
  for +t: Ti.Asn1Time
  for +e: {Ti.Asn1.get_utc_time(r, pivot, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {Ti.Asn1Time.zone(t) == Ti.Asn1Zulu{} : Ti.Asn1Zone}

law gen_zulu:
  for +r: R.Asn1Rules
  for +hv: {R.Asn1Rules.values(r) == True{} : Bool}
  for +n: N.Asn1Node
  for +t: Ti.Asn1Time
  for +e: {Ti.Asn1.get_gen_time(r, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {Ti.Asn1Time.zone(t) == Ti.Asn1Zulu{} : Ti.Asn1Zone}

law time_zulu:
  for +r: R.Asn1Rules
  for +hv: {R.Asn1Rules.values(r) == True{} : Bool}
  for +pivot: Nat
  for +n: N.Asn1Node
  for +t: Ti.Asn1Time
  for +e: {Ti.Asn1.get_time(r, pivot, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {Ti.Asn1Time.zone(t) == Ti.Asn1Zulu{} : Ti.Asn1Zone}

law int_canonical:
  for +t: T.Asn1Tag
  for n: N.Asn1Node
  for i: P.Asn1Int
  for +e: {P.Asn1.get_int_as(t, n) == Done{i} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
  {P.Asn1.int_as(t, i) == n : N.Asn1Node}

law enum_canonical:
  for n: N.Asn1Node
  for i: P.Asn1Int
  for +e: {P.Asn1.get_enum(n) == Done{i} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
  {P.Asn1.enum(i) == n : N.Asn1Node}

law nat_canonical:
  for +n: N.Asn1Node
  for +m: Nat
  for +e: {P.Asn1.get_nat(n) == Done{m} : Result<&2, &2, E.Asn1Error, Nat>}
  {P.Asn1.int_nat(m) == n : N.Asn1Node}

law utc_canonical:
  for +r: R.Asn1Rules
  for +hv: {R.Asn1Rules.values(r) == True{} : Bool}
  for +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}
  for +pivot: Nat
  for +n: N.Asn1Node
  for t: Ti.Asn1Time
  for +e: {Ti.Asn1.get_utc_time(r, pivot, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {Ti.Asn1.utc_time(t) == n : N.Asn1Node}

law gen_canonical:
  for +r: R.Asn1Rules
  for +hv: {R.Asn1Rules.values(r) == True{} : Bool}
  for +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}
  for +n: N.Asn1Node
  for +y: Nat
  for +mo: Nat
  for +d: Nat
  for +h: Nat
  for +mi: Nat
  for +s: Nat
  for +z: Ti.Asn1Zone
  for +e: {Ti.Asn1.get_gen_time(r, n) == Done{Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, z}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {Ti.Asn1.gen_time(Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, z}) == n : N.Asn1Node}

# The string checks of the one-octet types are X.680's tables

law numeric_chars:
  for +o: B.Octets
  {S.Asn1Str.valid(S.Asn1Str{S.Asn1Numeric{}, o}) == asn1law.all_of(B.Octets.to_list(o), asn1law.numeric_chars()) : Bool}

law printable_chars:
  for +o: B.Octets
  {S.Asn1Str.valid(S.Asn1Str{S.Asn1Printable{}, o}) == asn1law.all_of(B.Octets.to_list(o), asn1law.printable_chars()) : Bool}

law ia5_chars:
  for +o: B.Octets
  {S.Asn1Str.valid(S.Asn1Str{S.Asn1Ia5{}, o}) == asn1law.all_of(B.Octets.to_list(o), asn1law.ia5_chars()) : Bool}

law visible_chars:
  for +o: B.Octets
  {S.Asn1Str.valid(S.Asn1Str{S.Asn1Visible{}, o}) == asn1law.all_of(B.Octets.to_list(o), asn1law.visible_chars()) : Bool}

law teletex_chars:
  for +o: B.Octets
  {S.Asn1Str.valid(S.Asn1Str{S.Asn1Teletex{}, o}) == True{} : Bool}
