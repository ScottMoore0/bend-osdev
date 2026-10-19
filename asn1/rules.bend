# bend-osdev-asn1, decoding rules: what a decoder accepts beyond the basic
# encoding rules' octet structure (ITU-T X.690 (02/2021)), each a parameter:
#
#   indefinite    the indefinite length form (8.1.3.6) is accepted; DER
#                 refuses it (10.1)
#   min_length    lengths must take the fewest octets (DER, 10.1)
#   forms         the forms X.690 fixes for universal types are enforced:
#                 BOOLEAN, INTEGER, NULL, OBJECT IDENTIFIER, REAL,
#                 ENUMERATED and RELATIVE-OID are primitive (8.2.1, 8.3.1,
#                 8.8.1, 8.19.1, 8.5.1, 8.4, 8.20.1); SEQUENCE and SET
#                 (and their -OF forms) constructed (8.9.1, 8.10.1, 8.11.1,
#                 8.12.1)
#   prim_strings  bit strings, octet strings and restricted character string
#                 types (and UTCTime and GeneralizedTime, which are
#                 VisibleStrings, X.680 46.3 and 47.3) must be primitive
#                 (DER, 10.2)
#   set_order     the order of a SET's elements: none, the SET OF order (the
#                 encodings ascending as octet strings padded with zeros,
#                 11.6), or the SET order (tags ascending in X.680 8.6's
#                 order, 10.3)
#   trailing      octets after the element are accepted (the caller's
#                 choice; X.690 does not say)
#   values        the typed readers apply DER's restrictions on values:
#                 BOOLEAN TRUE is FF (11.1), a bit string's unused bits are
#                 zero (11.2.1), times end in Z, keep their seconds and drop
#                 trailing fraction zeros (11.7, 11.8)
#
# Asn1Rules.der() is DER, Asn1Rules.ber() BER; Asn1Rules.default() is DER.
import Base
import ./tag.bend as T

type Asn1SetOrder is Data:
  Asn1SetAny{}
  Asn1SetOfOrder{}
  Asn1SetTagOrder{}

type Asn1Rules is Data:
  Asn1Rules{indefinite: Bool, min_length: Bool, forms: Bool, prim_strings: Bool, set_order: Asn1SetOrder, trailing: Bool, values: Bool}

def Asn1Rules.der() -> Asn1Rules:
  Asn1Rules{False{}, True{}, True{}, True{}, Asn1SetOfOrder{}, False{}, True{}}

def Asn1Rules.ber() -> Asn1Rules:
  Asn1Rules{True{}, False{}, True{}, False{}, Asn1SetAny{}, False{}, False{}}

def Asn1Rules.default() -> Asn1Rules:
  Asn1Rules.der()

def Asn1Rules.indefinite(r: Asn1Rules) -> Bool:
  match r:
    case Asn1Rules{i, m, f, p, s, t, v}:
      i

def Asn1Rules.min_length(r: Asn1Rules) -> Bool:
  match r:
    case Asn1Rules{i, m, f, p, s, t, v}:
      m

def Asn1Rules.forms(r: Asn1Rules) -> Bool:
  match r:
    case Asn1Rules{i, m, f, p, s, t, v}:
      f

def Asn1Rules.prim_strings(r: Asn1Rules) -> Bool:
  match r:
    case Asn1Rules{i, m, f, p, s, t, v}:
      p

def Asn1Rules.set_order(r: Asn1Rules) -> Asn1SetOrder:
  match r:
    case Asn1Rules{i, m, f, p, s, t, v}:
      s

def Asn1Rules.trailing(r: Asn1Rules) -> Bool:
  match r:
    case Asn1Rules{i, m, f, p, s, t, v}:
      t

def Asn1Rules.values(r: Asn1Rules) -> Bool:
  match r:
    case Asn1Rules{i, m, f, p, s, t, v}:
      v

# the same rules with trailing octets accepted or not
def Asn1Rules.with_trailing(r: Asn1Rules, t2: Bool) -> Asn1Rules:
  match r:
    case Asn1Rules{i, m, f, p, s, t, v}:
      Asn1Rules{i, m, f, p, s, t2, v}

# Universal forms

def a1.mem(+n: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.or(Nat.is_eq(n, x), a1.mem(n, t))

# universal types whose encoding is always primitive
def a1.prim_only() -> List<&2, Nat>:
  [1n, 2n, 5n, 6n, 9n, 10n, 13n]

# universal types whose encoding is always constructed
def a1.cons_only() -> List<&2, Nat>:
  [16n, 17n]

# bit and octet strings, restricted character strings and the time strings
def a1.strings() -> List<&2, Nat>:
  [3n, 4n, 12n, 18n, 19n, 20n, 21n, 22n, 23n, 24n, 25n, 26n, 27n, 28n, 30n]

def a1.when(on: Bool, ok: Bool) -> Bool:
  match on:
    case True{}:
      ok
    case False{}:
      True{}

def a1.form_univ(+r: Asn1Rules, +n: Nat, cons: Bool) -> Bool:
  match cons:
    case True{}:
      Bool.and(a1.when(Asn1Rules.forms(r), Bool.not(a1.mem(n, a1.prim_only()))), a1.when(Asn1Rules.prim_strings(r), Bool.not(a1.mem(n, a1.strings()))))
    case False{}:
      a1.when(Asn1Rules.forms(r), Bool.not(a1.mem(n, a1.cons_only())))

# whether rules r accept an element of this tag in this form (only
# universal tags have fixed forms)
def a1.form_ok(+r: Asn1Rules, t: T.Asn1Tag, cons: Bool) -> Bool:
  match t:
    case T.Asn1Tag{T.Asn1Universal{}, +n}:
      a1.form_univ(r, n, cons)
    case T.Asn1Tag{c, n}:
      True{}
