# bend-osdev-oid, the text form: the arcs in decimal, joined by full stops
# ("1.2.840.113549"), the XML value notation of ITU-T X.680 (02/2021) 32.3
# (XMLObjIdComponentList: XMLNumberForm items joined by ".").
#
# Reading takes a rule, whether an arc may have leading zeros ("1.02");
# Oid.text_rules() refuses them, as X.680 12.8's "number" does (its first
# digit is not zero unless it is the only one), so that text read is the
# text written. An arc has one to fourteen digits (oid.bend's bound).
import Base
import ./oid.bend as O

type OidTextRules is Data:
  OidTextRules{leading_zeros: Bool}

def Oid.text_rules() -> OidTextRules:
  OidTextRules{False{}}

def Oid.text_rules_lenient() -> OidTextRules:
  OidTextRules{True{}}

# Writing

def oid.dchar(+d: Nat) -> Char:
  Chr{U32.from_nat(Nat.add(48n, d))}

def oid.dstr(ds: List<&2, Nat>, rest: String) -> String:
  match ds:
    case Nil{}:
      rest
    case Con{d, t}:
      SCon{oid.dchar(d), oid.dstr(t, rest)}

# an arc in decimal, then rest
def oid.arc_text(+a: Nat, rest: String) -> String:
  oid.dstr(O.oid.digits(a), rest)

def oid.text.join(+a: Nat, t: List<&2, Nat>, rest: String) -> String:
  match t:
    case Nil{}:
      oid.arc_text(a, SNil{})
    case Con{b, u}:
      oid.arc_text(a, SCon{'.', rest})

def oid.text(arcs: List<&2, Nat>) -> String:
  match arcs:
    case Nil{}:
      SNil{}
    case Con{+a, +t}:
      oid.text.join(a, t, oid.text(t))

# o's arcs in decimal, joined by full stops
def Oid.to_text(o: O.Oid) -> String:
  oid.text(O.Oid.arcs(o))

# Reading

def oid.cval.go(ok: Bool, x: U32) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{U32.to_nat(U32.sub(x, 48))}
    case False{}:
      None{}

def oid.cval(c: Char) -> Maybe<&2, Nat>:
  match c:
    case Chr{+x}:
      oid.cval.go(Bool.and(U32.is_le(48, x), U32.is_le(x, 57)), x)

def oid.is_dot(c: Char) -> Bool:
  match c:
    case Chr{x}:
      U32.is_eq(x, 46)

# the text cut at full stops
def oid.put_first(c: Char, parts: List<&2, String>) -> List<&2, String>:
  match parts:
    case Nil{}:
      [SCon{c, SNil{}}]
    case Con{p, t}:
      Con{SCon{c, p}, t}

def oid.split.step(dot: Bool, c: Char, rest: List<&2, String>) -> List<&2, String>:
  match dot:
    case True{}:
      Con{SNil{}, rest}
    case False{}:
      oid.put_first(c, rest)

def oid.split(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{+c, t}:
      oid.split.step(oid.is_dot(c), c, oid.split(t))

def oid.fold.step(m: Maybe<&2, Nat>, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m acc:
    case Some{d} Some{a}:
      Some{Nat.add(Nat.mul(a, 10n), d)}
    case _ _:
      None{}

# the value of digits after acc (None for a character that is not a digit)
def oid.fold(s: String, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      oid.fold(t, oid.fold.step(oid.cval(c), acc))

def oid.is_zero(c: Char) -> Bool:
  match c:
    case Chr{x}:
      U32.is_eq(x, 48)

# no leading zero: "0" alone, or a first digit other than 0
def oid.lead_ok(s: String) -> Bool:
  match s:
    case SCon{c, SCon{d, t}}:
      Bool.not(oid.is_zero(c))
    case _:
      True{}

def oid.arc.pick(ok: Bool, +s: String) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      oid.fold(s, Some{0n})
    case False{}:
      None{}

# one arc's digits: one to fourteen, and no leading zero unless allowed
def oid.arc(+lz: Bool, +s: String) -> Maybe<&2, Nat>:
  +n = String.length(s)
  oid.arc.pick(Bool.and(Nat.is_le(1n, n), Bool.and(Nat.is_le(n, O.oid.max_digits()), Bool.or(lz, oid.lead_ok(s)))), s)

def oid.arcs.cons(m: Maybe<&2, Nat>, r: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match m r:
    case Some{a} Some{xs}:
      Some{Con{a, xs}}
    case _ _:
      None{}

def oid.arcs(ps: List<&2, String>, +lz: Bool) -> Maybe<&2, List<&2, Nat>>:
  match ps:
    case Nil{}:
      Some{Nil{}}
    case Con{+p, t}:
      oid.arcs.cons(oid.arc(lz, p), oid.arcs(t, lz))

def oid.of_text.go(m: Maybe<&2, List<&2, Nat>>) -> Result<&2, &2, O.OidError, O.Oid>:
  match m:
    case None{}:
      Fail{O.OidBadText{}}
    case Some{+arcs}:
      O.Oid.of_arcs(arcs)

# the Oid of dotted text (OidBadText for text that is not arcs, OidBadArcs
# for arcs that are not a valid Oid)
def Oid.of_text(r: OidTextRules, s: String) -> Result<&2, &2, O.OidError, O.Oid>:
  match r:
    case OidTextRules{lz}:
      oid.of_text.go(oid.arcs(oid.split(s), lz))
