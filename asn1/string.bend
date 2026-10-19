# bend-osdev-asn1, the restricted character string types (ITU-T X.680
# (02/2021) clause 41, Table 8; encoded per X.690 (02/2021) 8.23): their
# contents octets, checked against each type's characters, and as Unicode
# code points:
#
#   UTF8String (12)        UTF-8, checked against RFC 3629 (November 2003)
#                          section 4's syntax
#   NumericString (18)     digits and space (X.680 Table 9)
#   PrintableString (19)   X.680 Table 10's characters
#   TeletexString (20)     any octets; read as code points 0-255 (the
#                          T.61 repertoire is not mapped)
#   IA5String (22)         octets 0-127 (registrations 1 and 6)
#   VisibleString (26)     octets 32-126 (registration 6 and SPACE)
#   UniversalString (28)   four octets per character, big-endian
#   BMPString (30)         two octets per character, big-endian
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./prim.bend as P

type Asn1StrKind is Data:
  Asn1Utf8{}
  Asn1Numeric{}
  Asn1Printable{}
  Asn1Teletex{}
  Asn1Ia5{}
  Asn1Visible{}
  Asn1UniversalStr{}
  Asn1Bmp{}

type Asn1Str is Data:
  Asn1Str{kind: Asn1StrKind, octets: B.Octets}

type A1U8 is Data:
  A1U8{need: Nat, lo: U32, hi: U32, cp: U32}
  A1U8Bad{}

type A1U8Step is Data:
  A1U8Step{st: A1U8, emit: Maybe<&2, U32>}

def Asn1StrKind.num(k: Asn1StrKind) -> Nat:
  match k:
    case Asn1Utf8{}:
      12n
    case Asn1Numeric{}:
      18n
    case Asn1Printable{}:
      19n
    case Asn1Teletex{}:
      20n
    case Asn1Ia5{}:
      22n
    case Asn1Visible{}:
      26n
    case Asn1UniversalStr{}:
      28n
    case Asn1Bmp{}:
      30n

def Asn1StrKind.tag(k: Asn1StrKind) -> T.Asn1Tag:
  T.Asn1Tag.universal(Asn1StrKind.num(k))

def a1.kind.of_num(n: Nat) -> Maybe<&2, Asn1StrKind>:
  match n:
    case 12n:
      Some{Asn1Utf8{}}
    case 18n:
      Some{Asn1Numeric{}}
    case 19n:
      Some{Asn1Printable{}}
    case 20n:
      Some{Asn1Teletex{}}
    case 22n:
      Some{Asn1Ia5{}}
    case 26n:
      Some{Asn1Visible{}}
    case 28n:
      Some{Asn1UniversalStr{}}
    case 30n:
      Some{Asn1Bmp{}}
    case _:
      None{}

# the string type of a tag, if it is one
def Asn1StrKind.of_tag(t: T.Asn1Tag) -> Maybe<&2, Asn1StrKind>:
  match t:
    case T.Asn1Tag{T.Asn1Universal{}, n}:
      a1.kind.of_num(n)
    case _:
      None{}

# UTF-8 (RFC 3629 section 4), one octet at a time: the octets still
# needed for the character, the range the next must be in, and the code
# point so far

def a1.u8.in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

def a1.u8.lead(a1b: Bool, a2: Bool, e0: Bool, e1: Bool, ed: Bool, ee: Bool, f0: Bool, f1: Bool, f4: Bool, +x: U32) -> A1U8Step:
  match a1b a2 e0 e1 ed ee f0 f1 f4:
    case True{} _ _ _ _ _ _ _ _:
      A1U8Step{A1U8{0n, 0, 0, 0}, Some{x}}
    case False{} True{} _ _ _ _ _ _ _:
      A1U8Step{A1U8{1n, 128, 191, U32.sub(x, 192)}, None{}}
    case False{} False{} True{} _ _ _ _ _ _:
      A1U8Step{A1U8{2n, 160, 191, 0}, None{}}
    case False{} False{} False{} True{} _ _ _ _ _:
      A1U8Step{A1U8{2n, 128, 191, U32.sub(x, 224)}, None{}}
    case False{} False{} False{} False{} True{} _ _ _ _:
      A1U8Step{A1U8{2n, 128, 159, 13}, None{}}
    case False{} False{} False{} False{} False{} True{} _ _ _:
      A1U8Step{A1U8{2n, 128, 191, U32.sub(x, 224)}, None{}}
    case False{} False{} False{} False{} False{} False{} True{} _ _:
      A1U8Step{A1U8{3n, 144, 191, 0}, None{}}
    case False{} False{} False{} False{} False{} False{} False{} True{} _:
      A1U8Step{A1U8{3n, 128, 191, U32.sub(x, 240)}, None{}}
    case False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      A1U8Step{A1U8{3n, 128, 143, 4}, None{}}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      A1U8Step{A1U8Bad{}, None{}}

def a1.u8.start(+x: U32) -> A1U8Step:
  a1.u8.lead(U32.is_lt(x, 128), a1.u8.in(x, 194, 223), U32.is_eq(x, 224), a1.u8.in(x, 225, 236), U32.is_eq(x, 237), a1.u8.in(x, 238, 239), U32.is_eq(x, 240), a1.u8.in(x, 241, 243), U32.is_eq(x, 244), x)

def a1.u8.tail(ok: Bool, k: Nat, +cp: U32, +x: U32) -> A1U8Step:
  match ok k:
    case False{} _:
      A1U8Step{A1U8Bad{}, None{}}
    case True{} 0n:
      A1U8Step{A1U8Bad{}, None{}}
    case True{} 1n:
      A1U8Step{A1U8{0n, 0, 0, 0}, Some{U32.add(U32.mul(cp, 64), U32.sub(x, 128))}}
    case True{} 2n+j:
      A1U8Step{A1U8{1n+j, 128, 191, U32.add(U32.mul(cp, 64), U32.sub(x, 128))}, None{}}

def a1.u8.step(st: A1U8, +x: U32) -> A1U8Step:
  match st:
    case A1U8Bad{}:
      A1U8Step{A1U8Bad{}, None{}}
    case A1U8{0n, lo, hi, cp}:
      a1.u8.start(x)
    case A1U8{+k, lo, hi, cp}:
      a1.u8.tail(a1.u8.in(x, lo, hi), k, cp, x)

def a1.u8.st(s: A1U8Step) -> A1U8:
  match s:
    case A1U8Step{st, e}:
      st

def a1.u8.acc(s: A1U8Step, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case A1U8Step{st, None{}}:
      acc
    case A1U8Step{st, Some{c}}:
      Con{c, acc}

def a1.u8.done(st: A1U8, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match st:
    case A1U8{0n, lo, hi, cp}:
      Some{List.reverse(&2, U32, acc)}
    case _:
      None{}

def a1.u8.go(xs: List<&2, U32>, st: A1U8, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      a1.u8.done(st, acc)
    case Con{x, t}:
      +s = a1.u8.step(st, x)
      a1.u8.go(t, a1.u8.st(s), a1.u8.acc(s, acc))

# the code points of UTF-8 octets; None if they are not UTF-8
def Asn1.utf8_decode(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  a1.u8.go(xs, A1U8{0n, 0, 0, 0}, Nil{})

def a1.u8.cont(c: U32, k: Nat) -> U32:
  U32.add(128, U32.and(U32.shrn(c, k), 63))

def a1.u8.enc.pick(a: Bool, b: Bool, d: Bool, +c: U32) -> List<&2, U32>:
  match a b d:
    case True{} _ _:
      [c]
    case False{} True{} _:
      [U32.add(192, U32.shrn(c, 6n)), a1.u8.cont(c, 0n)]
    case False{} False{} True{}:
      [U32.add(224, U32.shrn(c, 12n)), a1.u8.cont(c, 6n), a1.u8.cont(c, 0n)]
    case False{} False{} False{}:
      [U32.add(240, U32.shrn(c, 18n)), a1.u8.cont(c, 12n), a1.u8.cont(c, 6n), a1.u8.cont(c, 0n)]

def a1.u8.enc1(+c: U32) -> List<&2, U32>:
  a1.u8.enc.pick(U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536), c)

# code points as UTF-8 octets
def Asn1.utf8_encode(cs: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      List.append(&2, U32, a1.u8.enc1(c), Asn1.utf8_encode(t))

# One-octet character sets

def a1.printable(+x: U32) -> Bool:
  Bool.or(a1.u8.in(x, 65, 90), Bool.or(a1.u8.in(x, 97, 122), Bool.or(a1.u8.in(x, 48, 57), Bool.or(U32.is_eq(x, 32), Bool.or(a1.u8.in(x, 39, 41), Bool.or(a1.u8.in(x, 43, 47), Bool.or(U32.is_eq(x, 58), Bool.or(U32.is_eq(x, 61), U32.is_eq(x, 63)))))))))

def a1.numeric(+x: U32) -> Bool:
  Bool.or(a1.u8.in(x, 48, 57), U32.is_eq(x, 32))

def a1.charset(k: Asn1StrKind, +x: U32) -> Bool:
  match k:
    case Asn1Numeric{}:
      a1.numeric(x)
    case Asn1Printable{}:
      a1.printable(x)
    case Asn1Ia5{}:
      U32.is_lt(x, 128)
    case Asn1Visible{}:
      a1.u8.in(x, 32, 126)
    case Asn1Teletex{}:
      True{}
    case Asn1Utf8{}:
      True{}
    case Asn1UniversalStr{}:
      True{}
    case Asn1Bmp{}:
      True{}

def a1.all_in(xs: List<&2, U32>, +k: Asn1StrKind) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(a1.charset(k, x), a1.all_in(t, k))

def a1.ok_chars(ok: Bool, +xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{xs}
    case False{}:
      None{}

# Wide characters, big-endian

def a1.wide.put(ok: Bool, c: U32, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match ok r:
    case True{} Some{cs}:
      Some{Con{c, cs}}
    case _ _:
      None{}

def a1.wide.cons(+c: U32, lo: U32, hi: U32, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  a1.wide.put(Bool.not(a1.u8.in(c, lo, hi)), c, r)

def a1.bmp(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{a, Con{b, t}}:
      a1.wide.cons(U32.add(U32.mul(a, 256), b), 55296, 57343, a1.bmp(t))
    case Con{a, Nil{}}:
      None{}

def a1.wide.cons4(+c: U32, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  a1.wide.put(Bool.and(U32.is_le(c, 1114111), Bool.not(a1.u8.in(c, 55296, 57343))), c, r)

def a1.ucs4(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      a1.wide.cons4(U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(a, 256), b), 256), c), 256), d), a1.ucs4(t))
    case _:
      None{}

# code points as text
def Asn1.points_text(cs: List<&2, U32>) -> String:
  match cs:
    case Nil{}:
      SNil{}
    case Con{c, t}:
      SCon{Chr{c}, Asn1.points_text(t)}

# the code points of a string's octets; None if they are not its type's
def a1.chars(k: Asn1StrKind, +xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match k:
    case Asn1Utf8{}:
      Asn1.utf8_decode(xs)
    case Asn1Bmp{}:
      a1.bmp(xs)
    case Asn1UniversalStr{}:
      a1.ucs4(xs)
    case Asn1Numeric{}:
      a1.ok_chars(a1.all_in(xs, Asn1Numeric{}), xs)
    case Asn1Printable{}:
      a1.ok_chars(a1.all_in(xs, Asn1Printable{}), xs)
    case Asn1Ia5{}:
      a1.ok_chars(a1.all_in(xs, Asn1Ia5{}), xs)
    case Asn1Visible{}:
      a1.ok_chars(a1.all_in(xs, Asn1Visible{}), xs)
    case Asn1Teletex{}:
      Some{xs}

def Asn1Str.chars(s: Asn1Str) -> Maybe<&2, List<&2, U32>>:
  match s:
    case Asn1Str{k, o}:
      a1.chars(k, B.Octets.to_list(o))

# the string's characters as text ("" if it is not valid)
def Asn1Str.text(s: Asn1Str) -> String:
  Asn1.points_text(Maybe.default(&2, List<&2, U32>, Asn1Str.chars(s), Nil{}))

def Asn1Str.valid(s: Asn1Str) -> Bool:
  Maybe.is_some(&2, List<&2, U32>, Asn1Str.chars(s))

# Elements

def Asn1.string(s: Asn1Str) -> N.Asn1Node:
  match s:
    case Asn1Str{k, o}:
      N.Asn1Prim{Asn1StrKind.tag(k), o}

def a1.text_points(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.to_u32(c), a1.text_points(t)}

# a UTF8String of text
def Asn1.utf8(s: String) -> N.Asn1Node:
  N.Asn1Prim{Asn1StrKind.tag(Asn1Utf8{}), B.Octets.of_list(Asn1.utf8_encode(a1.text_points(s)))}

def a1.str.mk(ok: Bool, k: Asn1StrKind, xs: List<&2, U32>) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match ok:
    case True{}:
      Done{N.Asn1Prim{Asn1StrKind.tag(k), B.Octets.of_list(xs)}}
    case False{}:
      Fail{E.Asn1BadString{}}

# a one-octet-per-character string of text (Asn1BadString for a character
# the type does not have)
def Asn1.text_string(+k: Asn1StrKind, s: String) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  +xs = a1.text_points(s)
  a1.str.mk(a1.all_in(xs, k), k, xs)

def a1.str.check.pick(ok: Bool, s: Asn1Str) -> Result<&2, &2, E.Asn1Error, Asn1Str>:
  match ok:
    case True{}:
      Done{s}
    case False{}:
      Fail{E.Asn1BadString{}}

def a1.str.check(+s: Asn1Str) -> Result<&2, &2, E.Asn1Error, Asn1Str>:
  a1.str.check.pick(Asn1Str.valid(s), s)

def a1.str.got(k: Asn1StrKind, r: Result<&2, &2, E.Asn1Error, B.Octets>) -> Result<&2, &2, E.Asn1Error, Asn1Str>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      a1.str.check(Asn1Str{k, o})

def a1.str.read(m: Maybe<&2, Asn1StrKind>, +r: R.Asn1Rules, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Str>:
  match m:
    case None{}:
      Fail{E.Asn1Unexpected{}}
    case Some{+k}:
      a1.str.got(k, P.a1.string_value(R.Asn1Rules.prim_strings(r), Asn1StrKind.tag(k), Asn1StrKind.tag(k), n))

# a character string element: its type and contents (BER segments joined),
# checked against the type's characters
def Asn1.get_string(+r: R.Asn1Rules, +n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Str>:
  a1.str.read(Asn1StrKind.of_tag(N.Asn1Node.tag(n)), r, n)

# a character string element of one type (an IMPLICIT tag t, contents of
# type k)
def Asn1.get_string_as(+r: R.Asn1Rules, +t: T.Asn1Tag, +k: Asn1StrKind, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Str>:
  a1.str.got(k, P.a1.string_value(R.Asn1Rules.prim_strings(r), t, Asn1StrKind.tag(k), n))
