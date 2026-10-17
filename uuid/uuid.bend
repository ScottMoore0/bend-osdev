# bend-osdev-uuid: universally unique identifiers (RFC 9562, "Universally
# Unique IDentifiers (UUIDs)", May 2024, which obsoletes RFC 4122).
#
# A Uuid holds its 16 octets in the RFC's order (network byte order: octet 0
# is the most significant). Each octet is a Word(8n), so a Uuid can never hold
# a value above 255. The text form is 8-4-4-4-12 hex digits (RFC 9562 section
# 4): read in either case, written in lower case.
#
# GPT, and Microsoft's GUID structure generally, store the first three fields
# (time_low, time_mid, time_hi_and_version) least significant byte first and
# the last eight octets as they are: to_guid and from_guid convert. This is
# the layout Python's uuid.UUID.bytes_le gives.
#
# The public interface is listed in README.md; everything else (the Uuid
# constructor, the octet and list helpers) is internal.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

type Uuid is Data:
  Uuid{b0: Word(8n), b1: Word(8n), b2: Word(8n), b3: Word(8n), b4: Word(8n), b5: Word(8n), b6: Word(8n), b7: Word(8n), b8: Word(8n), b9: Word(8n), b10: Word(8n), b11: Word(8n), b12: Word(8n), b13: Word(8n), b14: Word(8n), b15: Word(8n)}

# The variant field (RFC 9562 section 4.1): the top bits of octet 8
type UuidVariant is Data:
  UuidNcs{}
  UuidRfc{}
  UuidMicrosoft{}
  UuidFuture{}

# Octets

# the octets in RFC order
def Uuid.octets(u: Uuid) -> List<&2, Word(8n)>:
  match u:
    case Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}:
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]

# the Uuid with these octets, if there are exactly 16
def Uuid.of_octets(xs: List<&2, Word(8n)>) -> Maybe<&2, Uuid>:
  match xs:
    case Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, Con{b8, Con{b9, Con{b10, Con{b11, Con{b12, Con{b13, Con{b14, Con{b15, Nil{}}}}}}}}}}}}}}}}}:
      Some{Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}}
    case _:
      None{}

def Uuid.nil() -> Uuid:
  Uuid{Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)}

def Uuid.max() -> Uuid:
  +o = B.bits8(255)
  Uuid{o, o, o, o, o, o, o, o, o, o, o, o, o, o, o, o}

# Errors

type UuidError is Data:
  UuidBadLength{}
  UuidBadDash{}
  UuidBadDigit{}

def UuidError.show(e: UuidError) -> String:
  match e:
    case UuidBadLength{}:
      "bad length"
    case UuidBadDash{}:
      "missing dash"
    case UuidBadDigit{}:
      "bad digit"

# Byte strings

def Uuid.to_list(u: Uuid) -> List<&2, U32>:
  match u:
    case Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}:
      [B.of_bits8(b0), B.of_bits8(b1), B.of_bits8(b2), B.of_bits8(b3), B.of_bits8(b4), B.of_bits8(b5), B.of_bits8(b6), B.of_bits8(b7), B.of_bits8(b8), B.of_bits8(b9), B.of_bits8(b10), B.of_bits8(b11), B.of_bits8(b12), B.of_bits8(b13), B.of_bits8(b14), B.of_bits8(b15)]

def Uuid.guid_list(u: Uuid) -> List<&2, U32>:
  match u:
    case Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}:
      [B.of_bits8(b3), B.of_bits8(b2), B.of_bits8(b1), B.of_bits8(b0), B.of_bits8(b5), B.of_bits8(b4), B.of_bits8(b7), B.of_bits8(b6), B.of_bits8(b8), B.of_bits8(b9), B.of_bits8(b10), B.of_bits8(b11), B.of_bits8(b12), B.of_bits8(b13), B.of_bits8(b14), B.of_bits8(b15)]

def Uuid.of_list(xs: List<&2, U32>) -> Maybe<&2, Uuid>:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}:
      Some{Uuid{B.bits8(a0), B.bits8(a1), B.bits8(a2), B.bits8(a3), B.bits8(a4), B.bits8(a5), B.bits8(a6), B.bits8(a7), B.bits8(a8), B.bits8(a9), B.bits8(a10), B.bits8(a11), B.bits8(a12), B.bits8(a13), B.bits8(a14), B.bits8(a15)}}
    case _:
      None{}

def Uuid.of_guid_list(xs: List<&2, U32>) -> Maybe<&2, Uuid>:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}:
      Some{Uuid{B.bits8(a3), B.bits8(a2), B.bits8(a1), B.bits8(a0), B.bits8(a5), B.bits8(a4), B.bits8(a7), B.bits8(a6), B.bits8(a8), B.bits8(a9), B.bits8(a10), B.bits8(a11), B.bits8(a12), B.bits8(a13), B.bits8(a14), B.bits8(a15)}}
    case _:
      None{}

def Uuid.length_ok(m: Maybe<&2, Uuid>) -> Result<&2, &2, UuidError, Uuid>:
  match m:
    case Some{u}:
      Done{u}
    case None{}:
      Fail{UuidBadLength{}}

# The GUID layout on lists (the list layer, for packages that work on
# List<&2, U32>): the 16 bytes, and the Uuid of exactly 16 (each element
# masked to 8 bits)
def Uuid.to_guid_list(u: Uuid) -> List<&2, U32>:
  Uuid.guid_list(u)

def Uuid.from_guid_list(xs: List<&2, U32>) -> Result<&2, &2, UuidError, Uuid>:
  Uuid.length_ok(Uuid.of_guid_list(xs))

# the 16 bytes in RFC order
def Uuid.to_bytes(u: Uuid) -> B.Octets:
  B.Octets.of_list(Uuid.to_list(u))

# the Uuid of exactly 16 bytes in RFC order
def Uuid.from_bytes(o: B.Octets) -> Result<&2, &2, UuidError, Uuid>:
  Uuid.length_ok(Uuid.of_list(B.Octets.to_list(o)))

# the 16 bytes in the mixed-endian GUID layout GPT stores
def Uuid.to_guid(u: Uuid) -> B.Octets:
  B.Octets.of_list(Uuid.to_guid_list(u))

# the Uuid of exactly 16 bytes in the GUID layout
def Uuid.from_guid(o: B.Octets) -> Result<&2, &2, UuidError, Uuid>:
  Uuid.from_guid_list(B.Octets.to_list(o))

# field readers: the 16 bytes at offset i, in RFC order or in the GUID
# layout (None if the string is too short)
def Uuid.from_bytes_at(o: B.Octets, i: Nat) -> Maybe<&2, Uuid>:
  Uuid.of_list(B.Octets.to_list(B.Octets.slice(i, 16n, o)))

def Uuid.from_guid_at(o: B.Octets, i: Nat) -> Maybe<&2, Uuid>:
  Uuid.of_guid_list(B.Octets.to_list(B.Octets.slice(i, 16n, o)))

# Byte by byte

# the UUID whose 16 bytes, in RFC order, are these (each masked to 8 bits)
def Uuid.make(a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32, a6: U32, a7: U32, a8: U32, a9: U32, a10: U32, a11: U32, a12: U32, a13: U32, a14: U32, a15: U32) -> Uuid:
  Uuid{B.bits8(a0), B.bits8(a1), B.bits8(a2), B.bits8(a3), B.bits8(a4), B.bits8(a5), B.bits8(a6), B.bits8(a7), B.bits8(a8), B.bits8(a9), B.bits8(a10), B.bits8(a11), B.bits8(a12), B.bits8(a13), B.bits8(a14), B.bits8(a15)}

# byte i (0 to 15) in RFC order; 0 past the end
def Uuid.byte(u: Uuid, i: Nat) -> U32:
  Maybe.default(&2, U32, B.at(Uuid.to_list(u), i), 0)

# Comparing

def Uuid.is_eq(a: Uuid, b: Uuid) -> Bool:
  B.Octets.is_eq(Uuid.to_bytes(a), Uuid.to_bytes(b))

def Uuid.is_nil(u: Uuid) -> Bool:
  Uuid.is_eq(u, Uuid.nil())

# Version and variant (RFC 9562 sections 4.1 and 4.2)

# the version field: the high four bits of octet 6 (meaningful when the
# variant is UuidRfc)
def Uuid.version(u: Uuid) -> U32:
  match u:
    case Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}:
      U32.shrn(B.of_bits8(b6), 4n)

def Uuid.variant.c(lt: Bool) -> UuidVariant:
  match lt:
    case True{}:
      UuidMicrosoft{}
    case False{}:
      UuidFuture{}

def Uuid.variant.b(lt: Bool, +v: U32) -> UuidVariant:
  match lt:
    case True{}:
      UuidRfc{}
    case False{}:
      Uuid.variant.c(U32.is_lt(v, 224))

def Uuid.variant.a(lt: Bool, +v: U32) -> UuidVariant:
  match lt:
    case True{}:
      UuidNcs{}
    case False{}:
      Uuid.variant.b(U32.is_lt(v, 192), v)

# 0xx: NCS; 10x: this RFC; 110: Microsoft; 111: reserved for the future
def Uuid.variant(u: Uuid) -> UuidVariant:
  match u:
    case Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}:
      +v = B.of_bits8(b8)
      Uuid.variant.a(U32.is_lt(v, 128), v)

def UuidVariant.show(v: UuidVariant) -> String:
  match v:
    case UuidNcs{}:
      "ncs"
    case UuidRfc{}:
      "rfc9562"
    case UuidMicrosoft{}:
      "microsoft"
    case UuidFuture{}:
      "future"

# Text: writing

def Uuid.nibble.hi(b: Word(8n)) -> Word(4n):
  W.W64.bits.hi(4n, 4n, b)

def Uuid.nibble.lo(b: Word(8n)) -> Word(4n):
  W.W64.bits.lo(4n, 4n, b)

# the lower-case hex digit of a nibble
def Uuid.hexdigit(n: Word(4n)) -> Char:
  B.hex.digit(U32{W.W64.bits.cat(4n, 28n, n, Word.zero(28n))})

# two hex digits per octet, high nibble first
def Uuid.digits(bs: List<&2, Word(8n)>) -> List<&2, Char>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+b, t}:
      Con{Uuid.hexdigit(Uuid.nibble.hi(b)), Con{Uuid.hexdigit(Uuid.nibble.lo(b)), Uuid.digits(t)}}

# 32 hex digits, with the dashes of the 8-4-4-4-12 form
def Uuid.show.dashes(cs: List<&2, Char>) -> String:
  match cs:
    case Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, Con{c8, Con{c9, Con{c10, Con{c11, Con{c12, Con{c13, Con{c14, Con{c15, Con{c16, Con{c17, Con{c18, Con{c19, Con{c20, Con{c21, Con{c22, Con{c23, Con{c24, Con{c25, Con{c26, Con{c27, Con{c28, Con{c29, Con{c30, Con{c31, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      SCon{c0, SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{'-', SCon{c8, SCon{c9, SCon{c10, SCon{c11, SCon{'-', SCon{c12, SCon{c13, SCon{c14, SCon{c15, SCon{'-', SCon{c16, SCon{c17, SCon{c18, SCon{c19, SCon{'-', SCon{c20, SCon{c21, SCon{c22, SCon{c23, SCon{c24, SCon{c25, SCon{c26, SCon{c27, SCon{c28, SCon{c29, SCon{c30, SCon{c31, SNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
    case _:
      SNil{}

# the 36-character text form, in lower case
def Uuid.show(u: Uuid) -> String:
  Uuid.show.dashes(Uuid.digits(Uuid.octets(u)))

# Text: reading

def Uuid.hexval.word(x: U32) -> Word(4n):
  match x:
    case U32{w}:
      W.W64.bits.lo(4n, 28n, w)

def Uuid.hexval.upper(ok: Bool, x: U32) -> Maybe<&2, Word(4n)>:
  match ok:
    case True{}:
      Some{Uuid.hexval.word(U32.sub(x, 55))}
    case False{}:
      None{}

def Uuid.hexval.lower(ok: Bool, +x: U32) -> Maybe<&2, Word(4n)>:
  match ok:
    case True{}:
      Some{Uuid.hexval.word(U32.sub(x, 87))}
    case False{}:
      Uuid.hexval.upper(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70)), x)

def Uuid.hexval.digit(ok: Bool, +x: U32) -> Maybe<&2, Word(4n)>:
  match ok:
    case True{}:
      Some{Uuid.hexval.word(U32.sub(x, 48))}
    case False{}:
      Uuid.hexval.lower(Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)), x)

# the value of a hex digit, in either case
def Uuid.hexval(c: Char) -> Maybe<&2, Word(4n)>:
  match c:
    case Chr{+x}:
      Uuid.hexval.digit(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), x)

def Uuid.hexval.join(h: Maybe<&2, Word(4n)>, l: Maybe<&2, Word(4n)>) -> Maybe<&2, Word(8n)>:
  match h l:
    case Some{a} Some{b}:
      Some{W.W64.bits.cat(4n, 4n, b, a)}
    case _ _:
      None{}

# the octet of two hex digits, high nibble first
def Uuid.rdbyte(c1: Char, c2: Char) -> Maybe<&2, Word(8n)>:
  Uuid.hexval.join(Uuid.hexval(c1), Uuid.hexval(c2))

def Uuid.cons_m(m: Maybe<&2, Word(8n)>, r: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, List<&2, Word(8n)>>:
  match m r:
    case Some{b} Some{bs}:
      Some{Con{b, bs}}
    case _ _:
      None{}

# the octets of an even number of hex digits
def Uuid.hexlist(cs: List<&2, Char>) -> Maybe<&2, List<&2, Word(8n)>>:
  match cs:
    case Nil{}:
      Some{Nil{}}
    case Con{c1, Con{c2, t}}:
      Uuid.cons_m(Uuid.rdbyte(c1, c2), Uuid.hexlist(t))
    case _:
      None{}

def Uuid.is_dash(c: Char) -> Bool:
  Char.is_eq(c, '-')

def Uuid.strip.check(ok: Bool, cs: List<&2, Char>) -> Result<&2, &2, UuidError, List<&2, Char>>:
  match ok:
    case True{}:
      Done{cs}
    case False{}:
      Fail{UuidBadDash{}}

# the 32 digits of a 36-character string with dashes at 8, 13, 18 and 23
def Uuid.strip(s: String) -> Result<&2, &2, UuidError, List<&2, Char>>:
  match s:
    case SCon{c0, SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, SCon{c10, SCon{c11, SCon{c12, SCon{c13, SCon{c14, SCon{c15, SCon{c16, SCon{c17, SCon{c18, SCon{c19, SCon{c20, SCon{c21, SCon{c22, SCon{c23, SCon{c24, SCon{c25, SCon{c26, SCon{c27, SCon{c28, SCon{c29, SCon{c30, SCon{c31, SCon{c32, SCon{c33, SCon{c34, SCon{c35, SNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Uuid.strip.check(Bool.and(Uuid.is_dash(c8), Bool.and(Uuid.is_dash(c13), Bool.and(Uuid.is_dash(c18), Uuid.is_dash(c23)))), [c0, c1, c2, c3, c4, c5, c6, c7, c9, c10, c11, c12, c14, c15, c16, c17, c19, c20, c21, c22, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35])
    case _:
      Fail{UuidBadLength{}}

def Uuid.of_digits(m: Maybe<&2, List<&2, Word(8n)>>) -> Result<&2, &2, UuidError, Uuid>:
  match m:
    case Some{bs}:
      Uuid.length_ok(Uuid.of_octets(bs))
    case None{}:
      Fail{UuidBadDigit{}}

def Uuid.parse.go(r: Result<&2, &2, UuidError, List<&2, Char>>) -> Result<&2, &2, UuidError, Uuid>:
  match r:
    case Done{cs}:
      Uuid.of_digits(Uuid.hexlist(cs))
    case Fail{e}:
      Fail{e}

# the Uuid of the 36-character text form, in either case
def Uuid.parse(s: String) -> Result<&2, &2, UuidError, Uuid>:
  Uuid.parse.go(Uuid.strip(s))
