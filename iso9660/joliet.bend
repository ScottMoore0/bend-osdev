# bend-osdev-iso9660, joliet.bend: the Joliet extension (Microsoft, "Joliet
# Specification", 1995). A Joliet volume has a supplementary volume
# descriptor whose escape sequences field (ECMA-119 8.5.6) starts with
# "%/@" (level 1), "%/C" (level 2) or "%/E" (level 3); its identifiers,
# and the file identifiers of the directory hierarchy it points to, are
# UCS-2, each character two bytes, most significant byte first.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ./fields.bend as F

def iso.joliet.pick(a: Bool, b: Bool, c: Bool) -> Nat:
  match a b c:
    case True{} _ _:
      1n
    case False{} True{} _:
      2n
    case False{} False{} True{}:
      3n
    case False{} False{} False{}:
      0n

def iso.joliet.level3(c: Maybe<&2, U32>) -> Nat:
  match c:
    case Some{+x}:
      iso.joliet.pick(U32.is_eq(x, 64), U32.is_eq(x, 67), U32.is_eq(x, 69))
    case None{}:
      0n

def iso.joliet.lead(ok: Bool, c: Maybe<&2, U32>) -> Nat:
  match ok:
    case True{}:
      iso.joliet.level3(c)
    case False{}:
      0n

def iso.joliet.is(m: Maybe<&2, U32>, v: U32) -> Bool:
  match m:
    case Some{x}:
      U32.is_eq(x, v)
    case None{}:
      False{}

# the Joliet level (1, 2 or 3) of a supplementary descriptor's 32-byte escape
# sequences field, or 0 if it is not Joliet
def Iso.joliet_level(escapes: B.Octets) -> Nat:
  +xs = B.Octets.to_list(escapes)
  iso.joliet.lead(Bool.and(iso.joliet.is(B.at(xs, 0n), 37), iso.joliet.is(B.at(xs, 1n), 47)), B.at(xs, 2n))

# UCS-2, most significant byte first

def iso.ucs2.cons(c: Maybe<&2, U32>, r: Result<&2, &2, F.IsoError, String>) -> Result<&2, &2, F.IsoError, String>:
  match c r:
    case Some{x} Done{s}:
      Done{SCon{Chr{x}, s}}
    case _ Fail{e}:
      Fail{e}
    case None{} Done{s}:
      Fail{F.IsoTruncated{}}

# the characters of a UCS-2 byte list; an odd byte at the end is refused
def iso.ucs2.list(xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, String>:
  match xs:
    case Nil{}:
      Done{SNil{}}
    case Con{a, Nil{}}:
      Fail{F.IsoBadJolietName{}}
    case Con{a, Con{b, t}}:
      iso.ucs2.cons(B.be16.head([a, b]), iso.ucs2.list(t))

def iso.ucs2.bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      B.append(B.be16(c), iso.ucs2.bytes(t))

# a UCS-2 identifier as text, one character per code unit
def Iso.ucs2_decode(o: B.Octets) -> Result<&2, &2, F.IsoError, String>:
  iso.ucs2.list(B.Octets.to_list(o))

# a text as UCS-2 (each character's code to 16 bits)
def Iso.ucs2_encode(s: String) -> B.Octets:
  B.Octets.of_list(iso.ucs2.bytes(s))

# the text as UCS-2 stores it: each character's code to 16 bits
def Iso.ucs2_norm(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, t}:
      SCon{Chr{B.low16(c)}, Iso.ucs2_norm(t)}

# a UCS-2 text field (a volume identifier) with trailing spaces and NULs
# dropped; malformed text gives the empty string
def iso.ucs2.trim(s: String) -> String:
  String.trim_end(s)

def Iso.ucs2_text(o: B.Octets) -> String:
  iso.ucs2.trim(Result.default(&2, &2, F.IsoError, String, Iso.ucs2_decode(o), ""))
