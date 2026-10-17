# bend-osdev-bytes: byte strings, and the fixed-width fields that formats store
# in them.
#
# A byte string is a List<&2, U32> whose elements are 0 to 255 (the shape Base's
# own I/O uses). Readers take the low 8 bits of each element, so a malformed
# element is masked, never trusted.
#
# The field readers and writers work on bits (slicing and joining words), not
# with shifts and masks, so that their round trips can be proved for every
# value. That costs speed: use them for header fields, not bulk data.
import Base
import ../word64/word64.bend as W

# Bytes and bits

# the low 8 bits of a word, as bits
def bits8(b: U32) -> Word(8n):
  match b:
    case U32{w}:
      W.W64.bits.lo(8n, 24n, w)

# the byte (0 to 255) with these 8 bits
def of_bits8(s: Word(8n)) -> U32:
  U32{W.W64.bits.cat(8n, 24n, s, Word.zero(24n))}

# the byte of a word: its low 8 bits
def byte(b: U32) -> U32:
  of_bits8(bits8(b))

# List operations

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

# the first n bytes (all of them if there are fewer)
def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, take(p, t)}

# all but the first n bytes
def drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          drop(p, t)

def append(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

# n zero bytes
def zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{0, zeros(p)}

# the byte at offset i, if there is one
def at.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{h, t}:
      Some{byte(h)}
    case Nil{}:
      None{}

def at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  at.head(drop(i, xs))

# Fields: writing (each answers its bytes, in storage order)

# the low 16 bits of a word
def low16(v: U32) -> U32:
  match v:
    case U32{w}:
      U32{W.W64.bits.cat(16n, 16n, W.W64.bits.lo(16n, 16n, w), Word.zero(16n))}

def le16(v: U32) -> List<&2, U32>:
  match v:
    case U32{w}:
      +lo = W.W64.bits.lo(16n, 16n, w)
      [of_bits8(W.W64.bits.lo(8n, 8n, lo)), of_bits8(W.W64.bits.hi(8n, 8n, lo))]

def be16(v: U32) -> List<&2, U32>:
  match v:
    case U32{w}:
      +lo = W.W64.bits.lo(16n, 16n, w)
      [of_bits8(W.W64.bits.hi(8n, 8n, lo)), of_bits8(W.W64.bits.lo(8n, 8n, lo))]

# the four bytes of a word, least significant first
def le32(+v: U32) -> List<&2, U32>:
  match v:
    case U32{w}:
      +r1 = W.W64.bits.hi(8n, 24n, w)
      +r2 = W.W64.bits.hi(8n, 16n, r1)
      [of_bits8(W.W64.bits.lo(8n, 24n, w)), of_bits8(W.W64.bits.lo(8n, 16n, r1)), of_bits8(W.W64.bits.lo(8n, 8n, r2)), of_bits8(W.W64.bits.hi(8n, 8n, r2))]

def be32.rev(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      [d, c, b, a]
    case _:
      Nil{}

def be32(v: U32) -> List<&2, U32>:
  be32.rev(le32(v))

def le64(+v: W.W64) -> List<&2, U32>:
  append(le32(W.W64.lo(v)), le32(W.W64.hi(v)))

def be64(+v: W.W64) -> List<&2, U32>:
  append(be32(W.W64.hi(v)), be32(W.W64.lo(v)))

# Fields: reading at the head of a byte string

def le16.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, t}}:
      Some{U32{W.W64.bits.cat(16n, 16n, W.W64.bits.cat(8n, 8n, bits8(a), bits8(b)), Word.zero(16n))}}
    case _:
      None{}

def be16.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, t}}:
      Some{U32{W.W64.bits.cat(16n, 16n, W.W64.bits.cat(8n, 8n, bits8(b), bits8(a)), Word.zero(16n))}}
    case _:
      None{}

def le32.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Some{U32{W.W64.bits.cat(8n, 24n, bits8(a), W.W64.bits.cat(8n, 16n, bits8(b), W.W64.bits.cat(8n, 8n, bits8(c), bits8(d))))}}
    case _:
      None{}

def be32.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Some{U32{W.W64.bits.cat(8n, 24n, bits8(d), W.W64.bits.cat(8n, 16n, bits8(c), W.W64.bits.cat(8n, 8n, bits8(b), bits8(a))))}}
    case _:
      None{}

def le64.join(lo: Maybe<&2, U32>, hi: Maybe<&2, U32>) -> Maybe<&2, W.W64>:
  match lo hi:
    case Some{l} Some{h}:
      Some{W.W64.from_parts(h, l)}
    case _ _:
      None{}

# Fields: reading at an offset (None if the string is too short)

def le16_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  le16.head(drop(i, xs))

def be16_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  be16.head(drop(i, xs))

def le32_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  le32.head(drop(i, xs))

def be32_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  be32.head(drop(i, xs))

def le64_at(+xs: List<&2, U32>, +i: Nat) -> Maybe<&2, W.W64>:
  le64.join(le32_at(xs, i), le32_at(xs, Nat.add(i, 4n)))

def be64_at(+xs: List<&2, U32>, +i: Nat) -> Maybe<&2, W.W64>:
  le64.join(be32_at(xs, Nat.add(i, 4n)), be32_at(xs, i))

# Text

def of_string(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{byte(c), of_string(t)}

def to_string(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      SCon{Chr{byte(h)}, to_string(t)}

def hex.digit.pick(lt: Bool, d: U32) -> Char:
  match lt:
    case True{}:
      Chr{U32.add(48, d)}
    case False{}:
      Chr{U32.add(87, d)}

def hex.digit(+d: U32) -> Char:
  hex.digit.pick(U32.is_lt(d, 10), d)

# two lower-case hex digits per byte
def hex(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      +b = byte(h)
      SCon{hex.digit(U32.shrn(b, 4n)), SCon{hex.digit(U32.and(b, 15)), hex(t)}}

# The list layer, tail-recursive. Bend 2.0.37's runtime overflows its stack
# at some tens of thousands of nested non-tail calls, so the structural forms
# above cannot run on long lists; these build their answer in an accumulator
# (reversed where order matters). Each is proved equal to its structural form
# for every input (LAWS.bend: *_fast), so code can run these while proofs
# reason about the structural forms.

def rev_onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev_onto(t, Con{h, acc})

def rev(xs: List<&2, U32>) -> List<&2, U32>:
  rev_onto(xs, Nil{})

def len.go(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      len.go(t, 1n+n)

def len.fast(xs: List<&2, U32>) -> Nat:
  len.go(xs, 0n)

def take.go(n: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Nil{}:
          acc
        case Con{h, t}:
          take.go(p, t, Con{h, acc})

def take.fast(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  rev(take.go(n, xs, Nil{}))

def append.fast(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  rev_onto(rev(xs), ys)

def zeros.go(n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      zeros.go(p, Con{0, acc})

def zeros.fast(n: Nat) -> List<&2, U32>:
  zeros.go(n, Nil{})

def of_string.go(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{c}, t}:
      of_string.go(t, Con{byte(c), acc})

def of_string.fast(s: String) -> List<&2, U32>:
  rev(of_string.go(s, Nil{}))

# the string of xs's bytes in front of acc (structural; the laws' form)
def to_string.cat(xs: List<&2, U32>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      SCon{Chr{byte(h)}, to_string.cat(t, acc)}

def to_string.go(rs: List<&2, U32>, acc: String) -> String:
  match rs:
    case Nil{}:
      acc
    case Con{h, t}:
      to_string.go(t, SCon{Chr{byte(h)}, acc})

def to_string.fast(xs: List<&2, U32>) -> String:
  to_string.go(rev(xs), SNil{})

def hex.cat(xs: List<&2, U32>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      +b = byte(h)
      SCon{hex.digit(U32.shrn(b, 4n)), SCon{hex.digit(U32.and(b, 15)), hex.cat(t, acc)}}

def hex.go(rs: List<&2, U32>, acc: String) -> String:
  match rs:
    case Nil{}:
      acc
    case Con{h, t}:
      +b = byte(h)
      hex.go(t, SCon{hex.digit(U32.shrn(b, 4n)), SCon{hex.digit(U32.and(b, 15)), acc}})

def hex.fast(xs: List<&2, U32>) -> String:
  hex.go(rev(xs), SNil{})

# Octets: the byte-string interface
#
# Public interfaces take and answer Octets. Its representation is internal:
# other packages use only the Octets.* defs below and, in proofs, this
# package's laws, never the constructor. Today an Octets is a list of 8-bit
# words, so every value of the type is a valid byte string (no element can
# be 256 or more), which is what makes laws like of_list(to_list(o)) == o
# hold for every o.

type Octets is Data:
  Octets{words: List<&2, Word(8n)>}

# masking every element of a list to 8 bits (the list layer's view)
def mask(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{byte(h), mask(t)}

def list_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, s} Con{b, t}:
      Bool.and(U32.is_eq(a, b), list_eq(s, t))
    case _ _:
      False{}

def mask.go(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      mask.go(t, Con{byte(h), acc})

# mask, tail-recursive (LAWS.bend: mask_fast)
def mask.fast(xs: List<&2, U32>) -> List<&2, U32>:
  rev(mask.go(xs, Nil{}))

def list_eq.go(xs: List<&2, U32>, ys: List<&2, U32>, ok: Bool) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      ok
    case Con{a, s} Con{b, t}:
      list_eq.go(s, t, Bool.and(ok, U32.is_eq(a, b)))
    case _ _:
      False{}

# list_eq, tail-recursive; every element is compared (LAWS.bend: list_eq_fast)
def list_eq.fast(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  list_eq.go(xs, ys, True{})

# Word lists: the operations Octets is built from

def w8s.of_list(xs: List<&2, U32>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{bits8(h), w8s.of_list(t)}

def w8s.to_list(ws: List<&2, Word(8n)>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{of_bits8(h), w8s.to_list(t)}

def w8s.take(n: Nat, ws: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match ws:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, w8s.take(p, t)}

def w8s.drop(n: Nat, ws: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match n:
    case 0n:
      ws
    case 1n+p:
      match ws:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          w8s.drop(p, t)

def w8s.zeros(n: Nat) -> List<&2, Word(8n)>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{Word.zero(8n), w8s.zeros(p)}

def w8s.at(ws: List<&2, Word(8n)>) -> Maybe<&2, U32>:
  match ws:
    case Con{h, t}:
      Some{of_bits8(h)}
    case Nil{}:
      None{}

# The same operations, tail-recursive: what Octets runs. Bend 2.0.37's
# runtime overflows its stack at a depth of some tens of thousands of nested
# non-tail calls, so the structural forms above, which the proofs reason
# about, cannot run on long strings. Each form here builds its answer in an
# accumulator (reversed where order matters) and is proved equal to its
# structural form for every input (PROOF.bend: *_fast).

def w8s.rev_onto(ws: List<&2, Word(8n)>, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match ws:
    case Nil{}:
      acc
    case Con{h, t}:
      w8s.rev_onto(t, Con{h, acc})

def w8s.of_list.go(xs: List<&2, U32>, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      w8s.of_list.go(t, Con{bits8(h), acc})

def w8s.of_list.fast(xs: List<&2, U32>) -> List<&2, Word(8n)>:
  w8s.rev_onto(w8s.of_list.go(xs, Nil{}), Nil{})

def w8s.to_list.go(ws: List<&2, Word(8n)>, acc: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      acc
    case Con{h, t}:
      w8s.to_list.go(t, Con{of_bits8(h), acc})

def w8s.to_list.fast(ws: List<&2, Word(8n)>) -> List<&2, U32>:
  rev_onto(w8s.to_list.go(ws, Nil{}), Nil{})

def w8s.take.go(n: Nat, ws: List<&2, Word(8n)>, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match n:
    case 0n:
      acc
    case 1n+p:
      match ws:
        case Nil{}:
          acc
        case Con{h, t}:
          w8s.take.go(p, t, Con{h, acc})

def w8s.take.fast(n: Nat, ws: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  w8s.rev_onto(w8s.take.go(n, ws, Nil{}), Nil{})

def w8s.append.fast(xs: List<&2, Word(8n)>, ys: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  w8s.rev_onto(w8s.rev_onto(xs, Nil{}), ys)

def w8s.len.go(ws: List<&2, Word(8n)>, n: Nat) -> Nat:
  match ws:
    case Nil{}:
      n
    case Con{h, t}:
      w8s.len.go(t, 1n+n)

def w8s.len.fast(ws: List<&2, Word(8n)>) -> Nat:
  w8s.len.go(ws, 0n)

def w8s.zeros.go(n: Nat, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match n:
    case 0n:
      acc
    case 1n+p:
      w8s.zeros.go(p, Con{Word.zero(8n), acc})

def w8s.zeros.fast(n: Nat) -> List<&2, Word(8n)>:
  w8s.zeros.go(n, Nil{})

# whether two word lists are equal; every word is compared (no early exit)
def w8s.eq(xs: List<&2, Word(8n)>, ys: List<&2, Word(8n)>, ok: Bool) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      ok
    case Con{a, s} Con{b, t}:
      w8s.eq(s, t, Bool.and(ok, Cmp.is_eq(Word.cmp(8n, a, b))))
    case _ _:
      False{}

# text and hex, built from the last byte back (rs is the string reversed)
def w8s.text.go(rs: List<&2, Word(8n)>, acc: String) -> String:
  match rs:
    case Nil{}:
      acc
    case Con{h, t}:
      w8s.text.go(t, SCon{Chr{of_bits8(h)}, acc})

def w8s.hex.go(rs: List<&2, Word(8n)>, acc: String) -> String:
  match rs:
    case Nil{}:
      acc
    case Con{h, t}:
      +b = of_bits8(h)
      w8s.hex.go(t, SCon{hex.digit(U32.shrn(b, 4n)), SCon{hex.digit(U32.and(b, 15)), acc}})

# Conversions: of_list masks every element to 8 bits

def Octets.of_list(xs: List<&2, U32>) -> Octets:
  Octets{w8s.of_list.fast(xs)}

def Octets.to_list(o: Octets) -> List<&2, U32>:
  match o:
    case Octets{ws}:
      w8s.to_list.fast(ws)

def Octets.of_string(s: String) -> Octets:
  Octets.of_list(of_string(s))

def Octets.to_string(o: Octets) -> String:
  match o:
    case Octets{ws}:
      w8s.text.go(w8s.rev_onto(ws, Nil{}), SNil{})

def Octets.hex(o: Octets) -> String:
  match o:
    case Octets{ws}:
      w8s.hex.go(w8s.rev_onto(ws, Nil{}), SNil{})

# Building and slicing

def Octets.empty() -> Octets:
  Octets{Nil{}}

def Octets.zeros(n: Nat) -> Octets:
  Octets{w8s.zeros.fast(n)}

# a byte (the low 8 bits of b) in front of o
def Octets.cons(b: U32, o: Octets) -> Octets:
  match o:
    case Octets{ws}:
      Octets{Con{bits8(b), ws}}

def Octets.append(a: Octets, b: Octets) -> Octets:
  match a b:
    case Octets{xs} Octets{ys}:
      Octets{w8s.append.fast(xs, ys)}

# concat as the laws state it: each piece in front of the rest
def Octets.concat.ref(os: List<&2, Octets>) -> Octets:
  match os:
    case Nil{}:
      Octets.empty()
    case Con{h, t}:
      Octets.append(h, Octets.concat.ref(t))

# every piece's words pushed, reversed, onto acc
def w8s.concat.go(os: List<&2, Octets>, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match os:
    case Nil{}:
      acc
    case Con{Octets{ws}, t}:
      w8s.concat.go(t, w8s.rev_onto(ws, acc))

# the pieces joined in order, tail-recursive (LAWS.bend: octets_concat_*)
def Octets.concat(os: List<&2, Octets>) -> Octets:
  Octets{w8s.rev_onto(w8s.concat.go(os, Nil{}), Nil{})}

# the words of an Octets (internal; for the proofs)
def Octets.words(o: Octets) -> List<&2, Word(8n)>:
  match o:
    case Octets{ws}:
      ws

def Octets.len(o: Octets) -> Nat:
  match o:
    case Octets{ws}:
      w8s.len.fast(ws)

def Octets.take(n: Nat, o: Octets) -> Octets:
  match o:
    case Octets{ws}:
      Octets{w8s.take.fast(n, ws)}

def Octets.drop(n: Nat, o: Octets) -> Octets:
  match o:
    case Octets{ws}:
      Octets{w8s.drop(n, ws)}

# the n bytes at offset i (fewer if o ends first)
def Octets.slice(+i: Nat, n: Nat, o: Octets) -> Octets:
  Octets.take(n, Octets.drop(i, o))

# a byte string cut in two
type OctetsSplit is Data:
  OctetsSplit{head: Octets, rest: Octets}

def Octets.split_at.pick(fits: Bool, +n: Nat, +o: Octets) -> Maybe<&2, OctetsSplit>:
  match fits:
    case True{}:
      Some{OctetsSplit{Octets.take(n, o), Octets.drop(n, o)}}
    case False{}:
      None{}

# the first n bytes and the rest, or None if o has fewer than n bytes
def Octets.split_at(+n: Nat, +o: Octets) -> Maybe<&2, OctetsSplit>:
  Octets.split_at.pick(Nat.is_le(n, Octets.len(o)), n, o)

def Octets.is_eq(a: Octets, b: Octets) -> Bool:
  match a b:
    case Octets{xs} Octets{ys}:
      w8s.eq(xs, ys, True{})

def Octets.at(o: Octets, i: Nat) -> Maybe<&2, U32>:
  match o:
    case Octets{ws}:
      w8s.at(w8s.drop(i, ws))

# Fields: written as bytes, read through the list layer over just the
# bytes a field needs (a read walks to its offset, never past it)

def Octets.le16(v: U32) -> Octets:
  Octets.of_list(le16(v))

def Octets.be16(v: U32) -> Octets:
  Octets.of_list(be16(v))

def Octets.le32(v: U32) -> Octets:
  Octets.of_list(le32(v))

def Octets.be32(v: U32) -> Octets:
  Octets.of_list(be32(v))

def Octets.le64(v: W.W64) -> Octets:
  Octets.of_list(le64(v))

def Octets.be64(v: W.W64) -> Octets:
  Octets.of_list(be64(v))

def Octets.field(+i: Nat, n: Nat, o: Octets) -> List<&2, U32>:
  Octets.to_list(Octets.slice(i, n, o))

def Octets.le16_at(o: Octets, +i: Nat) -> Maybe<&2, U32>:
  le16.head(Octets.field(i, 2n, o))

def Octets.be16_at(o: Octets, +i: Nat) -> Maybe<&2, U32>:
  be16.head(Octets.field(i, 2n, o))

def Octets.le32_at(o: Octets, +i: Nat) -> Maybe<&2, U32>:
  le32.head(Octets.field(i, 4n, o))

def Octets.be32_at(o: Octets, +i: Nat) -> Maybe<&2, U32>:
  be32.head(Octets.field(i, 4n, o))

def Octets.le64_at(o: Octets, +i: Nat) -> Maybe<&2, W.W64>:
  le64_at(Octets.field(i, 8n, o), 0n)

def Octets.be64_at(o: Octets, +i: Nat) -> Maybe<&2, W.W64>:
  be64_at(Octets.field(i, 8n, o), 0n)
