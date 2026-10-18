# bend-osdev-packing, the logical view of a buffer: its bits numbered from
# the least significant, as the quirks lay them out.
#
# Without quirks a buffer of L bytes is one big-endian number: byte 0 holds
# the most significant bits, bit 0 of byte L - 1 is bit 0 of the buffer.
# The quirks (as the documentation of Linux's lib/packing describes them):
#
#   little_endian   within each 4-byte word, the bytes are in the opposite
#                   order (the word's least significant byte first)
#   lsw32_first     the 4-byte words are in the opposite order (the least
#                   significant word first)
#   msb_right       within each byte, the bits are in the opposite order
#                   (bit 0 of the field is the byte's most significant bit)
#
# packing.view lists the buffer's bits, bit 0 first; packing.unview turns
# such a list back into bytes. They are inverse to each other (LAWS.bend).
import Base

type PkQuirks is Data:
  PkQuirks{msb_right: Bool, little_endian: Bool, lsw32_first: Bool}

# no quirks: the buffer is one big-endian number
def packing.quirks_none() -> PkQuirks:
  PkQuirks{False{}, False{}, False{}}

# the bytes of each 4-byte word in the opposite order (a shorter tail as
# it is)
def packing.le_swap(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Con{d, Con{c, Con{b, Con{a, packing.le_swap(t)}}}}
    case ys:
      ys

def packing.order.go(le: Bool, lsw: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match le lsw:
    case False{} False{}:
      xs
    case True{} False{}:
      packing.le_swap(xs)
    case False{} True{}:
      packing.le_swap(List.reverse(&2, U32, xs))
    case True{} True{}:
      List.reverse(&2, U32, xs)

def packing.unorder.go(le: Bool, lsw: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match le lsw:
    case False{} False{}:
      xs
    case True{} False{}:
      packing.le_swap(xs)
    case False{} True{}:
      List.reverse(&2, U32, packing.le_swap(xs))
    case True{} True{}:
      List.reverse(&2, U32, xs)

# the bytes in logical order, most significant first
def packing.order(q: PkQuirks, xs: List<&2, U32>) -> List<&2, U32>:
  match q:
    case PkQuirks{m, le, lsw}:
      packing.order.go(le, lsw, xs)

# the bytes in buffer order, from logical order
def packing.unorder(q: PkQuirks, xs: List<&2, U32>) -> List<&2, U32>:
  match q:
    case PkQuirks{m, le, lsw}:
      packing.unorder.go(le, lsw, xs)

# the quirks that view the buffer as 4-byte words
def packing.wordwise(q: PkQuirks) -> Bool:
  match q:
    case PkQuirks{m, le, lsw}:
      Bool.or(le, lsw)

def packing.msb_right(q: PkQuirks) -> Bool:
  match q:
    case PkQuirks{m, le, lsw}:
      m

# the 8 bits of a byte, the field's bit 0 first: the byte's bit 0 first, or
# its bit 7 first when msb_right
def packing.byte_bits(m: Bool, y: U32, rest: List<&2, Bool>) -> List<&2, Bool>:
  match m y:
    case False{} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
      Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, rest}}}}}}}}
    case True{} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
      Con{c7, Con{c6, Con{c5, Con{c4, Con{c3, Con{c2, Con{c1, Con{c0, rest}}}}}}}}

# the byte of 8 bits listed as byte_bits lists them
def packing.bits_byte(m: Bool, c0: Bool, c1: Bool, c2: Bool, c3: Bool, c4: Bool, c5: Bool, c6: Bool, c7: Bool) -> U32:
  match m:
    case False{}:
      U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, Word.zero(24n)}}}}}}}}}
    case True{}:
      U32{WCon{c7, WCon{c6, WCon{c5, WCon{c4, WCon{c3, WCon{c2, WCon{c1, WCon{c0, Word.zero(24n)}}}}}}}}}

# the bits of bytes listed least significant byte first
def packing.bits_of(+m: Bool, ys: List<&2, U32>) -> List<&2, Bool>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      packing.byte_bits(m, y, packing.bits_of(m, t))

# bytes from bits, 8 at a time (a shorter tail dropped)
def packing.bytes_of(+m: Bool, bs: List<&2, Bool>) -> List<&2, U32>:
  match bs:
    case Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, t}}}}}}}}:
      Con{packing.bits_byte(m, c0, c1, c2, c3, c4, c5, c6, c7), packing.bytes_of(m, t)}
    case r:
      Nil{}

# the buffer's bits, bit 0 first
def packing.view(+q: PkQuirks, xs: List<&2, U32>) -> List<&2, Bool>:
  packing.bits_of(packing.msb_right(q), List.reverse(&2, U32, packing.order(q, xs)))

# the buffer whose bits, bit 0 first, are bs
def packing.unview(+q: PkQuirks, bs: List<&2, Bool>) -> List<&2, U32>:
  packing.unorder(q, List.reverse(&2, U32, packing.bytes_of(packing.msb_right(q), bs)))
