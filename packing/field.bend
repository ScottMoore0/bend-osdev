# bend-osdev-packing, fields: a run of bits in a list of bits, and a W64
# value as its bits.
import Base
import ../word64/word64.bend as W

# Runs of bits

# the w bits from position i
def packing.slice(bs: List<&2, Bool>, i: Nat, w: Nat) -> List<&2, Bool>:
  List.take(&2, Bool, List.drop(&2, Bool, bs, i), w)

# the bits from position i replaced by f (those past the end ignored)
def packing.splice(bs: List<&2, Bool>, i: Nat, f: List<&2, Bool>) -> List<&2, Bool>:
  match bs i f:
    case Nil{} _ _:
      Nil{}
    case Con{b, t} 0n Nil{}:
      Con{b, t}
    case Con{b, t} 0n Con{x, r}:
      Con{x, packing.splice(t, 0n, r)}
    case Con{b, t} 1n+j g:
      Con{b, packing.splice(t, j, g)}

# bit k of a list (False past the end)
def packing.nth(bs: List<&2, Bool>, k: Nat) -> Bool:
  match bs k:
    case Nil{} _:
      False{}
    case Con{b, t} 0n:
      b
    case Con{b, t} 1n+j:
      packing.nth(t, j)

# Values

def packing.word_bits(n: Nat, w: Word(n), rest: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      rest
    case 1n+p:
      match w:
        case WCon{b, t}:
          Con{b, packing.word_bits(p, t, rest)}

# the word whose bits are the first n of bs (False past the end)
def packing.bits_word(n: Nat, bs: List<&2, Bool>) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match bs:
        case Nil{}:
          WCon{False{}, packing.bits_word(p, Nil{})}
        case Con{b, t}:
          WCon{b, packing.bits_word(p, t)}

def packing.u32_bits(x: U32, rest: List<&2, Bool>) -> List<&2, Bool>:
  match x:
    case U32{w}:
      packing.word_bits(32n, w, rest)

# the 64 bits of a value, bit 0 first
def packing.w64_bits(+v: W.W64) -> List<&2, Bool>:
  packing.u32_bits(W.W64.lo(v), packing.u32_bits(W.W64.hi(v), Nil{}))

# the value whose bits, bit 0 first, are bs (False past the end, bits past
# 64 ignored)
def packing.bits_w64(+bs: List<&2, Bool>) -> W.W64:
  W.W64.from_parts(U32{packing.bits_word(32n, List.drop(&2, Bool, bs, 32n))}, U32{packing.bits_word(32n, bs)})

def packing.none_set(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, t}:
      Bool.and(Bool.not(b), packing.none_set(t))

# v fits in w bits: none of its bits from w on is set
def packing.fits(+v: W.W64, w: Nat) -> Bool:
  packing.none_set(List.drop(&2, Bool, packing.w64_bits(v), w))

# v's low w bits
def packing.low(+v: W.W64, w: Nat) -> W.W64:
  packing.bits_w64(List.take(&2, Bool, packing.w64_bits(v), w))
