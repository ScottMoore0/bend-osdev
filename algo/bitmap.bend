# bend-osdev-algo, bitmaps: a bitmap is a List<&2, U32> of words, bit i in
# word i / 32 at position i mod 32, as the kernel lays out its bitmaps.
# next_set and next_clear find the next set or clear bit at or after an
# index and below a size, and answer the size when there is none (the
# kernel's find_next_bit and find_next_zero_bit).
import Base
import ./algo.bend as A

# Bit sequences

# bit i (False past the end)
def bitseq.at(bs: List<&2, Bool>, i: Nat) -> Bool:
  match bs i:
    case Nil{} _:
      False{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      bitseq.at(t, j)

# the least i with start <= i < size whose bit is want, or size if there is
# none (bits past the end of bs are clear)
def bitseq.next(size: Nat, start: Nat, want: Bool, bs: List<&2, Bool>) -> Nat:
  match size:
    case 0n:
      0n
    case 1n+s:
      match start want bs:
        case 1n+st w Nil{}:
          1n+bitseq.next(s, st, w, Nil{})
        case 1n+st w Con{h, t}:
          1n+bitseq.next(s, st, w, t)
        case 0n False{} Nil{}:
          0n
        case 0n True{} Nil{}:
          1n+s
        case 0n True{} Con{True{}, t}:
          0n
        case 0n False{} Con{False{}, t}:
          0n
        case 0n True{} Con{False{}, t}:
          1n+bitseq.next(s, 0n, True{}, t)
        case 0n False{} Con{True{}, t}:
          1n+bitseq.next(s, 0n, False{}, t)

# Bitmaps

# the bits of the words, bit 0 of the first word first
def bitmap.bits(words: List<&2, U32>) -> List<&2, Bool>:
  match words:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      A.bitw.to_list(32n, A.bits32.word(x), bitmap.bits(t))

# bit i of the bitmap (False past its end)
def bitmap.test(words: List<&2, U32>, i: Nat) -> Bool:
  bitseq.at(bitmap.bits(words), i)

# the first set bit at or after start and below size, or size
def bitmap.next_set(words: List<&2, U32>, size: Nat, start: Nat) -> Nat:
  bitseq.next(size, start, True{}, bitmap.bits(words))

# the first clear bit at or after start and below size, or size
def bitmap.next_clear(words: List<&2, U32>, size: Nat, start: Nat) -> Nat:
  bitseq.next(size, start, False{}, bitmap.bits(words))

def bitmap.first_set(words: List<&2, U32>, size: Nat) -> Nat:
  bitmap.next_set(words, size, 0n)

def bitmap.first_clear(words: List<&2, U32>, size: Nat) -> Nat:
  bitmap.next_clear(words, size, 0n)
