# The canonical Huffman codes of RFC 1951, 3.2.2, for every set of code
# lengths: the code huff_tree gives a symbol (huff_code) is the code 3.2.2's
# three steps give it.
#
# The steps are written below as the RFC writes them (its C code counts in
# integers; here in U32, as huffman.bend does):
#
# 1. "Count the number of codes for each code length. Let bl_count[N] be
#    the number of codes of length N, N >= 1."  canon_count(ls, n).
# 2. "Find the numerical value of the smallest code for each code length":
#    code = 0; bl_count[0] = 0; for bits from 1 to MAX_BITS, code = (code
#    + bl_count[bits-1]) << 1 and next_code[bits] = code.  canon_next(ls,
#    bits).
# 3. "Assign numerical values to all codes, using consecutive values for
#    all codes of the same length with the base values determined at step
#    2. Codes that are never used (which have a bit length of zero) must
#    not be assigned a value."  So symbol i of length len gets
#    next_code[len] counted on by every symbol before it of the same
#    length: canon_code(ls, s), its len bits sent most significant first
#    (3.1.1, "Huffman codes are packed starting with the most significant
#    bit of the code").
#
# huff_code_canonical holds for every list of lengths: when the tree holds a
# code for a symbol, it is that symbol's canonical code. It needs the
# symbol's own length to be at most 15 (MAX_BITS: 3.2.7's code lengths are
# 0 to 15) and the list to be no longer than a word's value (so that symbol
# numbers, counted in U32, do not wrap). That every symbol with a length
# has its code in the tree when the lengths are not over-subscribed is not
# stated here (see README.md, Laws).
import Base
import ./huffman.bend as H

# c, one more if b
def canon_step(b: Bool, c: U32) -> U32:
  match b:
    case True{}:
      U32.add(c, 1)
    case False{}:
      c

# step 1: c counted on by every symbol of ls whose length is n
def canon_count.go(ls: List<&2, U32>, +n: Nat, c: U32) -> U32:
  match ls:
    case Nil{}:
      c
    case Con{h, t}:
      canon_count.go(t, n, canon_step(Nat.is_eq(U32.to_nat(h), n), c))

# bl_count[n]: how many symbols of ls have length n
def canon_count(ls: List<&2, U32>, +n: Nat) -> U32:
  canon_count.go(ls, n, 0)

# step 2: next_code[bits], the smallest code of length bits
def canon_next(+ls: List<&2, U32>, bits: Nat) -> U32:
  match bits:
    case 0n:
      0
    case 1n+ +b:
      match b:
        case 0n:
          0
        case 1n+c:
          U32.shl(U32.add(canon_next(ls, b), canon_count(ls, b)))

# the length of symbol i (0 past the end of the list)
def canon_len(ls: List<&2, U32>, i: Nat) -> U32:
  match ls:
    case Nil{}:
      0
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+j:
          canon_len(t, j)

# the l-bit code v, its most significant bit first
def canon_bits(l: Nat, +v: U32) -> List<&2, Bool>:
  match l:
    case 0n:
      Nil{}
    case 1n+ +p:
      Con{U32.is_eq(U32.and(U32.shrn(v, p), 1), 1), canon_bits(p, v)}

# step 3, for symbol i of length l: none for a length of 0; else
# next_code[l] counted on by the symbols before i of length l
def canon_code.of(l: Nat, +ls: List<&2, U32>, +i: Nat) -> Maybe<&2, List<&2, Bool>>:
  match l:
    case 0n:
      None{}
    case 1n+ +p:
      Some{canon_bits(1n+p, canon_count.go(List.take(&2, U32, ls, i), 1n+p, canon_next(ls, 1n+p)))}

# symbol s's code in the canonical code with lengths ls (ls[i]: symbol i's
# length)
def canon_code(+ls: List<&2, U32>, +s: U32) -> Maybe<&2, List<&2, Bool>>:
  canon_code.of(U32.to_nat(canon_len(ls, U32.to_nat(s))), ls, U32.to_nat(s))

# the code huff_code gives a symbol is its canonical code
law huff_code_canonical:
  for +ls: List<&2, U32>
  for +s: U32
  for +p: List<&2, Bool>
  for +c: U32
  for hc: {Nat.is_le(List.length(&2, U32, ls), U32.to_nat(c)) == True{} : Bool}
  for +hl: {Nat.is_le(U32.to_nat(canon_len(ls, U32.to_nat(s))), 15n) == True{} : Bool}
  for h: {H.huff_code(ls, s) == Some{p} : Maybe<&2, List<&2, Bool>>}
  {canon_code(ls, s) == Some{p} : Maybe<&2, List<&2, Bool>>}
