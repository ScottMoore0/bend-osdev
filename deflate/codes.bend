# bend-osdev-deflate: the length and distance codes of RFC 1951, 3.2.5, both
# ways: a symbol's base and extra bits (the inflater), a length's or a
# distance's symbol and extra bits (the deflater).
#
# Lengths: symbols 257 to 264 are lengths 3 to 10, with no extra bits; then
# four symbols for each count of extra bits from 1 to 5 (265 to 284, 11 to
# 257); 285 is 258, with none. Distances: symbols 0 to 3 are distances 1 to 4;
# then two symbols for each count of extra bits from 1 to 13 (4 to 29, 5 to
# 32768). Below, c is a length symbol minus 257.
import Base

def cd.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def cd.lbase.at(small: Bool, last: Bool, +c: U32) -> U32:
  match small:
    case True{}:
      U32.add(c, 3)
    case False{}:
      match last:
        case True{}:
          258
        case False{}:
          U32.add(U32.shln(U32.add(4, U32.and(c, 3)), Nat.sub(U32.to_nat(U32.shrn(c, 2n)), 1n)), 3)

# the least length of length symbol c + 257
def code_lbase(+c: U32) -> U32:
  cd.lbase.at(U32.is_lt(c, 8), U32.is_eq(c, 28), c)

def cd.lext.at(small: Bool, last: Bool, +c: U32) -> Nat:
  match small:
    case True{}:
      0n
    case False{}:
      match last:
        case True{}:
          0n
        case False{}:
          Nat.sub(U32.to_nat(U32.shrn(c, 2n)), 1n)

# how many extra bits length symbol c + 257 has
def code_lext(+c: U32) -> Nat:
  cd.lext.at(U32.is_lt(c, 8), U32.is_eq(c, 28), c)

def cd.dbase.at(small: Bool, +d: U32) -> U32:
  match small:
    case True{}:
      U32.add(d, 1)
    case False{}:
      U32.add(U32.shln(U32.add(2, U32.and(d, 1)), Nat.sub(U32.to_nat(U32.shrn(d, 1n)), 1n)), 1)

# the least distance of distance symbol d
def code_dbase(+d: U32) -> U32:
  cd.dbase.at(U32.is_lt(d, 4), d)

def cd.dext.at(small: Bool, +d: U32) -> Nat:
  match small:
    case True{}:
      0n
    case False{}:
      Nat.sub(U32.to_nat(U32.shrn(d, 1n)), 1n)

# how many extra bits distance symbol d has
def code_dext(+d: U32) -> Nat:
  cd.dext.at(U32.is_lt(d, 4), d)

# The other way

# for v = length - 3, 8 to 254: e = log2(v) - 2 extra bits, the symbol is
# 4 (e + 1) + (v >> e) - 4
def cd.lsym.at(small: Bool, last: Bool, +v: U32) -> U32:
  match small:
    case True{}:
      v
    case False{}:
      match last:
        case True{}:
          28
        case False{}:
          +e = Nat.sub(U32.log2(v), 2n)
          U32.sub(U32.add(U32.shln(U32.from_nat(1n+e), 2n), U32.shrn(v, e)), 4)

# the length symbol (minus 257) of a length from 3 to 258
def code_of_len(+l: U32) -> U32:
  +v = U32.sub(l, 3)
  cd.lsym.at(U32.is_lt(v, 8), U32.is_eq(l, 258), v)

# for v = distance - 1, 4 to 32767: e = log2(v) - 1 extra bits, the symbol
# is 2 (e + 1) + (v >> e) - 2
def cd.dsym.at(small: Bool, +v: U32) -> U32:
  match small:
    case True{}:
      v
    case False{}:
      +e = Nat.sub(U32.log2(v), 1n)
      U32.sub(U32.add(U32.shln(U32.from_nat(1n+e), 1n), U32.shrn(v, e)), 2)

# the distance symbol of a distance from 1 to 32768
def code_of_dist(+d: U32) -> U32:
  +v = U32.sub(d, 1)
  cd.dsym.at(U32.is_lt(v, 4), v)
