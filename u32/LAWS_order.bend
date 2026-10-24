# The order of Nat and of Base's words: transitivity, reflexivity and
# antisymmetry, for Nat.is_lt and Nat.is_le (and x <= x + w), Word.cmp of
# every width n, and U32.cmp, U32.is_lt and U32.is_le. Other bend-osdev packages' proofs use
# these laws instead of each proving them again.
import Base

# Nat

law nat_le_trans:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for h1: {Nat.is_le(x, y) == True{} : Bool}
  for h2: {Nat.is_le(y, z) == True{} : Bool}
  {Nat.is_le(x, z) == True{} : Bool}

law nat_lt_trans:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for h1: {Nat.is_lt(x, y) == True{} : Bool}
  for h2: {Nat.is_lt(y, z) == True{} : Bool}
  {Nat.is_lt(x, z) == True{} : Bool}

law nat_lt_le_trans:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for h1: {Nat.is_lt(x, y) == True{} : Bool}
  for h2: {Nat.is_le(y, z) == True{} : Bool}
  {Nat.is_lt(x, z) == True{} : Bool}

law nat_le_lt_trans:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for h1: {Nat.is_le(x, y) == True{} : Bool}
  for h2: {Nat.is_lt(y, z) == True{} : Bool}
  {Nat.is_lt(x, z) == True{} : Bool}

law nat_le_add_r:
  for +x: Nat
  for +w: Nat
  {Nat.is_le(x, Nat.add(x, w)) == True{} : Bool}

# Words of any width n

law word_cmp_refl:
  for +n: Nat
  for +a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

law word_cmp_eq:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

law word_cmp_lt_trans:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  for h1: {Word.cmp(n, a, b) == LT{} : Cmp}
  for h2: {Word.cmp(n, b, c) == LT{} : Cmp}
  {Word.cmp(n, a, c) == LT{} : Cmp}

# U32

law u32_cmp_refl:
  for +a: U32
  {U32.cmp(a, a) == EQ{} : Cmp}

law u32_cmp_eq:
  for +a: U32
  for +b: U32
  for e: {U32.cmp(a, b) == EQ{} : Cmp}
  {a == b : U32}

law u32_cmp_lt_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for h1: {U32.cmp(a, b) == LT{} : Cmp}
  for h2: {U32.cmp(b, c) == LT{} : Cmp}
  {U32.cmp(a, c) == LT{} : Cmp}

law u32_le_refl:
  for +a: U32
  {U32.is_le(a, a) == True{} : Bool}

law u32_lt_irrefl:
  for +a: U32
  for e: {U32.is_lt(a, a) == True{} : Bool}
  Empty

law u32_lt_le:
  for +a: U32
  for +b: U32
  for e: {U32.is_lt(a, b) == True{} : Bool}
  {U32.is_le(a, b) == True{} : Bool}

law u32_lt_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for h1: {U32.is_lt(a, b) == True{} : Bool}
  for h2: {U32.is_lt(b, c) == True{} : Bool}
  {U32.is_lt(a, c) == True{} : Bool}

law u32_le_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for h1: {U32.is_le(a, b) == True{} : Bool}
  for h2: {U32.is_le(b, c) == True{} : Bool}
  {U32.is_le(a, c) == True{} : Bool}

law u32_lt_le_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for h1: {U32.is_lt(a, b) == True{} : Bool}
  for h2: {U32.is_le(b, c) == True{} : Bool}
  {U32.is_lt(a, c) == True{} : Bool}

law u32_le_lt_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for h1: {U32.is_le(a, b) == True{} : Bool}
  for h2: {U32.is_lt(b, c) == True{} : Bool}
  {U32.is_lt(a, c) == True{} : Bool}

law u32_le_antisym:
  for +a: U32
  for +b: U32
  for h1: {U32.is_le(a, b) == True{} : Bool}
  for h2: {U32.is_le(b, a) == True{} : Bool}
  {a == b : U32}

law u32_not_lt:
  for +a: U32
  for +b: U32
  for e: {U32.is_lt(a, b) == False{} : Bool}
  {U32.is_le(b, a) == True{} : Bool}

law u32_not_le:
  for +a: U32
  for +b: U32
  for e: {U32.is_le(a, b) == False{} : Bool}
  {U32.is_lt(b, a) == True{} : Bool}

law u32_lt_not_le:
  for +a: U32
  for +b: U32
  for e: {U32.is_lt(a, b) == True{} : Bool}
  {U32.is_le(b, a) == False{} : Bool}

law u32_le_not_lt:
  for +a: U32
  for +b: U32
  for e: {U32.is_le(a, b) == True{} : Bool}
  {U32.is_lt(b, a) == False{} : Bool}
