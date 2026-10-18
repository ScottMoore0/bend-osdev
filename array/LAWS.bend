# Laws about Base's Array (Array.size, Array.get, Array.set, Array.new), as
# Base 2.0.37 defines them, for every input:
#
# * for every array, of any shape: a read hands back the same array; a read
#   after a write at the same index answers the value written; a write keeps
#   the size; every slot of Array.new holds its value;
# * perfect trees (`Arrays.is_perfect`): Array.new builds one, Array.set keeps
#   one, and the size of one of depth d is 2^d;
# * for a perfect tree of depth d < 32, against the list model
#   (`Arrays.leaves`, the slots in index order): a read answers the model's
#   element at the masked index (`Arrays.index`), a write sets it, the model
#   has 2^d elements, and a write leaves every read at a different masked
#   index unchanged;
# * the masked index is below 2^d, and is k itself for a k below 2^d (for
#   2^d + k as well, which wraps to k; and for a U32 below 2^d, its value);
# * arrays built from a Data list (`Arrays.of_list`): every perfect array is
#   one (`reflect`), and get, set and new answer one, so that a proof can
#   follow a sequence of reads and writes on Data alone.
#
# Arrays are single-owner values (Type), but a law's statement is checked
# dead, so it may mention one array several times; the proofs consume each
# array once (they reflect it into a Data tree).
import Base
import ./array.bend as A

# For every array

law get_same_array:
  for -T: Data
  for a: Array<T>
  for i: U32
  {Pair.fst(Array<T>, T, Array.get(T, a, i)) == a : Array<T>}

law get_set_same:
  for -T: Data
  for a: Array<T>
  for i: U32
  for v: T
  {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), i)) == v : T}

law set_keeps_size:
  for -T: Data
  for a: Array<T>
  for i: U32
  for v: T
  {Pair.snd(Array<T>, U32, Array.size(T, Array.set(T, a, i, v))) == Pair.snd(Array<T>, U32, Array.size(T, a)) : U32}

law get_new:
  for -T: Data
  for d: Nat
  for v: T
  for i: U32
  {Pair.snd(Array<T>, T, Array.get(T, Array.new(T, d, v), i)) == v : T}

# Perfect trees

law new_perfect:
  for -T: Data
  for d: Nat
  for v: T
  {A.Arrays.is_perfect(T, d, Array.new(T, d, v)) == True{} : Bool}

law set_perfect:
  for -T: Data
  for d: Nat
  for a: Array<T>
  for h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}
  for i: U32
  for v: T
  {A.Arrays.is_perfect(T, d, Array.set(T, a, i, v)) == True{} : Bool}

law size_perfect:
  for -T: Data
  for d: Nat
  for a: Array<T>
  for h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}
  {Array.size(T, a) == (a, U32.shln(1, d)) : Array<T> & U32}

law new_leaves:
  for -T: Data
  for d: Nat
  for v: T
  {A.Arrays.leaves(T, Array.new(T, d, v)) == List.replicate(T, A.Arrays.slots(d), v) : List<&2, T>}

# The list model, for perfect trees

law model_length:
  for -T: Data
  for d: Nat
  for a: Array<T>
  for h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}
  {List.length(&2, T, A.Arrays.leaves(T, a)) == A.Arrays.slots(d) : Nat}

law model_get:
  for -T: Data
  for d: Nat
  for a: Array<T>
  for h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for i: U32
  {List.get(&2, T, A.Arrays.leaves(T, a), A.Arrays.index(d, i)) == Some{Pair.snd(Array<T>, T, Array.get(T, a, i))} : Maybe<&2, T>}

law model_set:
  for -T: Data
  for d: Nat
  for a: Array<T>
  for h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for i: U32
  for v: T
  {A.Arrays.leaves(T, Array.set(T, a, i, v)) == List.set(&2, T, A.Arrays.leaves(T, a), A.Arrays.index(d, i), v) : List<&2, T>}

law get_set_other:
  for -T: Data
  for d: Nat
  for a: Array<T>
  for h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for i: U32
  for j: U32
  for v: T
  for hij: {U32.is_eq(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.and(j, U32.sub(U32.shln(1, d), 1))) == False{} : Bool}
  {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), j)) == Pair.snd(Array<T>, T, Array.get(T, a, j)) : T}

# Indices

law index_below:
  for d: Nat
  for i: U32
  {Nat.is_lt(A.Arrays.index(d, i), A.Arrays.slots(d)) == True{} : Bool}

law index_of_nat:
  for d: Nat
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for k: Nat
  for hk: {Nat.is_lt(k, A.Arrays.slots(d)) == True{} : Bool}
  {A.Arrays.index(d, U32.from_nat(k)) == k : Nat}

# DRAFT: not yet reviewed by the maintainer
law index_wrap:
  for d: Nat
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for k: Nat
  for hk: {Nat.is_lt(k, A.Arrays.slots(d)) == True{} : Bool}
  {A.Arrays.index(d, U32.from_nat(Nat.add(A.Arrays.slots(d), k))) == k : Nat}

# DRAFT: not yet reviewed by the maintainer
law index_of_u32:
  for d: Nat
  for i: U32
  for hi: {Nat.is_lt(U32.to_nat(i), A.Arrays.slots(d)) == True{} : Bool}
  {A.Arrays.index(d, i) == U32.to_nat(i) : Nat}

# Arrays built from a Data list: a proof may name such an array as often as
# it needs, since it is rebuilt from Data each time. `reflect` turns a
# perfect array into one (using the array once), and get, set and new keep
# the form, so a proof about a sequence of reads and writes consumes each
# array once, as the program does.

law of_list_perfect:
  for -T: Data
  for +d: Nat
  for +xs: List<&2, T>
  for +f: T
  {A.Arrays.is_perfect(T, d, A.Arrays.of_list(T, d, xs, f)) == True{} : Bool}

law of_list_leaves:
  for -T: Data
  for +d: Nat
  for +xs: List<&2, T>
  for +f: T
  for +hl: {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}
  {A.Arrays.leaves(T, A.Arrays.of_list(T, d, xs, f)) == xs : List<&2, T>}

law of_list_size:
  for -T: Data
  for +d: Nat
  for +xs: List<&2, T>
  for +f: T
  {Array.size(T, A.Arrays.of_list(T, d, xs, f)) == (A.Arrays.of_list(T, d, xs, f), U32.shln(1, d)) : Array<T> & U32}

law of_list_get:
  for -T: Data
  for +d: Nat
  for +xs: List<&2, T>
  for +f: T
  for +hl: {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +i: U32
  {Array.get(T, A.Arrays.of_list(T, d, xs, f), i) == (A.Arrays.of_list(T, d, xs, f), A.Arrays.nth(T, xs, A.Arrays.index(d, i), f)) : Array<T> & T}

law of_list_set:
  for -T: Data
  for +d: Nat
  for +xs: List<&2, T>
  for +f: T
  for +hl: {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +i: U32
  for +v: T
  {Array.set(T, A.Arrays.of_list(T, d, xs, f), i, v) == A.Arrays.of_list(T, d, List.set(&2, T, xs, A.Arrays.index(d, i), v), f) : Array<T>}

law of_list_new:
  for -T: Data
  for +d: Nat
  for +v: T
  {Array.new(T, d, v) == A.Arrays.of_list(T, d, List.replicate(T, A.Arrays.slots(d), v), v) : Array<T>}

law reflect:
  for -T: Data
  for +d: Nat
  for a: Array<T>
  for h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}
  for +f: T
  exs xs: List<&2, T>
  {A.Arrays.of_list(T, d, xs, f) == a : Array<T>} & {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}

# The list model's own facts, for every list

law set_length:
  for -T: Data
  for xs: List<&2, T>
  for k: Nat
  for v: T
  {List.length(&2, T, List.set(&2, T, xs, k, v)) == List.length(&2, T, xs) : Nat}

law nth_set_same:
  for -T: Data
  for xs: List<&2, T>
  for k: Nat
  for v: T
  for f: T
  for h: {Nat.is_lt(k, List.length(&2, T, xs)) == True{} : Bool}
  {A.Arrays.nth(T, List.set(&2, T, xs, k, v), k, f) == v : T}

law nth_set_other:
  for -T: Data
  for xs: List<&2, T>
  for k: Nat
  for m: Nat
  for v: T
  for f: T
  for h: {Nat.is_eq(k, m) == False{} : Bool}
  {A.Arrays.nth(T, List.set(&2, T, xs, k, v), m, f) == A.Arrays.nth(T, xs, m, f) : T}

law nth_replicate:
  for -T: Data
  for n: Nat
  for v: T
  for k: Nat
  for f: T
  for h: {Nat.is_lt(k, n) == True{} : Bool}
  {A.Arrays.nth(T, List.replicate(T, n, v), k, f) == v : T}

# Witnesses: the hypotheses above hold together (depth 2, an array from
# Array.new, the indices 1 and 2, the slot 3)

law witness_perfect:
  {Bool.and(A.Arrays.is_perfect(U32, 2n, Array.new(U32, 2n, 0)), Nat.is_lt(2n, 32n)) == True{} : Bool}

law witness_other:
  {U32.is_eq(U32.and(1, U32.sub(U32.shln(1, 2n), 1)), U32.and(2, U32.sub(U32.shln(1, 2n), 1))) == False{} : Bool}

law witness_index:
  {Nat.is_lt(3n, A.Arrays.slots(2n)) == True{} : Bool}

# DRAFT: not yet reviewed by the maintainer
law witness_index_wrap:
  {Bool.and(Nat.is_lt(U32.to_nat(5), A.Arrays.slots(3n)), Nat.is_lt(3n, A.Arrays.slots(2n))) == True{} : Bool}

law witness_list:
  {Bool.and(Nat.is_eq(List.length(&2, U32, [5, 6, 7, 8]), A.Arrays.slots(2n)), Bool.and(Nat.is_lt(1n, 4n), Nat.is_ne(1n, 2n))) == True{} : Bool}

# Vectors

law vector_wrap:
  {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.new(U32, 2n, 0), 6, 9), 2)) == 9 : U32}

law vector_leaves:
  {A.Arrays.leaves(U32, Array.set(U32, Array.new(U32, 2n, 0), 1, 7)) == [0, 7, 0, 0] : List<&2, U32>}

law vector_index:
  {A.Arrays.index(3n, 13) == 5n : Nat}

law vector_of_list:
  {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, A.Arrays.of_list(U32, 2n, [5, 6, 7, 8], 0), 1, 9), 5)) == 9 : U32}

# DRAFT: not yet reviewed by the maintainer
law vector_index_wrap:
  {A.Arrays.index(2n, U32.from_nat(Nat.add(A.Arrays.slots(2n), 3n))) == 3n : Nat}

law vector_not_perfect:
  {A.Arrays.is_perfect(U32, 2n, ANode{ALeaf{1}, ANode{ALeaf{2}, ALeaf{3}}}) == False{} : Bool}
