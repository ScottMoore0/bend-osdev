# Properties, for every element type, comparison, list and predicate:
#
# * list_sort answers a permutation of its input: every predicate f counts
#   the same elements in both (for every comparison le, lawful or not);
# * list_sort_by (list_sort by a Nat key) answers a sorted list, and is
#   stable: the elements of any one key come out in their input order.
#
# * heap_sort, on an Array, permutes its slots (every predicate counts the
#   same elements), leaves every slot from n on unchanged, and keeps the
#   array's shape.
#
# Vectors: sorts of small lists and arrays, ties kept in order.
import Base
import ./ksort.bend as K
import ./spec.bend as S
import ./heapsort.bend as H
import ../array/array.bend as AR

# The list merge sort

law list_sort_count:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~f: A -> Bool
  for +xs: List<&2, A>
  {S.ksort.count(~A, ~f, K.ksort.list_sort(~A, ~le, xs)) == S.ksort.count(~A, ~f, xs) : Nat}

law list_sort_length:
  for ~A: Data
  for ~le: A -> A -> Bool
  for +xs: List<&2, A>
  {List.length(&2, A, K.ksort.list_sort(~A, ~le, xs)) == List.length(&2, A, xs) : Nat}

law list_sort_by_sorted:
  for ~A: Data
  for ~key: A -> Nat
  for +xs: List<&2, A>
  {S.ksort.sorted_by(~A, ~key, K.ksort.list_sort_by(~A, ~key, xs)) == True{} : Bool}

law list_sort_by_stable:
  for ~A: Data
  for ~key: A -> Nat
  for k: Nat
  for +xs: List<&2, A>
  {S.ksort.keep(~A, ~key, k, K.ksort.list_sort_by(~A, ~key, xs)) == S.ksort.keep(~A, ~key, k, xs) : List<&2, A>}

law list_sort_by_count:
  for ~A: Data
  for ~key: A -> Nat
  for ~f: A -> Bool
  for +xs: List<&2, A>
  {S.ksort.count(~A, ~f, K.ksort.list_sort_by(~A, ~key, xs)) == S.ksort.count(~A, ~f, xs) : Nat}

# The Array heapsort, on every array of depth d < 32 (built from a list of
# its 2^d slots, as bend-osdev-array's reflect law shows every perfect array
# is) and every n

law heap_sort_count:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~f: A -> Bool
  for +d: Nat
  for +xs: List<&2, A>
  for +fl: A
  for +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +n: U32
  {S.ksort.count(~A, ~f, AR.Arrays.leaves(A, H.ksort.heap_sort(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), n))) == S.ksort.count(~A, ~f, xs) : Nat}

law heap_sort_rest:
  for ~A: Data
  for ~le: A -> A -> Bool
  for +d: Nat
  for +xs: List<&2, A>
  for +fl: A
  for +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +n: U32
  for +k: Nat
  for +hk: {Nat.is_le(U32.to_nat(n), k) == True{} : Bool}
  {AR.Arrays.nth(A, AR.Arrays.leaves(A, H.ksort.heap_sort(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), n)), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}

law heap_sort_perfect:
  for ~A: Data
  for ~le: A -> A -> Bool
  for +d: Nat
  for +xs: List<&2, A>
  for +fl: A
  for +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +n: U32
  {AR.Arrays.is_perfect(A, d, H.ksort.heap_sort(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), n)) == True{} : Bool}

# Vectors

law vec_list_sort:
  {K.ksort.list_sort(~U32, ~U32.is_le, [5, 3, 9, 1, 4, 1, 8]) == [1, 1, 3, 4, 5, 8, 9] : List<&2, U32>}

law vec_list_sort_desc:
  {K.ksort.list_sort(~U32, ~U32.is_ge, [5, 3, 9, 1, 4]) == [9, 5, 4, 3, 1] : List<&2, U32>}

law vec_list_sort_empty:
  {K.ksort.list_sort(~U32, ~U32.is_le, []) == [] : List<&2, U32>}

# sorted by key x / 16, ties (the same key) keep their input order: keys
# 2 1 2 0 1 2 for 32 17 34 3 20 37
law vec_list_sort_by_stable:
  {K.ksort.list_sort_by(~U32, ~(x => U32.to_nat(U32.shrn(x, 4n))), [32, 17, 34, 3, 20, 37]) == [3, 17, 20, 32, 34, 37] : List<&2, U32>}

# the first 7 of 8 slots sorted, the last left alone
law vec_heap_sort:
  {AR.Arrays.leaves(U32, H.ksort.heap_sort(~U32, ~U32.is_le, AR.Arrays.of_list(U32, 3n, [5, 3, 9, 1, 4, 1, 8, 2], 0), 7)) == [1, 1, 3, 4, 5, 8, 9, 2] : List<&2, U32>}
