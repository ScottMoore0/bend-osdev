# Properties, for every input:
#
# * bit search in a U32 and in a W64: popcount is at most the width, and the
#   popcounts of a word and of its complement add up to the width; the bit
#   first_set names is set, and no bit below it is; the bit last_set names is
#   set, and no bit above it is; each is None only for zero; ctz is the index
#   of the lowest set bit, clz plus the index of the highest set bit is the
#   width less one, and so for a nonzero word ctz + clz is at most the width
#   less one;
# * bitmaps: next_set and next_clear answer at most the size; an answer below
#   the size is at or after the start and has the bit wanted, and no bit from
#   the start up to the answer has it;
# * binary search on a sorted list: every element before lower_bound is below
#   the key, and every element from it on is not; find answers an index that
#   holds the key, and None only when no element is the key.
#
# * binary search on an Array<U32> (through bend-osdev-array's laws): for
#   every perfect array whose first n slots are sorted, array_lower_bound
#   and array_find answer what lower_bound and find answer on the list of
#   those slots, and hand the array back.
#
# Vectors: the values of each function on edge cases, and binary search on a
# sorted Array<U32>.
import Base
import ../word64/word64.bend as W
import ../array/array.bend as AR
import ./algo.bend as A
import ./bitmap.bend as M
import ./bsearch.bend as S

# U32

law popcount_le:
  for x: U32
  {Nat.is_le(A.bits32.popcount(x), 32n) == True{} : Bool}

law popcount_not:
  for x: U32
  {Nat.add(A.bits32.popcount(x), A.bits32.popcount(U32.not(x))) == 32n : Nat}

law first_set_is_set:
  for x: U32
  for k: Nat
  for e: {A.bits32.first_set(x) == Some{k} : Maybe<&2, Nat>}
  {A.bits32.test(x, k) == True{} : Bool}

law first_set_lowest:
  for x: U32
  for k: Nat
  for j: Nat
  for e: {A.bits32.first_set(x) == Some{k} : Maybe<&2, Nat>}
  for l: {Nat.is_lt(j, k) == True{} : Bool}
  {A.bits32.test(x, j) == False{} : Bool}

law first_set_none:
  for x: U32
  for e: {A.bits32.first_set(x) == None{} : Maybe<&2, Nat>}
  {x == 0 : U32}

law last_set_is_set:
  for x: U32
  for k: Nat
  for e: {A.bits32.last_set(x) == Some{k} : Maybe<&2, Nat>}
  {A.bits32.test(x, k) == True{} : Bool}

law last_set_highest:
  for x: U32
  for k: Nat
  for j: Nat
  for e: {A.bits32.last_set(x) == Some{k} : Maybe<&2, Nat>}
  for l: {Nat.is_lt(k, j) == True{} : Bool}
  {A.bits32.test(x, j) == False{} : Bool}

law last_set_none:
  for x: U32
  for e: {A.bits32.last_set(x) == None{} : Maybe<&2, Nat>}
  {x == 0 : U32}

law ctz_first_set:
  for x: U32
  for k: Nat
  for e: {A.bits32.first_set(x) == Some{k} : Maybe<&2, Nat>}
  {A.bits32.ctz(x) == k : Nat}

law clz_last_set:
  for x: U32
  for k: Nat
  for e: {A.bits32.last_set(x) == Some{k} : Maybe<&2, Nat>}
  {Nat.add(A.bits32.clz(x), k) == 31n : Nat}

law first_le_last:
  for x: U32
  for i: Nat
  for k: Nat
  for e: {A.bits32.first_set(x) == Some{i} : Maybe<&2, Nat>}
  for f: {A.bits32.last_set(x) == Some{k} : Maybe<&2, Nat>}
  {Nat.is_le(i, k) == True{} : Bool}

law ctz_clz:
  for x: U32
  for k: Nat
  for e: {A.bits32.first_set(x) == Some{k} : Maybe<&2, Nat>}
  {Nat.is_le(Nat.add(A.bits32.ctz(x), A.bits32.clz(x)), 31n) == True{} : Bool}

# W64

law popcount64_le:
  for a: W.W64
  {Nat.is_le(A.bits64.popcount(a), 64n) == True{} : Bool}

law first_set64_is_set:
  for a: W.W64
  for k: Nat
  for e: {A.bits64.first_set(a) == Some{k} : Maybe<&2, Nat>}
  {A.bits64.test(a, k) == True{} : Bool}

law first_set64_lowest:
  for a: W.W64
  for k: Nat
  for j: Nat
  for e: {A.bits64.first_set(a) == Some{k} : Maybe<&2, Nat>}
  for l: {Nat.is_lt(j, k) == True{} : Bool}
  {A.bits64.test(a, j) == False{} : Bool}

law first_set64_none:
  for a: W.W64
  for e: {A.bits64.first_set(a) == None{} : Maybe<&2, Nat>}
  {a == W.W64.zero() : W.W64}

law last_set64_is_set:
  for a: W.W64
  for k: Nat
  for e: {A.bits64.last_set(a) == Some{k} : Maybe<&2, Nat>}
  {A.bits64.test(a, k) == True{} : Bool}

law last_set64_highest:
  for a: W.W64
  for k: Nat
  for j: Nat
  for e: {A.bits64.last_set(a) == Some{k} : Maybe<&2, Nat>}
  for l: {Nat.is_lt(k, j) == True{} : Bool}
  {A.bits64.test(a, j) == False{} : Bool}

law ctz64_first_set:
  for a: W.W64
  for k: Nat
  for e: {A.bits64.first_set(a) == Some{k} : Maybe<&2, Nat>}
  {A.bits64.ctz(a) == k : Nat}

law clz64_last_set:
  for a: W.W64
  for k: Nat
  for e: {A.bits64.last_set(a) == Some{k} : Maybe<&2, Nat>}
  {Nat.add(A.bits64.clz(a), k) == 63n : Nat}

law ctz_clz64:
  for a: W.W64
  for k: Nat
  for e: {A.bits64.first_set(a) == Some{k} : Maybe<&2, Nat>}
  {Nat.is_le(Nat.add(A.bits64.ctz(a), A.bits64.clz(a)), 63n) == True{} : Bool}

# Bitmaps

law next_set_le_size:
  for words: List<&2, U32>
  for size: Nat
  for start: Nat
  {Nat.is_le(M.bitmap.next_set(words, size, start), size) == True{} : Bool}

law next_set_is_set:
  for words: List<&2, U32>
  for size: Nat
  for start: Nat
  for l: {Nat.is_lt(M.bitmap.next_set(words, size, start), size) == True{} : Bool}
  {M.bitmap.test(words, M.bitmap.next_set(words, size, start)) == True{} : Bool}

law next_set_at_least:
  for words: List<&2, U32>
  for size: Nat
  for start: Nat
  for l: {Nat.is_lt(M.bitmap.next_set(words, size, start), size) == True{} : Bool}
  {Nat.is_le(start, M.bitmap.next_set(words, size, start)) == True{} : Bool}

law next_set_none_before:
  for words: List<&2, U32>
  for size: Nat
  for start: Nat
  for j: Nat
  for l: {Nat.is_le(start, j) == True{} : Bool}
  for m: {Nat.is_lt(j, M.bitmap.next_set(words, size, start)) == True{} : Bool}
  {M.bitmap.test(words, j) == False{} : Bool}

law next_clear_le_size:
  for words: List<&2, U32>
  for size: Nat
  for start: Nat
  {Nat.is_le(M.bitmap.next_clear(words, size, start), size) == True{} : Bool}

law next_clear_is_clear:
  for words: List<&2, U32>
  for size: Nat
  for start: Nat
  for l: {Nat.is_lt(M.bitmap.next_clear(words, size, start), size) == True{} : Bool}
  {M.bitmap.test(words, M.bitmap.next_clear(words, size, start)) == False{} : Bool}

law next_clear_at_least:
  for words: List<&2, U32>
  for size: Nat
  for start: Nat
  for l: {Nat.is_lt(M.bitmap.next_clear(words, size, start), size) == True{} : Bool}
  {Nat.is_le(start, M.bitmap.next_clear(words, size, start)) == True{} : Bool}

law next_clear_none_before:
  for words: List<&2, U32>
  for size: Nat
  for start: Nat
  for j: Nat
  for l: {Nat.is_le(start, j) == True{} : Bool}
  for m: {Nat.is_lt(j, M.bitmap.next_clear(words, size, start)) == True{} : Bool}
  {M.bitmap.test(words, j) == True{} : Bool}

# Binary search (the reference, on a list)

law lower_bound_le_length:
  for xs: List<&2, U32>
  for key: U32
  {Nat.is_le(S.bsearch.lower_bound(xs, key), List.length(&2, U32, xs)) == True{} : Bool}

law lower_bound_below:
  for xs: List<&2, U32>
  for key: U32
  for i: Nat
  for x: U32
  for e: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}
  for l: {Nat.is_lt(i, S.bsearch.lower_bound(xs, key)) == True{} : Bool}
  {U32.is_lt(x, key) == True{} : Bool}

law lower_bound_above:
  for xs: List<&2, U32>
  for key: U32
  for i: Nat
  for x: U32
  for s: {S.bsearch.sorted(xs) == True{} : Bool}
  for e: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}
  for l: {Nat.is_le(S.bsearch.lower_bound(xs, key), i) == True{} : Bool}
  {U32.is_lt(x, key) == False{} : Bool}

law find_some:
  for xs: List<&2, U32>
  for key: U32
  for i: Nat
  for e: {S.bsearch.find(xs, key) == Some{i} : Maybe<&2, Nat>}
  {List.get(&2, U32, xs, i) == Some{key} : Maybe<&2, U32>}

law find_none:
  for xs: List<&2, U32>
  for key: U32
  for i: Nat
  for x: U32
  for s: {S.bsearch.sorted(xs) == True{} : Bool}
  for e: {S.bsearch.find(xs, key) == None{} : Maybe<&2, Nat>}
  for g: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}
  {U32.is_eq(x, key) == False{} : Bool}

# Binary search on an Array<U32> (the fast implementation), against the
# reference: for an array a that is a perfect tree of depth d < 32 (as
# Array.new and Array.set build), searched in its first n slots (n <= 2^d)
# whose elements, in index order (array's Arrays.leaves), are sorted. The
# array search answers a U32 and Maybe<&2, U32>; algo_index_nat reads the
# latter as the list search's Maybe<&2, Nat>.

def algo_index_nat(m: Maybe<&2, U32>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{U32.to_nat(i)}

# DRAFT: not yet reviewed by the maintainer
law array_lower_bound_list:
  for +d: Nat
  for a: Array<U32>
  for hp: {AR.Arrays.is_perfect(U32, d, a) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for n: U32
  for hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}
  for key: U32
  for hs: {S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n))) == True{} : Bool}
  {U32.to_nat(Pair.snd(Array<U32>, U32, S.bsearch.array_lower_bound(a, n, key))) == S.bsearch.lower_bound(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n)), key) : Nat}

# DRAFT: not yet reviewed by the maintainer
law array_lower_bound_same:
  for +d: Nat
  for a: Array<U32>
  for hp: {AR.Arrays.is_perfect(U32, d, a) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for n: U32
  for key: U32
  {Pair.fst(Array<U32>, U32, S.bsearch.array_lower_bound(a, n, key)) == a : Array<U32>}

# DRAFT: not yet reviewed by the maintainer
law array_find_list:
  for +d: Nat
  for a: Array<U32>
  for hp: {AR.Arrays.is_perfect(U32, d, a) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for n: U32
  for hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}
  for key: U32
  for hs: {S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n))) == True{} : Bool}
  {algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(a, n, key))) == S.bsearch.find(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n)), key) : Maybe<&2, Nat>}

# DRAFT: not yet reviewed by the maintainer
law array_find_same:
  for +d: Nat
  for a: Array<U32>
  for hp: {AR.Arrays.is_perfect(U32, d, a) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for n: U32
  for key: U32
  {Pair.fst(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(a, n, key)) == a : Array<U32>}

# Vectors (0x80000000 = 2147483648, 0xFFFFFFFF = 4294967295, 40 = 0b101000)

law vec_popcount:
  {A.bits32.popcount(4294967295) == 32n : Nat}

law vec_zero:
  {(A.bits32.ffs(0), A.bits32.fls(0), A.bits32.ctz(0), A.bits32.clz(0)) == (0n, 0n, 32n, 32n) : Nat & Nat & Nat & Nat}

law vec_forty:
  {(A.bits32.ffs(40), A.bits32.fls(40), A.bits32.ctz(40), A.bits32.clz(40)) == (4n, 6n, 3n, 26n) : Nat & Nat & Nat & Nat}

law vec_top:
  {(A.bits32.first_set(2147483648), A.bits32.last_set(1)) == (Some{31n}, Some{0n}) : Maybe<&2, Nat> & Maybe<&2, Nat>}

law vec64_halves:
  {(A.bits64.ctz(W.W64.from_parts(1, 0)), A.bits64.clz(W.W64.from_parts(0, 1)), A.bits64.popcount(W.W64.max())) == (32n, 63n, 64n) : Nat & Nat & Nat}

law vec64_zero:
  {(A.bits64.first_set(W.W64.zero()), A.bits64.ctz(W.W64.zero())) == (None{}, 64n) : Maybe<&2, Nat> & Nat}

law vec_next_set:
  {M.bitmap.next_set([0, 8], 64n, 3n) == 35n : Nat}

law vec_next_set_none:
  {M.bitmap.next_set([0, 8], 35n, 0n) == 35n : Nat}

law vec_next_clear:
  {M.bitmap.next_clear([4294967295, 1], 64n, 3n) == 33n : Nat}

law vec_next_past_size:
  {M.bitmap.next_clear([0], 10n, 12n) == 10n : Nat}

law vec_lower_bound:
  {(S.bsearch.lower_bound([1, 3, 3, 7, 9], 3), S.bsearch.lower_bound([1, 3, 3, 7, 9], 10), S.bsearch.find([1, 3, 3, 7, 9], 7), S.bsearch.find([1, 3, 3, 7, 9], 8)) == (1n, 5n, Some{3n}, None{}) : Nat & Nat & Maybe<&2, Nat> & Maybe<&2, Nat>}

# the array [1, 3, 3, 7, 9, 0, 0, 0], searched in its first 5 slots
law vec_array_lower_bound:
  {Pair.snd(Array<U32>, U32, S.bsearch.array_lower_bound(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, [0 : U32*8n], 0, 1), 1, 3), 2, 3), 3, 7), 4, 9), 5, 3)) == 1 : U32}

law vec_array_lower_bound_end:
  {Pair.snd(Array<U32>, U32, S.bsearch.array_lower_bound(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, [0 : U32*8n], 0, 1), 1, 3), 2, 3), 3, 7), 4, 9), 5, 10)) == 5 : U32}

law vec_array_find:
  {Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, [0 : U32*8n], 0, 1), 1, 3), 2, 3), 3, 7), 4, 9), 5, 7)) == Some{3} : Maybe<&2, U32>}

law vec_array_find_none:
  {Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, [0 : U32*8n], 0, 1), 1, 3), 2, 3), 3, 7), 4, 9), 5, 8)) == None{} : Maybe<&2, U32>}

# Witnesses: each hypothesis above can hold

# first_set and last_set answer Some (40 = 0b101000: bits 3 and 5), with a
# j below and above; and None for zero
law wit_first_last:
  {(A.bits32.first_set(40), Nat.is_lt(1n, 3n), A.bits32.last_set(40), Nat.is_lt(5n, 7n), A.bits32.first_set(0), A.bits32.last_set(0)) == (Some{3n}, True{}, Some{5n}, True{}, None{}, None{}) : Maybe<&2, Nat> & Bool & Maybe<&2, Nat> & Bool & Maybe<&2, Nat> & Maybe<&2, Nat>}

law wit_first_last64:
  {(A.bits64.first_set(W.W64.from_parts(1, 0)), A.bits64.last_set(W.W64.from_parts(1, 0)), A.bits64.first_set(W.W64.zero())) == (Some{32n}, Some{32n}, None{}) : Maybe<&2, Nat> & Maybe<&2, Nat> & Maybe<&2, Nat>}

# an answer below the size, and a j with start <= j < answer
law wit_next:
  {(Nat.is_lt(M.bitmap.next_set([0, 8], 64n, 3n), 64n), Nat.is_le(3n, 10n), Nat.is_lt(10n, M.bitmap.next_set([0, 8], 64n, 3n)), Nat.is_lt(M.bitmap.next_clear([4294967295, 1], 64n, 3n), 64n), Nat.is_lt(10n, M.bitmap.next_clear([4294967295, 1], 64n, 3n))) == (True{}, True{}, True{}, True{}, True{}) : Bool & Bool & Bool & Bool & Bool}

# a sorted list; an element before the lower bound of 7 (index 1) and one
# from it on (index 4); find answering Some and None
law wit_bsearch:
  {(S.bsearch.sorted([1, 3, 3, 7, 9]), S.bsearch.lower_bound([1, 3, 3, 7, 9], 7), List.get(&2, U32, [1, 3, 3, 7, 9], 1n), List.get(&2, U32, [1, 3, 3, 7, 9], 4n), S.bsearch.find([1, 3, 3, 7, 9], 7), S.bsearch.find([1, 3, 3, 7, 9], 8)) == (True{}, 3n, Some{3}, Some{9}, Some{3n}, None{}) : Bool & Nat & Maybe<&2, U32> & Maybe<&2, U32> & Maybe<&2, Nat> & Maybe<&2, Nat>}

# the array [1, 3, 3, 7, 9, 0, 0, 0] (depth 3), searched in its first 5
# slots: perfect, of depth below 32, 5 <= 2^3, and those slots sorted
# DRAFT: not yet reviewed by the maintainer
law wit_array_bsearch:
  {(AR.Arrays.is_perfect(U32, 3n, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, [0 : U32*8n], 0, 1), 1, 3), 2, 3), 3, 7), 4, 9)), Nat.is_lt(3n, 32n), Nat.is_le(U32.to_nat(5), AR.Arrays.slots(3n)), S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, [0 : U32*8n], 0, 1), 1, 3), 2, 3), 3, 7), 4, 9)), U32.to_nat(5)))) == (True{}, True{}, True{}, True{}) : Bool & Bool & Bool & Bool}
