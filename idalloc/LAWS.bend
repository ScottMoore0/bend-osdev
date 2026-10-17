# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every state, range, ID and value:
#
# * IDA allocation: an allocated ID was free before and is in use after; it
#   lies in the range; every ID of the range below it was in use, so it is
#   the lowest free one; no other ID changes; allocation fails with
#   IdExhausted only when every ID of the range is in use, and with
#   IdBadRange only when max < min;
# * IDA free: the freed ID is free after, and no other ID changes;
# * allocating again after freeing the ID just allocated gives the same ID
#   and the same state; freeing any ID of the range below the one allocation
#   would answer makes it the one allocation answers, and allocating it gives
#   back the state from before the free;
# * IDR: the same for allocation, which also maps the ID to its value; find,
#   remove and replace read, free and change one ID's value and no other's.
#
# Vectors: a few allocation sequences.
import Base
import ./idalloc.bend as I

# IDA: allocation

law ida_alloc_was_free:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for t: I.Idr<Unit>
  for id: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  {I.ida.in_use(s, id) == False{} : Bool}

law ida_alloc_in_use:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for t: I.Idr<Unit>
  for id: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  {I.ida.in_use(t, id) == True{} : Bool}

law ida_alloc_at_least:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for t: I.Idr<Unit>
  for id: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  {Nat.is_le(min, id) == True{} : Bool}

law ida_alloc_at_most:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for t: I.Idr<Unit>
  for id: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  {Nat.is_le(id, max) == True{} : Bool}

law ida_alloc_lowest:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for t: I.Idr<Unit>
  for id: Nat
  for j: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  for l: {Nat.is_le(min, j) == True{} : Bool}
  for m: {Nat.is_lt(j, id) == True{} : Bool}
  {I.ida.in_use(s, j) == True{} : Bool}

law ida_alloc_others:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for t: I.Idr<Unit>
  for id: Nat
  for j: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  for n: {Nat.is_eq(j, id) == False{} : Bool}
  {I.ida.in_use(t, j) == I.ida.in_use(s, j) : Bool}

law ida_alloc_exhausted:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for j: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Fail{I.IdExhausted{}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  for l: {Nat.is_le(min, j) == True{} : Bool}
  for m: {Nat.is_le(j, max) == True{} : Bool}
  {I.ida.in_use(s, j) == True{} : Bool}

law ida_alloc_bad_range:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Fail{I.IdBadRange{}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  {Nat.is_lt(max, min) == True{} : Bool}

# IDA: free

law ida_free_frees:
  for s: I.Idr<Unit>
  for k: Nat
  {I.ida.in_use(I.ida.free(s, k), k) == False{} : Bool}

law ida_free_others:
  for s: I.Idr<Unit>
  for k: Nat
  for j: Nat
  for n: {Nat.is_eq(j, k) == False{} : Bool}
  {I.ida.in_use(I.ida.free(s, k), j) == I.ida.in_use(s, j) : Bool}

# IDA: allocation after free

law ida_realloc:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for t: I.Idr<Unit>
  for id: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  {I.ida.alloc_range(I.ida.free(t, id), I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}

law ida_free_lowest:
  for s: I.Idr<Unit>
  for min: Nat
  for max: Nat
  for t: I.Idr<Unit>
  for id: Nat
  for k: Nat
  for e: {I.ida.alloc_range(s, I.IdRange{min, max}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
  for l: {Nat.is_le(min, k) == True{} : Bool}
  for m: {Nat.is_lt(k, id) == True{} : Bool}
  {I.ida.alloc_range(I.ida.free(s, k), I.IdRange{min, max}) == Done{I.IdrAlloc{s, k}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}

# IDR

law idr_alloc_find:
  for -V: Data
  for r: I.Idr<V>
  for min: Nat
  for max: Nat
  for v: V
  for t: I.Idr<V>
  for id: Nat
  for e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
  {I.idr.find(V, t, id) == Some{v} : Maybe<&2, V>}

law idr_alloc_was_free:
  for -V: Data
  for r: I.Idr<V>
  for min: Nat
  for max: Nat
  for v: V
  for t: I.Idr<V>
  for id: Nat
  for e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
  {I.idr.find(V, r, id) == None{} : Maybe<&2, V>}

law idr_alloc_in_range:
  for -V: Data
  for r: I.Idr<V>
  for min: Nat
  for max: Nat
  for v: V
  for t: I.Idr<V>
  for id: Nat
  for e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
  {Bool.and(Nat.is_le(min, id), Nat.is_le(id, max)) == True{} : Bool}

law idr_alloc_lowest:
  for -V: Data
  for r: I.Idr<V>
  for min: Nat
  for max: Nat
  for v: V
  for t: I.Idr<V>
  for id: Nat
  for j: Nat
  for e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
  for l: {Nat.is_le(min, j) == True{} : Bool}
  for m: {Nat.is_lt(j, id) == True{} : Bool}
  {I.idr.in_use(V, r, j) == True{} : Bool}

law idr_alloc_others:
  for -V: Data
  for r: I.Idr<V>
  for min: Nat
  for max: Nat
  for v: V
  for t: I.Idr<V>
  for id: Nat
  for j: Nat
  for e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
  for n: {Nat.is_eq(j, id) == False{} : Bool}
  {I.idr.find(V, t, j) == I.idr.find(V, r, j) : Maybe<&2, V>}

law idr_realloc:
  for -V: Data
  for r: I.Idr<V>
  for min: Nat
  for max: Nat
  for v: V
  for t: I.Idr<V>
  for id: Nat
  for e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
  {I.idr.alloc_range(V, I.idr.free(V, t, id), I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}

law idr_remove_old:
  for -V: Data
  for r: I.Idr<V>
  for k: Nat
  {Pair.snd(I.Idr<V>, Maybe<&2, V>, I.idr.remove(V, r, k)) == I.idr.find(V, r, k) : Maybe<&2, V>}

law idr_remove_frees:
  for -V: Data
  for r: I.Idr<V>
  for k: Nat
  {I.idr.find(V, Pair.fst(I.Idr<V>, Maybe<&2, V>, I.idr.remove(V, r, k)), k) == None{} : Maybe<&2, V>}

law idr_remove_others:
  for -V: Data
  for r: I.Idr<V>
  for k: Nat
  for j: Nat
  for n: {Nat.is_eq(j, k) == False{} : Bool}
  {I.idr.find(V, Pair.fst(I.Idr<V>, Maybe<&2, V>, I.idr.remove(V, r, k)), j) == I.idr.find(V, r, j) : Maybe<&2, V>}

law idr_free_is_remove:
  for -V: Data
  for r: I.Idr<V>
  for k: Nat
  {I.idr.free(V, r, k) == Pair.fst(I.Idr<V>, Maybe<&2, V>, I.idr.remove(V, r, k)) : I.Idr<V>}

law idr_replace_find:
  for -V: Data
  for r: I.Idr<V>
  for k: Nat
  for v: V
  for t: I.Idr<V>
  for old: V
  for e: {I.idr.replace(V, r, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}
  {I.idr.find(V, t, k) == Some{v} : Maybe<&2, V>}

law idr_replace_old:
  for -V: Data
  for r: I.Idr<V>
  for k: Nat
  for v: V
  for t: I.Idr<V>
  for old: V
  for e: {I.idr.replace(V, r, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}
  {I.idr.find(V, r, k) == Some{old} : Maybe<&2, V>}

law idr_replace_others:
  for -V: Data
  for r: I.Idr<V>
  for k: Nat
  for v: V
  for t: I.Idr<V>
  for old: V
  for j: Nat
  for e: {I.idr.replace(V, r, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}
  for n: {Nat.is_eq(j, k) == False{} : Bool}
  {I.idr.find(V, t, j) == I.idr.find(V, r, j) : Maybe<&2, V>}

law idr_replace_absent:
  for -V: Data
  for r: I.Idr<V>
  for k: Nat
  for v: V
  for e: {I.idr.find(V, r, k) == None{} : Maybe<&2, V>}
  {I.idr.replace(V, r, k, v) == Fail{I.IdNotFound{}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}

# Vectors (over the range 0 to 9: the Lean kernel behind --verdict does not
# yet evaluate the default range, whose maximum is the Nat literal
# 2147483647n)

# three allocations from empty: 0, 1, 2
law vec_three:
  {I.ida.ids(I.ida.state(I.ida.alloc_range(I.ida.state(I.ida.alloc_range(I.ida.state(I.ida.alloc_range(I.ida.new(), I.IdRange{0n, 9n}), I.ida.new()), I.IdRange{0n, 9n}), I.ida.new()), I.IdRange{0n, 9n}), I.ida.new())) == [0n, 1n, 2n] : List<&2, Nat>}

# with 0, 1, 2 in use and 1 freed, the next is 1
law vec_gap:
  {I.ida.id(I.ida.alloc_range(I.ida.free(I.ida.state(I.ida.alloc_range(I.ida.state(I.ida.alloc_range(I.ida.state(I.ida.alloc_range(I.ida.new(), I.IdRange{0n, 9n}), I.ida.new()), I.IdRange{0n, 9n}), I.ida.new()), I.IdRange{0n, 9n}), I.ida.new()), 1n), I.IdRange{0n, 9n})) == Some{1n} : Maybe<&2, Nat>}

law vec_min:
  {I.ida.id(I.ida.alloc_range(I.ida.new(), I.IdRange{3n, 9n})) == Some{3n} : Maybe<&2, Nat>}

law vec_exhausted:
  {I.ida.alloc_range(I.ida.state(I.ida.alloc_range(I.ida.new(), I.IdRange{0n, 9n}), I.ida.new()), I.IdRange{0n, 0n}) == Fail{I.IdExhausted{}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}

law vec_bad_range:
  {I.ida.alloc_range(I.ida.new(), I.IdRange{2n, 1n}) == Fail{I.IdBadRange{}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}

law vec_idr:
  {I.idr.find(U32, I.idr.state(U32, I.idr.alloc_range(U32, I.idr.new(U32), I.IdRange{0n, 9n}, 7), I.idr.new(U32)), 0n) == Some{7} : Maybe<&2, U32>}

# Witnesses: each hypothesis above can hold

# with 0 and 1 in use, allocation over 0..9 answers Done with ID 2, and
# j = 1 lies in [min, id) and is in use (for alloc_lowest and free_lowest)
law wit_alloc_below:
  {(I.ida.id(I.ida.alloc_range(I.ida.state(I.ida.alloc_range(I.ida.state(I.ida.alloc_range(I.ida.new(), I.IdRange{0n, 9n}), I.ida.new()), I.IdRange{0n, 9n}), I.ida.new()), I.IdRange{0n, 9n})), Nat.is_le(0n, 1n), Nat.is_lt(1n, 2n), I.ida.in_use(I.ida.state(I.ida.alloc_range(I.ida.state(I.ida.alloc_range(I.ida.new(), I.IdRange{0n, 9n}), I.ida.new()), I.IdRange{0n, 9n}), I.ida.new()), 1n)) == (Some{2n}, True{}, True{}, True{}) : Maybe<&2, Nat> & Bool & Bool & Bool}

# replace answers Done on an ID in use, and find answers None on a free one
law wit_replace:
  {(Result.is_done(&2, &2, I.IdError, I.IdrOld<U32>, I.idr.replace(U32, I.idr.state(U32, I.idr.alloc_range(U32, I.idr.new(U32), I.IdRange{0n, 9n}, 7), I.idr.new(U32)), 0n, 9)), I.idr.find(U32, I.idr.new(U32), 0n)) == (True{}, None{}) : Bool & Maybe<&2, U32>}
