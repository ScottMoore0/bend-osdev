# The laws are stated for the named default, Maple32 (U32 indices in
# U32.cmp's order), and for every value type V. "valid" is Maple32.valid:
# the entries are in index order, no two share an index, each has
# first <= last, and every pivot is its child's last index. Properties, for
# every tree, range, index and value:
#
# * the invariant: the empty tree is valid, and set_range, clear_range and
#   erase keep a tree valid, so ranges never overlap;
# * balance: in the empty tree, and after set_range, clear_range and erase,
#   every leaf is at the same depth, the tree's height (leveled);
# * the contents (entries, in index order) change as the list model says
#   (model.bend): set_range keeps every entry's part below a, then [a, b],
#   then every entry's part above b; clear_range the same without [a, b];
#   an inverted range (a > b) changes nothing, and store_range refuses it
#   with MapleInverted;
# * the lookups (load, lookup, find, next, prev) and the gap search answer
#   exactly what the model's scan of the entries answers;
# * after set_range(t, a, b, v), every index of [a, b] loads v and every
#   other index loads what it loaded before; after clear_range(t, a, b),
#   every index of [a, b] loads nothing and every other index is unchanged;
#   erase(t, i) clears exactly the range of the entry holding i;
# * iteration: find(t, 0) is the first entry, next(t, last of an entry) the
#   entry after it, and None after the last; prev(t, first of an entry) is
#   the entry before it;
# * the gap search: an answer s lies within [min, max] with its run
#   [s, s + size - 1], which does not wrap and holds nothing; whenever some
#   run of size free indices lies within [min, max], the search answers, and
#   at or below that run's start; size 0 and max < min are refused.
#
# Vectors: updates and lookups on a small tree, and an instance of each
# hypothesis the properties carry, so that none is vacuous. That nodes stay
# between half full and full (balanced, which bounds the height by the
# logarithm of the size) is tested (ref/, check.bend) and checked on a
# vector, not proved for every input.
import Base
import ./model.bend as M
import ./node.bend as N
import ./maple.bend as T
import ./gap.bend as G

# The invariant

law valid_empty:
  for -V: Data
  {T.Maple32.valid(V, T.Maple32.empty(V)) == True{} : Bool}

law valid_empty_with:
  for -V: Data
  for o: N.MapleOptions
  {T.Maple32.valid(V, T.Maple32.empty_with(V, o)) == True{} : Bool}

law valid_set_range:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.valid(V, T.Maple32.set_range(V, t, a, b, v)) == True{} : Bool}

law valid_clear_range:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.valid(V, T.Maple32.clear_range(V, t, a, b)) == True{} : Bool}

law valid_erase:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.valid(V, T.Maple32.erase(V, t, i)) == True{} : Bool}

# the entries of a valid tree are in index order and disjoint
law valid_disjoint:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {M.MapleModel32.wf(V, T.Maple32.entries(V, t)) == True{} : Bool}

# every leaf is at the same depth, the tree's height

law leveled_empty:
  for -V: Data
  {T.Maple32.leveled(V, T.Maple32.empty(V)) == True{} : Bool}

law leveled_empty_with:
  for -V: Data
  for o: N.MapleOptions
  {T.Maple32.leveled(V, T.Maple32.empty_with(V, o)) == True{} : Bool}

law leveled_set_range:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +e: {T.Maple32.leveled(V, t) == True{} : Bool}
  {T.Maple32.leveled(V, T.Maple32.set_range(V, t, a, b, v)) == True{} : Bool}

law leveled_clear_range:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +e: {T.Maple32.leveled(V, t) == True{} : Bool}
  {T.Maple32.leveled(V, T.Maple32.clear_range(V, t, a, b)) == True{} : Bool}

law leveled_erase:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +e: {T.Maple32.leveled(V, t) == True{} : Bool}
  {T.Maple32.leveled(V, T.Maple32.erase(V, t, i)) == True{} : Bool}

# The contents

law set_range_entries:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.entries(V, T.Maple32.set_range(V, t, a, b, v)) == M.MapleModel32.set_range(V, T.Maple32.entries(V, t), a, b, v) : List<&2, M.MapleEntry<U32, V>>}

law clear_range_entries:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.entries(V, T.Maple32.clear_range(V, t, a, b)) == M.MapleModel32.clear_range(V, T.Maple32.entries(V, t), a, b) : List<&2, M.MapleEntry<U32, V>>}

law set_range_inverted:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +e: {U32.is_lt(b, a) == True{} : Bool}
  {T.Maple32.set_range(V, t, a, b, v) == t : N.MapleTree<U32, V>}

law clear_range_inverted:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +e: {U32.is_lt(b, a) == True{} : Bool}
  {T.Maple32.clear_range(V, t, a, b) == t : N.MapleTree<U32, V>}

law store_range_inverted:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +e: {U32.is_lt(b, a) == True{} : Bool}
  {T.Maple32.store_range(V, t, a, b, v) == Fail{M.MapleInverted{a, b}} : Result<&2, &2, M.MapleError<U32>, N.MapleTree<U32, V>>}

law store_range_ok:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +e: {U32.is_le(a, b) == True{} : Bool}
  {T.Maple32.store_range(V, t, a, b, v) == Done{T.Maple32.set_range(V, t, a, b, v)} : Result<&2, &2, M.MapleError<U32>, N.MapleTree<U32, V>>}

law store_single:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +v: V
  {T.Maple32.store(V, t, i, v) == T.Maple32.set_range(V, t, i, i, v) : N.MapleTree<U32, V>}

# The lookups

law load_spec:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.load(V, t, i) == M.MapleModel32.load(V, T.Maple32.entries(V, t), i) : Maybe<&2, V>}

law lookup_spec:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.lookup(V, t, i) == M.MapleModel32.lookup(V, T.Maple32.entries(V, t), i) : Maybe<&2, M.MapleEntry<U32, V>>}

law find_spec:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.find(V, t, i) == M.MapleModel32.find(V, T.Maple32.entries(V, t), i) : Maybe<&2, M.MapleEntry<U32, V>>}

law next_spec:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.next(V, t, i) == M.MapleModel32.next(V, T.Maple32.entries(V, t), i) : Maybe<&2, M.MapleEntry<U32, V>>}

law prev_spec:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {T.Maple32.prev(V, t, i) == M.MapleModel32.prev(V, T.Maple32.entries(V, t), i) : Maybe<&2, M.MapleEntry<U32, V>>}

law empty_area_spec:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +min: U32
  for +max: U32
  for +size: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  {G.Maple32.empty_area(V, t, min, max, size) == M.MapleModel32.empty_area(V, T.Maple32.entries(V, t), min, max, size) : Result<&2, &2, M.MapleError<U32>, U32>}

# After an update

law set_range_load_in:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {U32.is_le(a, i) == True{} : Bool}
  for +g: {U32.is_le(i, b) == True{} : Bool}
  {T.Maple32.load(V, T.Maple32.set_range(V, t, a, b, v), i) == Some{v} : Maybe<&2, V>}

law set_range_load_out:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {Bool.and(U32.is_le(a, i), U32.is_le(i, b)) == False{} : Bool}
  {T.Maple32.load(V, T.Maple32.set_range(V, t, a, b, v), i) == T.Maple32.load(V, t, i) : Maybe<&2, V>}

law clear_range_load_in:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {U32.is_le(a, i) == True{} : Bool}
  for +g: {U32.is_le(i, b) == True{} : Bool}
  {T.Maple32.load(V, T.Maple32.clear_range(V, t, a, b), i) == None{} : Maybe<&2, V>}

law clear_range_load_out:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {Bool.and(U32.is_le(a, i), U32.is_le(i, b)) == False{} : Bool}
  {T.Maple32.load(V, T.Maple32.clear_range(V, t, a, b), i) == T.Maple32.load(V, t, i) : Maybe<&2, V>}

law lookup_holds:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +x: M.MapleEntry<U32, V>
  for +f: {T.Maple32.lookup(V, t, i) == Some{x} : Maybe<&2, M.MapleEntry<U32, V>>}
  {M.MapleEntry32.holds(V, x, i) == True{} : Bool}

law erase_load_in:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +x: M.MapleEntry<U32, V>
  for +j: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {T.Maple32.lookup(V, t, i) == Some{x} : Maybe<&2, M.MapleEntry<U32, V>>}
  for +g: {M.MapleEntry32.holds(V, x, j) == True{} : Bool}
  {T.Maple32.load(V, T.Maple32.erase(V, t, i), j) == None{} : Maybe<&2, V>}

law erase_load_out:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +x: M.MapleEntry<U32, V>
  for +j: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {T.Maple32.lookup(V, t, i) == Some{x} : Maybe<&2, M.MapleEntry<U32, V>>}
  for +g: {M.MapleEntry32.holds(V, x, j) == False{} : Bool}
  {T.Maple32.load(V, T.Maple32.erase(V, t, i), j) == T.Maple32.load(V, t, j) : Maybe<&2, V>}

law erase_absent:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +f: {T.Maple32.lookup(V, t, i) == None{} : Maybe<&2, M.MapleEntry<U32, V>>}
  {T.Maple32.erase(V, t, i) == t : N.MapleTree<U32, V>}

# Iteration

law find_first:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +x: M.MapleEntry<U32, V>
  for +ys: List<&2, M.MapleEntry<U32, V>>
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {T.Maple32.entries(V, t) == Con{x, ys} : List<&2, M.MapleEntry<U32, V>>}
  {T.Maple32.find(V, t, 0) == Some{x} : Maybe<&2, M.MapleEntry<U32, V>>}

law next_after:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +xs: List<&2, M.MapleEntry<U32, V>>
  for +x: M.MapleEntry<U32, V>
  for +y: M.MapleEntry<U32, V>
  for +ys: List<&2, M.MapleEntry<U32, V>>
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {T.Maple32.entries(V, t) == List.append(&2, M.MapleEntry<U32, V>, xs, Con{x, Con{y, ys}}) : List<&2, M.MapleEntry<U32, V>>}
  {T.Maple32.next(V, t, M.MapleEntry.last(U32, V, x)) == Some{y} : Maybe<&2, M.MapleEntry<U32, V>>}

law next_none:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +xs: List<&2, M.MapleEntry<U32, V>>
  for +x: M.MapleEntry<U32, V>
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {T.Maple32.entries(V, t) == List.append(&2, M.MapleEntry<U32, V>, xs, Con{x, Nil{}}) : List<&2, M.MapleEntry<U32, V>>}
  {T.Maple32.next(V, t, M.MapleEntry.last(U32, V, x)) == None{} : Maybe<&2, M.MapleEntry<U32, V>>}

law prev_before:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +xs: List<&2, M.MapleEntry<U32, V>>
  for +x: M.MapleEntry<U32, V>
  for +y: M.MapleEntry<U32, V>
  for +ys: List<&2, M.MapleEntry<U32, V>>
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {T.Maple32.entries(V, t) == List.append(&2, M.MapleEntry<U32, V>, xs, Con{x, Con{y, ys}}) : List<&2, M.MapleEntry<U32, V>>}
  {T.Maple32.prev(V, t, M.MapleEntry.first(U32, V, y)) == Some{x} : Maybe<&2, M.MapleEntry<U32, V>>}

# The gap search

law empty_area_zero:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +min: U32
  for +max: U32
  {G.Maple32.empty_area(V, t, min, max, 0) == Fail{M.MapleBadSize{}} : Result<&2, &2, M.MapleError<U32>, U32>}

law empty_area_inverted:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +min: U32
  for +max: U32
  for +size: U32
  for +f: {U32.is_eq(size, 0) == False{} : Bool}
  for +g: {U32.is_lt(max, min) == True{} : Bool}
  {G.Maple32.empty_area(V, t, min, max, size) == Fail{M.MapleBadRange{min, max}} : Result<&2, &2, M.MapleError<U32>, U32>}

law empty_area_bounds:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +min: U32
  for +max: U32
  for +size: U32
  for +s: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {G.Maple32.empty_area(V, t, min, max, size) == Done{s} : Result<&2, &2, M.MapleError<U32>, U32>}
  {Bool.and(U32.is_le(min, s), Bool.and(U32.is_le(s, U32.add(s, U32.sub(size, 1))), U32.is_le(U32.add(s, U32.sub(size, 1)), max))) == True{} : Bool}

law empty_area_free:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +min: U32
  for +max: U32
  for +size: U32
  for +s: U32
  for +i: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {G.Maple32.empty_area(V, t, min, max, size) == Done{s} : Result<&2, &2, M.MapleError<U32>, U32>}
  for +g: {U32.is_le(s, i) == True{} : Bool}
  for +h: {U32.is_le(i, U32.add(s, U32.sub(size, 1))) == True{} : Bool}
  {T.Maple32.load(V, t, i) == None{} : Maybe<&2, V>}

# a free run of size indices from s, within [min, max], is found
law empty_area_found:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +min: U32
  for +max: U32
  for +size: U32
  for +s: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {U32.is_eq(size, 0) == False{} : Bool}
  for +g: {Bool.and(U32.is_le(min, s), Bool.and(U32.is_le(s, U32.add(s, U32.sub(size, 1))), U32.is_le(U32.add(s, U32.sub(size, 1)), max))) == True{} : Bool}
  for h: @i:U32 -> {U32.is_le(s, i) == True{} : Bool} -> {U32.is_le(i, U32.add(s, U32.sub(size, 1))) == True{} : Bool} -> {T.Maple32.load(V, t, i) == None{} : Maybe<&2, V>}
  {Result.is_done(&2, &2, M.MapleError<U32>, U32, G.Maple32.empty_area(V, t, min, max, size)) == True{} : Bool}

# ... and the answer is the lowest such start
law empty_area_lowest:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +min: U32
  for +max: U32
  for +size: U32
  for +r: U32
  for +s: U32
  for +e: {T.Maple32.valid(V, t) == True{} : Bool}
  for +f: {G.Maple32.empty_area(V, t, min, max, size) == Done{r} : Result<&2, &2, M.MapleError<U32>, U32>}
  for +g: {Bool.and(U32.is_le(min, s), Bool.and(U32.is_le(s, U32.add(s, U32.sub(size, 1))), U32.is_le(U32.add(s, U32.sub(size, 1)), max))) == True{} : Bool}
  for h: @i:U32 -> {U32.is_le(s, i) == True{} : Bool} -> {U32.is_le(i, U32.add(s, U32.sub(size, 1))) == True{} : Bool} -> {T.Maple32.load(V, t, i) == None{} : Maybe<&2, V>}
  {U32.is_le(r, s) == True{} : Bool}

# Vectors, on the tree holding [10, 20] -> 1 and [30, 40] -> 2, overwritten
# by [15, 35] -> 3: [10, 14] -> 1, [15, 35] -> 3, [36, 40] -> 2

law example_entries:
  {T.Maple32.entries(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3)) == [M.MapleEntry{10, 14, 1}, M.MapleEntry{15, 35, 3}, M.MapleEntry{36, 40, 2}] : List<&2, M.MapleEntry<U32, U32>>}

law example_valid:
  {T.Maple32.valid(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3)) == True{} : Bool}

law example_balanced:
  {T.Maple32.balanced(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3)) == True{} : Bool}

law example_split:
  {T.Maple32.entries(U32, T.Maple32.store(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 100, 200, 4), 150, 5)) == [M.MapleEntry{100, 149, 4}, M.MapleEntry{150, 150, 5}, M.MapleEntry{151, 200, 4}] : List<&2, M.MapleEntry<U32, U32>>}

law example_load:
  {T.Maple32.load(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 36) == Some{2} : Maybe<&2, U32>}

law example_clear:
  {T.Maple32.entries(U32, T.Maple32.clear_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 12, 16)) == [M.MapleEntry{10, 11, 1}, M.MapleEntry{17, 35, 3}, M.MapleEntry{36, 40, 2}] : List<&2, M.MapleEntry<U32, U32>>}

law example_erase:
  {T.Maple32.entries(U32, T.Maple32.erase(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 20)) == [M.MapleEntry{10, 14, 1}, M.MapleEntry{36, 40, 2}] : List<&2, M.MapleEntry<U32, U32>>}

law example_lookup:
  {T.Maple32.lookup(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 20) == Some{M.MapleEntry{15, 35, 3}} : Maybe<&2, M.MapleEntry<U32, U32>>}

law example_lookup_none:
  {T.Maple32.lookup(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 41) == None{} : Maybe<&2, M.MapleEntry<U32, U32>>}

law example_next:
  {T.Maple32.next(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 15) == Some{M.MapleEntry{36, 40, 2}} : Maybe<&2, M.MapleEntry<U32, U32>>}

law example_prev:
  {T.Maple32.prev(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 15) == Some{M.MapleEntry{10, 14, 1}} : Maybe<&2, M.MapleEntry<U32, U32>>}

law example_gap:
  {G.Maple32.empty_area(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 5, 100, 11) == Done{41} : Result<&2, &2, M.MapleError<U32>, U32>}

law example_gap_busy:
  {G.Maple32.empty_area(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3), 10, 40, 1) == Fail{M.MapleBusy{}} : Result<&2, &2, M.MapleError<U32>, U32>}

law example_store_inverted:
  {T.Maple32.store_range(U32, T.Maple32.empty(U32), 9, 3, 0) == Fail{M.MapleInverted{9, 3}} : Result<&2, &2, M.MapleError<U32>, N.MapleTree<U32, U32>>}

# a tree of order 3 holding ten ranges, then cleared over [25, 44]: height
# 2, every leaf at depth 2, and within the fill bounds
law example_deep:
  {Bool.and(Nat.is_eq(T.Maple32.height(U32, T.Maple32.clear_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty_with(U32, N.MapleOptions{3n}), 80, 89, 8), 90, 99, 9), 0, 9, 0), 10, 19, 1), 20, 29, 2), 30, 39, 3), 40, 49, 4), 50, 59, 5), 60, 69, 6), 70, 79, 7), 25, 44)), 2n), Bool.and(T.Maple32.leveled(U32, T.Maple32.clear_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty_with(U32, N.MapleOptions{3n}), 80, 89, 8), 90, 99, 9), 0, 9, 0), 10, 19, 1), 20, 29, 2), 30, 39, 3), 40, 49, 4), 50, 59, 5), 60, 69, 6), 70, 79, 7), 25, 44)), T.Maple32.balanced(U32, T.Maple32.clear_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty_with(U32, N.MapleOptions{3n}), 80, 89, 8), 90, 99, 9), 0, 9, 0), 10, 19, 1), 20, 29, 2), 30, 39, 3), 40, 49, 4), 50, 59, 5), 60, 69, 6), 70, 79, 7), 25, 44)))) == True{} : Bool}

# instances of the hypotheses: indices in a range and outside it, an
# inverted range, the demo tree's entries split around an entry and ending
# in one, an entry holding an index and one not, a nonzero size, and a free
# run (in the empty tree, every index is free)

law example_in_range:
  {Bool.and(U32.is_le(15, 20), U32.is_le(20, 35)) == True{} : Bool}

law example_out_of_range:
  {Bool.and(U32.is_le(15, 41), U32.is_le(41, 35)) == False{} : Bool}

law example_inverted:
  {U32.is_lt(3, 9) == True{} : Bool}

law example_split_entries:
  {T.Maple32.entries(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3)) == List.append(&2, M.MapleEntry<U32, U32>, [M.MapleEntry{10, 14, 1}], Con{M.MapleEntry{15, 35, 3}, Con{M.MapleEntry{36, 40, 2}, Nil{}}}) : List<&2, M.MapleEntry<U32, U32>>}

law example_last_entry:
  {T.Maple32.entries(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3)) == List.append(&2, M.MapleEntry<U32, U32>, [M.MapleEntry{10, 14, 1}, M.MapleEntry{15, 35, 3}], Con{M.MapleEntry{36, 40, 2}, Nil{}}) : List<&2, M.MapleEntry<U32, U32>>}

law example_holds:
  {Bool.and(M.MapleEntry32.holds(U32, M.MapleEntry{15, 35, 3}, 30), Bool.not(M.MapleEntry32.holds(U32, M.MapleEntry{15, 35, 3}, 36))) == True{} : Bool}

law example_size:
  {U32.is_eq(5, 0) == False{} : Bool}

law example_free_run:
  for i: U32
  for +f: {U32.is_le(0, i) == True{} : Bool}
  for +g: {U32.is_le(i, U32.add(0, U32.sub(5, 1))) == True{} : Bool}
  {T.Maple32.load(U32, T.Maple32.empty(U32), i) == None{} : Maybe<&2, U32>}

law example_gap_empty:
  {G.Maple32.empty_area(U32, T.Maple32.empty(U32), 0, 100, 5) == Done{0} : Result<&2, &2, M.MapleError<U32>, U32>}

law example_free_run_bounds:
  {Bool.and(U32.is_le(0, 0), Bool.and(U32.is_le(0, U32.add(0, U32.sub(5, 1))), U32.is_le(U32.add(0, U32.sub(5, 1)), 100))) == True{} : Bool}
