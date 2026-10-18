# The laws of the XArray, for every array t, every index and every value
# (and every value type V), over the public interface only. Indices are U32,
# compared with Base's U32.cmp; "i != j" is U32.is_eq(i, j) == False.
#
# Entries: a load after a store at the same index gives the value; a store
# leaves every other index's load unchanged; a load after an erase gives
# nothing, and an erase leaves every other index unchanged. insert is store
# at an index that holds no entry, and fails with XArrayBusy at one that does.
#
# Emptiness: is_empty is True exactly when no index holds an entry.
#
# Search: find(t, s) answers the smallest index at or after s that holds an
# entry, or None when there is none; find_last(t, s) the largest at or before
# s. Each is stated as: the answer holds an entry, lies on the right side of
# s, and nothing lies between s and it; and None means nothing lies past s.
#
# Iteration: range(t, a, b) lists exactly the entries whose indices lie in
# [a, b], each with its value, in strictly ascending order of index.
#
# Marks: a mark set on an index that holds an entry is seen; a mark is never
# set on an index that holds none; a cleared mark is not seen; setting or
# clearing a mark changes no other index, no other mark and no entry; an
# erase clears the index's marks; a store keeps them; find_marked is find over
# the indices that carry the mark.
#
# Vectors: a small array, its searches and its range.
import Base
import ./xarray.bend as X

# Entries

law load_empty:
  for -V: Data
  for i: U32
  {X.XArray.load(V, X.XArray.empty(V), i) == None{} : Maybe<&2, V>}

law load_store:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for v: V
  {X.XArray.load(V, X.XArray.store(V, t, i, v), i) == Some{v} : Maybe<&2, V>}

law load_store_other:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for v: V
  for e: {U32.is_eq(i, j) == False{} : Bool}
  {X.XArray.load(V, X.XArray.store(V, t, i, v), j) == X.XArray.load(V, t, j) : Maybe<&2, V>}

law load_erase:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  {X.XArray.load(V, X.XArray.erase(V, t, i), i) == None{} : Maybe<&2, V>}

law load_erase_other:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for e: {U32.is_eq(i, j) == False{} : Bool}
  {X.XArray.load(V, X.XArray.erase(V, t, i), j) == X.XArray.load(V, t, j) : Maybe<&2, V>}

# insert stores only at an index that holds no entry
law insert_absent:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for v: V
  for e: {X.XArray.load(V, t, i) == None{} : Maybe<&2, V>}
  {X.XArray.insert(V, t, i, v) == Done{X.XArray.store(V, t, i, v)} : Result<&2, &2, X.XArrayError, X.XArray<V>>}

law insert_present:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for v: V
  for w: V
  for e: {X.XArray.load(V, t, i) == Some{w} : Maybe<&2, V>}
  {X.XArray.insert(V, t, i, v) == Fail{X.XArrayBusy{}} : Result<&2, &2, X.XArrayError, X.XArray<V>>}

# Emptiness

law is_empty_empty:
  for -V: Data
  {X.XArray.is_empty(V, X.XArray.empty(V)) == True{} : Bool}

law is_empty_load:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for e: {X.XArray.is_empty(V, t) == True{} : Bool}
  {X.XArray.load(V, t, i) == None{} : Maybe<&2, V>}

law is_empty_store:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for v: V
  {X.XArray.is_empty(V, X.XArray.store(V, t, i, v)) == False{} : Bool}

law is_empty_false:
  for -V: Data
  for t: X.XArray<V>
  for e: {X.XArray.is_empty(V, t) == False{} : Bool}
  exs i: U32
  {Maybe.is_some(&2, V, X.XArray.load(V, t, i)) == True{} : Bool}

# Search upward: find

law find_present:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for k: U32
  for e: {X.XArray.find(V, t, s) == Some{k} : Maybe<&2, U32>}
  {Maybe.is_some(&2, V, X.XArray.load(V, t, k)) == True{} : Bool}

law find_at_or_after:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for k: U32
  for e: {X.XArray.find(V, t, s) == Some{k} : Maybe<&2, U32>}
  {U32.is_le(s, k) == True{} : Bool}

law find_first:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for k: U32
  for j: U32
  for e: {X.XArray.find(V, t, s) == Some{k} : Maybe<&2, U32>}
  for h1: {U32.is_le(s, j) == True{} : Bool}
  for h2: {U32.is_lt(j, k) == True{} : Bool}
  {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}

law find_none:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for j: U32
  for e: {X.XArray.find(V, t, s) == None{} : Maybe<&2, U32>}
  for h: {U32.is_le(s, j) == True{} : Bool}
  {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}

# Search downward: find_last

law find_last_present:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for k: U32
  for e: {X.XArray.find_last(V, t, s) == Some{k} : Maybe<&2, U32>}
  {Maybe.is_some(&2, V, X.XArray.load(V, t, k)) == True{} : Bool}

law find_last_at_or_before:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for k: U32
  for e: {X.XArray.find_last(V, t, s) == Some{k} : Maybe<&2, U32>}
  {U32.is_le(k, s) == True{} : Bool}

law find_last_last:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for k: U32
  for j: U32
  for e: {X.XArray.find_last(V, t, s) == Some{k} : Maybe<&2, U32>}
  for h1: {U32.is_le(j, s) == True{} : Bool}
  for h2: {U32.is_lt(k, j) == True{} : Bool}
  {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}

law find_last_none:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for j: U32
  for e: {X.XArray.find_last(V, t, s) == None{} : Maybe<&2, U32>}
  for h: {U32.is_le(j, s) == True{} : Bool}
  {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}

# Iteration over a range

law range_present:
  for -V: Data
  for t: X.XArray<V>
  for a: U32
  for b: U32
  for k: Nat
  for i: U32
  for v: V
  for e: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}
  {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>}

law range_from:
  for -V: Data
  for t: X.XArray<V>
  for a: U32
  for b: U32
  for k: Nat
  for i: U32
  for v: V
  for e: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}
  {U32.is_le(a, i) == True{} : Bool}

law range_to:
  for -V: Data
  for t: X.XArray<V>
  for a: U32
  for b: U32
  for k: Nat
  for i: U32
  for v: V
  for e: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}
  {U32.is_le(i, b) == True{} : Bool}

law range_ascending:
  for -V: Data
  for t: X.XArray<V>
  for a: U32
  for b: U32
  for k: Nat
  for i: U32
  for v: V
  for j: U32
  for w: V
  for e1: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}
  for e2: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), 1n+k) == Some{X.XEntry{j, w}} : Maybe<&2, X.XEntry<V>>}
  {U32.is_lt(i, j) == True{} : Bool}

law range_complete:
  for -V: Data
  for t: X.XArray<V>
  for a: U32
  for b: U32
  for i: U32
  for v: V
  for h1: {U32.is_le(a, i) == True{} : Bool}
  for h2: {U32.is_le(i, b) == True{} : Bool}
  for h3: {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>}
  exs k: Nat
  {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}

# Marks

law mark_empty:
  for -V: Data
  for i: U32
  for m: X.XMark
  {X.XArray.get_mark(V, X.XArray.empty(V), i, m) == False{} : Bool}

law mark_set:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for m: X.XMark
  for v: V
  for e: {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>}
  {X.XArray.get_mark(V, X.XArray.set_mark(V, t, i, m), i, m) == True{} : Bool}

law mark_set_absent:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for m: X.XMark
  for e: {X.XArray.load(V, t, i) == None{} : Maybe<&2, V>}
  {X.XArray.set_mark(V, t, i, m) == t : X.XArray<V>}

law mark_clear:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for m: X.XMark
  {X.XArray.get_mark(V, X.XArray.clear_mark(V, t, i, m), i, m) == False{} : Bool}

law mark_set_other_index:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for m: X.XMark
  for n: X.XMark
  for e: {U32.is_eq(i, j) == False{} : Bool}
  {X.XArray.get_mark(V, X.XArray.set_mark(V, t, i, m), j, n) == X.XArray.get_mark(V, t, j, n) : Bool}

law mark_set_other_mark:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for m: X.XMark
  for n: X.XMark
  for e: {X.XMark.is_eq(m, n) == False{} : Bool}
  {X.XArray.get_mark(V, X.XArray.set_mark(V, t, i, m), j, n) == X.XArray.get_mark(V, t, j, n) : Bool}

law mark_clear_other_index:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for m: X.XMark
  for n: X.XMark
  for e: {U32.is_eq(i, j) == False{} : Bool}
  {X.XArray.get_mark(V, X.XArray.clear_mark(V, t, i, m), j, n) == X.XArray.get_mark(V, t, j, n) : Bool}

law mark_clear_other_mark:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for m: X.XMark
  for n: X.XMark
  for e: {X.XMark.is_eq(m, n) == False{} : Bool}
  {X.XArray.get_mark(V, X.XArray.clear_mark(V, t, i, m), j, n) == X.XArray.get_mark(V, t, j, n) : Bool}

law load_set_mark:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for m: X.XMark
  {X.XArray.load(V, X.XArray.set_mark(V, t, i, m), j) == X.XArray.load(V, t, j) : Maybe<&2, V>}

law load_clear_mark:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for m: X.XMark
  {X.XArray.load(V, X.XArray.clear_mark(V, t, i, m), j) == X.XArray.load(V, t, j) : Maybe<&2, V>}

law mark_erase:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for m: X.XMark
  {X.XArray.get_mark(V, X.XArray.erase(V, t, i), i, m) == False{} : Bool}

law mark_erase_other:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for m: X.XMark
  for e: {U32.is_eq(i, j) == False{} : Bool}
  {X.XArray.get_mark(V, X.XArray.erase(V, t, i), j, m) == X.XArray.get_mark(V, t, j, m) : Bool}

law mark_store:
  for -V: Data
  for t: X.XArray<V>
  for i: U32
  for j: U32
  for v: V
  for m: X.XMark
  {X.XArray.get_mark(V, X.XArray.store(V, t, i, v), j, m) == X.XArray.get_mark(V, t, j, m) : Bool}

# Search over a mark

law find_marked_present:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for m: X.XMark
  for k: U32
  for e: {X.XArray.find_marked(V, t, s, m) == Some{k} : Maybe<&2, U32>}
  {X.XArray.get_mark(V, t, k, m) == True{} : Bool}

law find_marked_at_or_after:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for m: X.XMark
  for k: U32
  for e: {X.XArray.find_marked(V, t, s, m) == Some{k} : Maybe<&2, U32>}
  {U32.is_le(s, k) == True{} : Bool}

law find_marked_first:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for m: X.XMark
  for k: U32
  for j: U32
  for e: {X.XArray.find_marked(V, t, s, m) == Some{k} : Maybe<&2, U32>}
  for h1: {U32.is_le(s, j) == True{} : Bool}
  for h2: {U32.is_lt(j, k) == True{} : Bool}
  {X.XArray.get_mark(V, t, j, m) == False{} : Bool}

law find_marked_none:
  for -V: Data
  for t: X.XArray<V>
  for s: U32
  for m: X.XMark
  for j: U32
  for e: {X.XArray.find_marked(V, t, s, m) == None{} : Maybe<&2, U32>}
  for h: {U32.is_le(s, j) == True{} : Bool}
  {X.XArray.get_mark(V, t, j, m) == False{} : Bool}

# Vectors: entries at 5, 6 and 4000000000 (0xEE6B2800), and a mark on 6

law vec_find:
  {X.XArray.find(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.empty(U32), 5, 50), 4000000000, 7), 6, 60), 7) == Some{4000000000} : Maybe<&2, U32>}

law vec_find_last:
  {X.XArray.find_last(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.empty(U32), 5, 50), 4000000000, 7), 6, 60), 3999999999) == Some{6} : Maybe<&2, U32>}

law vec_find_none:
  {X.XArray.find(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.empty(U32), 5, 50), 4000000000, 7), 6, 60), 4000000001) == None{} : Maybe<&2, U32>}

law vec_range:
  {X.XArray.range(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.empty(U32), 5, 50), 4000000000, 7), 6, 60), 0, 4294967295) == [X.XEntry{5, 50}, X.XEntry{6, 60}, X.XEntry{4000000000, 7}] : List<&2, X.XEntry<U32>>}

law vec_erase_empty:
  {X.XArray.is_empty(U32, X.XArray.erase(U32, X.XArray.erase(U32, X.XArray.erase(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.empty(U32), 5, 50), 4000000000, 7), 6, 60), 6), 5), 4000000000)) == True{} : Bool}

law vec_find_marked:
  {X.XArray.find_marked(U32, X.XArray.set_mark(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.empty(U32), 5, 50), 4000000000, 7), 6, 60), 6, X.XMark1{}), 0, X.XMark1{}) == Some{6} : Maybe<&2, U32>}
