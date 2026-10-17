# DRAFT: not yet reviewed by the maintainer
#
# The laws are stated for the named default, ITree32 (U32 keys in U32.cmp's
# order), and for every value type V. "valid" is ITree32.valid: the keys of
# the contents strictly increase, and every node stores the largest last of
# its subtree. Properties, for every tree, interval and query:
#
# * the invariant: the empty tree is valid, and set and remove keep a tree
#   valid;
# * the contents (to_list, in key order) change as the list model says (a
#   plain scan, in model.bend): set puts the interval in its place, replacing
#   the value of an equal key; an inverted interval (start > last) changes
#   nothing, and insert refuses it with ITreeInverted; remove drops exactly
#   the interval with that key;
# * the queries return exactly what the model's scan of the contents
#   returns: overlapping and stab the overlapping entries in key order,
#   first the first of them, next the first after a given key, lookup the
#   value of a key;
# * after set, lookup finds the value, and so does a query that overlaps the
#   interval; after remove, lookup finds nothing;
# * the augmented maximum: max_last is at least every last in the tree, and
#   is the last of one of its entries.
#
# Vectors: queries and updates on a small tree, and an instance of each
# hypothesis the properties carry, so that each is satisfiable.
import Base
import ./itree.bend as T
import ./model.bend as M

# The invariant

law valid_empty:
  for -V: Data
  {T.ITree32.valid(V, T.ITree32.empty(V)) == True{} : Bool}

law valid_set:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +v: V
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.valid(V, T.ITree32.set(V, t, s, l, v)) == True{} : Bool}

law valid_remove:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.valid(V, T.ITree32.remove(V, t, s, l)) == True{} : Bool}

# The contents

law set_contents:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +v: V
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.to_list(V, T.ITree32.set(V, t, s, l, v)) == M.ITreeModel32.set(V, T.ITree32.to_list(V, t), s, l, v) : List<&2, T.ITreeEntry<U32, V>>}

law remove_contents:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.to_list(V, T.ITree32.remove(V, t, s, l)) == M.ITreeModel32.remove(V, T.ITree32.to_list(V, t), s, l) : List<&2, T.ITreeEntry<U32, V>>}

law set_inverted:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +v: V
  for e: {U32.is_lt(l, s) == True{} : Bool}
  {T.ITree32.set(V, t, s, l, v) == t : T.ITree<U32, V>}

law insert_inverted:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +v: V
  for e: {U32.is_lt(l, s) == True{} : Bool}
  {T.ITree32.insert(V, t, s, l, v) == Fail{T.ITreeInverted{s, l}} : Result<&2, &2, T.ITreeError<U32>, T.ITree<U32, V>>}

law insert_set:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +v: V
  for e: {U32.is_le(s, l) == True{} : Bool}
  {T.ITree32.insert(V, t, s, l, v) == Done{T.ITree32.set(V, t, s, l, v)} : Result<&2, &2, T.ITreeError<U32>, T.ITree<U32, V>>}

# The queries

law overlapping_spec:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +a: U32
  for +b: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.overlapping(V, t, a, b) == M.ITreeModel32.overlapping(V, T.ITree32.to_list(V, t), a, b) : List<&2, T.ITreeEntry<U32, V>>}

law stab_spec:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +p: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.stab(V, t, p) == M.ITreeModel32.overlapping(V, T.ITree32.to_list(V, t), p, p) : List<&2, T.ITreeEntry<U32, V>>}

law first_spec:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +a: U32
  for +b: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.first(V, t, a, b) == M.ITreeModel32.first(V, T.ITree32.to_list(V, t), a, b) : Maybe<&2, T.ITreeEntry<U32, V>>}

law next_spec:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +a: U32
  for +b: U32
  for +s: U32
  for +l: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.next(V, t, a, b, s, l) == M.ITreeModel32.next(V, T.ITree32.to_list(V, t), a, b, s, l) : Maybe<&2, T.ITreeEntry<U32, V>>}

law lookup_spec:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.lookup(V, t, s, l) == M.ITreeModel32.lookup(V, T.ITree32.to_list(V, t), s, l) : Maybe<&2, V>}

# After an update

law set_lookup:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +v: V
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  for f: {U32.is_le(s, l) == True{} : Bool}
  {T.ITree32.lookup(V, T.ITree32.set(V, t, s, l, v), s, l) == Some{v} : Maybe<&2, V>}

law set_found:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +v: V
  for +a: U32
  for +b: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  for f: {U32.is_le(s, l) == True{} : Bool}
  for g: {T.ITree32.overlaps(s, l, a, b) == True{} : Bool}
  {M.ITreeModel32.lookup(V, T.ITree32.overlapping(V, T.ITree32.set(V, t, s, l, v), a, b), s, l) == Some{v} : Maybe<&2, V>}

law remove_lookup:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  {T.ITree32.lookup(V, T.ITree32.remove(V, t, s, l), s, l) == None{} : Maybe<&2, V>}

# The augmented maximum

law max_last_upper:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +m: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  for f: {T.ITree32.max_last(V, t) == Some{m} : Maybe<&2, U32>}
  {M.ITreeModel32.lasts_le(V, T.ITree32.to_list(V, t), m) == True{} : Bool}

law max_last_attained:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +m: U32
  for +e: {T.ITree32.valid(V, t) == True{} : Bool}
  for f: {T.ITree32.max_last(V, t) == Some{m} : Maybe<&2, U32>}
  {M.ITreeModel32.has_last(V, T.ITree32.to_list(V, t), m) == True{} : Bool}

law max_last_empty:
  for -V: Data
  for +t: T.ITree<U32, V>
  for f: {T.ITree32.max_last(V, t) == None{} : Maybe<&2, U32>}
  {T.ITree32.to_list(V, t) == Nil{} : List<&2, T.ITreeEntry<U32, V>>}

# Vectors, on the tree holding [10, 20], [5, 8], [15, 30], [25, 26] and
# [1, 3] (with values 1 to 5), built by set

law example_valid:
  {T.ITree32.valid(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5)) == True{} : Bool}

law example_balanced:
  {T.ITree32.balanced(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5)) == True{} : Bool}

law example_contents:
  {T.ITree32.to_list(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5)) == [T.ITreeEntry{1, 3, 5}, T.ITreeEntry{5, 8, 2}, T.ITreeEntry{10, 20, 1}, T.ITreeEntry{15, 30, 3}, T.ITreeEntry{25, 26, 4}] : List<&2, T.ITreeEntry<U32, U32>>}

law example_overlapping:
  {T.ITree32.overlapping(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5), 7, 12) == [T.ITreeEntry{5, 8, 2}, T.ITreeEntry{10, 20, 1}] : List<&2, T.ITreeEntry<U32, U32>>}

law example_stab:
  {T.ITree32.stab(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5), 25) == [T.ITreeEntry{15, 30, 3}, T.ITreeEntry{25, 26, 4}] : List<&2, T.ITreeEntry<U32, U32>>}

law example_first:
  {T.ITree32.first(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5), 9, 40) == Some{T.ITreeEntry{10, 20, 1}} : Maybe<&2, T.ITreeEntry<U32, U32>>}

law example_next:
  {T.ITree32.next(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5), 9, 40, 15, 30) == Some{T.ITreeEntry{25, 26, 4}} : Maybe<&2, T.ITreeEntry<U32, U32>>}

law example_none:
  {T.ITree32.first(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5), 31, 40) == None{} : Maybe<&2, T.ITreeEntry<U32, U32>>}

law example_remove:
  {T.ITree32.overlapping(U32, T.ITree32.remove(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5), 15, 30), 21, 40) == [T.ITreeEntry{25, 26, 4}] : List<&2, T.ITreeEntry<U32, U32>>}

law example_lookup:
  {T.ITree32.lookup(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5), 15, 30) == Some{3} : Maybe<&2, U32>}

law example_max_last:
  {T.ITree32.max_last(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5)) == Some{30} : Maybe<&2, U32>}

law example_insert_inverted:
  {T.ITree32.insert(U32, T.ITree32.empty(U32), 9, 3, 0) == Fail{T.ITreeInverted{9, 3}} : Result<&2, &2, T.ITreeError<U32>, T.ITree<U32, U32>>}

# instances of the hypotheses: an interval in order, one inverted, an
# overlap, and an empty tree's maximum (a valid tree with a maximum is
# example_valid's, by example_max_last)
law example_max_last_empty:
  {T.ITree32.max_last(U32, T.ITree32.empty(U32)) == None{} : Maybe<&2, U32>}

law example_in_order:
  {U32.is_le(10, 20) == True{} : Bool}

law example_inverted:
  {U32.is_lt(3, 9) == True{} : Bool}

law example_overlaps:
  {T.ITree32.overlaps(10, 20, 15, 40) == True{} : Bool}
