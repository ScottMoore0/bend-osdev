# Balance: the AVL condition (ITree32.balanced: every node stores its
# height, and its subtrees' heights differ by at most one) and what it
# gives. Properties, for every tree, interval and value type:
#
# * the empty tree is balanced, and set and remove keep a tree balanced;
# * the height bound: a balanced tree of height at least 2k holds at least
#   2^k - 1 entries, so a balanced tree of n entries has height at most
#   2 log2(n + 1) + 1.
#
# These hold for every tree, valid or not: balance is about the shape, and
# the shape does not depend on the order of the keys.
#
# Vectors: the bound on the five-interval tree of LAWS.bend, and an
# instance of the bound's hypothesis.
import Base
import ./itree.bend as T

law balanced_empty:
  for -V: Data
  {T.ITree32.balanced(V, T.ITree32.empty(V)) == True{} : Bool}

law balanced_set:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +v: V
  for +e: {T.ITree32.balanced(V, t) == True{} : Bool}
  {T.ITree32.balanced(V, T.ITree32.set(V, t, s, l, v)) == True{} : Bool}

law balanced_remove:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +s: U32
  for +l: U32
  for +e: {T.ITree32.balanced(V, t) == True{} : Bool}
  {T.ITree32.balanced(V, T.ITree32.remove(V, t, s, l)) == True{} : Bool}

# a balanced tree of height at least 2k holds at least 2^k - 1 entries
law size_bound:
  for -V: Data
  for +t: T.ITree<U32, V>
  for +k: Nat
  for +e: {T.ITree32.balanced(V, t) == True{} : Bool}
  for +f: {Nat.is_le(Nat.double(k), T.ITree32.height(V, t)) == True{} : Bool}
  {Nat.is_le(Nat.pow(2n, k), 1n+T.ITree32.size(V, t)) == True{} : Bool}

# Vectors, on the tree holding [10, 20], [5, 8], [15, 30], [25, 26] and
# [1, 3] (with values 1 to 5), built by set: its height is 3, so k = 1
# bounds it, 2^1 <= 5 + 1

law example_height:
  {T.ITree32.height(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5)) == 3n : Nat}

law example_bound_hyp:
  {Nat.is_le(Nat.double(1n), T.ITree32.height(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5))) == True{} : Bool}

law example_balanced_remove:
  {T.ITree32.balanced(U32, T.ITree32.remove(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5), 10, 20)) == True{} : Bool}
