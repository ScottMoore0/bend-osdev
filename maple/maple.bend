# bend-osdev-maple: a range-indexed B-tree, in the style of the maple tree
# (the Linux kernel's tree of non-overlapping ranges), written from that
# tree's documented behaviour as an abstract data type.
#
# A tree maps ranges [first, last] of indices to values; no two ranges share
# an index. Storing a range overwrites whatever it covers: an entry it
# overlaps keeps only the part outside it (an entry spanning it is split in
# two). Erasing clears a range, or the entry holding an index. Lookups load
# the value at an index and find the entry at or after an index, the next
# entry after it and the previous one before it; entries iterate in index
# order. gap.bend adds the search for a free run of indices.
#
# This first version is a plain B-tree of fixed order (MapleOptions, 16 by
# default): leaves hold entries, branches hold children with their last
# index (a pivot), every leaf at the same depth. The index type, its order
# and its successor and predecessor are template arguments (~K, ~cmp, ~inc,
# ~dec); Maple32.* is the named default, on U32.
import Base
import ./model.bend as M
import ./node.bend as N
import ./tree.bend as T

# Building

# the empty tree, built with opts
def Maple.empty(-K: Data, -V: Data, opts: N.MapleOptions) -> N.MapleTree<K, V>:
  T.MapleTree.empty_of(K, V, N.MapleOptions.order(opts))

def Maple.set_range.go(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, ok: Bool, +t: N.MapleTree<K, V>, +a: K, +b: K, v: V) -> N.MapleTree<K, V>:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+order, +h, +root}:
          T.MapleTree.join(K, V, T.MapleTree.join(K, V, T.MapleTree.lo(~K, ~cmp, ~dec, V, root, h, a, N.MapleNil{}, N.MapleNode.probe(~K, ~cmp, V, root, a), order), N.MapleTree{order, 0n, N.MapleLeaf{[M.MapleEntry{a, b, v}]}}), T.MapleTree.hi(~K, ~cmp, ~inc, V, root, h, b, N.MapleNode.probe(~K, ~cmp, V, root, b), order))
    case False{}:
      t

# t with [a, b] holding v, overwriting what was there (mtree_store_range);
# t unchanged if a > b
def Maple.set_range(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, +t: N.MapleTree<K, V>, +a: K, +b: K, v: V) -> N.MapleTree<K, V>:
  Maple.set_range.go(~K, ~cmp, ~inc, ~dec, V, M.MapleKey.le(~K, ~cmp, a, b), t, a, b, v)

def Maple.store_range.go(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, ok: Bool, +t: N.MapleTree<K, V>, +a: K, +b: K, v: V) -> Result<&2, &2, M.MapleError<K>, N.MapleTree<K, V>>:
  match ok:
    case True{}:
      Done{Maple.set_range(~K, ~cmp, ~inc, ~dec, V, t, a, b, v)}
    case False{}:
      Fail{M.MapleInverted{a, b}}

# the same, failing with MapleInverted if a > b
def Maple.store_range(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, +t: N.MapleTree<K, V>, +a: K, +b: K, v: V) -> Result<&2, &2, M.MapleError<K>, N.MapleTree<K, V>>:
  Maple.store_range.go(~K, ~cmp, ~inc, ~dec, V, M.MapleKey.le(~K, ~cmp, a, b), t, a, b, v)

# t with the index i holding v (mtree_store)
def Maple.store(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, +t: N.MapleTree<K, V>, +i: K, v: V) -> N.MapleTree<K, V>:
  Maple.set_range(~K, ~cmp, ~inc, ~dec, V, t, i, i, v)

def Maple.clear_range.go(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, ok: Bool, +t: N.MapleTree<K, V>, +a: K, +b: K) -> N.MapleTree<K, V>:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+order, +h, +root}:
          T.MapleTree.join(K, V, T.MapleTree.lo(~K, ~cmp, ~dec, V, root, h, a, N.MapleNil{}, N.MapleNode.probe(~K, ~cmp, V, root, a), order), T.MapleTree.hi(~K, ~cmp, ~inc, V, root, h, b, N.MapleNode.probe(~K, ~cmp, V, root, b), order))
    case False{}:
      t

# t with nothing stored in [a, b] (an entry overlapping it keeps the part
# outside it); t unchanged if a > b
def Maple.clear_range(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, +t: N.MapleTree<K, V>, +a: K, +b: K) -> N.MapleTree<K, V>:
  Maple.clear_range.go(~K, ~cmp, ~inc, ~dec, V, M.MapleKey.le(~K, ~cmp, a, b), t, a, b)

# Lookups

# the value at i (mtree_load)
def Maple.load(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: N.MapleTree<K, V>, +i: K) -> Maybe<&2, V>:
  match t:
    case N.MapleTree{o, h, +root}:
      N.MapleNode.load(~K, ~cmp, V, root, i, N.MapleNode.probe(~K, ~cmp, V, root, i))

# the first entry ending at or after i: the one holding i, or the next
# (mt_find)
def Maple.find(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: N.MapleTree<K, V>, +i: K) -> Maybe<&2, M.MapleEntry<K, V>>:
  match t:
    case N.MapleTree{o, h, +root}:
      N.MapleNode.find(~K, ~cmp, V, root, i, N.MapleNode.probe(~K, ~cmp, V, root, i))

def Maple.lookup.go(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, m: Maybe<&2, M.MapleEntry<K, V>>, +i: K) -> Maybe<&2, M.MapleEntry<K, V>>:
  match m:
    case None{}:
      None{}
    case Some{+e}:
      M.MapleModel.pick(K, V, M.MapleEntry.holds(~K, ~cmp, V, e, i), e, None{})

# the entry holding i, with its range
def Maple.lookup(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: N.MapleTree<K, V>, +i: K) -> Maybe<&2, M.MapleEntry<K, V>>:
  Maple.lookup.go(~K, ~cmp, V, Maple.find(~K, ~cmp, V, t, i), i)

# the first entry starting after i (mt_next)
def Maple.next(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: N.MapleTree<K, V>, +i: K) -> Maybe<&2, M.MapleEntry<K, V>>:
  match t:
    case N.MapleTree{o, h, +root}:
      N.MapleNode.next(~K, ~cmp, V, root, i, N.MapleNode.probe(~K, ~cmp, V, root, i))

# the last entry ending before i (mt_prev)
def Maple.prev(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: N.MapleTree<K, V>, +i: K) -> Maybe<&2, M.MapleEntry<K, V>>:
  match t:
    case N.MapleTree{o, h, +root}:
      N.MapleNode.prev(~K, ~cmp, V, root, i, N.MapleNode.probe(~K, ~cmp, V, root, i), N.MapleNil{})

def Maple.erase.go(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, m: Maybe<&2, M.MapleEntry<K, V>>, +t: N.MapleTree<K, V>) -> N.MapleTree<K, V>:
  match m:
    case None{}:
      t
    case Some{M.MapleEntry{f, l, v}}:
      Maple.clear_range(~K, ~cmp, ~inc, ~dec, V, t, f, l)

# t without the entry holding i, all of its range (mtree_erase); t
# unchanged if no entry holds i
def Maple.erase(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, +t: N.MapleTree<K, V>, +i: K) -> N.MapleTree<K, V>:
  Maple.erase.go(~K, ~cmp, ~inc, ~dec, V, Maple.lookup(~K, ~cmp, V, t, i), t)

# Iteration and shape

# every entry, in index order
def Maple.entries(-K: Data, -V: Data, t: N.MapleTree<K, V>) -> List<&2, M.MapleEntry<K, V>>:
  match t:
    case N.MapleTree{o, h, root}:
      N.MapleNode.entries_onto(K, V, root, Nil{})

def Maple.size(-K: Data, -V: Data, t: N.MapleTree<K, V>) -> Nat:
  List.length(&2, M.MapleEntry<K, V>, Maple.entries(K, V, t))

def Maple.height(-K: Data, -V: Data, t: N.MapleTree<K, V>) -> Nat:
  match t:
    case N.MapleTree{o, h, root}:
      h

def Maple.order(-K: Data, -V: Data, t: N.MapleTree<K, V>) -> Nat:
  match t:
    case N.MapleTree{o, h, root}:
      o

# the invariant every operation keeps: the entries are in index order, no
# two share an index, each has first <= last, and every pivot is its
# child's last index
def Maple.valid(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: N.MapleTree<K, V>) -> Bool:
  match t:
    case N.MapleTree{o, h, +root}:
      Bool.and(M.MapleModel.wf(~K, ~cmp, V, N.MapleNode.entries(K, V, root)), N.MapleNode.pivots_ok(~K, ~cmp, V, root))

# the B-tree shape: every leaf at depth height, every node but the root
# holding from half of order + 1 to order items, the root at most order
# (and, if a branch, at least 2)
def Maple.balanced(-K: Data, -V: Data, t: N.MapleTree<K, V>) -> Bool:
  match t:
    case N.MapleTree{+o, +h, +root}:
      N.MapleNode.root_shape(K, V, h, root, o)

def Maple.leveled.go(-K: Data, -V: Data, h: Nat, +n: N.MapleNode<K, V>) -> Bool:
  match h:
    case 0n:
      N.MapleNode.is_leaf(K, V, n)
    case 1n+g:
      Bool.and(N.MapleNode.is_chain(K, V, n), N.MapleNode.level(K, V, n, g))

# every leaf at depth height: a root of height 0 is a leaf, one of height
# h + 1 a nonempty chain whose children have height h (the part of balanced
# the laws prove; balanced adds the bounds on how full each node is)
def Maple.leveled(-K: Data, -V: Data, t: N.MapleTree<K, V>) -> Bool:
  match t:
    case N.MapleTree{o, h, n}:
      Maple.leveled.go(K, V, h, n)

# The named default: U32 indices in their usual order

def Maple32.empty(-V: Data) -> N.MapleTree<U32, V>:
  Maple.empty(U32, V, N.MapleOptions.default())

def Maple32.empty_with(-V: Data, opts: N.MapleOptions) -> N.MapleTree<U32, V>:
  Maple.empty(U32, V, opts)

def Maple32.set_range(-V: Data, +t: N.MapleTree<U32, V>, +a: U32, +b: U32, v: V) -> N.MapleTree<U32, V>:
  Maple.set_range(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, t, a, b, v)

def Maple32.store_range(-V: Data, +t: N.MapleTree<U32, V>, +a: U32, +b: U32, v: V) -> Result<&2, &2, M.MapleError<U32>, N.MapleTree<U32, V>>:
  Maple.store_range(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, t, a, b, v)

def Maple32.store(-V: Data, +t: N.MapleTree<U32, V>, +i: U32, v: V) -> N.MapleTree<U32, V>:
  Maple.store(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, t, i, v)

def Maple32.clear_range(-V: Data, +t: N.MapleTree<U32, V>, +a: U32, +b: U32) -> N.MapleTree<U32, V>:
  Maple.clear_range(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, t, a, b)

def Maple32.erase(-V: Data, +t: N.MapleTree<U32, V>, +i: U32) -> N.MapleTree<U32, V>:
  Maple.erase(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, t, i)

def Maple32.load(-V: Data, t: N.MapleTree<U32, V>, +i: U32) -> Maybe<&2, V>:
  Maple.load(~U32, ~U32.cmp, V, t, i)

def Maple32.lookup(-V: Data, t: N.MapleTree<U32, V>, +i: U32) -> Maybe<&2, M.MapleEntry<U32, V>>:
  Maple.lookup(~U32, ~U32.cmp, V, t, i)

def Maple32.find(-V: Data, t: N.MapleTree<U32, V>, +i: U32) -> Maybe<&2, M.MapleEntry<U32, V>>:
  Maple.find(~U32, ~U32.cmp, V, t, i)

def Maple32.next(-V: Data, t: N.MapleTree<U32, V>, +i: U32) -> Maybe<&2, M.MapleEntry<U32, V>>:
  Maple.next(~U32, ~U32.cmp, V, t, i)

def Maple32.prev(-V: Data, t: N.MapleTree<U32, V>, +i: U32) -> Maybe<&2, M.MapleEntry<U32, V>>:
  Maple.prev(~U32, ~U32.cmp, V, t, i)

def Maple32.entries(-V: Data, t: N.MapleTree<U32, V>) -> List<&2, M.MapleEntry<U32, V>>:
  Maple.entries(U32, V, t)

def Maple32.size(-V: Data, t: N.MapleTree<U32, V>) -> Nat:
  Maple.size(U32, V, t)

def Maple32.height(-V: Data, t: N.MapleTree<U32, V>) -> Nat:
  Maple.height(U32, V, t)

def Maple32.valid(-V: Data, t: N.MapleTree<U32, V>) -> Bool:
  Maple.valid(~U32, ~U32.cmp, V, t)

def Maple32.balanced(-V: Data, t: N.MapleTree<U32, V>) -> Bool:
  Maple.balanced(U32, V, t)

def Maple32.leveled(-V: Data, t: N.MapleTree<U32, V>) -> Bool:
  Maple.leveled(U32, V, t)
