# bend-osdev-maple: B-tree nodes.
#
# A node of height 0 is a leaf: a list of entries in index order. A node of
# height h + 1 is a branch: a chain of slots, each holding a child of height
# h and its pivot, the last index of the child's last entry, ending in
# MapleNil. Every slot is built by MapleNode.cons, which computes the pivot
# from the child (and leaves out an empty child), so the pivots stay right
# through every change.
#
# The contents of a node (entries) are its leaves' entries, left to right.
# Every restructuring here (appending chains, taking and dropping slots,
# merging two nodes, splitting an overfull one) keeps the contents in order,
# for every node, well formed or not.
import Base
import ./model.bend as M

# Types

# A node. Internal: use it only through the defs of this package.
type MapleNode<-K: Data, -V: Data> is Data:
  MapleLeaf{entries: List<&2, M.MapleEntry<K, V>>}
  MapleNil{}
  MapleSlot{pivot: K, child: MapleNode<K, V>, rest: MapleNode<K, V>}

# The choices a tree is built with: the most items (entries in a leaf,
# slots in a branch) a node holds. Below 3 a node could not split into two
# halves that keep the tree's height logarithmic, so 3 is used then.
type MapleOptions is Data:
  MapleOptions{order: Nat}

# A tree: its order, its height and its root. Internal: use it only through
# the defs of this package.
type MapleTree<-K: Data, -V: Data> is Data:
  MapleTree{order: Nat, height: Nat, root: MapleNode<K, V>}

def MapleOptions.default() -> MapleOptions:
  MapleOptions{16n}

def MapleOptions.order(o: MapleOptions) -> Nat:
  match o:
    case MapleOptions{n}:
      Nat.max(3n, n)

# Contents

# the entries of n, left to right (the reference form, used by the proofs)
def MapleNode.entries(-K: Data, -V: Data, n: MapleNode<K, V>) -> List<&2, M.MapleEntry<K, V>>:
  match n:
    case MapleLeaf{es}:
      es
    case MapleNil{}:
      Nil{}
    case MapleSlot{p, c, r}:
      M.MapleModel.append(K, V, MapleNode.entries(K, V, c), MapleNode.entries(K, V, r))

# entries(n) ++ acc, appending only leaves (what the interface uses)
def MapleNode.entries_onto(-K: Data, -V: Data, n: MapleNode<K, V>, acc: List<&2, M.MapleEntry<K, V>>) -> List<&2, M.MapleEntry<K, V>>:
  match n:
    case MapleLeaf{es}:
      M.MapleModel.append(K, V, es, acc)
    case MapleNil{}:
      acc
    case MapleSlot{p, c, r}:
      MapleNode.entries_onto(K, V, c, MapleNode.entries_onto(K, V, r, acc))

# the number of items: entries of a leaf, slots of a branch
def MapleNode.count(-K: Data, -V: Data, n: MapleNode<K, V>) -> Nat:
  match n:
    case MapleLeaf{es}:
      List.length(&2, M.MapleEntry<K, V>, es)
    case MapleNil{}:
      0n
    case MapleSlot{p, c, r}:
      1n+MapleNode.count(K, V, r)

# the last index of the last entry (None if there is none)
def MapleNode.last_key(-K: Data, -V: Data, n: MapleNode<K, V>) -> Maybe<&2, K>:
  match n:
    case MapleLeaf{es}:
      M.MapleModel.last_key(K, V, es)
    case MapleNil{}:
      None{}
    case MapleSlot{p, c, r}:
      Maybe.or(&2, K, MapleNode.last_key(K, V, r), Some{p})

def MapleNode.is_empty(-K: Data, -V: Data, n: MapleNode<K, V>) -> Bool:
  Maybe.is_none(&2, K, MapleNode.last_key(K, V, n))

# Building chains

def MapleNode.cons.go(-K: Data, -V: Data, m: Maybe<&2, K>, c: MapleNode<K, V>, rest: MapleNode<K, V>) -> MapleNode<K, V>:
  match m:
    case None{}:
      rest
    case Some{p}:
      MapleSlot{p, c, rest}

# the slot holding c, then rest; nothing for an empty c
def MapleNode.cons(-K: Data, -V: Data, +c: MapleNode<K, V>, rest: MapleNode<K, V>) -> MapleNode<K, V>:
  MapleNode.cons.go(K, V, MapleNode.last_key(K, V, c), c, rest)

# the slots of x, then those of y (a leaf x is one slot)
def MapleNode.append(-K: Data, -V: Data, x: MapleNode<K, V>, y: MapleNode<K, V>) -> MapleNode<K, V>:
  match x:
    case MapleLeaf{es}:
      MapleNode.cons(K, V, MapleLeaf{es}, y)
    case MapleNil{}:
      y
    case MapleSlot{p, c, r}:
      MapleSlot{p, c, MapleNode.append(K, V, r, y)}

# the first k items
def MapleNode.take(-K: Data, -V: Data, n: MapleNode<K, V>, k: Nat) -> MapleNode<K, V>:
  match n:
    case MapleLeaf{es}:
      MapleLeaf{List.take(&2, M.MapleEntry<K, V>, es, k)}
    case MapleNil{}:
      MapleNil{}
    case MapleSlot{p, c, r}:
      match k:
        case 0n:
          MapleNil{}
        case 1n+j:
          MapleSlot{p, c, MapleNode.take(K, V, r, j)}

# all but the first k items
def MapleNode.drop(-K: Data, -V: Data, n: MapleNode<K, V>, k: Nat) -> MapleNode<K, V>:
  match n:
    case MapleLeaf{es}:
      MapleLeaf{List.drop(&2, M.MapleEntry<K, V>, es, k)}
    case MapleNil{}:
      MapleNil{}
    case MapleSlot{p, c, r}:
      match k:
        case 0n:
          MapleSlot{p, c, r}
        case 1n+j:
          MapleNode.drop(K, V, r, j)

# the items of x, then those of y, as one node (two leaves make a leaf)
def MapleNode.merge(-K: Data, -V: Data, x: MapleNode<K, V>, y: MapleNode<K, V>) -> MapleNode<K, V>:
  match x:
    case MapleLeaf{es}:
      match y:
        case MapleLeaf{fs}:
          MapleLeaf{M.MapleModel.append(K, V, es, fs)}
        case MapleNil{}:
          MapleLeaf{es}
        case MapleSlot{q, d, s}:
          MapleNode.cons(K, V, MapleLeaf{es}, MapleSlot{q, d, s})
    case MapleNil{}:
      y
    case MapleSlot{p, c, r}:
      MapleNode.append(K, V, MapleSlot{p, c, r}, y)

def MapleNode.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+MapleNode.half(q)

def MapleNode.fit.go(-K: Data, -V: Data, over: Bool, +n: MapleNode<K, V>, +k: Nat) -> MapleNode<K, V>:
  match over:
    case False{}:
      MapleNode.cons(K, V, n, MapleNil{})
    case True{}:
      MapleNode.cons(K, V, MapleNode.take(K, V, n, k), MapleNode.cons(K, V, MapleNode.drop(K, V, n, k), MapleNil{}))

# n as the slot of one node, or of two halves if it holds more than order
# items: the chain a parent puts in n's place
def MapleNode.fit(-K: Data, -V: Data, +order: Nat, +n: MapleNode<K, V>) -> MapleNode<K, V>:
  +k = MapleNode.count(K, V, n)
  MapleNode.fit.go(K, V, Nat.is_lt(order, k), n, MapleNode.half(k))

# Taking a chain apart at its ends

def MapleNode.init.go(-K: Data, -V: Data, n: MapleNode<K, V>, p: K, c: MapleNode<K, V>) -> MapleNode<K, V>:
  match n:
    case MapleNil{}:
      MapleNil{}
    case MapleSlot{q, d, r}:
      MapleSlot{p, c, MapleNode.init.go(K, V, r, q, d)}
    case MapleLeaf{es}:
      MapleSlot{p, c, MapleNil{}}

# a chain without its last slot
def MapleNode.init(-K: Data, -V: Data, n: MapleNode<K, V>) -> MapleNode<K, V>:
  match n:
    case MapleLeaf{es}:
      MapleNil{}
    case MapleNil{}:
      MapleNil{}
    case MapleSlot{p, c, r}:
      MapleNode.init.go(K, V, r, p, c)

def MapleNode.last.go(-K: Data, -V: Data, n: MapleNode<K, V>, c: MapleNode<K, V>) -> MapleNode<K, V>:
  match n:
    case MapleNil{}:
      c
    case MapleSlot{q, d, r}:
      MapleNode.last.go(K, V, r, d)
    case MapleLeaf{es}:
      MapleLeaf{es}

# the child of a chain's last slot (a leaf is its own)
def MapleNode.last(-K: Data, -V: Data, n: MapleNode<K, V>) -> MapleNode<K, V>:
  match n:
    case MapleLeaf{es}:
      MapleLeaf{es}
    case MapleNil{}:
      MapleNil{}
    case MapleSlot{p, c, r}:
      MapleNode.last.go(K, V, r, c)

# the child of a chain's first slot (a leaf is its own)
def MapleNode.first(-K: Data, -V: Data, n: MapleNode<K, V>) -> MapleNode<K, V>:
  match n:
    case MapleLeaf{es}:
      MapleLeaf{es}
    case MapleNil{}:
      MapleNil{}
    case MapleSlot{p, c, r}:
      c

# a chain without its first slot
def MapleNode.tail(-K: Data, -V: Data, n: MapleNode<K, V>) -> MapleNode<K, V>:
  match n:
    case MapleLeaf{es}:
      MapleNil{}
    case MapleNil{}:
      MapleNil{}
    case MapleSlot{p, c, r}:
      r

# Searching. A recursive def cannot match a computed value, so each search
# takes the comparison of its node's first pivot with the index: probe
# computes it.

def MapleNode.probe(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, n: MapleNode<K, V>, +i: K) -> Cmp:
  match n:
    case MapleLeaf{es}:
      EQ{}
    case MapleNil{}:
      EQ{}
    case MapleSlot{p, c, r}:
      cmp(p, i)

# the first entry of n
def MapleNode.first_entry(-K: Data, -V: Data, n: MapleNode<K, V>) -> Maybe<&2, M.MapleEntry<K, V>>:
  match n:
    case MapleLeaf{es}:
      List.head(&2, M.MapleEntry<K, V>, es)
    case MapleNil{}:
      None{}
    case MapleSlot{p, c, r}:
      MapleNode.first_entry(K, V, c)

# the value at i; c = cmp(first pivot, i)
def MapleNode.load(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, n: MapleNode<K, V>, +i: K, c: Cmp) -> Maybe<&2, V>:
  match n:
    case MapleLeaf{es}:
      M.MapleModel.load(~K, ~cmp, V, es, i)
    case MapleNil{}:
      None{}
    case MapleSlot{p, +ch, +r}:
      match c:
        case LT{}:
          MapleNode.load(~K, ~cmp, V, r, i, MapleNode.probe(~K, ~cmp, V, r, i))
        case o:
          MapleNode.load(~K, ~cmp, V, ch, i, MapleNode.probe(~K, ~cmp, V, ch, i))

# the first entry ending at or after i; c = cmp(first pivot, i)
def MapleNode.find(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, n: MapleNode<K, V>, +i: K, c: Cmp) -> Maybe<&2, M.MapleEntry<K, V>>:
  match n:
    case MapleLeaf{es}:
      M.MapleModel.find(~K, ~cmp, V, es, i)
    case MapleNil{}:
      None{}
    case MapleSlot{p, +ch, +r}:
      match c:
        case LT{}:
          MapleNode.find(~K, ~cmp, V, r, i, MapleNode.probe(~K, ~cmp, V, r, i))
        case o:
          M.MapleModel.later(K, V, MapleNode.find(~K, ~cmp, V, ch, i, MapleNode.probe(~K, ~cmp, V, ch, i)), MapleNode.first_entry(K, V, r))

# the first entry starting after i; c = cmp(first pivot, i)
def MapleNode.next(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, n: MapleNode<K, V>, +i: K, c: Cmp) -> Maybe<&2, M.MapleEntry<K, V>>:
  match n:
    case MapleLeaf{es}:
      M.MapleModel.next(~K, ~cmp, V, es, i)
    case MapleNil{}:
      None{}
    case MapleSlot{p, +ch, +r}:
      match c:
        case GT{}:
          M.MapleModel.later(K, V, MapleNode.next(~K, ~cmp, V, ch, i, MapleNode.probe(~K, ~cmp, V, ch, i)), MapleNode.first_entry(K, V, r))
        case o:
          MapleNode.next(~K, ~cmp, V, r, i, MapleNode.probe(~K, ~cmp, V, r, i))

def MapleNode.last_entry.go(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: MapleNode<K, V>, m: Maybe<&2, K>) -> Maybe<&2, M.MapleEntry<K, V>>:
  match m:
    case None{}:
      None{}
    case Some{+k}:
      MapleNode.find(~K, ~cmp, V, n, k, MapleNode.probe(~K, ~cmp, V, n, k))

# the last entry of n: the first ending at or after its last index
def MapleNode.last_entry(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: MapleNode<K, V>) -> Maybe<&2, M.MapleEntry<K, V>>:
  MapleNode.last_entry.go(~K, ~cmp, V, n, MapleNode.last_key(K, V, n))

# the last entry ending before i, in sib (the slot before n's, whose
# entries all end before i) or in n; c = cmp(first pivot, i)
def MapleNode.prev(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, n: MapleNode<K, V>, +i: K, c: Cmp, sib: MapleNode<K, V>) -> Maybe<&2, M.MapleEntry<K, V>>:
  match n:
    case MapleLeaf{es}:
      M.MapleModel.later(K, V, M.MapleModel.prev(~K, ~cmp, V, es, i), MapleNode.last_entry(~K, ~cmp, V, sib))
    case MapleNil{}:
      MapleNode.last_entry(~K, ~cmp, V, sib)
    case MapleSlot{p, +ch, +r}:
      match c:
        case LT{}:
          MapleNode.prev(~K, ~cmp, V, r, i, MapleNode.probe(~K, ~cmp, V, r, i), ch)
        case o:
          M.MapleModel.later(K, V, MapleNode.prev(~K, ~cmp, V, ch, i, MapleNode.probe(~K, ~cmp, V, ch, i), MapleNil{}), MapleNode.last_entry(~K, ~cmp, V, sib))

# Invariants

def MapleNode.key_is(~K: Data, ~cmp: K -> K -> Cmp, m: Maybe<&2, K>, +p: K) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      Cmp.is_eq(cmp(k, p))

# every slot's pivot is its child's last index
def MapleNode.pivots_ok(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, n: MapleNode<K, V>) -> Bool:
  match n:
    case MapleLeaf{es}:
      True{}
    case MapleNil{}:
      True{}
    case MapleSlot{+p, +c, r}:
      Bool.and(MapleNode.key_is(~K, ~cmp, MapleNode.last_key(K, V, c), p), Bool.and(MapleNode.pivots_ok(~K, ~cmp, V, c), MapleNode.pivots_ok(~K, ~cmp, V, r)))

def MapleNode.fill_ok(+order: Nat, +root: Bool, +low: Nat, +k: Nat) -> Bool:
  match root:
    case True{}:
      Bool.and(Nat.is_le(low, k), Nat.is_le(k, order))
    case False{}:
      Bool.and(Nat.is_le(MapleNode.half(1n+order), k), Nat.is_le(k, order))

def MapleNode.leaf_ok(-K: Data, -V: Data, n: MapleNode<K, V>, +order: Nat) -> Bool:
  match n:
    case MapleLeaf{+es}:
      MapleNode.fill_ok(order, False{}, 0n, List.length(&2, M.MapleEntry<K, V>, es))
    case MapleNil{}:
      False{}
    case MapleSlot{p, c, r}:
      False{}

# n is a chain of slots whose children are nodes of height h, not roots:
# every leaf below them at depth h, every node holding at most order items
# and at least half of order + 1
def MapleNode.shape(-K: Data, -V: Data, n: MapleNode<K, V>, h: Nat, +order: Nat) -> Bool:
  match n:
    case MapleSlot{p, +c, r}:
      match h:
        case 0n:
          Bool.and(MapleNode.leaf_ok(K, V, c, order), MapleNode.shape(K, V, r, 0n, order))
        case 1n+(+g):
          Bool.and(MapleNode.fill_ok(order, False{}, 0n, MapleNode.count(K, V, c)), Bool.and(MapleNode.shape(K, V, c, g, order), MapleNode.shape(K, V, r, 1n+g, order)))
    case MapleNil{}:
      True{}
    case MapleLeaf{es}:
      False{}

def MapleNode.is_chain(-K: Data, -V: Data, n: MapleNode<K, V>) -> Bool:
  match n:
    case MapleSlot{p, c, r}:
      True{}
    case MapleNil{}:
      False{}
    case MapleLeaf{es}:
      False{}

# a root of height h: a leaf of at most order entries, or a branch of 2 to
# order slots whose children have the shape above

def MapleNode.is_leaf(-K: Data, -V: Data, n: MapleNode<K, V>) -> Bool:
  match n:
    case MapleLeaf{es}:
      True{}
    case MapleNil{}:
      False{}
    case MapleSlot{p, c, r}:
      False{}

# n is a chain of slots whose children are nodes of height h: leaves if h is
# 0, else nonempty chains whose own children have height h - 1
def MapleNode.level(-K: Data, -V: Data, n: MapleNode<K, V>, +h: Nat) -> Bool:
  match n:
    case MapleSlot{p, +c, r}:
      match h:
        case 0n:
          Bool.and(MapleNode.is_leaf(K, V, c), MapleNode.level(K, V, r, 0n))
        case 1n+(+g):
          Bool.and(MapleNode.is_chain(K, V, c), Bool.and(MapleNode.level(K, V, c, g), MapleNode.level(K, V, r, 1n+g)))
    case MapleNil{}:
      True{}
    case MapleLeaf{es}:
      False{}
def MapleNode.root_shape(-K: Data, -V: Data, h: Nat, +n: MapleNode<K, V>, +order: Nat) -> Bool:
  match h:
    case 0n:
      match n:
        case MapleLeaf{+es}:
          MapleNode.fill_ok(order, True{}, 0n, List.length(&2, M.MapleEntry<K, V>, es))
        case MapleNil{}:
          False{}
        case MapleSlot{p, c, r}:
          False{}
    case 1n+g:
      Bool.and(MapleNode.is_chain(K, V, n), Bool.and(MapleNode.fill_ok(order, True{}, 2n, MapleNode.count(K, V, n)), MapleNode.shape(K, V, n, g, order)))
