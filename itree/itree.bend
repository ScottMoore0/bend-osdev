# bend-osdev-itree: an interval tree (Cormen, Leiserson, Rivest and Stein,
# Introduction to Algorithms, section 14.3, "Interval trees").
#
# A tree holds a set of closed intervals [start, last] over an ordered key,
# each with a value; an interval is in the tree at most once. It answers the
# intervals that overlap a point or a range, the first of them in key order,
# and the next one after a given interval, which is how a caller iterates.
#
# The tree is a binary search tree on the key (start, last), in
# lexicographic order, balanced as an AVL tree (the heights of a node's two
# subtrees differ by at most one). Every node also stores the largest `last`
# in its subtree: a query skips a subtree whose largest `last` is below the
# query's start, and a right subtree whose node starts after the query's end.
#
# The key type and its order are template arguments (~K, ~cmp); ITree32.* is
# the named default, on U32 with U32.cmp.
import Base

# Types

# A stored interval: [start, last] and its value. Open: callers read it.
type ITreeEntry<-K: Data, -V: Data> is Data:
  ITreeEntry{start: K, last: K, value: V}

# The tree. Internal: use it only through the defs below.
type ITree<-K: Data, -V: Data> is Data:
  ITreeLeaf{}
  ITreeNode{height: Nat, max: K, left: ITree<K, V>, entry: ITreeEntry<K, V>, right: ITree<K, V>}

type ITreeError<-K: Data> is Data:
  ITreeInverted{start: K, last: K}

# Internal: where a search starts (from the first interval, or after a key).
type ITreeBound<-K: Data> is Data:
  ITreeFromStart{}
  ITreeAfter{start: K, last: K}

# Entries

def ITreeEntry.start(-K: Data, -V: Data, e: ITreeEntry<K, V>) -> K:
  match e:
    case ITreeEntry{s, l, v}:
      s

def ITreeEntry.last(-K: Data, -V: Data, e: ITreeEntry<K, V>) -> K:
  match e:
    case ITreeEntry{s, l, v}:
      l

def ITreeEntry.value(-K: Data, -V: Data, e: ITreeEntry<K, V>) -> V:
  match e:
    case ITreeEntry{s, l, v}:
      v

# Keys and intervals

def ITree.kmax.pick(-K: Data, c: Cmp, a: K, b: K) -> K:
  match c:
    case LT{}:
      b
    case o:
      a

# the larger of two keys
def ITree.kmax(~K: Data, ~cmp: K -> K -> Cmp, +a: K, +b: K) -> K:
  ITree.kmax.pick(K, cmp(a, b), a, b)

def ITree.key_cmp.go(~K: Data, ~cmp: K -> K -> Cmp, c: Cmp, +l1: K, +l2: K) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      cmp(l1, l2)
    case GT{}:
      GT{}

# the order of the keys (s1, l1) and (s2, l2): by start, then by last
def ITree.key_cmp(~K: Data, ~cmp: K -> K -> Cmp, +s1: K, +l1: K, +s2: K, +l2: K) -> Cmp:
  ITree.key_cmp.go(~K, ~cmp, cmp(s1, s2), l1, l2)

# whether [s, l] and [a, b] share a point: s <= b and a <= l
def ITree.overlaps(~K: Data, ~cmp: K -> K -> Cmp, +s: K, +l: K, +a: K, +b: K) -> Bool:
  Bool.and(Cmp.is_le(cmp(s, b)), Cmp.is_le(cmp(a, l)))

def ITree.entry_overlaps(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: ITreeEntry<K, V>, +a: K, +b: K) -> Bool:
  ITree.overlaps(~K, ~cmp, ITreeEntry.start(K, V, e), ITreeEntry.last(K, V, e), a, b)

# the key (s, l) against the key of e
def ITree.entry_cmp(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +s: K, +l: K, +e: ITreeEntry<K, V>) -> Cmp:
  ITree.key_cmp(~K, ~cmp, s, l, ITreeEntry.start(K, V, e), ITreeEntry.last(K, V, e))

# whether e comes after the bound lo
def ITree.after(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, lo: ITreeBound<K>, +e: ITreeEntry<K, V>) -> Bool:
  match lo:
    case ITreeFromStart{}:
      True{}
    case ITreeAfter{s, l}:
      Cmp.is_lt(ITree.entry_cmp(~K, ~cmp, V, s, l, e))

# Lists of entries (the contents, in key order)

def ITree.keep(-K: Data, -V: Data, b: Bool, x: ITreeEntry<K, V>, rest: List<&2, ITreeEntry<K, V>>) -> List<&2, ITreeEntry<K, V>>:
  match b:
    case True{}:
      Con{x, rest}
    case False{}:
      rest

def ITree.pick(-K: Data, -V: Data, b: Bool, x: ITreeEntry<K, V>) -> Maybe<&2, ITreeEntry<K, V>>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      None{}

def ITree.orelse(-K: Data, -V: Data, m: Maybe<&2, ITreeEntry<K, V>>, n: Maybe<&2, ITreeEntry<K, V>>) -> Maybe<&2, ITreeEntry<K, V>>:
  match m:
    case Some{x}:
      Some{x}
    case None{}:
      n

# every entry of xs comes after the key (s, l)
def ITree.all_after(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +s: K, +l: K, xs: List<&2, ITreeEntry<K, V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      Bool.and(Cmp.is_lt(ITree.entry_cmp(~K, ~cmp, V, s, l, x)), ITree.all_after(~K, ~cmp, V, s, l, r))

# the keys of xs strictly increase
def ITree.sorted(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, ITreeEntry<K, V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +r}:
      Bool.and(ITree.all_after(~K, ~cmp, V, ITreeEntry.start(K, V, x), ITreeEntry.last(K, V, x), r), ITree.sorted(~K, ~cmp, V, r))

# Tree structure

def ITree.height(-K: Data, -V: Data, t: ITree<K, V>) -> Nat:
  match t:
    case ITreeLeaf{}:
      0n
    case ITreeNode{h, m, l, e, r}:
      h

# the larger of x and the largest last in t
def ITree.bound(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, +x: K) -> K:
  match t:
    case ITreeLeaf{}:
      x
    case ITreeNode{h, +m, l, e, r}:
      ITree.kmax(~K, ~cmp, m, x)

# a node, with its height and largest last computed from its children
def ITree.mk(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +l: ITree<K, V>, +e: ITreeEntry<K, V>, +r: ITree<K, V>) -> ITree<K, V>:
  ITreeNode{1n+Nat.max(ITree.height(K, V, l), ITree.height(K, V, r)), ITree.bound(~K, ~cmp, V, l, ITree.bound(~K, ~cmp, V, r, ITreeEntry.last(K, V, e))), l, e, r}

# Rebalancing (AVL rotations)

def ITree.rot_r.go(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, dbl: Bool, ll: ITree<K, V>, le: ITreeEntry<K, V>, lr: ITree<K, V>, e: ITreeEntry<K, V>, r: ITree<K, V>) -> ITree<K, V>:
  match dbl:
    case False{}:
      ITree.mk(~K, ~cmp, V, ll, le, ITree.mk(~K, ~cmp, V, lr, e, r))
    case True{}:
      match lr:
        case ITreeLeaf{}:
          ITree.mk(~K, ~cmp, V, ll, le, ITree.mk(~K, ~cmp, V, ITreeLeaf{}, e, r))
        case ITreeNode{h, m, lrl, lre, lrr}:
          ITree.mk(~K, ~cmp, V, ITree.mk(~K, ~cmp, V, ll, le, lrl), lre, ITree.mk(~K, ~cmp, V, lrr, e, r))

# l is two higher than r (so not a leaf: that case only keeps the def total)
def ITree.rot_r(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, l: ITree<K, V>, e: ITreeEntry<K, V>, r: ITree<K, V>) -> ITree<K, V>:
  match l:
    case ITreeLeaf{}:
      ITree.mk(~K, ~cmp, V, ITreeLeaf{}, e, r)
    case ITreeNode{h, m, +ll, le, +lr}:
      ITree.rot_r.go(~K, ~cmp, V, Nat.is_lt(ITree.height(K, V, ll), ITree.height(K, V, lr)), ll, le, lr, e, r)

def ITree.rot_l.go(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, dbl: Bool, l: ITree<K, V>, e: ITreeEntry<K, V>, rl: ITree<K, V>, re: ITreeEntry<K, V>, rr: ITree<K, V>) -> ITree<K, V>:
  match dbl:
    case False{}:
      ITree.mk(~K, ~cmp, V, ITree.mk(~K, ~cmp, V, l, e, rl), re, rr)
    case True{}:
      match rl:
        case ITreeLeaf{}:
          ITree.mk(~K, ~cmp, V, ITree.mk(~K, ~cmp, V, l, e, ITreeLeaf{}), re, rr)
        case ITreeNode{h, m, rll, rle, rlr}:
          ITree.mk(~K, ~cmp, V, ITree.mk(~K, ~cmp, V, l, e, rll), rle, ITree.mk(~K, ~cmp, V, rlr, re, rr))

# r is two higher than l (so not a leaf: that case only keeps the def total)
def ITree.rot_l(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, l: ITree<K, V>, e: ITreeEntry<K, V>, r: ITree<K, V>) -> ITree<K, V>:
  match r:
    case ITreeLeaf{}:
      ITree.mk(~K, ~cmp, V, l, e, ITreeLeaf{})
    case ITreeNode{h, m, +rl, re, +rr}:
      ITree.rot_l.go(~K, ~cmp, V, Nat.is_lt(ITree.height(K, V, rr), ITree.height(K, V, rl)), l, e, rl, re, rr)

def ITree.bal.go(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, lh: Bool, rh: Bool, l: ITree<K, V>, e: ITreeEntry<K, V>, r: ITree<K, V>) -> ITree<K, V>:
  match lh:
    case True{}:
      ITree.rot_r(~K, ~cmp, V, l, e, r)
    case False{}:
      match rh:
        case True{}:
          ITree.rot_l(~K, ~cmp, V, l, e, r)
        case False{}:
          ITree.mk(~K, ~cmp, V, l, e, r)

# a node from subtrees whose heights differ by at most two, rebalanced
def ITree.bal(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +l: ITree<K, V>, e: ITreeEntry<K, V>, +r: ITree<K, V>) -> ITree<K, V>:
  ITree.bal.go(~K, ~cmp, V, Nat.is_lt(1n+ITree.height(K, V, r), ITree.height(K, V, l)), Nat.is_lt(1n+ITree.height(K, V, l), ITree.height(K, V, r)), l, e, r)

# Searching by key. A recursive def cannot match a computed value, so each
# takes the comparison for its own root as an argument: probe computes it.

def ITree.probe(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, +s: K, +l: K) -> Cmp:
  match t:
    case ITreeLeaf{}:
      EQ{}
    case ITreeNode{h, m, tl, +e, tr}:
      ITree.entry_cmp(~K, ~cmp, V, s, l, e)

def ITree.ins(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, c: Cmp, +s: K, +l: K, +v: V) -> ITree<K, V>:
  match t:
    case ITreeLeaf{}:
      ITree.mk(~K, ~cmp, V, ITreeLeaf{}, ITreeEntry{s, l, v}, ITreeLeaf{})
    case ITreeNode{h, m, +tl, e, +tr}:
      match c:
        case LT{}:
          ITree.bal(~K, ~cmp, V, ITree.ins(~K, ~cmp, V, tl, ITree.probe(~K, ~cmp, V, tl, s, l), s, l, v), e, tr)
        case EQ{}:
          ITree.mk(~K, ~cmp, V, tl, ITreeEntry{s, l, v}, tr)
        case GT{}:
          ITree.bal(~K, ~cmp, V, tl, e, ITree.ins(~K, ~cmp, V, tr, ITree.probe(~K, ~cmp, V, tr, s, l), s, l, v))

# the first entry of the tree with left subtree t and root e
def ITree.min_of(-K: Data, -V: Data, t: ITree<K, V>, e: ITreeEntry<K, V>) -> ITreeEntry<K, V>:
  match t:
    case ITreeLeaf{}:
      e
    case ITreeNode{h, m, l, e2, r}:
      ITree.min_of(K, V, l, e2)

# the tree with subtrees t and r and root e, less its first entry
def ITree.del_min(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, e: ITreeEntry<K, V>, r: ITree<K, V>) -> ITree<K, V>:
  match t:
    case ITreeLeaf{}:
      r
    case ITreeNode{h, m, l2, e2, r2}:
      ITree.bal(~K, ~cmp, V, ITree.del_min(~K, ~cmp, V, l2, e2, r2), e, r)

# the entries of l, then those of r
def ITree.merge(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, l: ITree<K, V>, r: ITree<K, V>) -> ITree<K, V>:
  match r:
    case ITreeLeaf{}:
      l
    case ITreeNode{h, m, +rl, +re, rr}:
      ITree.bal(~K, ~cmp, V, l, ITree.min_of(K, V, rl, re), ITree.del_min(~K, ~cmp, V, rl, re, rr))

def ITree.rem(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, c: Cmp, +s: K, +l: K) -> ITree<K, V>:
  match t:
    case ITreeLeaf{}:
      ITreeLeaf{}
    case ITreeNode{h, m, +tl, e, +tr}:
      match c:
        case LT{}:
          ITree.bal(~K, ~cmp, V, ITree.rem(~K, ~cmp, V, tl, ITree.probe(~K, ~cmp, V, tl, s, l), s, l), e, tr)
        case EQ{}:
          ITree.merge(~K, ~cmp, V, tl, tr)
        case GT{}:
          ITree.bal(~K, ~cmp, V, tl, e, ITree.rem(~K, ~cmp, V, tr, ITree.probe(~K, ~cmp, V, tr, s, l), s, l))

def ITree.find(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, c: Cmp, +s: K, +l: K) -> Maybe<&2, V>:
  match t:
    case ITreeLeaf{}:
      None{}
    case ITreeNode{h, m, +tl, e, +tr}:
      match c:
        case LT{}:
          ITree.find(~K, ~cmp, V, tl, ITree.probe(~K, ~cmp, V, tl, s, l), s, l)
        case EQ{}:
          Some{ITreeEntry.value(K, V, e)}
        case GT{}:
          ITree.find(~K, ~cmp, V, tr, ITree.probe(~K, ~cmp, V, tr, s, l), s, l)

# Overlap queries. Each takes whether its subtree can hold an answer.

# whether the largest last in t reaches a
def ITree.reaches(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, +a: K) -> Bool:
  match t:
    case ITreeLeaf{}:
      False{}
    case ITreeNode{h, +m, l, e, r}:
      Cmp.is_ge(cmp(m, a))

# whether the right subtree r of a node with entry e can hold an answer
def ITree.go_right(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: ITreeEntry<K, V>, r: ITree<K, V>, +a: K, +b: K) -> Bool:
  Bool.and(Cmp.is_le(cmp(ITreeEntry.start(K, V, e), b)), ITree.reaches(~K, ~cmp, V, r, a))

def ITree.ov(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, go: Bool, +a: K, +b: K) -> List<&2, ITreeEntry<K, V>>:
  match t:
    case ITreeLeaf{}:
      Nil{}
    case ITreeNode{h, m, +tl, +e, +tr}:
      match go:
        case False{}:
          Nil{}
        case True{}:
          List.append(&2, ITreeEntry<K, V>, ITree.ov(~K, ~cmp, V, tl, ITree.reaches(~K, ~cmp, V, tl, a), a, b), ITree.keep(K, V, ITree.entry_overlaps(~K, ~cmp, V, e, a, b), e, ITree.ov(~K, ~cmp, V, tr, ITree.go_right(~K, ~cmp, V, e, tr, a, b), a, b)))

# the first entry after lo that overlaps [a, b]; prev is what was found
# before t, if anything
def ITree.seek(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, go: Bool, +a: K, +b: K, +lo: ITreeBound<K>, prev: Maybe<&2, ITreeEntry<K, V>>) -> Maybe<&2, ITreeEntry<K, V>>:
  match t:
    case ITreeLeaf{}:
      prev
    case ITreeNode{h, m, +tl, +e, +tr}:
      match go:
        case False{}:
          prev
        case True{}:
          match prev:
            case Some{x}:
              Some{x}
            case None{}:
              ITree.seek(~K, ~cmp, V, tr, ITree.go_right(~K, ~cmp, V, e, tr, a, b), a, b, lo, ITree.orelse(K, V, ITree.seek(~K, ~cmp, V, tl, Bool.and(ITree.after(~K, ~cmp, V, lo, e), ITree.reaches(~K, ~cmp, V, tl, a)), a, b, lo, None{}), ITree.pick(K, V, Bool.and(ITree.after(~K, ~cmp, V, lo, e), ITree.entry_overlaps(~K, ~cmp, V, e, a, b)), e)))

# The public interface

def ITree.empty(-K: Data, -V: Data) -> ITree<K, V>:
  ITreeLeaf{}

def ITree.set.go(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, c: Cmp, +t: ITree<K, V>, +s: K, +l: K, v: V) -> ITree<K, V>:
  match c:
    case GT{}:
      t
    case o:
      ITree.ins(~K, ~cmp, V, t, ITree.probe(~K, ~cmp, V, t, s, l), s, l, v)

# t with [s, l] holding v (replacing its value if it is there already);
# t unchanged if s > l
def ITree.set(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, +s: K, +l: K, v: V) -> ITree<K, V>:
  ITree.set.go(~K, ~cmp, V, cmp(s, l), t, s, l, v)

def ITree.insert.go(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, c: Cmp, +t: ITree<K, V>, +s: K, +l: K, v: V) -> Result<&2, &2, ITreeError<K>, ITree<K, V>>:
  match c:
    case GT{}:
      Fail{ITreeInverted{s, l}}
    case o:
      Done{ITree.ins(~K, ~cmp, V, t, ITree.probe(~K, ~cmp, V, t, s, l), s, l, v)}

# the same, failing with ITreeInverted if s > l
def ITree.insert(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>, +s: K, +l: K, v: V) -> Result<&2, &2, ITreeError<K>, ITree<K, V>>:
  ITree.insert.go(~K, ~cmp, V, cmp(s, l), t, s, l, v)

# t without [s, l] (unchanged if it is not there)
def ITree.remove(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: ITree<K, V>, +s: K, +l: K) -> ITree<K, V>:
  ITree.rem(~K, ~cmp, V, t, ITree.probe(~K, ~cmp, V, t, s, l), s, l)

# the value of [s, l], if it is in t
def ITree.lookup(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: ITree<K, V>, +s: K, +l: K) -> Maybe<&2, V>:
  ITree.find(~K, ~cmp, V, t, ITree.probe(~K, ~cmp, V, t, s, l), s, l)

# every entry overlapping [a, b], in key order
def ITree.overlapping(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: ITree<K, V>, +a: K, +b: K) -> List<&2, ITreeEntry<K, V>>:
  ITree.ov(~K, ~cmp, V, t, ITree.reaches(~K, ~cmp, V, t, a), a, b)

# every entry containing the point p, in key order
def ITree.stab(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: ITree<K, V>, +p: K) -> List<&2, ITreeEntry<K, V>>:
  ITree.overlapping(~K, ~cmp, V, t, p, p)

# the first entry, in key order, overlapping [a, b]
def ITree.first(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: ITree<K, V>, +a: K, +b: K) -> Maybe<&2, ITreeEntry<K, V>>:
  ITree.seek(~K, ~cmp, V, t, ITree.reaches(~K, ~cmp, V, t, a), a, b, ITreeFromStart{}, None{})

# the first entry overlapping [a, b] whose key comes after (s, l): from
# first, repeated calls with the last answer's key visit every overlapping
# entry in key order
def ITree.next(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: ITree<K, V>, +a: K, +b: K, +s: K, +l: K) -> Maybe<&2, ITreeEntry<K, V>>:
  ITree.seek(~K, ~cmp, V, t, ITree.reaches(~K, ~cmp, V, t, a), a, b, ITreeAfter{s, l}, None{})

# every entry, in key order
def ITree.to_list(-K: Data, -V: Data, t: ITree<K, V>) -> List<&2, ITreeEntry<K, V>>:
  match t:
    case ITreeLeaf{}:
      Nil{}
    case ITreeNode{h, m, l, e, r}:
      List.append(&2, ITreeEntry<K, V>, ITree.to_list(K, V, l), Con{e, ITree.to_list(K, V, r)})

def ITree.size(-K: Data, -V: Data, t: ITree<K, V>) -> Nat:
  match t:
    case ITreeLeaf{}:
      0n
    case ITreeNode{h, m, l, e, r}:
      1n+Nat.add(ITree.size(K, V, l), ITree.size(K, V, r))

# the largest last in t (None if t is empty)
def ITree.max_last(-K: Data, -V: Data, t: ITree<K, V>) -> Maybe<&2, K>:
  match t:
    case ITreeLeaf{}:
      None{}
    case ITreeNode{h, m, l, e, r}:
      Some{m}

# every node stores the largest last of its subtree
def ITree.max_ok(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: ITree<K, V>) -> Bool:
  match t:
    case ITreeLeaf{}:
      True{}
    case ITreeNode{h, +m, +l, +e, +r}:
      Bool.and(Cmp.is_eq(cmp(m, ITree.bound(~K, ~cmp, V, l, ITree.bound(~K, ~cmp, V, r, ITreeEntry.last(K, V, e))))), Bool.and(ITree.max_ok(~K, ~cmp, V, l), ITree.max_ok(~K, ~cmp, V, r)))

# the invariant every operation keeps: the keys increase in order, and every
# node stores the largest last of its subtree
def ITree.valid(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: ITree<K, V>) -> Bool:
  Bool.and(ITree.sorted(~K, ~cmp, V, ITree.to_list(K, V, t)), ITree.max_ok(~K, ~cmp, V, t))

# the AVL condition: every node stores its height, and its subtrees'
# heights differ by at most one
def ITree.balanced(-K: Data, -V: Data, t: ITree<K, V>) -> Bool:
  match t:
    case ITreeLeaf{}:
      True{}
    case ITreeNode{+h, m, +l, e, +r}:
      Bool.and(Nat.is_eq(h, 1n+Nat.max(ITree.height(K, V, l), ITree.height(K, V, r))), Bool.and(Nat.is_le(ITree.height(K, V, l), 1n+ITree.height(K, V, r)), Bool.and(Nat.is_le(ITree.height(K, V, r), 1n+ITree.height(K, V, l)), Bool.and(ITree.balanced(K, V, l), ITree.balanced(K, V, r)))))

# The named default: U32 keys in their usual order

def ITree32.empty(-V: Data) -> ITree<U32, V>:
  ITreeLeaf{}

def ITree32.set(-V: Data, t: ITree<U32, V>, +s: U32, +l: U32, v: V) -> ITree<U32, V>:
  ITree.set(~U32, ~U32.cmp, V, t, s, l, v)

def ITree32.insert(-V: Data, t: ITree<U32, V>, +s: U32, +l: U32, v: V) -> Result<&2, &2, ITreeError<U32>, ITree<U32, V>>:
  ITree.insert(~U32, ~U32.cmp, V, t, s, l, v)

def ITree32.remove(-V: Data, +t: ITree<U32, V>, +s: U32, +l: U32) -> ITree<U32, V>:
  ITree.remove(~U32, ~U32.cmp, V, t, s, l)

def ITree32.lookup(-V: Data, +t: ITree<U32, V>, +s: U32, +l: U32) -> Maybe<&2, V>:
  ITree.lookup(~U32, ~U32.cmp, V, t, s, l)

def ITree32.overlapping(-V: Data, +t: ITree<U32, V>, +a: U32, +b: U32) -> List<&2, ITreeEntry<U32, V>>:
  ITree.overlapping(~U32, ~U32.cmp, V, t, a, b)

def ITree32.stab(-V: Data, +t: ITree<U32, V>, +p: U32) -> List<&2, ITreeEntry<U32, V>>:
  ITree.stab(~U32, ~U32.cmp, V, t, p)

def ITree32.first(-V: Data, +t: ITree<U32, V>, +a: U32, +b: U32) -> Maybe<&2, ITreeEntry<U32, V>>:
  ITree.first(~U32, ~U32.cmp, V, t, a, b)

def ITree32.next(-V: Data, +t: ITree<U32, V>, +a: U32, +b: U32, +s: U32, +l: U32) -> Maybe<&2, ITreeEntry<U32, V>>:
  ITree.next(~U32, ~U32.cmp, V, t, a, b, s, l)

def ITree32.to_list(-V: Data, t: ITree<U32, V>) -> List<&2, ITreeEntry<U32, V>>:
  ITree.to_list(U32, V, t)

def ITree32.size(-V: Data, t: ITree<U32, V>) -> Nat:
  ITree.size(U32, V, t)

def ITree32.height(-V: Data, t: ITree<U32, V>) -> Nat:
  ITree.height(U32, V, t)

def ITree32.max_last(-V: Data, t: ITree<U32, V>) -> Maybe<&2, U32>:
  ITree.max_last(U32, V, t)

def ITree32.valid(-V: Data, +t: ITree<U32, V>) -> Bool:
  ITree.valid(~U32, ~U32.cmp, V, t)

def ITree32.balanced(-V: Data, t: ITree<U32, V>) -> Bool:
  ITree.balanced(U32, V, t)

def ITree32.overlaps(+s: U32, +l: U32, +a: U32, +b: U32) -> Bool:
  ITree.overlaps(~U32, ~U32.cmp, s, l, a, b)
