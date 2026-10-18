# bend-osdev-maple: restructuring B-trees: joining two trees, and cutting
# a tree at an index.
#
# join(t1, t2) is the tree holding t1's entries, then t2's: the shorter is
# merged into the taller one's right (or left) edge at its own height, and
# every node on the way back up that overflows is split in two (as a
# B-tree insertion splits). Below an index a, lo keeps the part of the tree
# below a, and hi the part above an index b: each walks down to the leaf
# holding the index, cutting the entry there, and joins what lies on either
# side on the way back. Storing [a, b] is then join(join(lo(a), [a, b]),
# hi(b)), and erasing [a, b] is join(lo(a), hi(b)).
#
# Each of these keeps the contents in order for every tree; that the result
# is a B-tree again (every leaf at the same depth, nodes between half full
# and full) is what the joins are built to keep.
import Base
import ./model.bend as M
import ./node.bend as N

def MapleTree.empty_of(-K: Data, -V: Data, order: Nat) -> N.MapleTree<K, V>:
  N.MapleTree{order, 0n, N.MapleLeaf{Nil{}}}

def MapleTree.entries(-K: Data, -V: Data, t: N.MapleTree<K, V>) -> List<&2, M.MapleEntry<K, V>>:
  match t:
    case N.MapleTree{o, h, n}:
      N.MapleNode.entries(K, V, n)

# a root of height h, with a lone child pulled up (and an empty chain made
# the empty leaf)
def MapleTree.norm(-K: Data, -V: Data, h: Nat, n: N.MapleNode<K, V>, order: Nat) -> N.MapleTree<K, V>:
  match h:
    case 0n:
      N.MapleTree{order, 0n, n}
    case 1n+g:
      match n:
        case N.MapleSlot{p, c, r}:
          match r:
            case N.MapleNil{}:
              MapleTree.norm(K, V, g, c, order)
            case N.MapleLeaf{es}:
              N.MapleTree{order, 1n+g, N.MapleSlot{p, c, N.MapleLeaf{es}}}
            case N.MapleSlot{q, d, s}:
              N.MapleTree{order, 1n+g, N.MapleSlot{p, c, N.MapleSlot{q, d, s}}}
        case N.MapleNil{}:
          MapleTree.empty_of(K, V, order)
        case N.MapleLeaf{es}:
          N.MapleTree{order, 1n+g, N.MapleLeaf{es}}

# n1 is d levels taller than n2: n2 merged into n1's right edge, as the
# chain of the one or two nodes that replace n1
def MapleTree.join_right(-K: Data, -V: Data, d: Nat, +n1: N.MapleNode<K, V>, n2: N.MapleNode<K, V>, +order: Nat) -> N.MapleNode<K, V>:
  match d:
    case 0n:
      N.MapleNode.fit(K, V, order, N.MapleNode.merge(K, V, n1, n2))
    case 1n+e:
      N.MapleNode.fit(K, V, order, N.MapleNode.append(K, V, N.MapleNode.init(K, V, n1), MapleTree.join_right(K, V, e, N.MapleNode.last(K, V, n1), n2, order)))

# n2 is d levels taller than n1: n1 merged into n2's left edge
def MapleTree.join_left(-K: Data, -V: Data, d: Nat, n1: N.MapleNode<K, V>, +n2: N.MapleNode<K, V>, +order: Nat) -> N.MapleNode<K, V>:
  match d:
    case 0n:
      N.MapleNode.fit(K, V, order, N.MapleNode.merge(K, V, n1, n2))
    case 1n+e:
      N.MapleNode.fit(K, V, order, N.MapleNode.append(K, V, MapleTree.join_left(K, V, e, n1, N.MapleNode.first(K, V, n2), order), N.MapleNode.tail(K, V, n2)))

def MapleTree.join.tall(-K: Data, -V: Data, right: Bool, +h1: Nat, n1: N.MapleNode<K, V>, +h2: Nat, n2: N.MapleNode<K, V>, +order: Nat) -> N.MapleTree<K, V>:
  match right:
    case True{}:
      MapleTree.norm(K, V, 1n+h1, MapleTree.join_right(K, V, Nat.sub(h1, h2), n1, n2, order), order)
    case False{}:
      MapleTree.norm(K, V, 1n+h2, MapleTree.join_left(K, V, Nat.sub(h2, h1), n1, n2, order), order)

def MapleTree.join.go(-K: Data, -V: Data, e1: Bool, e2: Bool, +order: Nat, +h1: Nat, n1: N.MapleNode<K, V>, +h2: Nat, n2: N.MapleNode<K, V>) -> N.MapleTree<K, V>:
  match e1:
    case True{}:
      N.MapleTree{order, h2, n2}
    case False{}:
      match e2:
        case True{}:
          N.MapleTree{order, h1, n1}
        case False{}:
          MapleTree.join.tall(K, V, Nat.is_le(h2, h1), h1, n1, h2, n2, order)

# t1's entries, then t2's (with t1's order)
def MapleTree.join(-K: Data, -V: Data, t1: N.MapleTree<K, V>, t2: N.MapleTree<K, V>) -> N.MapleTree<K, V>:
  match t1:
    case N.MapleTree{o1, h1, +n1}:
      match t2:
        case N.MapleTree{o2, h2, +n2}:
          MapleTree.join.go(K, V, N.MapleNode.is_empty(K, V, n1), N.MapleNode.is_empty(K, V, n2), o1, h1, n1, h2, n2)

# The part of n (a node of height h) below a, after pre (a chain of
# children of height h - 1, all below a): c = cmp(first pivot, a). Children
# whose pivot is below a join pre; the child holding a is cut there, and
# what follows it is dropped.
def MapleTree.lo(~K: Data, ~cmp: K -> K -> Cmp, ~dec: K -> K, -V: Data, n: N.MapleNode<K, V>, h: Nat, +a: K, pre: N.MapleNode<K, V>, c: Cmp, +order: Nat) -> N.MapleTree<K, V>:
  match n:
    case N.MapleSlot{p, +ch, +r}:
      match h:
        case 0n:
          MapleTree.join(K, V, MapleTree.norm(K, V, 0n, pre, order), N.MapleTree{order, 0n, N.MapleLeaf{M.MapleModel.below(~K, ~cmp, ~dec, V, N.MapleNode.entries(K, V, N.MapleSlot{p, ch, r}), a)}})
        case 1n+(+g):
          match c:
            case LT{}:
              MapleTree.lo(~K, ~cmp, ~dec, V, r, 1n+g, a, N.MapleNode.append(K, V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), N.MapleNode.probe(~K, ~cmp, V, r, a), order)
            case o:
              MapleTree.join(K, V, MapleTree.norm(K, V, 1n+g, pre, order), MapleTree.lo(~K, ~cmp, ~dec, V, ch, g, a, N.MapleNil{}, N.MapleNode.probe(~K, ~cmp, V, ch, a), order))
    case N.MapleNil{}:
      MapleTree.norm(K, V, h, pre, order)
    case N.MapleLeaf{es}:
      MapleTree.join(K, V, MapleTree.norm(K, V, h, pre, order), N.MapleTree{order, 0n, N.MapleLeaf{M.MapleModel.below(~K, ~cmp, ~dec, V, es, a)}})

# The part of n (a node of height h) above b: c = cmp(first pivot, b).
# Children whose pivot is at most b are dropped; the child holding b's
# successor is cut there, and joined with the children after it.
def MapleTree.hi(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, -V: Data, n: N.MapleNode<K, V>, h: Nat, +b: K, c: Cmp, +order: Nat) -> N.MapleTree<K, V>:
  match n:
    case N.MapleSlot{p, +ch, +r}:
      match h:
        case 0n:
          N.MapleTree{order, 0n, N.MapleLeaf{M.MapleModel.above(~K, ~cmp, ~inc, V, N.MapleNode.entries(K, V, N.MapleSlot{p, ch, r}), b)}}
        case 1n+(+g):
          match c:
            case GT{}:
              MapleTree.join(K, V, MapleTree.hi(~K, ~cmp, ~inc, V, ch, g, b, N.MapleNode.probe(~K, ~cmp, V, ch, b), order), MapleTree.norm(K, V, 1n+g, r, order))
            case o:
              MapleTree.hi(~K, ~cmp, ~inc, V, r, 1n+g, b, N.MapleNode.probe(~K, ~cmp, V, r, b), order)
    case N.MapleNil{}:
      MapleTree.empty_of(K, V, order)
    case N.MapleLeaf{es}:
      N.MapleTree{order, 0n, N.MapleLeaf{M.MapleModel.above(~K, ~cmp, ~inc, V, es, b)}}
