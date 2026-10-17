# bend-osdev-xarray: a sparse array from 32-bit indices to values, in the
# style of the Linux kernel's XArray (its documented behaviour as an abstract
# data type: load, store, erase, find, iteration over a range, and three
# independent marks per entry). Written from that public description only.
#
# An XArray<V> is a persistent (pure) radix tree. An index is read as its 32
# bits, most significant first, so the tree's left-to-right order is the
# indices' numeric order. Each node splits on one bit (fan-out 2, height 32);
# a subtree with no entries is XNil, so the tree stays sparse. Marks are kept
# as three more trees over the same indices (XArray.mark0..2), each a set of
# marked indices, so a marked search is the same search over the mark's tree.
#
# The representation is internal: other packages use only the defs listed in
# the README.
import Base

# The radix tree

type XTree<-V: Data> is Data:
  XNil{}
  XLeaf{value: V}
  XBin{lo: XTree<V>, hi: XTree<V>}

# An index path: the index's bits, most significant first, as a Word(n) whose
# head is the bit nearest the root. Base's Word(32n) holds a U32's bits least
# significant first, so a path is that word reversed.

# n + m, counted so that moving one bit from a word to its accumulator keeps
# the type: plus(1 + p, m) is plus(p, 1 + m)
def XPath.plus(n: Nat, m: Nat) -> Nat:
  match n:
    case 0n:
      m
    case 1n+p:
      XPath.plus(p, 1n+m)

# the bits of w, reversed, in front of acc
def XPath.rev(n: Nat, w: Word(n), -m: Nat, acc: Word(m)) -> Word(XPath.plus(n, m)):
  match n:
    case 0n:
      acc
    case 1n+p:
      match w:
        case WCon{b, t}:
          XPath.rev(p, t, 1n+m, WCon{b, acc})

# n copies of the bit b
def XPath.fill(n: Nat, +b: Bool) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{b, XPath.fill(p, b)}

def XArray.path(i: U32) -> Word(32n):
  match i:
    case U32{w}:
      XPath.rev(32n, w, 0n, WNil{})

def XArray.index(p: Word(32n)) -> U32:
  U32{XPath.rev(32n, p, 0n, WNil{})}

# The tree on paths

def XTree.leaf(-V: Data, t: XTree<V>) -> Maybe<&2, V>:
  match t:
    case XLeaf{v}:
      Some{v}
    case other:
      None{}

def XTree.load(-V: Data, n: Nat, p: Word(n), t: XTree<V>) -> Maybe<&2, V>:
  match n:
    case 0n:
      XTree.leaf(V, t)
    case 1n+m:
      match p:
        case WCon{b, bs}:
          match b:
            case False{}:
              match t:
                case XBin{lo, hi}:
                  XTree.load(V, m, bs, lo)
                case other:
                  None{}
            case True{}:
              match t:
                case XBin{lo, hi}:
                  XTree.load(V, m, bs, hi)
                case other:
                  None{}

def XTree.store(-V: Data, n: Nat, p: Word(n), t: XTree<V>, v: V) -> XTree<V>:
  match n:
    case 0n:
      XLeaf{v}
    case 1n+m:
      match p:
        case WCon{b, bs}:
          match b:
            case False{}:
              match t:
                case XBin{lo, hi}:
                  XBin{XTree.store(V, m, bs, lo, v), hi}
                case other:
                  XBin{XTree.store(V, m, bs, XNil{}, v), XNil{}}
            case True{}:
              match t:
                case XBin{lo, hi}:
                  XBin{lo, XTree.store(V, m, bs, hi, v)}
                case other:
                  XBin{XNil{}, XTree.store(V, m, bs, XNil{}, v)}

# a node from its two halves, or XNil when both are empty
def XTree.join(-V: Data, lo: XTree<V>, hi: XTree<V>) -> XTree<V>:
  match lo:
    case XNil{}:
      match hi:
        case XNil{}:
          XNil{}
        case h:
          XBin{XNil{}, h}
    case l:
      XBin{l, hi}

def XTree.erase(-V: Data, n: Nat, p: Word(n), t: XTree<V>) -> XTree<V>:
  match n:
    case 0n:
      XNil{}
    case 1n+m:
      match p:
        case WCon{b, bs}:
          match b:
            case False{}:
              match t:
                case XBin{lo, hi}:
                  XTree.join(V, XTree.erase(V, m, bs, lo), hi)
                case other:
                  other
            case True{}:
              match t:
                case XBin{lo, hi}:
                  XTree.join(V, lo, XTree.erase(V, m, bs, hi))
                case other:
                  other

# Searching. The direction d is False for the smallest path first and True
# for the largest first.

def XTree.pre(n: Nat, b: Bool, r: Maybe<&2, Word(n)>) -> Maybe<&2, Word(1n+n)>:
  match r:
    case None{}:
      None{}
    case Some{q}:
      Some{WCon{b, q}}

# r, or else the result of k: k runs only when r is None
def XTree.orelse(n: Nat, r: Maybe<&2, Word(n)>, k: Unit -> Maybe<&2, Word(n)>) -> Maybe<&2, Word(n)>:
  match r:
    case None{}:
      k(Unit{})
    case Some{q}:
      Some{q}

# the first path in direction d, at or after p in that direction, that holds
# an entry. Where p's bit points to the nearer half (False going up, True
# going down), the search continues in the farther half, from its extreme
# path, only if the nearer half has nothing.
def XTree.seek(-V: Data, n: Nat, p: Word(n), t: XTree<V>, d: Bool) -> Maybe<&2, Word(n)>:
  match n:
    case 0n:
      match t:
        case XLeaf{v}:
          Some{WNil{}}
        case other:
          None{}
    case 1n+ +m:
      match p:
        case WCon{b, bs}:
          match b:
            case False{}:
              match t:
                case XBin{lo, hi}:
                  match d:
                    case False{}:
                      XTree.orelse(1n+m, XTree.pre(m, False{}, XTree.seek(V, m, bs, lo, False{})), u => XTree.pre(m, True{}, XTree.seek(V, m, XPath.fill(m, False{}), hi, False{})))
                    case True{}:
                      XTree.pre(m, False{}, XTree.seek(V, m, bs, lo, True{}))
                case other:
                  None{}
            case True{}:
              match t:
                case XBin{lo, hi}:
                  match d:
                    case False{}:
                      XTree.pre(m, True{}, XTree.seek(V, m, bs, hi, False{}))
                    case True{}:
                      XTree.orelse(1n+m, XTree.pre(m, True{}, XTree.seek(V, m, bs, hi, True{})), u => XTree.pre(m, False{}, XTree.seek(V, m, XPath.fill(m, True{}), lo, True{})))
                case other:
                  None{}

# Iteration: the entries whose paths lie in [a, b], in ascending order

type XAt<-n: Nat, -V: Data> is Data:
  XAt{path: Word(n), value: V}

def XTree.tag(-V: Data, -n: Nat, +b: Bool, xs: List<&2, XAt<n, V>>) -> List<&2, XAt<1n+n, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case XAt{q, v}:
          Con{XAt{WCon{b, q}, v}, XTree.tag(V, n, b, t)}

def XTree.range(-V: Data, +n: Nat, t: XTree<V>, a: Word(n), b: Word(n)) -> List<&2, XAt<n, V>>:
  match n:
    case 0n:
      match t:
        case XLeaf{v}:
          Con{XAt{WNil{}, v}, Nil{}}
        case other:
          Nil{}
    case 1n+ +m:
      match t:
        case XBin{lo, hi}:
          match a:
            case WCon{x, as}:
              match x:
                case False{}:
                  match b:
                    case WCon{y, bs}:
                      match y:
                        case False{}:
                          XTree.tag(V, m, False{}, XTree.range(V, m, lo, as, bs))
                        case True{}:
                          List.append(&2, XAt<1n+m, V>, XTree.tag(V, m, False{}, XTree.range(V, m, lo, as, XPath.fill(m, True{}))), XTree.tag(V, m, True{}, XTree.range(V, m, hi, XPath.fill(m, False{}), bs)))
                case True{}:
                  match b:
                    case WCon{y, bs}:
                      match y:
                        case False{}:
                          Nil{}
                        case True{}:
                          XTree.tag(V, m, True{}, XTree.range(V, m, hi, as, bs))
        case other:
          Nil{}

# The public interface

# The three marks, as the kernel's XA_MARK_0, XA_MARK_1 and XA_MARK_2
type XMark is Data:
  XMark0{}
  XMark1{}
  XMark2{}

def XMark.is_eq(a: XMark, b: XMark) -> Bool:
  match a b:
    case XMark0{} XMark0{}:
      True{}
    case XMark1{} XMark1{}:
      True{}
    case XMark2{} XMark2{}:
      True{}
    case x y:
      False{}

# an entry of a range: its index and its value
type XEntry<-V: Data> is Data:
  XEntry{index: U32, value: V}

type XArray<-V: Data> is Data:
  XArray{vals: XTree<V>, mark0: XTree<Unit>, mark1: XTree<Unit>, mark2: XTree<Unit>}

def XArray.empty(-V: Data) -> XArray<V>:
  XArray{XNil{}, XNil{}, XNil{}, XNil{}}

# the entry at index i, if any
def XArray.load(-V: Data, t: XArray<V>, i: U32) -> Maybe<&2, V>:
  match t:
    case XArray{vals, m0, m1, m2}:
      XTree.load(V, 32n, XArray.path(i), vals)

# the array with v at index i; the index keeps its marks
def XArray.store(-V: Data, t: XArray<V>, i: U32, v: V) -> XArray<V>:
  match t:
    case XArray{vals, m0, m1, m2}:
      XArray{XTree.store(V, 32n, XArray.path(i), vals, v), m0, m1, m2}

# Why an insert fails
type XArrayError is Data:
  XArrayBusy{}

def XArray.insert.go(-V: Data, present: Bool, t: XArray<V>, i: U32, v: V) -> Result<&2, &2, XArrayError, XArray<V>>:
  match present:
    case True{}:
      Fail{XArrayBusy{}}
    case False{}:
      Done{XArray.store(V, t, i, v)}

# the array with v at index i, if i holds no entry yet; XArrayBusy if it does
def XArray.insert(-V: Data, +t: XArray<V>, +i: U32, v: V) -> Result<&2, &2, XArrayError, XArray<V>>:
  XArray.insert.go(V, Maybe.is_some(&2, V, XArray.load(V, t, i)), t, i, v)

# the array with no entry at index i, and no marks there
def XArray.erase(-V: Data, t: XArray<V>, i: U32) -> XArray<V>:
  match t:
    case XArray{vals, m0, m1, m2}:
      +p = XArray.path(i)
      XArray{XTree.erase(V, 32n, p, vals), XTree.erase(Unit, 32n, p, m0), XTree.erase(Unit, 32n, p, m1), XTree.erase(Unit, 32n, p, m2)}

def XArray.found(r: Maybe<&2, Word(32n)>) -> Maybe<&2, U32>:
  match r:
    case None{}:
      None{}
    case Some{q}:
      Some{XArray.index(q)}

# the smallest index at or after start that holds an entry
def XArray.find(-V: Data, t: XArray<V>, start: U32) -> Maybe<&2, U32>:
  match t:
    case XArray{vals, m0, m1, m2}:
      XArray.found(XTree.seek(V, 32n, XArray.path(start), vals, False{}))

# the largest index at or before start that holds an entry
def XArray.find_last(-V: Data, t: XArray<V>, start: U32) -> Maybe<&2, U32>:
  match t:
    case XArray{vals, m0, m1, m2}:
      XArray.found(XTree.seek(V, 32n, XArray.path(start), vals, True{}))

# whether the array holds no entry
def XArray.is_empty(-V: Data, t: XArray<V>) -> Bool:
  match t:
    case XArray{vals, m0, m1, m2}:
      Maybe.is_none(&2, Word(32n), XTree.seek(V, 32n, XPath.fill(32n, False{}), vals, False{}))

def XArray.entries(-V: Data, r: List<&2, XAt<32n, V>>) -> List<&2, XEntry<V>>:
  match r:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case XAt{q, v}:
          Con{XEntry{XArray.index(q), v}, XArray.entries(V, t)}

# the entries whose indices lie in [first, last], in ascending order of index
def XArray.range(-V: Data, t: XArray<V>, first: U32, last: U32) -> List<&2, XEntry<V>>:
  match t:
    case XArray{vals, m0, m1, m2}:
      XArray.entries(V, XTree.range(V, 32n, vals, XArray.path(first), XArray.path(last)))

# Marks

# the tree of indices that carry mark m
def XArray.marks(-V: Data, t: XArray<V>, m: XMark) -> XTree<Unit>:
  match t:
    case XArray{vals, m0, m1, m2}:
      match m:
        case XMark0{}:
          m0
        case XMark1{}:
          m1
        case XMark2{}:
          m2

# whether index i carries mark m
def XArray.get_mark(-V: Data, t: XArray<V>, i: U32, m: XMark) -> Bool:
  Maybe.is_some(&2, Unit, XTree.load(Unit, 32n, XArray.path(i), XArray.marks(V, t, m)))

def XArray.mark_with(-V: Data, m: XMark, vals: XTree<V>, m0: XTree<Unit>, m1: XTree<Unit>, m2: XTree<Unit>, f: XTree<Unit> -> XTree<Unit>) -> XArray<V>:
  match m:
    case XMark0{}:
      XArray{vals, f(m0), m1, m2}
    case XMark1{}:
      XArray{vals, m0, f(m1), m2}
    case XMark2{}:
      XArray{vals, m0, m1, f(m2)}

def XArray.set_mark.go(-V: Data, present: Bool, m: XMark, +p: Word(32n), vals: XTree<V>, m0: XTree<Unit>, m1: XTree<Unit>, m2: XTree<Unit>) -> XArray<V>:
  match present:
    case True{}:
      XArray.mark_with(V, m, vals, m0, m1, m2, s => XTree.store(Unit, 32n, p, s, Unit{}))
    case False{}:
      XArray{vals, m0, m1, m2}

# the array with mark m set on index i, if i holds an entry (else unchanged)
def XArray.set_mark(-V: Data, t: XArray<V>, i: U32, m: XMark) -> XArray<V>:
  match t:
    case XArray{+vals, m0, m1, m2}:
      +p = XArray.path(i)
      XArray.set_mark.go(V, Maybe.is_some(&2, V, XTree.load(V, 32n, p, vals)), m, p, vals, m0, m1, m2)

# the array with mark m cleared on index i
def XArray.clear_mark(-V: Data, t: XArray<V>, i: U32, m: XMark) -> XArray<V>:
  match t:
    case XArray{vals, m0, m1, m2}:
      +p = XArray.path(i)
      XArray.mark_with(V, m, vals, m0, m1, m2, s => XTree.erase(Unit, 32n, p, s))

# the smallest index at or after start that carries mark m
def XArray.find_marked(-V: Data, t: XArray<V>, start: U32, m: XMark) -> Maybe<&2, U32>:
  XArray.found(XTree.seek(Unit, 32n, XArray.path(start), XArray.marks(V, t, m), False{}))
