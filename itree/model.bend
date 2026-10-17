# bend-osdev-itree: the list model, the reference the tree is proved against.
#
# The contents of a tree are a list of entries in increasing key order (the
# key of [start, last] is (start, last), compared by start, then by last).
# Each operation here is a plain scan of that list, written to be obviously
# correct: a query keeps the entries that overlap, an insertion puts the
# entry in its place (replacing one with the same key), a removal drops the
# entry with the key.
import Base
import ./itree.bend as T

def ITreeModel.insert.go(-K: Data, -V: Data, c: Cmp, x: T.ITreeEntry<K, V>, r: List<&2, T.ITreeEntry<K, V>>, n: T.ITreeEntry<K, V>, rec: List<&2, T.ITreeEntry<K, V>>) -> List<&2, T.ITreeEntry<K, V>>:
  match c:
    case LT{}:
      Con{n, Con{x, r}}
    case EQ{}:
      Con{n, r}
    case GT{}:
      Con{x, rec}

# xs with [s, l] holding v, in its place in key order
def ITreeModel.insert(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +s: K, +l: K, +v: V) -> List<&2, T.ITreeEntry<K, V>>:
  match xs:
    case Nil{}:
      Con{T.ITreeEntry{s, l, v}, Nil{}}
    case Con{+x, +r}:
      ITreeModel.insert.go(K, V, T.ITree.entry_cmp(~K, ~cmp, V, s, l, x), x, r, T.ITreeEntry{s, l, v}, ITreeModel.insert(~K, ~cmp, V, r, s, l, v))

def ITreeModel.set.go(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, c: Cmp, xs: List<&2, T.ITreeEntry<K, V>>, +s: K, +l: K, v: V) -> List<&2, T.ITreeEntry<K, V>>:
  match c:
    case GT{}:
      xs
    case o:
      ITreeModel.insert(~K, ~cmp, V, xs, s, l, v)

# what ITree.set does to the contents: an inverted interval changes nothing
def ITreeModel.set(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +s: K, +l: K, v: V) -> List<&2, T.ITreeEntry<K, V>>:
  ITreeModel.set.go(~K, ~cmp, V, cmp(s, l), xs, s, l, v)

# xs without the entries whose key is (s, l)
def ITreeModel.remove(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +s: K, +l: K) -> List<&2, T.ITreeEntry<K, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      T.ITree.keep(K, V, Bool.not(Cmp.is_eq(T.ITree.entry_cmp(~K, ~cmp, V, s, l, x))), x, ITreeModel.remove(~K, ~cmp, V, r, s, l))

def ITreeModel.lookup.go(-K: Data, -V: Data, b: Bool, x: T.ITreeEntry<K, V>, rest: Maybe<&2, V>) -> Maybe<&2, V>:
  match b:
    case True{}:
      Some{T.ITreeEntry.value(K, V, x)}
    case False{}:
      rest

# the value of the first entry whose key is (s, l)
def ITreeModel.lookup(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +s: K, +l: K) -> Maybe<&2, V>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      ITreeModel.lookup.go(K, V, Cmp.is_eq(T.ITree.entry_cmp(~K, ~cmp, V, s, l, x)), x, ITreeModel.lookup(~K, ~cmp, V, r, s, l))

# the entries overlapping [a, b], in order
def ITreeModel.overlapping(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +a: K, +b: K) -> List<&2, T.ITreeEntry<K, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      T.ITree.keep(K, V, T.ITree.entry_overlaps(~K, ~cmp, V, x, a, b), x, ITreeModel.overlapping(~K, ~cmp, V, r, a, b))

# the first entry after lo overlapping [a, b]
def ITreeModel.seek(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +a: K, +b: K, +lo: T.ITreeBound<K>) -> Maybe<&2, T.ITreeEntry<K, V>>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      T.ITree.orelse(K, V, T.ITree.pick(K, V, Bool.and(T.ITree.after(~K, ~cmp, V, lo, x), T.ITree.entry_overlaps(~K, ~cmp, V, x, a, b)), x), ITreeModel.seek(~K, ~cmp, V, r, a, b, lo))

def ITreeModel.first(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +a: K, +b: K) -> Maybe<&2, T.ITreeEntry<K, V>>:
  ITreeModel.seek(~K, ~cmp, V, xs, a, b, T.ITreeFromStart{})

def ITreeModel.next(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +a: K, +b: K, +s: K, +l: K) -> Maybe<&2, T.ITreeEntry<K, V>>:
  ITreeModel.seek(~K, ~cmp, V, xs, a, b, T.ITreeAfter{s, l})

# every entry of xs ends at or before m
def ITreeModel.lasts_le(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +m: K) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      Bool.and(Cmp.is_le(cmp(T.ITreeEntry.last(K, V, x), m)), ITreeModel.lasts_le(~K, ~cmp, V, r, m))

# some entry of xs ends at m
def ITreeModel.has_last(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, T.ITreeEntry<K, V>>, +m: K) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, r}:
      Bool.or(Cmp.is_eq(cmp(T.ITreeEntry.last(K, V, x), m)), ITreeModel.has_last(~K, ~cmp, V, r, m))

# The named default: U32 keys

def ITreeModel32.set(-V: Data, xs: List<&2, T.ITreeEntry<U32, V>>, +s: U32, +l: U32, v: V) -> List<&2, T.ITreeEntry<U32, V>>:
  ITreeModel.set(~U32, ~U32.cmp, V, xs, s, l, v)

def ITreeModel32.remove(-V: Data, xs: List<&2, T.ITreeEntry<U32, V>>, +s: U32, +l: U32) -> List<&2, T.ITreeEntry<U32, V>>:
  ITreeModel.remove(~U32, ~U32.cmp, V, xs, s, l)

def ITreeModel32.lookup(-V: Data, xs: List<&2, T.ITreeEntry<U32, V>>, +s: U32, +l: U32) -> Maybe<&2, V>:
  ITreeModel.lookup(~U32, ~U32.cmp, V, xs, s, l)

def ITreeModel32.overlapping(-V: Data, xs: List<&2, T.ITreeEntry<U32, V>>, +a: U32, +b: U32) -> List<&2, T.ITreeEntry<U32, V>>:
  ITreeModel.overlapping(~U32, ~U32.cmp, V, xs, a, b)

def ITreeModel32.first(-V: Data, xs: List<&2, T.ITreeEntry<U32, V>>, +a: U32, +b: U32) -> Maybe<&2, T.ITreeEntry<U32, V>>:
  ITreeModel.first(~U32, ~U32.cmp, V, xs, a, b)

def ITreeModel32.next(-V: Data, xs: List<&2, T.ITreeEntry<U32, V>>, +a: U32, +b: U32, +s: U32, +l: U32) -> Maybe<&2, T.ITreeEntry<U32, V>>:
  ITreeModel.next(~U32, ~U32.cmp, V, xs, a, b, s, l)

def ITreeModel32.lasts_le(-V: Data, xs: List<&2, T.ITreeEntry<U32, V>>, +m: U32) -> Bool:
  ITreeModel.lasts_le(~U32, ~U32.cmp, V, xs, m)

def ITreeModel32.has_last(-V: Data, xs: List<&2, T.ITreeEntry<U32, V>>, +m: U32) -> Bool:
  ITreeModel.has_last(~U32, ~U32.cmp, V, xs, m)
