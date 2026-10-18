# bend-osdev-maple: the list model, the reference the tree is held to.
#
# What a maple tree holds is a list of entries [first, last] -> value in
# increasing order, no two sharing an index. Each operation here is a plain
# scan of that list, written to be obviously correct:
#
# * load(xs, i) is the value of the entry holding i;
# * set_range(xs, a, b, v) keeps the part of every entry below a, then
#   [a, b] -> v, then the part of every entry above b: an entry that
#   straddles a or b is cut there, and one that spans [a, b] is split in
#   two;
# * clear_range(xs, a, b) is the same without the new entry;
# * find, next and prev pick the first entry ending at or after i, the first
#   starting after i, and the last ending before i;
# * the gap search walks the entries from min with a cursor: the lowest
#   start of a free run of size indices within [min, max].
#
# The key type, its order and its successor and predecessor are template
# arguments (~K, ~cmp, ~inc, ~dec; the gap search also takes ~add and
# ~zero); MapleModel32.* is the U32 instance.
import Base

# Types

# A stored range [first, last] and its value. Open: callers read it.
type MapleEntry<-K: Data, -V: Data> is Data:
  MapleEntry{first: K, last: K, value: V}

# Why an operation refused its arguments.
type MapleError<-K: Data> is Data:
  MapleInverted{first: K, last: K}
  MapleBadSize{}
  MapleBadRange{min: K, max: K}
  MapleBusy{}

# Internal: the state of a gap search (still looking from a cursor, found,
# or out of room).
type MapleGap<-K: Data> is Data:
  MapleGapScan{cur: K}
  MapleGapFound{start: K}
  MapleGapBusy{}

# Entries

def MapleEntry.first(-K: Data, -V: Data, e: MapleEntry<K, V>) -> K:
  match e:
    case MapleEntry{f, l, v}:
      f

def MapleEntry.last(-K: Data, -V: Data, e: MapleEntry<K, V>) -> K:
  match e:
    case MapleEntry{f, l, v}:
      l

def MapleEntry.value(-K: Data, -V: Data, e: MapleEntry<K, V>) -> V:
  match e:
    case MapleEntry{f, l, v}:
      v

# Keys

def MapleKey.lt(~K: Data, ~cmp: K -> K -> Cmp, +a: K, +b: K) -> Bool:
  Cmp.is_lt(cmp(a, b))

def MapleKey.le(~K: Data, ~cmp: K -> K -> Cmp, +a: K, +b: K) -> Bool:
  Cmp.is_le(cmp(a, b))

# whether e holds the index i
def MapleEntry.holds(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: MapleEntry<K, V>, +i: K) -> Bool:
  Bool.and(MapleKey.le(~K, ~cmp, MapleEntry.first(K, V, e), i), MapleKey.le(~K, ~cmp, i, MapleEntry.last(K, V, e)))

# Small list helpers

def MapleModel.pick(-K: Data, -V: Data, b: Bool, x: MapleEntry<K, V>, rest: Maybe<&2, MapleEntry<K, V>>) -> Maybe<&2, MapleEntry<K, V>>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

def MapleModel.pick_value(-V: Data, b: Bool, x: V, rest: Maybe<&2, V>) -> Maybe<&2, V>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

# m if it is something, else n
def MapleModel.later(-K: Data, -V: Data, m: Maybe<&2, MapleEntry<K, V>>, n: Maybe<&2, MapleEntry<K, V>>) -> Maybe<&2, MapleEntry<K, V>>:
  match m:
    case Some{x}:
      Some{x}
    case None{}:
      n

def MapleModel.append(-K: Data, -V: Data, xs: List<&2, MapleEntry<K, V>>, ys: List<&2, MapleEntry<K, V>>) -> List<&2, MapleEntry<K, V>>:
  List.append(&2, MapleEntry<K, V>, xs, ys)

# the last index of the last entry
def MapleModel.last_key(-K: Data, -V: Data, xs: List<&2, MapleEntry<K, V>>) -> Maybe<&2, K>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, r}:
      Maybe.or(&2, K, MapleModel.last_key(K, V, r), Some{MapleEntry.last(K, V, x)})

# The invariant: in order, disjoint, each first <= last

# every entry of xs starts after k
def MapleModel.after(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +k: K, xs: List<&2, MapleEntry<K, V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      Bool.and(MapleKey.lt(~K, ~cmp, k, MapleEntry.first(K, V, x)), MapleModel.after(~K, ~cmp, V, k, r))

def MapleModel.wf(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, MapleEntry<K, V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +r}:
      Bool.and(MapleKey.le(~K, ~cmp, MapleEntry.first(K, V, x), MapleEntry.last(K, V, x)), Bool.and(MapleModel.after(~K, ~cmp, V, MapleEntry.last(K, V, x), r), MapleModel.wf(~K, ~cmp, V, r)))

# Lookup

# the entry holding i
def MapleModel.lookup(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, MapleEntry<K, V>>, +i: K) -> Maybe<&2, MapleEntry<K, V>>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      MapleModel.pick(K, V, MapleEntry.holds(~K, ~cmp, V, x, i), x, MapleModel.lookup(~K, ~cmp, V, r, i))

# the value at i
def MapleModel.load(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, MapleEntry<K, V>>, +i: K) -> Maybe<&2, V>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      MapleModel.pick_value(V, MapleEntry.holds(~K, ~cmp, V, x, i), MapleEntry.value(K, V, x), MapleModel.load(~K, ~cmp, V, r, i))

# the first entry ending at or after i (the one holding i, or the next)
def MapleModel.find(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, MapleEntry<K, V>>, +i: K) -> Maybe<&2, MapleEntry<K, V>>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      MapleModel.pick(K, V, MapleKey.le(~K, ~cmp, i, MapleEntry.last(K, V, x)), x, MapleModel.find(~K, ~cmp, V, r, i))

# the first entry starting after i
def MapleModel.next(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, MapleEntry<K, V>>, +i: K) -> Maybe<&2, MapleEntry<K, V>>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      MapleModel.pick(K, V, MapleKey.lt(~K, ~cmp, i, MapleEntry.first(K, V, x)), x, MapleModel.next(~K, ~cmp, V, r, i))

# the last entry ending before i
def MapleModel.prev(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, MapleEntry<K, V>>, +i: K) -> Maybe<&2, MapleEntry<K, V>>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      MapleModel.later(K, V, MapleModel.prev(~K, ~cmp, V, r, i), MapleModel.pick(K, V, MapleKey.lt(~K, ~cmp, MapleEntry.last(K, V, x), i), x, None{}))

# Cutting at an index

def MapleModel.cut_lo(-K: Data, -V: Data, ends_before: Bool, starts_before: Bool, x: MapleEntry<K, V>, d: K, rest: List<&2, MapleEntry<K, V>>) -> List<&2, MapleEntry<K, V>>:
  match ends_before:
    case True{}:
      Con{x, rest}
    case False{}:
      match starts_before:
        case True{}:
          match x:
            case MapleEntry{f, l, v}:
              Con{MapleEntry{f, d, v}, rest}
        case False{}:
          rest

# every entry cut to its part below a (dec(a) is a's predecessor)
def MapleModel.below(~K: Data, ~cmp: K -> K -> Cmp, ~dec: K -> K, -V: Data, xs: List<&2, MapleEntry<K, V>>, +a: K) -> List<&2, MapleEntry<K, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      MapleModel.cut_lo(K, V, MapleKey.lt(~K, ~cmp, MapleEntry.last(K, V, x), a), MapleKey.lt(~K, ~cmp, MapleEntry.first(K, V, x), a), x, dec(a), MapleModel.below(~K, ~cmp, ~dec, V, r, a))

def MapleModel.cut_hi(-K: Data, -V: Data, starts_after: Bool, ends_after: Bool, x: MapleEntry<K, V>, s: K, rest: List<&2, MapleEntry<K, V>>) -> List<&2, MapleEntry<K, V>>:
  match starts_after:
    case True{}:
      Con{x, rest}
    case False{}:
      match ends_after:
        case True{}:
          match x:
            case MapleEntry{f, l, v}:
              Con{MapleEntry{s, l, v}, rest}
        case False{}:
          rest

# every entry cut to its part above b (inc(b) is b's successor)
def MapleModel.above(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, -V: Data, xs: List<&2, MapleEntry<K, V>>, +b: K) -> List<&2, MapleEntry<K, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      MapleModel.cut_hi(K, V, MapleKey.lt(~K, ~cmp, b, MapleEntry.first(K, V, x)), MapleKey.lt(~K, ~cmp, b, MapleEntry.last(K, V, x)), x, inc(b), MapleModel.above(~K, ~cmp, ~inc, V, r, b))

# Updates

def MapleModel.set_range.go(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, ok: Bool, +xs: List<&2, MapleEntry<K, V>>, +a: K, +b: K, v: V) -> List<&2, MapleEntry<K, V>>:
  match ok:
    case True{}:
      MapleModel.append(K, V, MapleModel.below(~K, ~cmp, ~dec, V, xs, a), Con{MapleEntry{a, b, v}, MapleModel.above(~K, ~cmp, ~inc, V, xs, b)})
    case False{}:
      xs

# [a, b] holding v, overwriting what was there; nothing changes if a > b
def MapleModel.set_range(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, +xs: List<&2, MapleEntry<K, V>>, +a: K, +b: K, v: V) -> List<&2, MapleEntry<K, V>>:
  MapleModel.set_range.go(~K, ~cmp, ~inc, ~dec, V, MapleKey.le(~K, ~cmp, a, b), xs, a, b, v)

def MapleModel.clear_range.go(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, ok: Bool, +xs: List<&2, MapleEntry<K, V>>, +a: K, +b: K) -> List<&2, MapleEntry<K, V>>:
  match ok:
    case True{}:
      MapleModel.append(K, V, MapleModel.below(~K, ~cmp, ~dec, V, xs, a), MapleModel.above(~K, ~cmp, ~inc, V, xs, b))
    case False{}:
      xs

# nothing stored in [a, b]; nothing changes if a > b
def MapleModel.clear_range(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, -V: Data, +xs: List<&2, MapleEntry<K, V>>, +a: K, +b: K) -> List<&2, MapleEntry<K, V>>:
  MapleModel.clear_range.go(~K, ~cmp, ~inc, ~dec, V, MapleKey.le(~K, ~cmp, a, b), xs, a, b)

# The gap search. d is size - 1, so a run from s ends at add(s, d).

def MapleModel.gap_move(~K: Data, ~inc: K -> K, more: Bool, +l: K) -> MapleGap<K>:
  match more:
    case True{}:
      MapleGapScan{inc(l)}
    case False{}:
      MapleGapBusy{}

def MapleModel.gap_try(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, fits: Bool, +cur: K, +l: K, +max: K) -> MapleGap<K>:
  match fits:
    case True{}:
      MapleGapFound{cur}
    case False{}:
      MapleModel.gap_move(~K, ~inc, MapleKey.lt(~K, ~cmp, l, max), l)

def MapleModel.gap_entry(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~add: K -> K -> K, -V: Data, before: Bool, +x: MapleEntry<K, V>, +cur: K, +d: K, +max: K) -> MapleGap<K>:
  match before:
    case True{}:
      MapleGapScan{cur}
    case False{}:
      +e = add(cur, d)
      MapleModel.gap_try(~K, ~cmp, ~inc, Bool.and(MapleKey.le(~K, ~cmp, cur, e), Bool.and(MapleKey.lt(~K, ~cmp, e, MapleEntry.first(K, V, x)), MapleKey.le(~K, ~cmp, e, max))), cur, MapleEntry.last(K, V, x), max)

# one entry, from state st: an entry ending before the cursor changes
# nothing; otherwise the run [cur, cur + d] fits before it, or the cursor
# moves past it (or the search ends, when it reaches max)
def MapleModel.gap_step(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~add: K -> K -> K, -V: Data, st: MapleGap<K>, +x: MapleEntry<K, V>, +d: K, +max: K) -> MapleGap<K>:
  match st:
    case MapleGapScan{+cur}:
      MapleModel.gap_entry(~K, ~cmp, ~inc, ~add, V, MapleKey.lt(~K, ~cmp, MapleEntry.last(K, V, x), cur), x, cur, d, max)
    case MapleGapFound{s}:
      MapleGapFound{s}
    case MapleGapBusy{}:
      MapleGapBusy{}

def MapleModel.gap_scan(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~add: K -> K -> K, -V: Data, xs: List<&2, MapleEntry<K, V>>, st: MapleGap<K>, +d: K, +max: K) -> MapleGap<K>:
  match xs:
    case Nil{}:
      st
    case Con{+x, r}:
      MapleModel.gap_scan(~K, ~cmp, ~inc, ~add, V, r, MapleModel.gap_step(~K, ~cmp, ~inc, ~add, V, st, x, d, max), d, max)

def MapleModel.gap_end.go(-K: Data, fits: Bool, cur: K) -> Result<&2, &2, MapleError<K>, K>:
  match fits:
    case True{}:
      Done{cur}
    case False{}:
      Fail{MapleBusy{}}

# after the last entry: the run from the cursor fits below max, or nothing does
def MapleModel.gap_end(~K: Data, ~cmp: K -> K -> Cmp, ~add: K -> K -> K, st: MapleGap<K>, +d: K, +max: K) -> Result<&2, &2, MapleError<K>, K>:
  match st:
    case MapleGapScan{+cur}:
      +e = add(cur, d)
      MapleModel.gap_end.go(K, Bool.and(MapleKey.le(~K, ~cmp, cur, e), MapleKey.le(~K, ~cmp, e, max)), cur)
    case MapleGapFound{s}:
      Done{s}
    case MapleGapBusy{}:
      Fail{MapleBusy{}}

def MapleModel.empty_area.go(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, ~add: K -> K -> K, -V: Data, zero_size: Bool, inverted: Bool, xs: List<&2, MapleEntry<K, V>>, +min: K, +max: K, +size: K) -> Result<&2, &2, MapleError<K>, K>:
  match zero_size:
    case True{}:
      Fail{MapleBadSize{}}
    case False{}:
      match inverted:
        case True{}:
          Fail{MapleBadRange{min, max}}
        case False{}:
          +d = dec(size)
          MapleModel.gap_end(~K, ~cmp, ~add, MapleModel.gap_scan(~K, ~cmp, ~inc, ~add, V, xs, MapleGapScan{min}, d, max), d, max)

# the lowest s with [s, s + size - 1] free and within [min, max]
def MapleModel.empty_area(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, ~add: K -> K -> K, ~zero: K, -V: Data, xs: List<&2, MapleEntry<K, V>>, +min: K, +max: K, +size: K) -> Result<&2, &2, MapleError<K>, K>:
  MapleModel.empty_area.go(~K, ~cmp, ~inc, ~dec, ~add, V, Cmp.is_eq(cmp(size, zero)), MapleKey.lt(~K, ~cmp, max, min), xs, min, max, size)

# The named default: U32 indices

def MapleKey32.inc(a: U32) -> U32:
  U32.inc(a)

def MapleKey32.dec(a: U32) -> U32:
  U32.sub(a, 1)

def MapleKey32.add(a: U32, b: U32) -> U32:
  U32.add(a, b)

def MapleModel32.wf(-V: Data, xs: List<&2, MapleEntry<U32, V>>) -> Bool:
  MapleModel.wf(~U32, ~U32.cmp, V, xs)

def MapleModel32.load(-V: Data, xs: List<&2, MapleEntry<U32, V>>, +i: U32) -> Maybe<&2, V>:
  MapleModel.load(~U32, ~U32.cmp, V, xs, i)

def MapleModel32.lookup(-V: Data, xs: List<&2, MapleEntry<U32, V>>, +i: U32) -> Maybe<&2, MapleEntry<U32, V>>:
  MapleModel.lookup(~U32, ~U32.cmp, V, xs, i)

def MapleModel32.find(-V: Data, xs: List<&2, MapleEntry<U32, V>>, +i: U32) -> Maybe<&2, MapleEntry<U32, V>>:
  MapleModel.find(~U32, ~U32.cmp, V, xs, i)

def MapleModel32.next(-V: Data, xs: List<&2, MapleEntry<U32, V>>, +i: U32) -> Maybe<&2, MapleEntry<U32, V>>:
  MapleModel.next(~U32, ~U32.cmp, V, xs, i)

def MapleModel32.prev(-V: Data, xs: List<&2, MapleEntry<U32, V>>, +i: U32) -> Maybe<&2, MapleEntry<U32, V>>:
  MapleModel.prev(~U32, ~U32.cmp, V, xs, i)

def MapleModel32.set_range(-V: Data, +xs: List<&2, MapleEntry<U32, V>>, +a: U32, +b: U32, v: V) -> List<&2, MapleEntry<U32, V>>:
  MapleModel.set_range(~U32, ~U32.cmp, ~MapleKey32.inc, ~MapleKey32.dec, V, xs, a, b, v)

def MapleModel32.clear_range(-V: Data, +xs: List<&2, MapleEntry<U32, V>>, +a: U32, +b: U32) -> List<&2, MapleEntry<U32, V>>:
  MapleModel.clear_range(~U32, ~U32.cmp, ~MapleKey32.inc, ~MapleKey32.dec, V, xs, a, b)

def MapleModel32.empty_area(-V: Data, xs: List<&2, MapleEntry<U32, V>>, +min: U32, +max: U32, +size: U32) -> Result<&2, &2, MapleError<U32>, U32>:
  MapleModel.empty_area(~U32, ~U32.cmp, ~MapleKey32.inc, ~MapleKey32.dec, ~MapleKey32.add, ~0, V, xs, min, max, size)

def MapleEntry32.holds(-V: Data, +e: MapleEntry<U32, V>, +i: U32) -> Bool:
  MapleEntry.holds(~U32, ~U32.cmp, V, e, i)
