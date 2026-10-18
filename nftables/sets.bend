# bend-osdev-nftables: keys, sets, maps and verdict maps (nft(8), "SETS",
# "MAPS", "VERDICT MAPS"; the nftables wiki, "Sets", "Maps", "Verdict
# maps", "Intervals").
#
# A key is a byte string (Octets) in network byte order, compared
# byte by byte, most significant first: for keys of one length this is the
# order of the numbers they spell. A set is a list of elements, each a
# closed interval [lo, hi] of keys (a single key is the interval [k, k]) and
# the data a map gives for it: none for a set, a value for a map, a verdict
# for a verdict map. The elements are kept in key order and never overlap:
# inserting an element that overlaps one already there fails with
# NftErrSetOverlap, as nft refuses conflicting intervals.
import Base
import ../bytes/bytes.bend as B
import ./family.bend as F
import ./verdict.bend as V

# Keys

def NftKey.cmp.pick(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case EQ{}:
      rest
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def NftKey.cmp.list(a: List<&2, U32>, b: List<&2, U32>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{y, ys}:
      LT{}
    case Con{x, xs} Nil{}:
      GT{}
    case Con{x, xs} Con{y, ys}:
      NftKey.cmp.pick(U32.cmp(x, y), NftKey.cmp.list(xs, ys))

# byte by byte, most significant first; a proper prefix comes first
def NftKey.cmp(a: B.Octets, b: B.Octets) -> Cmp:
  NftKey.cmp.list(B.Octets.to_list(a), B.Octets.to_list(b))

def NftKey.lt(a: B.Octets, b: B.Octets) -> Bool:
  Cmp.is_lt(NftKey.cmp(a, b))

def NftKey.le(a: B.Octets, b: B.Octets) -> Bool:
  Cmp.is_le(NftKey.cmp(a, b))

def NftKey.eq(a: B.Octets, b: B.Octets) -> Bool:
  Cmp.is_eq(NftKey.cmp(a, b))

# Keys of the usual widths, in network byte order

def NftKey.u8(v: U32) -> B.Octets:
  B.Octets.of_list([v])

def NftKey.u16(v: U32) -> B.Octets:
  B.Octets.of_list(B.be16(v))

def NftKey.u32(v: U32) -> B.Octets:
  B.Octets.of_list(B.be32(v))

# the IPv4 address a.b.c.d
def NftKey.ipv4(a: U32, b: U32, c: U32, d: U32) -> B.Octets:
  B.Octets.of_list([a, b, c, d])

# a concatenation, as `ip saddr . tcp dport`
def NftKey.concat(a: B.Octets, b: B.Octets) -> B.Octets:
  B.Octets.append(a, b)

# Prefixes: the bits of a byte that the first n bits of a prefix keep
def NftKey.pmask(+n: Nat) -> U32:
  U32.and(U32.sub(0, U32.shln(1, Nat.sub(8n, n))), 255)

def NftKey.prefix_lo.go(xs: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{U32.and(b, NftKey.pmask(n)), NftKey.prefix_lo.go(t, Nat.sub(n, 8n))}

def NftKey.prefix_hi.go(xs: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{U32.and(U32.or(b, U32.xor(NftKey.pmask(n), 255)), 255), NftKey.prefix_hi.go(t, Nat.sub(n, 8n))}

# the lowest key with the first n bits of k
def NftKey.prefix_lo(k: B.Octets, +n: Nat) -> B.Octets:
  B.Octets.of_list(NftKey.prefix_lo.go(B.Octets.to_list(k), n))

# the highest key with the first n bits of k
def NftKey.prefix_hi(k: B.Octets, +n: Nat) -> B.Octets:
  B.Octets.of_list(NftKey.prefix_hi.go(B.Octets.to_list(k), n))

# Elements

# What a map gives for an element: nothing (a set), a value, or a verdict
type NftData is Data:
  NftNoData{}
  NftDataValue{value: B.Octets}
  NftDataVerdict{verdict: V.NftVerdict}

# The closed interval [lo, hi] of keys, with its data. Open type.
type NftElem is Data:
  NftElem{lo: B.Octets, hi: B.Octets, data: NftData}

def NftElem.lo(e: NftElem) -> B.Octets:
  match e:
    case NftElem{lo, hi, d}:
      lo

def NftElem.hi(e: NftElem) -> B.Octets:
  match e:
    case NftElem{lo, hi, d}:
      hi

def NftElem.data(e: NftElem) -> NftData:
  match e:
    case NftElem{lo, hi, d}:
      d

# one key
def NftElem.single(+k: B.Octets) -> NftElem:
  NftElem{k, k, NftNoData{}}

# the keys from lo to hi
def NftElem.range(lo: B.Octets, hi: B.Octets) -> NftElem:
  NftElem{lo, hi, NftNoData{}}

# the keys whose first n bits are those of k, as 10.0.0.0/8
def NftElem.prefix(+k: B.Octets, +n: Nat) -> NftElem:
  NftElem{NftKey.prefix_lo(k, n), NftKey.prefix_hi(k, n), NftNoData{}}

# e with the data d, for a map or a verdict map
def NftElem.to(e: NftElem, d: NftData) -> NftElem:
  match e:
    case NftElem{lo, hi, old}:
      NftElem{lo, hi, d}

# whether lo <= hi
def NftElem.valid(e: NftElem) -> Bool:
  match e:
    case NftElem{lo, hi, d}:
      NftKey.le(lo, hi)

# whether e holds the key x
def NftElem.contains(e: NftElem, +x: B.Octets) -> Bool:
  match e:
    case NftElem{lo, hi, d}:
      Bool.and(NftKey.le(lo, x), NftKey.le(x, hi))

# Sets. Opaque: use the defs below.
type NftSet is Data:
  NftSet{elems: List<&2, NftElem>}

def NftSet.empty() -> NftSet:
  NftSet{Nil{}}

# the elements, in key order
def NftSet.elements(s: NftSet) -> List<&2, NftElem>:
  match s:
    case NftSet{es}:
      es

def NftSet.mem.go(es: List<&2, NftElem>, +x: B.Octets) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, t}:
      Bool.or(NftElem.contains(e, x), NftSet.mem.go(t, x))

# whether some element holds the key x
def NftSet.mem(s: NftSet, +x: B.Octets) -> Bool:
  match s:
    case NftSet{es}:
      NftSet.mem.go(es, x)

def NftSet.lookup.pick(b: Bool, d: NftData, rest: Maybe<&2, NftData>) -> Maybe<&2, NftData>:
  match b:
    case True{}:
      Some{d}
    case False{}:
      rest

def NftSet.lookup.go(es: List<&2, NftElem>, +x: B.Octets) -> Maybe<&2, NftData>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, t}:
      NftSet.lookup.pick(NftElem.contains(e, x), NftElem.data(e), NftSet.lookup.go(t, x))

# the data of the element holding x, for a map
def NftSet.lookup(s: NftSet, +x: B.Octets) -> Maybe<&2, NftData>:
  match s:
    case NftSet{es}:
      NftSet.lookup.go(es, x)

# The invariant: every element valid, each one's high end below the next
# one's low end

def NftSet.sep(a: NftElem, es: List<&2, NftElem>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{b, t}:
      NftKey.lt(NftElem.hi(a), NftElem.lo(b))

def NftSet.wf.go(es: List<&2, NftElem>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+a, +t}:
      Bool.and(NftElem.valid(a), Bool.and(NftSet.sep(a, t), NftSet.wf.go(t)))

def NftSet.wf(s: NftSet) -> Bool:
  match s:
    case NftSet{es}:
      NftSet.wf.go(es)

# Insertion

def NftSet.cons(h: NftElem, r: Result<&2, &2, F.NftError, List<&2, NftElem>>) -> Result<&2, &2, F.NftError, List<&2, NftElem>>:
  match r:
    case Done{t}:
      Done{Con{h, t}}
    case Fail{e}:
      Fail{e}

# e goes before h, after h (and into t), or overlaps h; r is e inserted
# into t
def NftSet.ins.pick(before: Bool, after: Bool, e: NftElem, h: NftElem, t: List<&2, NftElem>, r: Result<&2, &2, F.NftError, List<&2, NftElem>>) -> Result<&2, &2, F.NftError, List<&2, NftElem>>:
  match before:
    case True{}:
      Done{Con{e, Con{h, t}}}
    case False{}:
      match after:
        case True{}:
          NftSet.cons(h, r)
        case False{}:
          Fail{F.NftErrSetOverlap{}}

def NftSet.ins(es: List<&2, NftElem>, +e: NftElem) -> Result<&2, &2, F.NftError, List<&2, NftElem>>:
  match es:
    case Nil{}:
      Done{Con{e, Nil{}}}
    case Con{+h, +t}:
      NftSet.ins.pick(NftKey.lt(NftElem.hi(e), NftElem.lo(h)), NftKey.lt(NftElem.hi(h), NftElem.lo(e)), e, h, t, NftSet.ins(t, e))

def NftSet.wrap(r: Result<&2, &2, F.NftError, List<&2, NftElem>>) -> Result<&2, &2, F.NftError, NftSet>:
  match r:
    case Done{es}:
      Done{NftSet{es}}
    case Fail{e}:
      Fail{e}

def NftSet.insert.go(ok: Bool, es: List<&2, NftElem>, e: NftElem) -> Result<&2, &2, F.NftError, NftSet>:
  match ok:
    case False{}:
      Fail{F.NftErrBadInterval{}}
    case True{}:
      NftSet.wrap(NftSet.ins(es, e))

# s with the element e: NftErrBadInterval if e's low end is above its high
# end, NftErrSetOverlap if e overlaps an element of s
def NftSet.insert(s: NftSet, +e: NftElem) -> Result<&2, &2, F.NftError, NftSet>:
  match s:
    case NftSet{es}:
      NftSet.insert.go(NftElem.valid(e), es, e)

def NftSet.add(r: Result<&2, &2, F.NftError, NftSet>, e: NftElem) -> Result<&2, &2, F.NftError, NftSet>:
  match r:
    case Done{s}:
      NftSet.insert(s, e)
    case Fail{err}:
      Fail{err}

def NftSet.of_list.go(es: List<&2, NftElem>, acc: Result<&2, &2, F.NftError, NftSet>) -> Result<&2, &2, F.NftError, NftSet>:
  match es:
    case Nil{}:
      acc
    case Con{e, t}:
      NftSet.of_list.go(t, NftSet.add(acc, e))

# the set of the elements es, inserted in order: the first error, if any
def NftSet.of_list(es: List<&2, NftElem>) -> Result<&2, &2, F.NftError, NftSet>:
  NftSet.of_list.go(es, Done{NftSet.empty()})

# Named sets and maps, as a table holds them

type NftNamedSet is Data:
  NftNamedSet{name: String, set: NftSet}

def NftNamedSet.pick(b: Bool, s: NftSet, rest: Maybe<&2, NftSet>) -> Maybe<&2, NftSet>:
  match b:
    case True{}:
      Some{s}
    case False{}:
      rest

# the set named n
def NftNamedSet.find(ss: List<&2, NftNamedSet>, +n: String) -> Maybe<&2, NftSet>:
  match ss:
    case Nil{}:
      None{}
    case Con{x, t}:
      match x:
        case NftNamedSet{name, s}:
          NftNamedSet.pick(String.eq(name, n), s, NftNamedSet.find(t, n))
