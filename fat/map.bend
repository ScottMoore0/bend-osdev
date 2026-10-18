# bend-osdev-fat, map.bend: the allocation table in memory, for writing.
#
# A FatMap holds the entry value of every cluster number of a volume (0 and
# 1, the reserved entries, then the clusters 2 to count - 1), in a balanced
# tree split by cluster number, so a read or a write of an entry walks one
# path: O(log n). It is pure Data: the writer (write.bend) keeps one in its
# state and writes the FAT sectors it changes back to the device, to every
# FAT copy.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000),
# section 4: an entry is 12 bits (FAT12), 16 bits (FAT16) or 28 bits (FAT32,
# the high 4 bits reserved: the map holds the low 28 and the writer keeps
# the stored high 4); 0 is a free cluster, a value from 2 to the last
# cluster the next cluster of a chain, the end-of-chain value its end.
#
# Allocation (FatMap.alloc, FatMap.extend) is first fit from a hint, the
# way FSInfo's FSI_Nxt_Free (section 5) asks: the search starts at the hint
# and wraps from the last cluster to cluster 2, visiting each cluster once.
# Each cluster found is marked as the end of a chain at once, so the next
# search cannot find it again; then the clusters are linked in the order
# found. Freeing (FatMap.free) writes 0 into each entry of a list.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T

# The tree: a node holds the count of cluster numbers on its left. A number
# the tree has no leaf for reads as 0.
type FatTree is Data:
  FatTEmpty{}
  FatTLeaf{value: U32}
  FatTNode{left_count: Nat, left: FatTree, right: FatTree}

def FatTree.left_count(t: FatTree) -> Nat:
  match t:
    case FatTNode{k, l, r}:
      k
    case FatTLeaf{v}:
      0n
    case FatTEmpty{}:
      0n

def FatTree.get.leaf(z: Bool, v: U32) -> U32:
  match z:
    case True{}:
      v
    case False{}:
      0

# entry n of t (z: whether n is left of t's split, computed by the caller)
def FatTree.get.at(t: FatTree, +n: Nat, z: Bool) -> U32:
  match t z:
    case FatTEmpty{} _:
      0
    case FatTLeaf{v} _:
      FatTree.get.leaf(Nat.is_eq(n, 0n), v)
    case FatTNode{k, +l, r} True{}:
      FatTree.get.at(l, n, Nat.is_lt(n, FatTree.left_count(l)))
    case FatTNode{+k, l, +r} False{}:
      +m = Nat.sub(n, k)
      FatTree.get.at(r, m, Nat.is_lt(m, FatTree.left_count(r)))

def FatTree.get(+t: FatTree, +n: Nat) -> U32:
  FatTree.get.at(t, n, Nat.is_lt(n, FatTree.left_count(t)))

def FatTree.set.leaf(+n: Nat, b: U32, v: U32) -> FatTree:
  match n:
    case 0n:
      FatTLeaf{v}
    case 1n+p:
      FatTNode{n, FatTLeaf{b}, FatTLeaf{v}}

# t with entry n set to v (a number t has no leaf for is added)
def FatTree.set.at(t: FatTree, +n: Nat, v: U32, z: Bool) -> FatTree:
  match t z:
    case FatTEmpty{} _:
      FatTNode{n, FatTEmpty{}, FatTLeaf{v}}
    case FatTLeaf{b} _:
      FatTree.set.leaf(n, b, v)
    case FatTNode{k, +l, r} True{}:
      FatTNode{k, FatTree.set.at(l, n, v, Nat.is_lt(n, FatTree.left_count(l))), r}
    case FatTNode{+k, l, +r} False{}:
      +m = Nat.sub(n, k)
      FatTNode{k, l, FatTree.set.at(r, m, v, Nat.is_lt(m, FatTree.left_count(r)))}

def FatTree.set(+t: FatTree, +n: Nat, v: U32) -> FatTree:
  FatTree.set.at(t, n, v, Nat.is_lt(n, FatTree.left_count(t)))

# Building a balanced tree from the entries in order

type FatTBuilt is Data:
  FatTBuilt{tree: FatTree, rest: List<&2, U32>}

def FatTree.build.fin(+h: Nat, l: FatTree, b: FatTBuilt) -> FatTBuilt:
  match b:
    case FatTBuilt{r, rest}:
      FatTBuilt{FatTNode{h, l, r}, rest}

def FatTree.build.node(+h: Nat, b: FatTBuilt, k: List<&2, U32> -> FatTBuilt) -> FatTBuilt:
  match b:
    case FatTBuilt{l, rest}:
      FatTree.build.fin(h, l, k(rest))

def FatTree.build.one(xs: List<&2, U32>) -> FatTBuilt:
  match xs:
    case Con{v, t}:
      FatTBuilt{FatTLeaf{v}, t}
    case Nil{}:
      FatTBuilt{FatTEmpty{}, Nil{}}

# the first n entries of xs as a tree (fuel: at least its depth), and the
# rest
def FatTree.build(+fuel: Nat, +n: Nat, xs: List<&2, U32>) -> FatTBuilt:
  match fuel:
    case 0n:
      FatTBuilt{FatTEmpty{}, xs}
    case 1n+f:
      match n:
        case 0n:
          FatTBuilt{FatTEmpty{}, xs}
        case 1n+p:
          match p:
            case 0n:
              FatTree.build.one(xs)
            case 1n+q:
              +h = Nat.div(n, 2n)
              FatTree.build.node(h, FatTree.build(f, h, xs), ys => FatTree.build(f, Nat.sub(n, h), ys))

def FatTree.of_list.fin(b: FatTBuilt) -> FatTree:
  match b:
    case FatTBuilt{t, rest}:
      t

# The map: the FAT type, the count of entries (the count of clusters + 2),
# and the tree

type FatMap is Data:
  FatMap{kind: P.FatType, count: Nat, tree: FatTree}

def FatMap.kind(m: FatMap) -> P.FatType:
  match m:
    case FatMap{t, c, tr}:
      t

def FatMap.count(m: FatMap) -> Nat:
  match m:
    case FatMap{t, c, tr}:
      c

# an entry value as the FAT type stores it: its low 12, 16 or 28 bits
def FatMap.mask(t: P.FatType, v: U32) -> U32:
  match t:
    case P.Fat12{}:
      U32.and(4095, v)
    case P.Fat16{}:
      U32.and(65535, v)
    case P.Fat32{}:
      U32.and(268435455, v)

# the map of the entries xs (in cluster order, from entry 0), each masked
def FatMap.of_list.mask(+t: P.FatType, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, r}:
      FatMap.of_list.mask(t, r, Con{FatMap.mask(t, h), acc})

def FatMap.rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, r}:
      FatMap.rev(r, Con{h, acc})

def FatMap.of_list(+t: P.FatType, +xs: List<&2, U32>) -> FatMap:
  +n = B.len.fast(xs)
  FatMap{t, n, FatTree.of_list.fin(FatTree.build(n, n, FatMap.rev(FatMap.of_list.mask(t, xs, Nil{}), Nil{})))}

# the entry of cluster n (0 for a number past the map)
def FatMap.get(m: FatMap, +n: Nat) -> U32:
  match m:
    case FatMap{t, c, +tr}:
      FatTree.get(tr, n)

# the map with the entry of cluster n set to v (masked to the FAT type)
def FatMap.set(m: FatMap, +n: Nat, v: U32) -> FatMap:
  match m:
    case FatMap{+t, c, +tr}:
      FatMap{t, c, FatTree.set(tr, n, FatMap.mask(t, v))}

# the entries of clusters 0 to n - 1, in order (onto acc)
def FatMap.entries.go(n: Nat, +m: FatMap, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+ +p:
      FatMap.entries.go(p, m, Con{FatMap.get(m, p), acc})

def FatMap.entries(+m: FatMap) -> List<&2, U32>:
  FatMap.entries.go(FatMap.count(m), m, Nil{})

# The end-of-chain value the writer stores
def FatMap.end(+m: FatMap) -> U32:
  FatMap.mask(FatMap.kind(m), T.FatEntry.end_value(FatMap.kind(m)))

# whether cluster n is a free cluster of the map: 2 <= n < count, entry 0
def FatMap.is_free(+m: FatMap, +n: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_le(2n, n), Nat.is_lt(n, FatMap.count(m))), U32.is_eq(FatMap.get(m, n), 0))

# the number of free clusters (a pass over the map)
def FatMap.free_count.go(n: Nat, +m: FatMap, +acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+ +p:
      FatMap.free_count.go(p, m, Nat.add(acc, U32.to_nat(Bool.to_u32(FatMap.is_free(m, p)))))

def FatMap.free_count(+m: FatMap) -> Nat:
  FatMap.free_count.go(FatMap.count(m), m, 0n)

# First fit from a hint

# c when it is a cluster of the map, else 2 (the search wraps there)
def FatMap.wrap.pick(ok: Bool, +c: Nat) -> Nat:
  match ok:
    case True{}:
      c
    case False{}:
      2n

def FatMap.wrap(+m: FatMap, +c: Nat) -> Nat:
  FatMap.wrap.pick(Bool.and(Nat.is_le(2n, c), Nat.is_lt(c, FatMap.count(m))), c)

# the first free cluster from c on (free: whether c is), in at most fuel
# more steps
def FatMap.find.go(fuel: Nat, +m: FatMap, +c: Nat, free: Bool) -> Maybe<&2, Nat>:
  match fuel free:
    case _ True{}:
      Some{c}
    case 0n False{}:
      None{}
    case 1n+f False{}:
      +c2 = FatMap.wrap(m, Nat.add(c, 1n))
      FatMap.find.go(f, m, c2, FatMap.is_free(m, c2))

# the first free cluster at or after hint, wrapping to cluster 2: every
# cluster is visited once
def FatMap.find(+m: FatMap, +hint: Nat) -> Maybe<&2, Nat>:
  +c = FatMap.wrap(m, hint)
  FatMap.find.go(Nat.sub(FatMap.count(m), 3n), m, c, FatMap.is_free(m, c))

# The result of an allocation: the map after it and the clusters it took,
# in chain order
type FatAlloc is Data:
  FatAlloc{map: FatMap, clusters: List<&2, Nat>}

def FatAlloc.map(a: FatAlloc) -> FatMap:
  match a:
    case FatAlloc{m, cs}:
      m

def FatAlloc.clusters(a: FatAlloc) -> List<&2, Nat>:
  match a:
    case FatAlloc{m, cs}:
      cs

def FatMap.rev_nat(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{h, r}:
      FatMap.rev_nat(r, Con{h, acc})

# the first phase: k free clusters, each marked as a chain's end when found
# (found: the search's answer for the next one; acc: those taken, latest
# first)
def FatMap.claim(k: Nat, +m: FatMap, found: Maybe<&2, Nat>, acc: List<&2, Nat>) -> Result<&2, &2, E.FatError, FatAlloc>:
  match k:
    case 0n:
      Done{FatAlloc{m, FatMap.rev_nat(acc, Nil{})}}
    case 1n+p:
      match found:
        case None{}:
          Fail{E.FatDiskFull{}}
        case Some{+c}:
          +m2 = FatMap.set(m, c, FatMap.end(m))
          FatMap.claim(p, m2, FatMap.find(m2, Nat.add(c, 1n)), Con{c, acc})

# the second phase: prev linked to the first of cs, each to the next
def FatMap.link(cs: List<&2, Nat>, m: FatMap, +prev: Nat) -> FatMap:
  match cs:
    case Nil{}:
      m
    case Con{+c, t}:
      FatMap.link(t, FatMap.set(m, prev, U32.from_nat(c)), c)

def FatMap.link.first(a: FatAlloc) -> FatAlloc:
  match a:
    case FatAlloc{m, Nil{}}:
      FatAlloc{m, Nil{}}
    case FatAlloc{m, Con{+c, +t}}:
      FatAlloc{FatMap.link(t, m, c), Con{c, t}}

def FatMap.link.after(+last: Nat, a: FatAlloc) -> FatAlloc:
  match a:
    case FatAlloc{m, +cs}:
      FatAlloc{FatMap.link(cs, m, last), cs}

# k free clusters, first fit from hint, linked as one new chain (FatDiskFull
# when fewer than k are free)
def FatMap.alloc(+m: FatMap, +hint: Nat, k: Nat) -> Result<&2, &2, E.FatError, FatAlloc>:
  Result.map(&2, &2, E.FatError, FatAlloc, FatAlloc, FatMap.link.first, FatMap.claim(k, m, FatMap.find(m, hint), Nil{}))

# k free clusters, first fit from hint, linked onto the chain that ends at
# cluster last
def FatMap.extend(+m: FatMap, +last: Nat, +hint: Nat, k: Nat) -> Result<&2, &2, E.FatError, FatAlloc>:
  Result.map(&2, &2, E.FatError, FatAlloc, FatAlloc, a => FatMap.link.after(last, a), FatMap.claim(k, m, FatMap.find(m, hint), Nil{}))

# every cluster of cs freed
def FatMap.free(cs: List<&2, Nat>, m: FatMap) -> FatMap:
  match cs:
    case Nil{}:
      m
    case Con{c, t}:
      FatMap.free(t, FatMap.set(m, c, 0))

# cluster c made the end of its chain
def FatMap.cut(m: FatMap, +c: Nat) -> FatMap:
  +m2 = m
  FatMap.set(m2, c, FatMap.end(m2))

# Following a chain in the map (the same checks as table.bend's walk)

def FatMap.link_of.check(ok: Bool, +n: U32) -> Result<&2, &2, E.FatError, T.FatLink>:
  match ok:
    case True{}:
      Done{T.FatLinkNext{n}}
    case False{}:
      Fail{E.FatBadCluster{n}}

def FatMap.link_of.go(e: T.FatEntry, +m: FatMap, +c: Nat) -> Result<&2, &2, E.FatError, T.FatLink>:
  match e:
    case T.FatFree{}:
      Fail{E.FatFreeInChain{U32.from_nat(c)}}
    case T.FatBad{}:
      Fail{E.FatBadInChain{U32.from_nat(c)}}
    case T.FatEnd{}:
      Done{T.FatLinkEnd{}}
    case T.FatNext{+n}:
      FatMap.link_of.check(Bool.and(U32.is_ge(n, 2), Nat.is_lt(U32.to_nat(n), FatMap.count(m))), n)

# where the chain goes after cluster c
def FatMap.link_of(+m: FatMap, +c: Nat) -> Result<&2, &2, E.FatError, T.FatLink>:
  FatMap.link_of.go(T.FatEntry.of(FatMap.kind(m), FatMap.get(m, c)), m, c)

def FatMap.chain.go(fuel: Nat, +m: FatMap, +c: Nat, l: Result<&2, &2, E.FatError, T.FatLink>, acc: List<&2, Nat>) -> Result<&2, &2, E.FatError, List<&2, Nat>>:
  match fuel:
    case 0n:
      Fail{E.FatChainLoop{}}
    case 1n+p:
      match l:
        case Fail{e}:
          Fail{e}
        case Done{T.FatLinkEnd{}}:
          Done{FatMap.rev_nat(Con{c, acc}, Nil{})}
        case Done{T.FatLinkNext{n}}:
          +k = U32.to_nat(n)
          FatMap.chain.go(p, m, k, FatMap.link_of(m, k), Con{c, acc})

def FatMap.chain.from(empty: Bool, ok: Bool, +m: FatMap, +start: Nat) -> Result<&2, &2, E.FatError, List<&2, Nat>>:
  match empty ok:
    case True{} _:
      Done{Nil{}}
    case False{} False{}:
      Fail{E.FatBadCluster{U32.from_nat(start)}}
    case False{} True{}:
      FatMap.chain.go(Nat.sub(FatMap.count(m), 2n), m, start, FatMap.link_of(m, start), Nil{})

# the clusters of the chain from start (none from cluster 0); a chain longer
# than the count of clusters is FatChainLoop
def FatMap.chain(+m: FatMap, +start: Nat) -> Result<&2, &2, E.FatError, List<&2, Nat>>:
  FatMap.chain.from(Nat.is_eq(start, 0n), Bool.and(Nat.is_le(2n, start), Nat.is_lt(start, FatMap.count(m))), m, start)

# Statements for the laws: what the allocation table must keep

def FatMap.member(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(x, h), FatMap.member(x, t))

# no cluster twice
def FatMap.distinct(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      +r = t
      Bool.and(Bool.not(FatMap.member(h, r)), FatMap.distinct(r))

# every cluster of cs free in m
def FatMap.all_free(+m: FatMap, cs: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, t}:
      Bool.and(FatMap.is_free(m, c), FatMap.all_free(m, t))

def FatMap.links.go(cs: List<&2, Nat>, +m: FatMap, +prev: Nat) -> Bool:
  match cs:
    case Nil{}:
      U32.is_eq(FatMap.get(m, prev), FatMap.end(m))
    case Con{+c, t}:
      Bool.and(U32.is_eq(FatMap.get(m, prev), FatMap.mask(FatMap.kind(m), U32.from_nat(c))), FatMap.links.go(t, m, c))

# whether cs is a chain in m: each cluster's entry the next cluster, the
# last's the end of the chain
def FatMap.links(+m: FatMap, cs: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      FatMap.links.go(t, m, c)
