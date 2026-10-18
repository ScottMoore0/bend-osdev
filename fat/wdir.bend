# bend-osdev-fat, wdir.bend: directories for writing, on blockdev's owned
# interface. Reading a directory with where each entry is and which are
# free, finding a name, choosing where a new entry's run of entries goes
# (growing a cluster-chain directory when it is full), and writing and
# erasing entries.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000),
# section 6: an entry whose first byte is 0xE5 is free; one whose first byte
# is 0x00 is free and so is every entry after it. Section 7: a long name's
# entries come just before its short entry, contiguous, so a new name needs
# a run of free entries one longer than its long-name entries (the run may
# cross from one cluster of the directory into the next). A directory holds
# at most 65536 entries; the FAT12/16 root directory cannot grow. Entries
# are erased by writing 0xE5 into their first byte.
#
# A directory is read through dir.bend's FatScan (so the writer sees exactly
# what the reader sees), fed a sector at a time; FatScan.spans gives each
# node's entries. The chain of a directory comes from the writer's map of
# the FAT (map.bend), not from the device.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T
import ./dirent.bend as R
import ./dir.bend as Q
import ./io.bend as I
import ./map.bend as A

# A directory as read for writing: which directory, whether it is the fixed
# FAT12/16 root, the clusters of its chain (none for the fixed root), the
# byte offsets of its sectors in order, its count of entries, the free
# entries before its end (0xE5, in order), the index of its end (the first
# 0x00 entry, or the count of entries), and its scan (dir.bend's FatScan: the
# nodes and where each one's entries are)
type FatDirView is Data:
  FatDirView{dir: Q.FatDir, fixed: Bool, clusters: List<&2, Nat>, sectors: List<&2, Nat>, slots: Nat, holes: List<&2, Nat>, end: Nat, scan: Q.FatScan}

def FatDirView.dir(v: FatDirView) -> Q.FatDir:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      d

def FatDirView.fixed(v: FatDirView) -> Bool:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      f

def FatDirView.clusters(v: FatDirView) -> List<&2, Nat>:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      cs

def FatDirView.sectors(v: FatDirView) -> List<&2, Nat>:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      ss

def FatDirView.slots(v: FatDirView) -> Nat:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      n

def FatDirView.holes(v: FatDirView) -> List<&2, Nat>:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      hs

def FatDirView.end(v: FatDirView) -> Nat:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      e

# the directory's nodes, in order (no ".", "..", or volume label)
def FatDirView.nodes(v: FatDirView) -> List<&2, Q.FatNode>:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      Q.FatScan.found(sc)

def FatDirView.spans(v: FatDirView) -> List<&2, Q.FatSpan>:
  match v:
    case FatDirView{d, f, cs, ss, n, hs, e, sc}:
      Q.FatScan.spans(sc)

def FatDirView.rev(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      FatDirView.rev(t, Con{h, acc})

def FatDirView.len(xs: List<&2, Nat>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      FatDirView.len(t, Nat.add(n, 1n))

# The sectors of a directory

# n sectors from byte offset at, a sector of bps bytes apart (onto acc,
# latest first)
def FatDirView.run(n: Nat, +at: Nat, +bps: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      FatDirView.run(p, Nat.add(at, bps), bps, Con{at, acc})

# the sectors of the clusters cs (onto acc, latest first)
def FatDirView.chain_sectors(cs: List<&2, Nat>, +vol: P.FatVolume, acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      +sec = P.FatVolume.sector(vol)
      FatDirView.chain_sectors(t, vol, FatDirView.run(Nat.div(P.FatVolume.cluster_bytes(vol), sec), P.FatVolume.cluster_offset(vol, U32.from_nat(c)), sec, acc))

# Reading: which entries of a sector are free, until the end

type FatDirFree is Data:
  FatDirFree{holes: List<&2, Nat>, end: Maybe<&2, Nat>}

def FatDirFree.end(f: FatDirFree) -> Maybe<&2, Nat>:
  match f:
    case FatDirFree{h, e}:
      e

def FatDirFree.first(zero: Bool, free: Bool, +i: Nat, hs: List<&2, Nat>) -> FatDirFree:
  match zero free:
    case True{} _:
      FatDirFree{hs, Some{i}}
    case False{} True{}:
      FatDirFree{Con{i, hs}, None{}}
    case False{} False{}:
      FatDirFree{hs, None{}}

def FatDirFree.step(+b: Maybe<&2, U32>, +i: Nat, f: FatDirFree) -> FatDirFree:
  match f:
    case FatDirFree{hs, None{}}:
      FatDirFree.first(P.Fat.byte_is(b, 0), P.Fat.byte_is(b, 229), i, hs)
    case FatDirFree{hs, Some{e}}:
      FatDirFree{hs, Some{e}}

# the first bytes of k entries (the bytes xs), entry i first
def FatDirFree.scan(k: Nat, xs: List<&2, U32>, +i: Nat, f: FatDirFree) -> FatDirFree:
  match k:
    case 0n:
      f
    case 1n+p:
      +ys = xs
      FatDirFree.scan(p, B.drop(32n, ys), Nat.add(i, 1n), FatDirFree.step(B.at(ys, 0n), i, f))

def FatDirFree.stopped(f: FatDirFree) -> Bool:
  Maybe.is_some(&2, Nat, FatDirFree.end(f))

# What a read of a directory found
type FatDirRead is Data:
  FatDirRead{free: FatDirFree, scan: Q.FatScan}

# the directory's sectors from ss on (left: entries of the directory left,
# i: the index of the first entry of this sector)
def FatDirView.load.go(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ss: List<&2, Nat>, stop: Bool, +per: Nat, +left: Nat, +i: Nat, +f: FatDirFree, +sc: Q.FatScan) -> I.FatRun<Dv, FatDirRead>:
  match ss stop:
    case Nil{} _:
      I.FatRun.pure(Dv, FatDirRead, FatDirRead{f, sc})
    case Con{at, t} True{}:
      I.FatRun.pure(Dv, FatDirRead, FatDirRead{f, sc})
    case Con{+at, t} False{}:
      +k = Nat.min(per, left)
      do I.FatRun<Dv, FatDirRead>:
        +o : B.Octets <- I.FatOIo.read(~Dv, ~block_size, ~read_block, at, Nat.mul(k, 32n))
        +f2 : FatDirFree = FatDirFree.scan(k, B.Octets.to_list(o), i, f)
        +sc2 : Q.FatScan <- I.FatRun.lift(Dv, Q.FatScan, Q.FatScan.feed(sc, o))
        FatDirView.load.go(~Dv, ~block_size, ~read_block, t, FatDirFree.stopped(f2), per, Nat.sub(left, k), Nat.add(i, k), f2, sc2)

def FatDirView.made(+d: Q.FatDir, +fixed: Bool, +cs: List<&2, Nat>, +ss: List<&2, Nat>, +slots: Nat, r: FatDirRead) -> FatDirView:
  match r:
    case FatDirRead{FatDirFree{hs, e}, sc}:
      FatDirView{d, fixed, cs, ss, slots, FatDirView.rev(hs, Nil{}), Maybe.default(&2, Nat, e, slots), sc}

def FatDirView.load.at(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +opts: P.FatOptions, +vol: P.FatVolume, +d: Q.FatDir, +fixed: Bool, +cs: List<&2, Nat>, +ss: List<&2, Nat>, +slots: Nat) -> I.FatRun<Dv, FatDirView>:
  do I.FatRun<Dv, FatDirView>:
    +r : FatDirRead <- FatDirView.load.go(~Dv, ~block_size, ~read_block, ss, False{}, Nat.div(P.FatVolume.sector(vol), 32n), slots, 0n, FatDirFree{Nil{}, None{}}, Q.FatScan.start(opts, Q.FatWantAll{}))
    return FatDirView.made(d, fixed, cs, ss, slots, r)

def FatDirView.load.chain(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +opts: P.FatOptions, +vol: P.FatVolume, +map: A.FatMap, +d: Q.FatDir, +c: Nat) -> I.FatRun<Dv, FatDirView>:
  do I.FatRun<Dv, FatDirView>:
    +cs : List<&2, Nat> <- I.FatRun.lift(Dv, List<&2, Nat>, A.FatMap.chain(map, c))
    +ss : List<&2, Nat> = FatDirView.rev(FatDirView.chain_sectors(cs, vol, Nil{}), Nil{})
    FatDirView.load.at(~Dv, ~block_size, ~read_block, opts, vol, d, False{}, cs, ss, Nat.mul(FatDirView.len(ss, 0n), Nat.div(P.FatVolume.sector(vol), 32n)))

def FatDirView.load.root(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, root: P.FatRoot, +opts: P.FatOptions, +vol: P.FatVolume, +map: A.FatMap) -> I.FatRun<Dv, FatDirView>:
  match root:
    case P.FatRootFixed{+start, +n}:
      +sec = P.FatVolume.sector(vol)
      FatDirView.load.at(~Dv, ~block_size, ~read_block, opts, vol, Q.FatDirRoot{}, True{}, Nil{}, FatDirView.rev(FatDirView.run(Nat.div(Nat.add(Nat.mul(n, 32n), Nat.sub(sec, 1n)), sec), start, sec, Nil{}), Nil{}), n)
    case P.FatRootChain{c}:
      FatDirView.load.chain(~Dv, ~block_size, ~read_block, opts, vol, map, Q.FatDirRoot{}, U32.to_nat(c))

# a directory read from the device (its chain from the map)
def FatDirView.load(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +opts: P.FatOptions, +vol: P.FatVolume, +map: A.FatMap, d: Q.FatDir) -> I.FatRun<Dv, FatDirView>:
  match d:
    case Q.FatDirRoot{}:
      FatDirView.load.root(~Dv, ~block_size, ~read_block, P.FatVolume.root(vol), opts, vol, map)
    case Q.FatDirAt{+c}:
      FatDirView.load.chain(~Dv, ~block_size, ~read_block, opts, vol, map, Q.FatDirAt{c}, U32.to_nat(c))

# Finding a name

# a node and where its entries are
type FatHit is Data:
  FatHit{node: Q.FatNode, span: Q.FatSpan}

def FatHit.node(h: FatHit) -> Q.FatNode:
  match h:
    case FatHit{n, s}:
      n

def FatHit.span(h: FatHit) -> Q.FatSpan:
  match h:
    case FatHit{n, s}:
      s

def FatDirView.find.pick(hit: Bool, n: Q.FatNode, s: Q.FatSpan, rest: Maybe<&2, FatHit>) -> Maybe<&2, FatHit>:
  match hit:
    case True{}:
      Some{FatHit{n, s}}
    case False{}:
      rest

def FatDirView.find.go(ns: List<&2, Q.FatNode>, ss: List<&2, Q.FatSpan>, +w: Q.FatWant) -> Maybe<&2, FatHit>:
  match ns ss:
    case Con{+n, nt} Con{+s, st}:
      FatDirView.find.pick(Q.FatWant.matches(w, n), n, s, FatDirView.find.go(nt, st, w))
    case _ _:
      None{}

# the first node a name names (long or 8.3, either case)
def FatDirView.find(+v: FatDirView, +name: String) -> Maybe<&2, FatHit>:
  FatDirView.find.go(FatDirView.nodes(v), FatDirView.spans(v), Q.FatWant.name(name))

# the short names of the directory's nodes
def FatDirView.taken.go(ns: List<&2, Q.FatNode>) -> List<&2, B.Octets>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{R.FatDirent.name(Q.FatNode.entry(n)), FatDirView.taken.go(t)}

def FatDirView.taken(+v: FatDirView) -> List<&2, B.Octets>:
  FatDirView.taken.go(FatDirView.nodes(v))

# Choosing where k new entries go: the first run of k free entries, where
# the free entries are the holes and every entry from the end on (past the
# directory's count of entries too: the directory grows to hold them)

def FatDirView.place.pick(c: Bool, a: Nat, b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

def FatDirView.place.found(hit: Bool, s: Nat, rest: Nat) -> Nat:
  match hit:
    case True{}:
      s
    case False{}:
      rest

def FatDirView.place.tail(join: Bool, start: Nat, len: Nat, end: Nat) -> Nat:
  match join:
    case True{}:
      FatDirView.place.pick(Nat.is_lt(0n, len), start, end)
    case False{}:
      end

def FatDirView.place.go(hs: List<&2, Nat>, +k: Nat, +end: Nat, +start: Nat, +len: Nat, +prev: Nat) -> Nat:
  match hs:
    case Nil{}:
      FatDirView.place.tail(Nat.is_eq(Nat.add(prev, 1n), end), start, len, end)
    case Con{+h, t}:
      +join = Bool.and(Nat.is_lt(0n, len), Nat.is_eq(Nat.add(prev, 1n), h))
      +s2 = FatDirView.place.pick(join, start, h)
      +l2 = Nat.add(FatDirView.place.pick(join, len, 0n), 1n)
      FatDirView.place.found(Nat.is_eq(l2, k), s2, FatDirView.place.go(t, k, end, s2, l2, h))

# the index of the first entry of a run of k free entries (k at least 1)
def FatDirView.place(+v: FatDirView, +k: Nat) -> Nat:
  FatDirView.place.go(FatDirView.holes(v), k, FatDirView.end(v), 0n, 0n, 0n)

# Writing entries

def FatDirView.nth(xs: List<&2, Nat>, n: Nat) -> Nat:
  match xs n:
    case Nil{} _:
      0n
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      FatDirView.nth(t, p)

# the byte offset of entry i of a directory with these sectors
def FatDirView.slot(ss: List<&2, Nat>, +per: Nat, +i: Nat) -> Nat:
  Nat.add(FatDirView.nth(ss, Nat.div(i, per)), Nat.mul(Nat.mod(i, per), 32n))

# the 32-byte entries es written from entry i on
def FatDirView.put(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, es: List<&2, B.Octets>, +ss: List<&2, Nat>, +per: Nat, +i: Nat) -> I.FatRun<Dv, Unit>:
  match es:
    case Nil{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case Con{e, t}:
      do I.FatRun<Dv, Unit>:
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, FatDirView.slot(ss, per, i), e)
        FatDirView.put(~Dv, ~block_size, ~read_block, ~write_block, t, ss, per, Nat.add(i, 1n))

# entries i to i + n - 1 erased (0xE5 in each first byte)
def FatDirView.erase(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, n: Nat, +ss: List<&2, Nat>, +per: Nat, +i: Nat) -> I.FatRun<Dv, Unit>:
  match n:
    case 0n:
      I.FatRun.pure(Dv, Unit, Unit{})
    case 1n+p:
      do I.FatRun<Dv, Unit>:
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, FatDirView.slot(ss, per, i), B.Octets.of_list([229]))
        FatDirView.erase(~Dv, ~block_size, ~read_block, ~write_block, p, ss, per, Nat.add(i, 1n))
