# bend-osdev-fat, dir.bend: directories. Scanning a directory's entries
# (streaming: a piece of directory data at a time), assembling long names,
# listing, finding a name, and resolving a path.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000),
# sections 6 and 7. The root directory of FAT12/16 is a fixed region after
# the FATs; every other directory, and the FAT32 root, is a cluster chain. A
# directory ends at its first entry whose first byte is 0x00, or at the end of
# its region or chain; it holds at most 65536 entries.
#
# Long names: the entries of a long name come just before its short entry,
# the one with ordinal 0x40 | n first, then n - 1 down to 1, all carrying the
# short name's checksum. A run out of sequence, or whose checksum does not
# match, is refused (FatLfnBadSequence, FatLfnBadChecksum) under the default
# options, or ignored (the short name used alone, as the specification's
# orphan handling) under FatOptions.lenient().
#
# Names compare ignoring the case of ASCII letters: a short name against a
# path component's 8.3 form (FatName.short_of), a long name against the
# component's code units. Listings leave out free entries, the volume label,
# and the "." and ".." entries.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T
import ./dirent.bend as R

# A directory entry as read: its long name (no units when it has none) and
# its short entry
type FatNode is Data:
  FatNode{long: List<&2, U32>, entry: R.FatDirent}

def FatNode.long(n: FatNode) -> List<&2, U32>:
  match n:
    case FatNode{l, e}:
      l

def FatNode.entry(n: FatNode) -> R.FatDirent:
  match n:
    case FatNode{l, e}:
      e

# the short name as text, with Windows NT's case flags applied
def FatNode.short_name(n: FatNode) -> String:
  match n:
    case FatNode{l, e}:
      R.FatDirent.short_text(e)

def FatNode.name.pick(+l: List<&2, U32>, e: R.FatDirent) -> String:
  match l:
    case Nil{}:
      R.FatDirent.short_text(e)
    case Con{h, t}:
      R.FatName.text_of(l)

# the long name if there is one, else the short name ("BOOTX64.EFI")
def FatNode.name(n: FatNode) -> String:
  match n:
    case FatNode{l, e}:
      FatNode.name.pick(l, e)

def FatNode.is_dir(n: FatNode) -> Bool:
  R.FatDirent.is_dir(FatNode.entry(n))

def FatNode.size(n: FatNode) -> U32:
  R.FatDirent.size(FatNode.entry(n))

def FatNode.cluster(n: FatNode) -> U32:
  R.FatDirent.cluster(FatNode.entry(n))

# A directory: the root, or the one whose chain starts at a cluster
type FatDir is Data:
  FatDirRoot{}
  FatDirAt{cluster: U32}

def FatDir.of_cluster.pick(root: Bool, +c: U32) -> FatDir:
  match root:
    case True{}:
      FatDirRoot{}
    case False{}:
      FatDirAt{c}

# the directory a node is (a ".." entry of a directory in the root holds
# cluster 0)
def FatDir.of_node(n: FatNode) -> FatDir:
  +c = FatNode.cluster(n)
  FatDir.of_cluster.pick(U32.is_eq(c, 0), c)

# What a scan looks for: every entry, or the first named by a path component
# (its code units and its 8.3 form, if it has one)
type FatWant is Data:
  FatWantAll{}
  FatWantName{units: List<&2, U32>, short: Maybe<&2, B.Octets>}

def FatWant.name(+s: String) -> FatWant:
  FatWantName{R.FatName.units(s), R.FatName.short_of(s)}

# A long name being read: the ordinal expected next (0 once complete), its
# checksum, and its units so far
type FatRun is Data:
  FatRunNone{}
  FatRunSome{next: U32, chk: U32, units: List<&2, U32>}

# The state of a scan: whether to refuse bad long names, what it looks for,
# the long name being read, the nodes found (latest first), whether the
# directory (or the search) has ended, and the entries seen
type FatScan is Data:
  FatScan{strict: Bool, want: FatWant, run: FatRun, found: List<&2, FatNode>, ended: Bool, seen: Nat}

def FatScan.start(opts: P.FatOptions, want: FatWant) -> FatScan:
  match opts:
    case P.FatOptions{m, strict}:
      FatScan{strict, want, FatRunNone{}, Nil{}, False{}, 0n}

def FatScan.ended(s: FatScan) -> Bool:
  match s:
    case FatScan{st, w, r, f, e, n}:
      e

def FatScan.reverse(xs: List<&2, FatNode>, acc: List<&2, FatNode>) -> List<&2, FatNode>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      FatScan.reverse(t, Con{h, acc})

# the nodes found, in directory order
def FatScan.found(s: FatScan) -> List<&2, FatNode>:
  match s:
    case FatScan{st, w, r, f, e, n}:
      FatScan.reverse(f, Nil{})

def FatScan.stopped(r: Result<&2, &2, E.FatError, FatScan>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{s}:
      FatScan.ended(s)

# a bad long name: refused when strict, else dropped (the scan goes on with s)
def FatScan.bad(strict: Bool, e: E.FatError, s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  match strict:
    case True{}:
      Fail{e}
    case False{}:
      Done{s}

def FatScan.with_run(s: FatScan, run: FatRun) -> FatScan:
  match s:
    case FatScan{st, w, r, f, e, n}:
      FatScan{st, w, run, f, e, n}

def FatScan.strict(s: FatScan) -> Bool:
  match s:
    case FatScan{st, w, r, f, e, n}:
      st

def FatScan.run(s: FatScan) -> FatRun:
  match s:
    case FatScan{st, w, r, f, e, n}:
      r

# Long-name entries

def FatScan.lfn.first(ok: Bool, +s: FatScan, +n: U32, +chk: U32, units: List<&2, U32>) -> Result<&2, &2, E.FatError, FatScan>:
  match ok:
    case True{}:
      Done{FatScan.with_run(s, FatRunSome{U32.sub(n, 1), chk, units})}
    case False{}:
      FatScan.bad(FatScan.strict(s), E.FatLfnBadSequence{}, FatScan.with_run(s, FatRunNone{}))

def FatScan.lfn.more(inseq: Bool, same: Bool, +s: FatScan, +next: U32, +chk: U32, units: List<&2, U32>, have: List<&2, U32>) -> Result<&2, &2, E.FatError, FatScan>:
  match inseq same:
    case True{} True{}:
      Done{FatScan.with_run(s, FatRunSome{U32.sub(next, 1), chk, B.append(units, have)})}
    case True{} False{}:
      FatScan.bad(FatScan.strict(s), E.FatLfnBadChecksum{}, FatScan.with_run(s, FatRunNone{}))
    case False{} _:
      FatScan.bad(FatScan.strict(s), E.FatLfnBadSequence{}, FatScan.with_run(s, FatRunNone{}))

# a long-name entry starts a run (ordinal 0x40 | n) or continues the one
# being read (ordinal next, the same checksum)
def FatScan.lfn.go(last: Bool, run: FatRun, +s: FatScan, +ord: U32, +chk: U32, units: List<&2, U32>) -> Result<&2, &2, E.FatError, FatScan>:
  match last run:
    case True{} FatRunNone{}:
      +n = U32.and(63, ord)
      FatScan.lfn.first(Bool.and(U32.is_ge(n, 1), U32.is_le(n, 20)), s, n, chk, units)
    case True{} FatRunSome{x, c, us}:
      FatScan.bad(FatScan.strict(s), E.FatLfnBadSequence{}, FatScan.with_run(s, FatRunNone{}))
    case False{} FatRunNone{}:
      FatScan.bad(FatScan.strict(s), E.FatLfnBadSequence{}, s)
    case False{} FatRunSome{+next, +c, us}:
      FatScan.lfn.more(Bool.and(U32.is_eq(ord, next), Bool.not(U32.is_eq(next, 0))), U32.is_eq(chk, c), s, next, c, units, us)

def FatScan.lfn(+s: FatScan, e: R.FatLfn) -> Result<&2, &2, E.FatError, FatScan>:
  match e:
    case R.FatLfn{+ord, units, chk}:
      FatScan.lfn.go(Bool.not(U32.is_eq(U32.and(64, ord), 0)), FatScan.run(s), s, ord, chk, units)

# Short entries

def FatWant.match_short(m: Maybe<&2, B.Octets>, name: B.Octets) -> Bool:
  match m:
    case Some{sb}:
      R.FatName.same(B.Octets.to_list(sb), B.Octets.to_list(name))
    case None{}:
      False{}

def FatWant.match_long(+want: List<&2, U32>, long: List<&2, U32>) -> Bool:
  match long:
    case Nil{}:
      False{}
    case Con{h, t}:
      R.FatName.same(want, long)

def FatWant.matches(w: FatWant, n: FatNode) -> Bool:
  match w n:
    case FatWantAll{} _:
      True{}
    case FatWantName{us, sh} FatNode{l, e}:
      Bool.or(FatWant.match_long(us, l), FatWant.match_short(sh, R.FatDirent.name(e)))

def FatWant.is_all(w: FatWant) -> Bool:
  match w:
    case FatWantAll{}:
      True{}
    case FatWantName{us, sh}:
      False{}

def FatScan.keep.add(hit: Bool, +all: Bool, n: FatNode, found: List<&2, FatNode>) -> List<&2, FatNode>:
  match hit:
    case True{}:
      Con{n, found}
    case False{}:
      found

# a node joins the found list if it is wanted; a search ends at its first hit
def FatScan.keep(listed: Bool, +s: FatScan, +n: FatNode) -> FatScan:
  match listed s:
    case False{} _:
      FatScan.with_run(s, FatRunNone{})
    case True{} FatScan{st, +w, r, f, e, c}:
      +hit = FatWant.matches(w, n)
      FatScan{st, w, FatRunNone{}, FatScan.keep.add(hit, FatWant.is_all(w), n, f), Bool.and(hit, Bool.not(FatWant.is_all(w))), c}

# whether a short entry is listed: not the volume label, not "." or ".."
def FatScan.listed(+d: R.FatDirent) -> Bool:
  Bool.and(Bool.not(Bool.and(R.FatDirent.is_volume_label(d), Bool.not(R.FatDirent.is_dir(d)))), Bool.not(P.Fat.byte_is(B.Octets.at(R.FatDirent.name(d), 0n), 46)))

def FatScan.short.named(ok: Bool, +s: FatScan, +units: List<&2, U32>, +d: R.FatDirent) -> Result<&2, &2, E.FatError, FatScan>:
  match ok:
    case True{}:
      Done{FatScan.keep(FatScan.listed(d), s, FatNode{R.FatLfn.cut(units), d})}
    case False{}:
      FatScan.bad(FatScan.strict(s), E.FatLfnBadChecksum{}, FatScan.keep(FatScan.listed(d), s, FatNode{Nil{}, d}))

def FatScan.short.complete(done: Bool, +s: FatScan, +c: U32, +us: List<&2, U32>, +d: R.FatDirent) -> Result<&2, &2, E.FatError, FatScan>:
  match done:
    case True{}:
      FatScan.short.named(U32.is_eq(R.FatLfn.checksum(R.FatDirent.name(d)), c), s, us, d)
    case False{}:
      FatScan.bad(FatScan.strict(s), E.FatLfnBadSequence{}, FatScan.keep(FatScan.listed(d), s, FatNode{Nil{}, d}))

def FatScan.short.go(run: FatRun, +s: FatScan, +d: R.FatDirent) -> Result<&2, &2, E.FatError, FatScan>:
  match run:
    case FatRunNone{}:
      Done{FatScan.keep(FatScan.listed(d), s, FatNode{Nil{}, d})}
    case FatRunSome{+next, +c, us}:
      FatScan.short.complete(U32.is_eq(next, 0), s, c, us, d)

# One 32-byte entry

type FatKind is Data:
  FatKindEnd{}
  FatKindFree{}
  FatKindLong{}
  FatKindShort{}

def FatKind.pick(end: Bool, free: Bool, long: Bool) -> FatKind:
  match end free long:
    case True{} _ _:
      FatKindEnd{}
    case False{} True{} _:
      FatKindFree{}
    case False{} False{} True{}:
      FatKindLong{}
    case False{} False{} False{}:
      FatKindShort{}

def FatKind.of(+xs: List<&2, U32>) -> FatKind:
  FatKind.pick(Bool.not(Maybe.is_some(&2, U32, B.at(xs, 31n))) || P.Fat.byte_is(B.at(xs, 0n), 0), P.Fat.byte_is(B.at(xs, 0n), 229), R.FatLfn.is_long.list(xs))

def FatScan.end(+s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  match s:
    case FatScan{st, w, FatRunNone{}, f, e, n}:
      Done{FatScan{st, w, FatRunNone{}, f, True{}, n}}
    case FatScan{st, w, FatRunSome{x, c, us}, f, e, n}:
      FatScan.bad(st, E.FatLfnBadSequence{}, FatScan{st, w, FatRunNone{}, f, True{}, n})

def FatScan.free.go(run: FatRun, +s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  match run:
    case FatRunNone{}:
      Done{s}
    case FatRunSome{x, c, us}:
      FatScan.bad(FatScan.strict(s), E.FatLfnBadSequence{}, FatScan.with_run(s, FatRunNone{}))

# a free entry: a long name before it is an orphan
def FatScan.free(+s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  FatScan.free.go(FatScan.run(s), s)

def FatScan.counted(ok: Bool, +s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  match ok s:
    case True{} FatScan{st, w, r, f, e, +n}:
      Done{FatScan{st, w, r, f, e, Nat.add(n, 1n)}}
    case False{} _:
      Fail{E.FatDirTooLong{}}

def FatScan.seen(s: FatScan) -> Nat:
  match s:
    case FatScan{st, w, r, f, e, n}:
      n

def FatScan.step.go(k: FatKind, +s: FatScan, +o: B.Octets) -> Result<&2, &2, E.FatError, FatScan>:
  match k:
    case FatKindEnd{}:
      FatScan.end(s)
    case FatKindFree{}:
      FatScan.free(s)
    case FatKindLong{}:
      do Result<&2, &2, E.FatError, FatScan>:
        e : R.FatLfn <- R.FatLfn.decode(o)
        FatScan.lfn(s, e)
    case FatKindShort{}:
      do Result<&2, &2, E.FatError, FatScan>:
        d : R.FatDirent <- R.FatDirent.decode(o)
        FatScan.short.go(FatScan.run(s), s, d)

def FatScan.step.live(ended: Bool, +s: FatScan, +o: B.Octets) -> Result<&2, &2, E.FatError, FatScan>:
  match ended:
    case True{}:
      Done{s}
    case False{}:
      do Result<&2, &2, E.FatError, FatScan>:
        c : FatScan <- FatScan.counted(Nat.is_lt(FatScan.seen(s), 65536n), s)
        FatScan.step.go(FatKind.of(B.Octets.to_list(o)), c, o)

# the scan after one 32-byte entry (an ended scan is unchanged)
def FatScan.step(+s: FatScan, +o: B.Octets) -> Result<&2, &2, E.FatError, FatScan>:
  FatScan.step.live(FatScan.ended(s), s, o)

def FatScan.feed.go(n: Nat, +o: B.Octets, r: Result<&2, &2, E.FatError, FatScan>) -> Result<&2, &2, E.FatError, FatScan>:
  match n:
    case 0n:
      r
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{+s}:
          FatScan.feed.go(p, B.Octets.drop(32n, o), FatScan.step(s, B.Octets.take(32n, o)))

# the scan after a piece of directory data (whole 32-byte entries; any
# bytes after the last whole entry are ignored)
def FatScan.feed(s: FatScan, +o: B.Octets) -> Result<&2, &2, E.FatError, FatScan>:
  FatScan.feed.go(Nat.div(B.Octets.len(o), 32n), o, Done{s})

# Reading directories from the device, a sector at a time

def FatScan.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, off: Nat, +len: Nat, s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  do Result<&2, &2, E.FatError, FatScan>:
    o : B.Octets <- T.FatIo.read(~Dv, ~block_size, ~read_block, d, off, len)
    FatScan.feed(s, o)

def FatScan.region.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, n: Nat, +off: Nat, +left: Nat, +sec: Nat, stop: Bool, r: Result<&2, &2, E.FatError, FatScan>) -> Result<&2, &2, E.FatError, FatScan>:
  match n:
    case 0n:
      r
    case 1n+p:
      match stop:
        case True{}:
          r
        case False{}:
          match r:
            case Fail{e}:
              Fail{e}
            case Done{s}:
              +len = Nat.min(sec, left)
              +r2 = FatScan.read(~Dv, ~block_size, ~read_block, d, off, len, s)
              FatScan.region.go(~Dv, ~block_size, ~read_block, d, p, Nat.add(off, len), Nat.sub(left, len), sec, FatScan.stopped(r2), r2)

# the scan after the len bytes of directory data at off (until it ends)
def FatScan.region(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, +off: Nat, +len: Nat, s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  +sec = P.FatVolume.sector(vol)
  FatScan.region.go(~Dv, ~block_size, ~read_block, d, Nat.div(Nat.add(len, Nat.sub(sec, 1n)), sec), off, len, sec, False{}, Done{s})

def FatScan.chain.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, fuel: Nat, stop: Bool, r: Result<&2, &2, E.FatError, FatScan>, l: Result<&2, &2, E.FatError, T.FatLink>) -> Result<&2, &2, E.FatError, FatScan>:
  match fuel:
    case 0n:
      match stop:
        case True{}:
          r
        case False{}:
          Fail{E.FatChainLoop{}}
    case 1n+p:
      match stop:
        case True{}:
          r
        case False{}:
          match r:
            case Fail{e}:
              Fail{e}
            case Done{s}:
              match l:
                case Fail{e}:
                  Fail{e}
                case Done{T.FatLinkEnd{}}:
                  Done{s}
                case Done{T.FatLinkNext{+c}}:
                  +r2 = FatScan.region(~Dv, ~block_size, ~read_block, d, vol, P.FatVolume.cluster_offset(vol, c), P.FatVolume.cluster_bytes(vol), s)
                  FatScan.chain.go(~Dv, ~block_size, ~read_block, d, vol, p, FatScan.stopped(r2), r2, T.FatChain.next(~Dv, ~block_size, ~read_block, d, vol, c))

def FatScan.chain.first(ok: Bool, +c: U32) -> Result<&2, &2, E.FatError, T.FatLink>:
  match ok:
    case True{}:
      Done{T.FatLinkNext{c}}
    case False{}:
      Fail{E.FatBadCluster{c}}

# the scan after a directory that is a cluster chain from c (at most the
# volume's count of clusters, a sector at a time)
def FatScan.chain(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, +c: U32, s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  FatScan.chain.go(~Dv, ~block_size, ~read_block, d, vol, Nat.add(U32.to_nat(P.FatVolume.clusters(vol)), 1n), False{}, Done{s}, FatScan.chain.first(P.FatVolume.valid_cluster(vol, c), c))

def FatDir.scan.root(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, root: P.FatRoot, +d: Dv, +vol: P.FatVolume, s: FatScan) -> Result<&2, &2, E.FatError, FatScan>:
  match root:
    case P.FatRootFixed{start, entries}:
      FatScan.region(~Dv, ~block_size, ~read_block, d, vol, start, Nat.mul(entries, 32n), s)
    case P.FatRootChain{c}:
      FatScan.chain(~Dv, ~block_size, ~read_block, d, vol, c, s)

# a directory's scan, from the start
def FatDir.scan(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, opts: P.FatOptions, +vol: P.FatVolume, dir: FatDir, want: FatWant) -> Result<&2, &2, E.FatError, FatScan>:
  match dir:
    case FatDirRoot{}:
      FatDir.scan.root(~Dv, ~block_size, ~read_block, P.FatVolume.root(vol), d, vol, FatScan.start(opts, want))
    case FatDirAt{c}:
      FatScan.chain(~Dv, ~block_size, ~read_block, d, vol, c, FatScan.start(opts, want))

# the entries of a directory, in order
def FatDir.list(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, opts: P.FatOptions, +vol: P.FatVolume, dir: FatDir) -> Result<&2, &2, E.FatError, List<&2, FatNode>>:
  do Result<&2, &2, E.FatError, List<&2, FatNode>>:
    s : FatScan <- FatDir.scan(~Dv, ~block_size, ~read_block, d, opts, vol, dir, FatWantAll{})
    return FatScan.found(s)

def FatDir.first(xs: List<&2, FatNode>) -> Maybe<&2, FatNode>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{h}

# the entry of a directory a name (long or 8.3, either case) names; the scan
# stops there
def FatDir.find(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, opts: P.FatOptions, +vol: P.FatVolume, dir: FatDir, name: String) -> Result<&2, &2, E.FatError, Maybe<&2, FatNode>>:
  do Result<&2, &2, E.FatError, Maybe<&2, FatNode>>:
    s : FatScan <- FatDir.scan(~Dv, ~block_size, ~read_block, d, opts, vol, dir, FatWant.name(name))
    return FatDir.first(FatScan.found(s))

# Paths

# where a path leads: the root directory, or an entry
type FatPath is Data:
  FatPathRoot{}
  FatPathNode{node: FatNode}

def FatPath.parts.keep(empty: Bool, s: String, rest: List<&2, String>) -> List<&2, String>:
  match empty:
    case True{}:
      rest
    case False{}:
      Con{s, rest}

def FatPath.parts.go(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      FatPath.parts.keep(String.is_empty(s), s, FatPath.parts.go(t))

# the components of a path ("/EFI/BOOT/BOOTX64.EFI": "EFI", "BOOT",
# "BOOTX64.EFI"; empty components are ignored)
def FatPath.parts(s: String) -> List<&2, String>:
  FatPath.parts.go(String.split(s, '/'))

def FatPath.dir.check(ok: Bool, +n: FatNode) -> Result<&2, &2, E.FatError, FatDir>:
  match ok:
    case True{}:
      Done{FatDir.of_node(n)}
    case False{}:
      Fail{E.FatNotADirectory{}}

# the directory a path names
def FatPath.dir(p: FatPath) -> Result<&2, &2, E.FatError, FatDir>:
  match p:
    case FatPathRoot{}:
      Done{FatDirRoot{}}
    case FatPathNode{+n}:
      FatPath.dir.check(FatNode.is_dir(n), n)

def FatPath.found(m: Maybe<&2, FatNode>) -> Result<&2, &2, E.FatError, FatPath>:
  match m:
    case Some{n}:
      Done{FatPathNode{n}}
    case None{}:
      Fail{E.FatNotFound{}}

def FatPath.step(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +opts: P.FatOptions, +vol: P.FatVolume, here: FatPath, name: String) -> Result<&2, &2, E.FatError, FatPath>:
  do Result<&2, &2, E.FatError, FatPath>:
    dir : FatDir <- FatPath.dir(here)
    m : Maybe<&2, FatNode> <- FatDir.find(~Dv, ~block_size, ~read_block, d, opts, vol, dir, name)
    FatPath.found(m)

def FatPath.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +opts: P.FatOptions, +vol: P.FatVolume, parts: List<&2, String>, r: Result<&2, &2, E.FatError, FatPath>) -> Result<&2, &2, E.FatError, FatPath>:
  match parts:
    case Nil{}:
      r
    case Con{c, t}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{h}:
          FatPath.go(~Dv, ~block_size, ~read_block, d, opts, vol, t, FatPath.step(~Dv, ~block_size, ~read_block, d, opts, vol, h, c))

# where a path leads ("/" and "" are the root), reading only the directories
# on the way (FatNotFound; FatNotADirectory when a component before the last
# is a file)
def FatPath.resolve(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +opts: P.FatOptions, +vol: P.FatVolume, path: String) -> Result<&2, &2, E.FatError, FatPath>:
  FatPath.go(~Dv, ~block_size, ~read_block, d, opts, vol, FatPath.parts(path), Done{FatPathRoot{}})
