# bend-osdev-fat, file.bend: reading a file's bytes, a sector at a time
# (streaming, through a cursor) or as a range. Never more than the file's
# size (DIR_FileSize): the clusters after it are not read.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000),
# sections 3.5 (the first sector of cluster N is FirstDataSector +
# (N - 2) * BPB_SecPerClus), 4 (cluster chains) and 6 (DIR_FileSize). A file
# of size 0 has first cluster 0. A chain that ends before the file's size is
# refused (FatChainShort); a chain that runs on is not read past the size.
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

# Where a read stands: the cluster, the sector within it, the bytes left to
# read (from the start of that sector), and how many more clusters the chain
# may enter before it is taken to loop
type FatCursor is Data:
  FatCursor{cluster: U32, sector: Nat, left: Nat, fuel: Nat}

# One piece of a file, and the cursor after it (None at the end)
type FatChunk is Data:
  FatChunk{data: B.Octets, rest: Maybe<&2, FatCursor>}

def FatChunk.data(c: FatChunk) -> B.Octets:
  match c:
    case FatChunk{d, r}:
      d

def FatChunk.rest(c: FatChunk) -> Maybe<&2, FatCursor>:
  match c:
    case FatChunk{d, r}:
      r

def FatFile.open.go(dir: Bool, empty: Bool, ok: Bool, +vol: P.FatVolume, +c: U32, +size: Nat) -> Result<&2, &2, E.FatError, FatCursor>:
  match dir empty ok:
    case True{} _ _:
      Fail{E.FatIsADirectory{}}
    case False{} True{} _:
      Done{FatCursor{c, 0n, 0n, 0n}}
    case False{} False{} True{}:
      Done{FatCursor{c, 0n, size, U32.to_nat(P.FatVolume.clusters(vol))}}
    case False{} False{} False{}:
      Fail{E.FatBadCluster{c}}

# a cursor at the start of a file (FatIsADirectory for a directory)
def FatFile.open(+vol: P.FatVolume, +n: Q.FatNode) -> Result<&2, &2, E.FatError, FatCursor>:
  +c = Q.FatNode.cluster(n)
  +size = U32.to_nat(Q.FatNode.size(n))
  FatFile.open.go(Q.FatNode.is_dir(n), Nat.is_eq(size, 0n), P.FatVolume.valid_cluster(vol, c), vol, c, size)

def FatFile.next.link(+data: B.Octets, +left: Nat, +fuel: Nat, l: T.FatLink) -> Result<&2, &2, E.FatError, FatChunk>:
  match l:
    case T.FatLinkEnd{}:
      Fail{E.FatChainShort{}}
    case T.FatLinkNext{n}:
      Done{FatChunk{data, Some{FatCursor{n, 0n, left, fuel}}}}

def FatFile.next.after(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, last: Bool, inside: Bool, +d: Dv, +vol: P.FatVolume, +c: U32, +sector: Nat, +left: Nat, fuel: Nat, +data: B.Octets) -> Result<&2, &2, E.FatError, FatChunk>:
  match last inside:
    case True{} _:
      Done{FatChunk{data, None{}}}
    case False{} True{}:
      Done{FatChunk{data, Some{FatCursor{c, Nat.add(sector, 1n), left, fuel}}}}
    case False{} False{}:
      match fuel:
        case 0n:
          Fail{E.FatChainLoop{}}
        case 1n+p:
          do Result<&2, &2, E.FatError, FatChunk>:
            l : T.FatLink <- T.FatChain.next(~Dv, ~block_size, ~read_block, d, vol, c)
            FatFile.next.link(data, left, p, l)

# the next piece of a file (one sector, or what is left of the file) and the
# cursor after it
def FatFile.next(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, cur: FatCursor) -> Result<&2, &2, E.FatError, FatChunk>:
  match cur:
    case FatCursor{+c, +sector, +left, +fuel}:
      +sec = P.FatVolume.sector(vol)
      +len = Nat.min(sec, left)
      do Result<&2, &2, E.FatError, FatChunk>:
        data : B.Octets <- T.FatIo.read(~Dv, ~block_size, ~read_block, d, Nat.add(P.FatVolume.cluster_offset(vol, c), Nat.mul(sector, sec)), len)
        FatFile.next.after(~Dv, ~block_size, ~read_block, Nat.is_eq(left, len), Nat.is_lt(Nat.mul(Nat.add(sector, 1n), sec), P.FatVolume.cluster_bytes(vol)), d, vol, c, sector, Nat.sub(left, len), fuel, data)

# Ranges

def FatFile.skip.to(l: T.FatLink) -> Result<&2, &2, E.FatError, U32>:
  match l:
    case T.FatLinkEnd{}:
      Fail{E.FatChainShort{}}
    case T.FatLinkNext{n}:
      Done{n}

# the cluster k links along the chain from the one r holds
def FatFile.skip(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, k: Nat, r: Result<&2, &2, E.FatError, U32>) -> Result<&2, &2, E.FatError, U32>:
  match k:
    case 0n:
      r
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{+c}:
          FatFile.skip(~Dv, ~block_size, ~read_block, d, vol, p, Result.bind(&2, &2, E.FatError, T.FatLink, U32, T.FatChain.next(~Dv, ~block_size, ~read_block, d, vol, c), FatFile.skip.to))

def FatFile.reverse(xs: List<&2, B.Octets>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      FatFile.reverse(t, Con{h, acc})

# the pieces from the chunk r on, until the end
def FatFile.collect(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, fuel: Nat, r: Result<&2, &2, E.FatError, FatChunk>, acc: List<&2, B.Octets>) -> Result<&2, &2, E.FatError, List<&2, B.Octets>>:
  match fuel:
    case 0n:
      Fail{E.FatChainLoop{}}
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{FatChunk{data, None{}}}:
          Done{FatFile.reverse(Con{data, acc}, Nil{})}
        case Done{FatChunk{data, Some{cur}}}:
          FatFile.collect(~Dv, ~block_size, ~read_block, d, vol, p, FatFile.next(~Dv, ~block_size, ~read_block, d, vol, cur), Con{data, acc})

def FatFile.read.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, none: Bool, +d: Dv, +vol: P.FatVolume, +first: U32, +start: Nat, +n: Nat) -> Result<&2, &2, E.FatError, B.Octets>:
  match none:
    case True{}:
      Done{B.Octets.empty()}
    case False{}:
      +sec = P.FatVolume.sector(vol)
      +clu = P.FatVolume.cluster_bytes(vol)
      +within = Nat.mod(start, clu)
      +skip = Nat.mod(within, sec)
      +left = Nat.add(n, skip)
      do Result<&2, &2, E.FatError, B.Octets>:
        c : U32 <- FatFile.skip(~Dv, ~block_size, ~read_block, d, vol, Nat.div(start, clu), Done{first})
        pieces : List<&2, B.Octets> <- FatFile.collect(~Dv, ~block_size, ~read_block, d, vol, Nat.add(Nat.div(left, sec), 2n), FatFile.next(~Dv, ~block_size, ~read_block, d, vol, FatCursor{c, Nat.div(within, sec), left, U32.to_nat(P.FatVolume.clusters(vol))}), Nil{})
        return B.Octets.drop(skip, B.Octets.concat(pieces))

# the bytes of a file from offset off, at most len of them and never past its
# size (fewer, or none, near or past the end). The result is one Octets, so
# its length is bounded by memory (see README.md, Speed and size limits);
# read a large file a piece at a time with FatFile.open and FatFile.next.
def FatFile.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, +node: Q.FatNode, +off: Nat, +len: Nat) -> Result<&2, &2, E.FatError, B.Octets>:
  +size = U32.to_nat(Q.FatNode.size(node))
  +start = Nat.min(off, size)
  +n = Nat.min(len, Nat.sub(size, start))
  do Result<&2, &2, E.FatError, B.Octets>:
    cur : FatCursor <- FatFile.open(vol, node)
    FatFile.read.go(~Dv, ~block_size, ~read_block, Nat.is_eq(n, 0n), d, vol, Q.FatNode.cluster(node), start, n)
