# Test support for ref/cases.bend: the queries gen.py asks of each image,
# and what the package answers, one line each (see gen.py for the expected
# lines). Names and link targets print as hex.
import Base
import ../../bytes/bytes.bend as B
import ../../word64/word64.bend as W
import ../../crc/crc.bend as C
import ../../blockdev/blockdev.bend as D
import ./image.bend as I
import ../error.bend as E
import ../options.bend as O
import ../super.bend as S
import ../inode.bend as N
import ../file.bend as FL
import ../dir.bend as DR
import ../ext2.bend as X

type Ext2Query is Data:
  Ext2QLs{path: B.Octets}
  Ext2QStat{path: B.Octets}
  Ext2QCat{path: B.Octets}
  Ext2QRange{path: B.Octets, off: Nat, len: Nat}
  Ext2QLink{path: B.Octets}
  Ext2QFollow{path: B.Octets, hops: Nat}
  Ext2QMap{path: B.Octets, block: Nat}
  Ext2QSum{path: B.Octets, off: Nat, len: Nat}

type Ext2Img is Data:
  Ext2Img{name: String, path: String, bs: Nat, count: Nat, nonzero: List<&2, Nat>, opts: O.Ext2Options, queries: List<&2, Ext2Query>}

def Ext2Drv.err(e: E.Ext2Error) -> String:
  "err " ++ E.Ext2Error.kind(e)

def Ext2Drv.err.detail(e: E.Ext2Error) -> String:
  match e:
    case E.Ext2Unsupported{f}:
      "err Ext2Unsupported " ++ f
    case _:
      Ext2Drv.err(e)

# the listing's lines, built from the last entry back (rs: the entries
# reversed), so each line is joined once
def Ext2Drv.ls.ents(+p: String, rs: List<&2, DR.Ext2Dirent>, acc: String) -> String:
  match rs:
    case Nil{}:
      acc
    case Con{+e, t}:
      Ext2Drv.ls.ents(p, t, "ls " ++ p ++ " " ++ B.Octets.hex(DR.Ext2Dirent.name(e)) ++ " " ++ U32.show(DR.Ext2Dirent.inode(e)) ++ " " ++ U32.show(DR.Ext2Dirent.file_type(e)) ++ "\n" ++ acc)

def Ext2Drv.ls(+p: String, r: Result<&2, &2, E.Ext2Error, List<&2, DR.Ext2Dirent>>) -> String:
  match r:
    case Done{es}:
      Ext2Drv.ls.ents(p, List.reverse(&2, DR.Ext2Dirent, es), "ls " ++ p ++ " end")
    case Fail{e}:
      "ls " ++ p ++ " " ++ Ext2Drv.err(e)

def Ext2Drv.stat(+p: String, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      "stat " ++ p ++ " " ++ Nat.show(N.Ext2Inode.number_of(i)) ++ " " ++ N.Ext2Kind.show(N.Ext2Inode.kind(i)) ++ " " ++ W.W64.show(N.Ext2Inode.size(i)) ++ " " ++ U32.show(N.Ext2Inode.links(i)) ++ " " ++ U32.show(U32.and(N.Ext2Inode.mode(i), 4095))
    case Fail{e}:
      "stat " ++ p ++ " " ++ Ext2Drv.err(e)

# a whole file, streamed a block at a time: blocks, bytes, CRC-32
def Ext2Drv.cat.go(fuel: Nat, ch: Result<&2, &2, E.Ext2Error, FL.Ext2Chunk>, +d: I.Ext2ImgDev, +fs: S.Ext2Fs, c: U32, n: Nat, len: Nat) -> String:
  match fuel ch:
    case 0n _:
      "fuel"
    case _ Fail{e}:
      Ext2Drv.err(e)
    case 1n+f Done{FL.Ext2Eof{}}:
      Nat.show(n) ++ " " ++ Nat.show(len) ++ " " ++ U32.show(C.Crc32Spec.finish(C.crc32.spec(), c))
    case 1n+f Done{FL.Ext2Piece{+o, r}}:
      Ext2Drv.cat.go(f, FL.Ext2File.next(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, r), d, fs, C.Crc32Spec.update(C.crc32.spec(), c, o), Nat.add(n, 1n), Nat.add(len, B.Octets.len(o)))

def Ext2Drv.cat(+p: String, +d: I.Ext2ImgDev, +fs: S.Ext2Fs, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      "cat " ++ p ++ " " ++ Ext2Drv.cat.go(Nat.add(FL.Ext2File.blocks_needed(fs, i), 2n), FL.Ext2File.next(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, FL.Ext2File.start(i)), d, fs, C.Crc32Spec.start(C.crc32.spec()), 0n, 0n)
    case Fail{e}:
      "cat " ++ p ++ " " ++ Ext2Drv.err(e)

def Ext2Drv.hex(r: Result<&2, &2, E.Ext2Error, B.Octets>) -> String:
  match r:
    case Done{o}:
      "=" ++ B.Octets.hex(o)
    case Fail{e}:
      Ext2Drv.err(e)

def Ext2Drv.range(+p: String, +d: I.Ext2ImgDev, +fs: S.Ext2Fs, +off: Nat, +len: Nat, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      "range " ++ p ++ " " ++ Nat.show(off) ++ " " ++ Nat.show(len) ++ " " ++ Ext2Drv.hex(FL.Ext2File.read_range(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, i, off, len))
    case Fail{e}:
      "range " ++ p ++ " " ++ Ext2Drv.err(e)

# a range's length and CRC-32 (for ranges too long to print)
def Ext2Drv.sum(r: Result<&2, &2, E.Ext2Error, B.Octets>) -> String:
  match r:
    case Done{+o}:
      Nat.show(B.Octets.len(o)) ++ " " ++ U32.show(C.Crc32Spec.finish(C.crc32.spec(), C.Crc32Spec.update(C.crc32.spec(), C.Crc32Spec.start(C.crc32.spec()), o)))
    case Fail{e}:
      Ext2Drv.err(e)

def Ext2Drv.rsum(+p: String, +d: I.Ext2ImgDev, +fs: S.Ext2Fs, +off: Nat, +len: Nat, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      "sum " ++ p ++ " " ++ Nat.show(off) ++ " " ++ Nat.show(len) ++ " " ++ Ext2Drv.sum(FL.Ext2File.read_range(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, i, off, len))
    case Fail{e}:
      "sum " ++ p ++ " " ++ Ext2Drv.err(e)

def Ext2Drv.follow(+p: String, +hops: Nat, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      "follow " ++ p ++ " " ++ Nat.show(hops) ++ " " ++ Nat.show(N.Ext2Inode.number_of(i))
    case Fail{e}:
      "follow " ++ p ++ " " ++ Nat.show(hops) ++ " " ++ Ext2Drv.err(e)

def Ext2Drv.bmap.show(m: Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>) -> String:
  match m:
    case Done{Some{b}}:
      Nat.show(b)
    case Done{None{}}:
      "hole"
    case Fail{e}:
      Ext2Drv.err(e)

def Ext2Drv.bmap(+p: String, +d: I.Ext2ImgDev, +fs: S.Ext2Fs, +l: Nat, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      "bmap " ++ p ++ " " ++ Nat.show(l) ++ " " ++ Ext2Drv.bmap.show(FL.Ext2File.map(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, i, l))
    case Fail{e}:
      "bmap " ++ p ++ " " ++ Nat.show(l) ++ " " ++ Ext2Drv.err(e)

def Ext2Drv.run(q: Ext2Query, +d: I.Ext2ImgDev, +fs: S.Ext2Fs) -> String:
  match q:
    case Ext2QLs{+p}:
      Ext2Drv.ls(B.Octets.hex(p), X.Ext2.list(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, p))
    case Ext2QStat{+p}:
      Ext2Drv.stat(B.Octets.hex(p), X.Ext2.lookup_link(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, p))
    case Ext2QCat{+p}:
      Ext2Drv.cat(B.Octets.hex(p), d, fs, X.Ext2.lookup_link(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, p))
    case Ext2QRange{+p, off, len}:
      Ext2Drv.range(B.Octets.hex(p), d, fs, off, len, X.Ext2.lookup_link(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, p))
    case Ext2QLink{+p}:
      "link " ++ B.Octets.hex(p) ++ " " ++ Ext2Drv.hex(X.Ext2.readlink(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, p))
    case Ext2QFollow{+p, +h}:
      Ext2Drv.follow(B.Octets.hex(p), h, X.Ext2.lookup(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, S.Ext2Fs.with_symlink_hops(fs, h), p))
    case Ext2QMap{+p, l}:
      Ext2Drv.bmap(B.Octets.hex(p), d, fs, l, X.Ext2.lookup_link(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, p))
    case Ext2QSum{+p, off, len}:
      Ext2Drv.rsum(B.Octets.hex(p), d, fs, off, len, X.Ext2.lookup_link(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, fs, p))

def Ext2Drv.queries(qs: List<&2, Ext2Query>, +d: I.Ext2ImgDev, +fs: S.Ext2Fs) -> IO(Unit):
  match qs:
    case Nil{}:
      IO.print("end")
    case Con{q, t}:
      do IO<Unit>:
        IO.print(Ext2Drv.run(q, d, fs))
        Ext2Drv.queries(t, d, fs)

def Ext2Drv.opened(r: Result<&2, &2, E.Ext2Error, S.Ext2Fs>, +d: I.Ext2ImgDev, qs: List<&2, Ext2Query>) -> IO(Unit):
  match r:
    case Done{+fs}:
      do IO<Unit>:
        IO.print("open ok " ++ Nat.show(S.Ext2Fs.block_size(fs)) ++ " " ++ Nat.show(S.Ext2Fs.blocks(fs)) ++ " " ++ Nat.show(S.Ext2Fs.groups(fs)))
        Ext2Drv.queries(qs, d, fs)
    case Fail{e}:
      IO.print("open " ++ Ext2Drv.err.detail(e))

# one image: its header line, then each query's line
def Ext2Img.run(m: Ext2Img) -> IO(Unit):
  match m:
    case Ext2Img{name, path, +bs, +count, nz, +opts, qs}:
      do IO<Unit>:
        +d : I.Ext2ImgDev <- I.Ext2ImgDev.open(path, bs, count, nz)
        IO.print("== " ++ name)
        Ext2Drv.opened(X.Ext2.open(~I.Ext2ImgDev, ~I.Ext2ImgDev.block_size, ~I.Ext2ImgDev.read_block, d, opts), d, qs)
