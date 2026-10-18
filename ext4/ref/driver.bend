# Test support for the ref/ case files: the queries gen.py asks of each
# image, and what the package answers, one line each (gen.py computes the
# expected lines). Names and paths print as hex.
import Base
import ../../bytes/bytes.bend as B
import ../../crc/crc.bend as C
import ../../blockdev/blockdev.bend as D
import ../../ext2/options.bend as XO
import ../../ext2/inode.bend as N
import ../../ext2/dir.bend as DR
import ./image.bend as I
import ../error.bend as E
import ../options.bend as O
import ../super.bend as S
import ../hash.bend as H
import ../xattr.bend as XA
import ../htwrite.bend as HW
import ../jwrite.bend as JW
import ../devwrite.bend as DW
import ../journal.bend as JR
import ../ext4.bend as X4

# a block of data for a commit: bs pseudo-random bytes from a seed, the
# first four the journal's magic number when magic is set
type Ext4QW is Data:
  Ext4QW{block: Nat, seed: U32, magic: Bool}

type Ext4Q is Data:
  Ext4QLookup{path: B.Octets}
  Ext4QList{path: B.Octets}
  Ext4QRead{path: B.Octets}
  Ext4QXattrs{path: B.Octets}
  Ext4QXattr{path: B.Octets, name: B.Octets}
  Ext4QHash{version: U32, seed: List<&2, U32>, name: B.Octets}
  Ext4QRecover{verify: Bool, skip: Bool, show: List<&2, Nat>}
  Ext4QCommit{rv: List<&2, Nat>, ws: List<&2, Ext4QW>, show: List<&2, Nat>}
  Ext4QBuild{ino: U32, gen: U32, parent: U32, pad: Nat, ents: List<&2, DR.Ext2Dirent>}

type Ext4ImgCase is Data:
  Ext4ImgCase{name: String, path: String, bs: Nat, count: Nat, nonzero: List<&2, Nat>, verify: Bool, queries: List<&2, Ext4Q>}

def Ext4Drv.err(+e: E.Ext4Error) -> String:
  "err " ++ E.Ext4Error.kind(e)

def Ext4Drv.hex(+o: B.Octets) -> String:
  B.Octets.hex(o)

# pseudo-random bytes (a linear congruential generator), last first
def Ext4Drv.gen(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      Ext4Drv.gen(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def Ext4Drv.data.pick(magic: Bool, +o: B.Octets) -> B.Octets:
  match magic:
    case True{}:
      B.Octets.append(B.Octets.of_list([192, 59, 57, 152]), B.Octets.drop(4n, o))
    case False{}:
      o

def Ext4Drv.writes(ws: List<&2, Ext4QW>, +bs: Nat, acc: List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  match ws:
    case Nil{}:
      List.reverse(&2, JW.Jbd2Write, acc)
    case Con{Ext4QW{b, s, m}, t}:
      Ext4Drv.writes(t, bs, Con{JW.Jbd2Write{b, Ext4Drv.data.pick(m, B.Octets.of_list(Ext4Drv.gen(bs, s, Nil{})))}, acc})

# Answers

def Ext4Drv.ino(+p: String, r: Result<&2, &2, E.Ext4Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      "lookup " ++ p ++ " " ++ Nat.show(N.Ext2Inode.number_of(i)) ++ " " ++ N.Ext2Kind.show(N.Ext2Inode.kind(i))
    case Fail{e}:
      "lookup " ++ p ++ " " ++ Ext4Drv.err(e)

def Ext4Drv.ents(+p: String, rs: List<&2, DR.Ext2Dirent>, acc: String) -> String:
  match rs:
    case Nil{}:
      acc
    case Con{+e, t}:
      Ext4Drv.ents(p, t, "ent " ++ p ++ " " ++ Ext4Drv.hex(DR.Ext2Dirent.name(e)) ++ " " ++ U32.show(DR.Ext2Dirent.inode(e)) ++ " " ++ U32.show(DR.Ext2Dirent.file_type(e)) ++ "\n" ++ acc)

def Ext4Drv.ls(+p: String, r: Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>) -> String:
  match r:
    case Done{es}:
      Ext4Drv.ents(p, List.reverse(&2, DR.Ext2Dirent, es), "ls " ++ p ++ " end")
    case Fail{e}:
      "ls " ++ p ++ " " ++ Ext4Drv.err(e)

def Ext4Drv.data(+tag: String, r: Result<&2, &2, E.Ext4Error, B.Octets>) -> String:
  match r:
    case Done{+o}:
      tag ++ " " ++ Nat.show(B.Octets.len(o)) ++ " " ++ U32.show(C.crc32(o))
    case Fail{e}:
      tag ++ " " ++ Ext4Drv.err(e)

def Ext4Drv.xas(xs: List<&2, XA.Ext4Xattr>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      Ext4Drv.xas(t, acc ++ " " ++ Ext4Drv.hex(XA.Ext4Xattr.full_name(x)) ++ "=" ++ Nat.show(XA.Ext4Xattr.size(x)))

def Ext4Drv.xattrs(+p: String, r: Result<&2, &2, E.Ext4Error, List<&2, XA.Ext4Xattr>>) -> String:
  match r:
    case Done{xs}:
      Ext4Drv.xas(xs, "xattrs " ++ p)
    case Fail{e}:
      "xattrs " ++ p ++ " " ++ Ext4Drv.err(e)

def Ext4Drv.hash(+tag: String, r: Result<&2, &2, E.Ext4Error, H.Ext4DxHash>) -> String:
  match r:
    case Done{+h}:
      tag ++ " " ++ U32.show(H.Ext4DxHash.major(h)) ++ " " ++ U32.show(H.Ext4DxHash.minor(h))
    case Fail{e}:
      tag ++ " " ++ Ext4Drv.err(e)

def Ext4Drv.blk(r: Result<&2, &2, D.DevError, B.Octets>) -> String:
  match r:
    case Done{+o}:
      Ext4Drv.hex(o)
    case Fail{e}:
      "fail"

def Ext4Drv.blocks(ns: List<&2, Nat>, +d: D.MemDev, acc: String) -> String:
  match ns:
    case Nil{}:
      acc
    case Con{+n, t}:
      Ext4Drv.blocks(t, d, acc ++ "\nblk " ++ Nat.show(n) ++ " " ++ Ext4Drv.blk(D.MemDev.read_block(d, n)))

def Ext4Drv.recovered(+show: List<&2, Nat>, r: Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>) -> String:
  match r:
    case Done{JR.Ext4Recovered{+d, +rep}}:
      Ext4Drv.blocks(show, d, "recover " ++ Nat.show(JR.Jbd2Report.transactions(rep)) ++ " " ++ Nat.show(JR.Jbd2Report.replayed(rep)) ++ " " ++ Nat.show(JR.Jbd2Report.skipped(rep)) ++ " " ++ Nat.show(JR.Jbd2Report.next(rep)))
    case Fail{e}:
      "recover " ++ Ext4Drv.err(e)

def Ext4Drv.committed(+show: List<&2, Nat>, r: Result<&2, &2, E.Ext4Error, JR.Ext4Committed<D.MemDev>>) -> String:
  match r:
    case Done{JR.Ext4Committed{+d, sq, n}}:
      Ext4Drv.blocks(show, d, "commit " ++ Nat.show(sq) ++ " " ++ Nat.show(n))
    case Fail{e}:
      "commit " ++ Ext4Drv.err(e)

def Ext4Drv.dirblocks(os: List<&2, B.Octets>, +k: Nat, acc: String) -> String:
  match os:
    case Nil{}:
      acc
    case Con{+o, t}:
      Ext4Drv.dirblocks(t, Nat.add(k, 1n), acc ++ "\ndirblk " ++ Nat.show(k) ++ " " ++ Ext4Drv.hex(o))

def Ext4Drv.built(r: Result<&2, &2, E.Ext4Error, List<&2, B.Octets>>) -> String:
  match r:
    case Done{+os}:
      Ext4Drv.dirblocks(os, 0n, "build " ++ Nat.show(List.length(&2, B.Octets, os)))
    case Fail{e}:
      "build " ++ Ext4Drv.err(e)

def Ext4Drv.jopts(verify: Bool, skip: Bool) -> O.Jbd2Options:
  O.Jbd2Options.with_skip_bad_data(O.Jbd2Options.with_verify(O.Jbd2Options.default(), verify), skip)

def Ext4Drv.answer(q: Ext4Q, +d: D.MemDev, +fs: S.Ext4Fs) -> String:
  match q:
    case Ext4QLookup{+p}:
      Ext4Drv.ino(Ext4Drv.hex(p), X4.Ext4.lookup(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, p))
    case Ext4QList{+p}:
      Ext4Drv.ls(Ext4Drv.hex(p), X4.Ext4.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, p))
    case Ext4QRead{+p}:
      Ext4Drv.data("read " ++ Ext4Drv.hex(p), X4.Ext4.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, p))
    case Ext4QXattrs{+p}:
      Ext4Drv.xattrs(Ext4Drv.hex(p), X4.Ext4.xattrs(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, p))
    case Ext4QXattr{+p, +n}:
      Ext4Drv.data("xattr " ++ Ext4Drv.hex(p) ++ " " ++ Ext4Drv.hex(n), X4.Ext4.xattr(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, p, n))
    case Ext4QHash{+v, sd, +n}:
      Ext4Drv.hash("hash " ++ U32.show(v) ++ " " ++ Ext4Drv.hex(n), H.Ext4Hash.name(v, sd, n))
    case Ext4QRecover{v, k, +show}:
      Ext4Drv.recovered(show, JR.Ext4Journal.recover(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, Ext4Drv.jopts(v, k)))
    case Ext4QCommit{rv, ws, +show}:
      Ext4Drv.committed(show, JR.Ext4Journal.commit(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, O.Jbd2Options.with_commit_time(O.Jbd2Options.default(), 1700000000, 0), rv, Ext4Drv.writes(ws, S.Ext4Fs.block_size(fs), Nil{})))
    case Ext4QBuild{+ino, gen, +parent, pad, es}:
      Ext4Drv.built(HW.Ext4Htree.build(HW.Ext4HtreeParams.with_pad(HW.Ext4HtreeParams.of_fs(fs, ino, gen, parent), pad), es))

def Ext4Drv.answers(qs: List<&2, Ext4Q>, +d: D.MemDev, +fs: S.Ext4Fs) -> IO(Unit):
  match qs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{q, t}:
      do IO<Unit>:
        IO.print(Ext4Drv.answer(q, d, fs))
        Ext4Drv.answers(t, d, fs)

def Ext4Drv.opened(r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>, +d: D.MemDev, qs: List<&2, Ext4Q>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("open " ++ Ext4Drv.err(e))
    case Done{+fs}:
      do IO<Unit>:
        IO.print("open ok")
        Ext4Drv.answers(qs, d, fs)

def Ext4Drv.opts(verify: Bool) -> O.Ext4Options:
  +o = O.Ext4Options.with_verify(O.Ext4Options.default(), verify)
  O.Ext4Options.with_ext2(o, XO.Ext2Options.with_recovery(O.Ext4Options.ext2(o), True{}))

# one image: its name, then the answers
def Ext4ImgCase.run(c: Ext4ImgCase) -> IO(Unit):
  match c:
    case Ext4ImgCase{name, path, +bs, +count, nz, v, qs}:
      do IO<Unit>:
        IO.print("== " ++ name)
        +d : D.MemDev <- I.Ext4Img.open(path, bs, count, nz)
        Ext4Drv.opened(S.Ext4Fs.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, Ext4Drv.opts(v)), d, qs)
