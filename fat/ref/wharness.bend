# The reference test's writing side: an image in an ImgDev (loaded from a
# file, or blank), a list of operations run through write.bend on it, one
# line of output per operation (in the format ref/wgen.py's model writes),
# then the blocks the operations wrote, dumped to a file for wgen.py to put
# back into the image and check with fsck.fat, mtools and its own reader.
#
# The device is wrapped (WDev) so that it remembers which blocks were
# written: the dump holds only those (as a 4-byte block number and the
# block), so a 34 MB FAT32 image is not written out whole.
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D
import ../../blockdev/imgdev.bend as G
import ../error.bend as E
import ../bpb.bend as P
import ../dirent.bend as R
import ../dir.bend as Q
import ../map.bend as A
import ../fat.bend as M
import ../format.bend as K
import ../write.bend as X

# The device: an image and the set of blocks written (a FatMap used as a
# set: entry n is 1 once block n is written)

type WDev is Type:
  WDev{img: G.ImgDev, marks: A.FatMap}

def WDev.size(r: G.ImgDev & Nat, +m: A.FatMap) -> WDev & Nat:
  (img, n) = r
  (WDev{img, m}, n)

def WDev.block_size(d: WDev) -> WDev & Nat:
  match d:
    case WDev{img, +m}:
      WDev.size(G.ImgDev.block_size(img), m)

def WDev.got(r: G.ImgDev & Result<&2, &2, D.DevError, B.Octets>, +m: A.FatMap) -> WDev & Result<&2, &2, D.DevError, B.Octets>:
  (img, res) = r
  (WDev{img, m}, res)

def WDev.read_block(d: WDev, n: Nat) -> WDev & Result<&2, &2, D.DevError, B.Octets>:
  match d:
    case WDev{img, +m}:
      WDev.got(G.ImgDev.read_block(img, n), m)

def WDev.put(r: G.ImgDev & Result<&2, &2, D.DevError, Unit>, +m: A.FatMap, +n: Nat) -> WDev & Result<&2, &2, D.DevError, Unit>:
  (img, res) = r
  (WDev{img, A.FatMap.set(m, n, 1)}, res)

def WDev.write_block(d: WDev, n: Nat, data: B.Octets) -> WDev & Result<&2, &2, D.DevError, Unit>:
  match d:
    case WDev{img, +m}:
      +k = n
      WDev.put(G.ImgDev.write_block(img, k, data), m, k)

# no block written yet: a balanced map of count zeros, so marking a block
# walks one path
def WDev.marks(+count: Nat) -> A.FatMap:
  A.FatMap.of_list(P.Fat32{}, B.zeros.fast(count))

def WDev.blank(+count: Nat) -> WDev:
  WDev{G.ImgDev.blank(128n, count), WDev.marks(count)}

# Loading: the listed blocks of an image file (the ones that are not all
# zero), each read on its own

def WLoad.put.fin(r: G.ImgDev & Result<&2, &2, D.DevError, Unit>) -> G.ImgDev:
  (img, res) = r
  img

def WLoad.put(res: Result<&1, &1, U32 & String, List<&2, U32>>, +n: Nat, img: G.ImgDev) -> G.ImgDev:
  match res:
    case Done{xs}:
      WLoad.put.fin(G.ImgDev.write_block(img, n, B.Octets.of_list(xs)))
    case Fail{e}:
      img

def WLoad.step(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, +n: Nat, img: G.ImgDev) -> IO(File & G.ImgDev):
  (f, res) = p
  IO.pure(File & G.ImgDev, (f, WLoad.put(res, n, img)))

def WLoad.go(ns: List<&2, Nat>, st: File & G.ImgDev) -> IO(File & G.ImgDev):
  match ns:
    case Nil{}:
      IO.pure(File & G.ImgDev, st)
    case Con{+n, t}:
      (f, img) = st
      do IO<File & G.ImgDev>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, U32.from_nat(Nat.mul(n, 512n)), 512)
        q : File & G.ImgDev <- WLoad.step(r, n, img)
        WLoad.go(t, q)

def WLoad.fin(r: File & G.ImgDev, +count: Nat) -> IO(WDev):
  (f, img) = r
  do IO<WDev>:
    File.close(f)
    return WDev{img, WDev.marks(count)}

def WLoad.opened(r: Result<&1, &1, U32 & String, File>, ns: List<&2, Nat>, +count: Nat) -> IO(WDev):
  match r:
    case Done{f}:
      do IO<WDev>:
        q : File & G.ImgDev <- WLoad.go(ns, (f, G.ImgDev.blank(128n, count)))
        WLoad.fin(q, count)
    case Fail{e}:
      IO.pure(WDev, WDev.blank(count))

# an image of count 512-byte blocks from a file, its blocks ns read
def WLoad.file(path: String, ns: List<&2, Nat>, +count: Nat) -> IO(WDev):
  do IO<WDev>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    WLoad.opened(r, ns, count)

# Dumping the written blocks: each as its number (4 bytes, little-endian)
# and its 512 bytes

def WDump.step(p: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  (f, r) = p
  IO.pure(File, f)

def WDump.flush(f: File, buf: List<&2, U32>) -> IO(File):
  IO.bind(File & Result<&1, &1, U32 & String, Unit>, File, File.write_bytes(f, B.rev(buf)), WDump.step)

def WDump.blk(r: WDev & Result<&2, &2, D.DevError, B.Octets>, +n: Nat, buf: List<&2, U32>, k: WDev -> List<&2, U32> -> IO(WDev)) -> IO(WDev):
  (d, res) = r
  match res:
    case Done{o}:
      k(d, B.rev_onto(B.Octets.to_list(o), B.rev_onto(B.le32(U32.from_nat(n)), buf)))
    case Fail{e}:
      k(d, buf)

def WDump.marked(d: WDev, +n: Nat) -> WDev & Bool:
  match d:
    case WDev{img, +m}:
      (WDev{img, m}, U32.is_eq(A.FatMap.get(m, n), 1))

def WDump.one(r: WDev & Bool, +n: Nat, buf: List<&2, U32>, k: WDev -> List<&2, U32> -> IO(WDev)) -> IO(WDev):
  (d, hit) = r
  match hit:
    case True{}:
      WDump.blk(WDev.read_block(d, n), n, buf, k)
    case False{}:
      k(d, buf)

# blocks i on (n of them); j more blocks before the buffer is written
def WDump.go(n: Nat, +i: Nat, j: Nat, d: WDev, f: File, buf: List<&2, U32>) -> IO(WDev):
  match n:
    case 0n:
      do IO<WDev>:
        f2 : File <- WDump.flush(f, buf)
        File.close(f2)
        return d
    case 1n+p:
      match j:
        case 0n:
          do IO<WDev>:
            f2 : File <- WDump.flush(f, buf)
            WDump.one(WDump.marked(d, i), i, Nil{}, d2 => b => WDump.go(p, Nat.add(i, 1n), 4095n, d2, f2, b))
        case 1n+q:
          WDump.one(WDump.marked(d, i), i, buf, d2 => b => WDump.go(p, Nat.add(i, 1n), q, d2, f, b))

def WDump.opened(r: Result<&1, &1, U32 & String, File>, n: Nat, d: WDev) -> IO(WDev):
  match r:
    case Done{f}:
      WDump.go(n, 0n, 4096n, d, f, Nil{})
    case Fail{e}:
      IO.pure(WDev, d)

def WDump.file(path: String, n: Nat, d: WDev) -> IO(WDev):
  do IO<WDev>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    WDump.opened(r, n, d)

# Text

def WH.hex32(v: U32) -> String:
  B.hex(B.be32(v))

def WH.esc.one(plain: Bool, +c: Char) -> String:
  match plain:
    case True{}:
      SCon{c, ""}
    case False{}:
      "\\u" ++ WH.hex32(Char.to_u32(c))

def WH.esc(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, t}:
      +x = Char.to_u32(c)
      WH.esc.one(Bool.and(Bool.and(U32.is_ge(x, 32), U32.is_lt(x, 127)), Bool.not(Bool.or(U32.is_eq(x, 92), Bool.or(U32.is_eq(x, 124), U32.is_eq(x, 59))))), c) ++ WH.esc(t)

def WH.kind(dir: Bool) -> String:
  match dir:
    case True{}:
      "D"
    case False{}:
      "F"

def WH.node(+n: Q.FatNode) -> String:
  +e = Q.FatNode.entry(n)
  WH.esc(Q.FatNode.name(n)) ++ "|" ++ WH.kind(Q.FatNode.is_dir(n)) ++ "|" ++ U32.show(Q.FatNode.size(n)) ++ "|" ++ WH.esc(Q.FatNode.short_name(n)) ++ "|" ++ U32.show(R.FatDirent.attr(e)) ++ "|" ++ U32.show(R.FatDirent.cluster(e))

def WH.nodes(ns: List<&2, Q.FatNode>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{h, t}:
      " " ++ WH.node(h) ++ ";" ++ WH.nodes(t)

def WH.hash.go(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      WH.hash.go(t, U32.add(U32.mul(h, 31), x))

def WH.bytes(+o: B.Octets) -> String:
  Nat.show(B.Octets.len(o)) ++ " " ++ WH.hex32(WH.hash.go(B.Octets.to_list(o), 0))

def WH.err(e: E.FatError) -> String:
  "error " ++ E.FatError.show(e)

# Test data: n bytes from a seed (a linear congruential generator; wgen.py
# makes the same bytes)
def WH.gen.go(n: Nat, +x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +y = U32.add(U32.mul(x, 1103515245), 12345)
      WH.gen.go(p, y, Con{U32.and(255, U32.shrn(y, 16n)), acc})

def WH.gen(+n: Nat, +seed: U32) -> B.Octets:
  B.Octets.of_list(B.rev(WH.gen.go(n, seed, Nil{})))

# The operations

type WOp is Data:
  WFormat{kind: P.FatType, sectors: Nat, opts: K.FatFormatOptions}
  WOpen{opts: X.FatWOptions}
  WClock{clock: X.FatClock}
  WMkdir{path: String}
  WCreate{path: String}
  WWrite{path: String, off: Nat, len: Nat, seed: U32}
  WAppend{path: String, len: Nat, seed: U32}
  WTrunc{path: String, size: Nat}
  WUnlink{path: String}
  WRmdir{path: String}
  WRename{from: String, to: String}
  WTimes{path: String, times: X.FatTimes}
  WAttr{path: String, attr: U32}
  WLs{path: String}
  WRead{path: String}
  WStat{path: String}

# a step that changes the volume: its line, and the state after (the state
# before when it fails)
def WRun.changed(r: WDev & Result<&2, &2, E.FatError, X.FatW>, +w0: X.FatW, +tag: String, k: WDev -> X.FatW -> IO(WDev)) -> IO(WDev):
  (d, res) = r
  match res:
    case Done{+w}:
      do IO<WDev>:
        IO.print(tag ++ " ok " ++ Nat.show(X.FatW.free_clusters(w)))
        k(d, w)
    case Fail{e}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ WH.err(e))
        k(d, w0)

def WRun.ls(r: WDev & Result<&2, &2, E.FatError, List<&2, Q.FatNode>>, +tag: String, k: WDev -> IO(WDev)) -> IO(WDev):
  (d, res) = r
  match res:
    case Done{+ns}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ Nat.show(List.length(&2, Q.FatNode, ns)) ++ WH.nodes(ns))
        k(d)
    case Fail{e}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ WH.err(e))
        k(d)

def WRun.read(r: WDev & Result<&2, &2, E.FatError, B.Octets>, +tag: String, k: WDev -> IO(WDev)) -> IO(WDev):
  (d, res) = r
  match res:
    case Done{o}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ WH.bytes(o))
        k(d)
    case Fail{e}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ WH.err(e))
        k(d)

def WRun.stat.show(p: Q.FatPath) -> String:
  match p:
    case Q.FatPathRoot{}:
      "root"
    case Q.FatPathNode{+n}:
      WH.node(n)

def WRun.stat(r: WDev & Result<&2, &2, E.FatError, Q.FatPath>, +tag: String, k: WDev -> IO(WDev)) -> IO(WDev):
  (d, res) = r
  match res:
    case Done{p}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ WRun.stat.show(p))
        k(d)
    case Fail{e}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ WH.err(e))
        k(d)

def WRun.formatted(r: WDev & Result<&2, &2, E.FatError, K.FatLayout>, +tag: String, k: WDev -> IO(WDev)) -> IO(WDev):
  (d, res) = r
  match res:
    case Done{l}:
      do IO<WDev>:
        IO.print(tag ++ " ok " ++ Nat.show(K.FatLayout.clusters(l)))
        k(d)
    case Fail{e}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ WH.err(e))
        k(d)

def WRun.opened(r: WDev & Result<&2, &2, E.FatError, X.FatW>, +tag: String, +w0: X.FatW, k: WDev -> X.FatW -> IO(WDev)) -> IO(WDev):
  (d, res) = r
  match res:
    case Done{+w}:
      do IO<WDev>:
        IO.print(tag ++ " ok " ++ Nat.show(X.FatW.free_clusters(w)) ++ " " ++ Nat.show(X.FatW.hint(w)))
        k(d, w)
    case Fail{e}:
      do IO<WDev>:
        IO.print(tag ++ " " ++ WH.err(e))
        k(d, w0)

# the operations ops run on the device d (w: the writer's state; only
# meaningful after a WOpen), each printing "name.k ..." (k counting from 0)
def WRun.go(ops: List<&2, WOp>, +name: String, +i: Nat, d: WDev, +w: X.FatW) -> IO(WDev):
  match ops:
    case Nil{}:
      IO.pure(WDev, d)
    case Con{WFormat{kind, n, o}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.formatted(K.FatFormat.format(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, kind, n, o), tag, d2 => WRun.go(t, name, j, d2, w))
    case Con{WOpen{wo}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.opened(X.FatW.open(~WDev, ~WDev.block_size, ~WDev.read_block, d, P.FatOptions.default(), wo), tag, w, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WClock{c}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      do IO<WDev>:
        IO.print(tag ++ " clock")
        WRun.go(t, name, j, d, X.FatW.set_clock(w, c))
    case Con{WMkdir{p}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.mkdir(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WCreate{p}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.create(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WWrite{p, off, len, seed}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.write(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p, off, WH.gen(len, seed)), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WAppend{p, len, seed}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.append(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p, WH.gen(len, seed)), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WTrunc{p, n}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.truncate(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p, n), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WUnlink{p}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.unlink(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WRmdir{p}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.rmdir(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WRename{a, b}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.rename(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, a, b), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WTimes{p, ts}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.set_times(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p, ts), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WAttr{p, a}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.changed(X.FatW.set_attr(~WDev, ~WDev.block_size, ~WDev.read_block, ~WDev.write_block, d, w, p, a), w, tag, d2 => w2 => WRun.go(t, name, j, d2, w2))
    case Con{WLs{p}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.ls(X.FatW.list(~WDev, ~WDev.block_size, ~WDev.read_block, d, w, p), tag, d2 => WRun.go(t, name, j, d2, w))
    case Con{WRead{p}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.read(X.FatW.read(~WDev, ~WDev.block_size, ~WDev.read_block, d, w, p, 0n, 4294967295n), tag, d2 => WRun.go(t, name, j, d2, w))
    case Con{WStat{p}, t}:
      +tag = name ++ "." ++ Nat.show(i)
      +j = Nat.add(i, 1n)
      WRun.stat(X.FatW.stat(~WDev, ~WDev.block_size, ~WDev.read_block, d, w, p), tag, d2 => WRun.go(t, name, j, d2, w))

# a state to start from, before WOpen (never used by an operation that
# changes the volume: the cases open first)
def WRun.none() -> X.FatW:
  X.FatW{M.FatFs{P.FatOptions.default(), P.FatBpb{B.Octets.empty(), B.Octets.empty(), 512, 1, 1, 1, 16, 0, 248, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, P.FatVolume{P.Fat12{}, 512n, 512n, 512n, 512n, 1n, P.FatRootFixed{1024n, 16n}, 1536n, 0}}, X.FatWOptions.default(), A.FatMap.of_list(P.Fat12{}, Nil{}), 0n, 2n, X.FatClock.epoch(), Nil{}, False{}, 512n}

# One case: an image (blank, or blocks ns of a file), the operations, and
# the file the written blocks are dumped to
def WRun.case(+name: String, src: String, ns: List<&2, Nat>, +count: Nat, ops: List<&2, WOp>, out: String) -> IO(Unit):
  do IO<Unit>:
    d : WDev <- WLoad.file(src, ns, count)
    d2 : WDev <- WRun.go(ops, name, 0n, d, WRun.none())
    d3 : WDev <- WDump.file(out, count, d2)
    IO.print(name ++ " end")
