# The differential test's runner (gen.py writes its input): for each image
# file named in the ops file, the image is opened three ways, as a FileDev
# under an overlay (read on demand from the file), as a MemDev (the whole
# file read once, through IOMem) and, when its block size is a multiple of
# 4, as an ImgDev (through IOImg); and a copy of it is opened as a FileRW
# on bend-osdev-fileio's effects (read and written in place); then every
# operation is run on each, through the same IO helpers, and each answer
# printed.
#
# The ops file is little-endian u32 words: a count of images, then for each
# the path's length and bytes, the copy's path (the same way), the block size, whether to run the ImgDev,
# the count of operations, and the operations:
#   0 off len            read_bytes
#   1 off len bytes...   write_bytes
#   2 pathlen path...    save the overlay (FileOv.save)
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D
import ../../blockdev/imgdev.bend as I
import ../iodev.bend as V
import ../mem.bend as M
import ../overlay.bend as O
import ../filedev.bend as F
import ../fileov.bend as FO
import ../filerw.bend as R
import ../../fileio/fileio.bend as FIO

# Parsing

def word(xs: List<&2, U32>) -> U32 & List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      (U32.or(a, U32.or(U32.shln(b, 8n), U32.or(U32.shln(c, 16n), U32.shln(d, 24n)))), t)
    case _:
      (0, Nil{})

def nat.fin(r: U32 & List<&2, U32>) -> Nat & List<&2, U32>:
  (w, t) = r
  (U32.to_nat(w), t)

def nat(xs: List<&2, U32>) -> Nat & List<&2, U32>:
  nat.fin(word(xs))

# Showing results

def err(e: D.DevError) -> String:
  match e:
    case D.DevOutOfRange{n}:
      "out of range " ++ Nat.show(n)
    case D.DevBadLength{x, g}:
      "bad length " ++ Nat.show(x) ++ " " ++ Nat.show(g)
    case D.DevFailed{c}:
      "failed " ++ U32.show(c)

def show(r: Result<&2, &2, D.DevError, B.Octets>) -> String:
  match r:
    case Done{o}:
      "ok " ++ B.Octets.hex(o)
    case Fail{e}:
      err(e)

def ushow(r: Result<&2, &2, D.DevError, Unit>) -> String:
  match r:
    case Done{u}:
      "ok"
    case Fail{e}:
      err(e)

def say(~T: Type, tag: String, r: T & Result<&2, &2, D.DevError, B.Octets>) -> IO(T):
  (d, x) = r
  do IO<T>:
    IO.print(tag ++ show(x))
    return d

def usay(~T: Type, tag: String, r: T & Result<&2, &2, D.DevError, Unit>) -> IO(T):
  (d, x) = r
  do IO<T>:
    IO.print(tag ++ ushow(x))
    return d

def open_err(e: F.FileDevError) -> String:
  match e:
    case F.FileDevOpenFailed{c}:
      "open failed " ++ U32.show(c)
    case F.FileDevSizeFailed{c}:
      "size failed " ++ U32.show(c)
    case F.FileDevBadBlockSize{n}:
      "bad block size " ++ Nat.show(n)

# The operations, on each device

def img_read(use: Bool, img: I.ImgDev, +off: Nat, +len: Nat) -> IO(I.ImgDev):
  match use:
    case True{}:
      do IO<I.ImgDev>:
        r : I.ImgDev & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~I.ImgDev, ~M.IOImg.block_size, ~M.IOImg.read_block, img, off, len)
        say(~I.ImgDev, "i ", r)
    case False{}:
      IO.pure(I.ImgDev, img)

def img_write(use: Bool, img: I.ImgDev, +off: Nat, +data: B.Octets) -> IO(I.ImgDev):
  match use:
    case True{}:
      do IO<I.ImgDev>:
        r : I.ImgDev & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~I.ImgDev, ~M.IOImg.block_size, ~M.IOImg.read_block, ~M.IOImg.write_block, img, off, data)
        usay(~I.ImgDev, "i ", r)
    case False{}:
      IO.pure(I.ImgDev, img)

type CaseDevs is Type:
  CaseDevs{ov: O.IOOverlay<F.FileDev>, mem: D.MemDev, img: I.ImgDev, rw: R.FileRW}

def read_op(ov: O.IOOverlay<F.FileDev>, +mem: D.MemDev, img: I.ImgDev, rw: R.FileRW, +use: Bool, +off: Nat, +len: Nat) -> IO(CaseDevs):
  do IO<CaseDevs>:
    r : O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~O.IOOverlay<F.FileDev>, ~FO.FileOv.block_size, ~FO.FileOv.read_block, ov, off, len)
    ov : O.IOOverlay<F.FileDev> <- say(~O.IOOverlay<F.FileDev>, "f ", r)
    m : D.MemDev & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, mem, off, len)
    mem : D.MemDev <- say(~D.MemDev, "m ", m)
    img : I.ImgDev <- img_read(use, img, off, len)
    x : R.FileRW & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~R.FileRW, ~R.FileRW.block_size, ~R.FileRW.read_block(~FIO.FileIO.read_at), rw, off, len)
    rw : R.FileRW <- say(~R.FileRW, "w ", x)
    return CaseDevs{ov, mem, img, rw}

def write_op(ov: O.IOOverlay<F.FileDev>, +mem: D.MemDev, img: I.ImgDev, rw: R.FileRW, +use: Bool, +off: Nat, +data: B.Octets) -> IO(CaseDevs):
  do IO<CaseDevs>:
    r : O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~O.IOOverlay<F.FileDev>, ~FO.FileOv.block_size, ~FO.FileOv.read_block, ~FO.FileOv.write_block, ov, off, data)
    ov : O.IOOverlay<F.FileDev> <- usay(~O.IOOverlay<F.FileDev>, "f ", r)
    m : D.MemDev & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, mem, off, data)
    mem : D.MemDev <- usay(~D.MemDev, "m ", m)
    img : I.ImgDev <- img_write(use, img, off, data)
    x : R.FileRW & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~R.FileRW, ~R.FileRW.block_size, ~R.FileRW.read_block(~FIO.FileIO.read_at), ~R.FileRW.write_block(~FIO.FileIO.write_at), rw, off, data)
    rw : R.FileRW <- usay(~R.FileRW, "w ", x)
    return CaseDevs{ov, mem, img, rw}

def save_op(ov: O.IOOverlay<F.FileDev>, mem: D.MemDev, img: I.ImgDev, rw: R.FileRW, path: String) -> IO(CaseDevs):
  do IO<CaseDevs>:
    r : O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, Unit> <- FO.FileOv.save(ov, path)
    ov : O.IOOverlay<F.FileDev> <- usay(~O.IOOverlay<F.FileDev>, "s ", r)
    return CaseDevs{ov, mem, img, rw}

def run_op.read(ov: O.IOOverlay<F.FileDev>, +mem: D.MemDev, img: I.ImgDev, rw: R.FileRW, +use: Bool, +off: Nat, r: Nat & List<&2, U32>, k: CaseDevs -> List<&2, U32> -> IO(List<&2, U32>)) -> IO(List<&2, U32>):
  (len, zs) = r
  IO.bind(CaseDevs, List<&2, U32>, read_op(ov, mem, img, rw, use, off, len), ds => k(ds, zs))

def run_op.write(ov: O.IOOverlay<F.FileDev>, +mem: D.MemDev, img: I.ImgDev, rw: R.FileRW, +use: Bool, +off: Nat, r: Nat & List<&2, U32>, k: CaseDevs -> List<&2, U32> -> IO(List<&2, U32>)) -> IO(List<&2, U32>):
  (+len, +zs) = r
  IO.bind(CaseDevs, List<&2, U32>, write_op(ov, mem, img, rw, use, off, B.Octets.of_list(B.take.fast(len, zs))), ds => k(ds, B.drop(len, zs)))

def run_op.pick(rd: Bool, wr: Bool, ov: O.IOOverlay<F.FileDev>, +mem: D.MemDev, img: I.ImgDev, rw: R.FileRW, +use: Bool, +off: Nat, +ys: List<&2, U32>, k: CaseDevs -> List<&2, U32> -> IO(List<&2, U32>)) -> IO(List<&2, U32>):
  match rd wr:
    case True{} _:
      run_op.read(ov, mem, img, rw, use, off, nat(ys), k)
    case False{} True{}:
      run_op.write(ov, mem, img, rw, use, off, nat(ys), k)
    case False{} False{}:
      IO.bind(CaseDevs, List<&2, U32>, save_op(ov, mem, img, rw, B.to_string.fast(B.take.fast(off, ys))), ds => k(ds, B.drop(off, ys)))

def run_op.go(+kind: U32, ov: O.IOOverlay<F.FileDev>, +mem: D.MemDev, img: I.ImgDev, rw: R.FileRW, +use: Bool, r: Nat & List<&2, U32>, k: CaseDevs -> List<&2, U32> -> IO(List<&2, U32>)) -> IO(List<&2, U32>):
  (+off, ys) = r
  run_op.pick(U32.is_eq(kind, 0), U32.is_eq(kind, 1), ov, mem, img, rw, use, off, ys, k)

def run_op(r: U32 & List<&2, U32>, ov: O.IOOverlay<F.FileDev>, +mem: D.MemDev, img: I.ImgDev, rw: R.FileRW, +use: Bool, k: CaseDevs -> List<&2, U32> -> IO(List<&2, U32>)) -> IO(List<&2, U32>):
  (+kind, xs) = r
  run_op.go(kind, ov, mem, img, rw, use, nat(xs), k)

def run_ops(n: Nat, ds: CaseDevs, +use: Bool, xs: List<&2, U32>) -> IO(List<&2, U32>):
  match n ds:
    case 0n CaseDevs{ov, mem, img, rw}:
      do IO<List<&2, U32>>:
        FO.FileOv.close(ov)
        R.FileRW.close(rw)
        return xs
    case 1n+p CaseDevs{ov, mem, img, rw}:
      run_op(word(xs), ov, mem, img, rw, use, ds2 => zs => run_ops(p, ds2, use, zs))

# The whole file, for the MemDev and ImgDev twins

def whole.got(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(B.Octets):
  (f, x) = r
  match x:
    case Done{xs}:
      do IO<B.Octets>:
        File.close(f)
        return B.Octets.of_list(xs)
    case Fail{e}:
      do IO<B.Octets>:
        File.close(f)
        return B.Octets.empty()

def whole(path: String) -> IO(B.Octets):
  do IO<B.Octets>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1073741824)
    whole.got(r)

def img_of(use: Bool, +bs: Nat, o: B.Octets) -> I.ImgDev:
  match use:
    case True{}:
      I.ImgDev.of_octets(Nat.div(bs, 4n), o)
    case False{}:
      I.ImgDev.blank(1n, 0n)

def section.opened(r: Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>>, q: Result<&1, &1, F.FileDevError, R.FileRW>, +o: B.Octets, +bs: Nat, +use: Bool, +nops: Nat, xs: List<&2, U32>) -> IO(List<&2, U32>):
  match r q:
    case Done{ov} Done{rw}:
      run_ops(nops, CaseDevs{ov, D.MemDev.of_octets(bs, o), img_of(use, bs, o), rw}, use, xs)
    case Fail{e} _:
      do IO<List<&2, U32>>:
        IO.print(open_err(e))
        return Nil{}
    case Done{ov} Fail{e}:
      do IO<List<&2, U32>>:
        IO.print("w " ++ open_err(e))
        return Nil{}

type CaseHead is Data:
  CaseHead{path: String, rw: String, bs: Nat, use: Bool, nops: Nat, rest: List<&2, U32>}

def head.nops(+path: String, +rw: String, +bs: Nat, +use: Bool, r: Nat & List<&2, U32>) -> CaseHead:
  (n, xs) = r
  CaseHead{path, rw, bs, use, n, xs}

def head.use(+path: String, +rw: String, +bs: Nat, r: U32 & List<&2, U32>) -> CaseHead:
  (u, xs) = r
  head.nops(path, rw, bs, U32.is_eq(u, 1), nat(xs))

def head.bs(+path: String, +rw: String, r: Nat & List<&2, U32>) -> CaseHead:
  (bs, xs) = r
  head.use(path, rw, bs, word(xs))

def head.rw(+path: String, r: Nat & List<&2, U32>) -> CaseHead:
  (+plen, +ys) = r
  head.bs(path, B.to_string.fast(B.take.fast(plen, ys)), nat(B.drop(plen, ys)))

def head.path(r: Nat & List<&2, U32>) -> CaseHead:
  (+plen, +ys) = r
  head.rw(B.to_string.fast(B.take.fast(plen, ys)), nat(B.drop(plen, ys)))

def section.go(h: CaseHead) -> IO(List<&2, U32>):
  match h:
    case CaseHead{+path, rw, +bs, +use, +nops, vs}:
      do IO<List<&2, U32>>:
        IO.print("image " ++ path ++ " " ++ Nat.show(bs))
        o : B.Octets <- whole(path)
        r : Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>> <- FO.FileOv.open(path, bs)
        q : Result<&1, &1, F.FileDevError, R.FileRW> <- R.FileRW.open(~FIO.FileIO.open_rw, ~FIO.FileIO.size, rw, bs)
        section.opened(r, q, o, bs, use, nops, vs)

def section(xs: List<&2, U32>) -> IO(List<&2, U32>):
  section.go(head.path(nat(xs)))

def sections(n: Nat, xs: List<&2, U32>) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      IO.bind(List<&2, U32>, Unit, section(xs), ys => sections(p, ys))

def go.run(r: Nat & List<&2, U32>) -> IO(Unit):
  (n, ys) = r
  sections(n, ys)

def go(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, x) = r
  match x:
    case Done{xs}:
      do IO<Unit>:
        File.close(f)
        go.run(nat(xs))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("cannot read the ops")

# the ops file named on the command line (default: work/ops.bin)
def path(args: List<&1, String>) -> String:
  match args:
    case Con{prog, Con{p, rest}}:
      p
    case _:
      "work/ops.bin"

def main() -> IO(Unit):
  do IO<Unit>:
    a : List<&1, String> <- IO.args()
    f : File <- IO.try(File, File.open(path(a), "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1073741824)
    go(r)
