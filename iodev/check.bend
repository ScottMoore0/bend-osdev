import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../blockdev/imgdev.bend as I
import ./span.bend as S
import ./iodev.bend as V
import ./mem.bend as M
import ./overlay.bend as O
import ./filedev.bend as F
import ./fileov.bend as FO
import ./filerw.bend as R

def path() -> String:
  "/tmp/bend-osdev-iodev-check.img"

def saved() -> String:
  "/tmp/bend-osdev-iodev-check-saved.img"

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

def nshow(r: Result<&2, &2, D.DevError, Nat>) -> String:
  match r:
    case Done{n}:
      "ok " ++ Nat.show(n)
    case Fail{e}:
      err(e)

def say(~T: Type, r: T & Result<&2, &2, D.DevError, B.Octets>) -> IO(T):
  (d, x) = r
  do IO<T>:
    IO.print(show(x))
    return d

def usay(~T: Type, r: T & Result<&2, &2, D.DevError, Unit>) -> IO(T):
  (d, x) = r
  do IO<T>:
    IO.print(ushow(x))
    return d

def nsay(~T: Type, r: T & Nat) -> IO(T):
  (d, x) = r
  do IO<T>:
    IO.print(Nat.show(x))
    return d

def fsay(~T: Type, r: T & Result<&2, &2, D.DevError, Nat>) -> IO(T):
  (d, x) = r
  do IO<T>:
    IO.print(nshow(x))
    return d

def sum_go(xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      sum_go(t, Nat.add(acc, U32.to_nat(h)))

# a byte sum, as a step for fold_blocks
def sum_step(acc: Nat, blk: B.Octets) -> Nat:
  sum_go(B.Octets.to_list(blk), acc)

def wrote(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, x) = r
  File.close(f)

def make_file() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path(), "w"))
    w : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, B.of_string("abcdefghij"))
    wrote(w)

def open_err(e: F.FileDevError) -> String:
  match e:
    case F.FileDevOpenFailed{c}:
      "open failed " ++ U32.show(c)
    case F.FileDevSizeFailed{c}:
      "size failed " ++ U32.show(c)
    case F.FileDevBadBlockSize{n}:
      "bad block size " ++ Nat.show(n)

# a FileDev on the 10-byte file, 4-byte blocks
def file_checks(d: F.FileDev) -> IO(Unit):
  do IO<Unit>:
    x : F.FileDev & Nat <- F.FileDev.block_count(d)
    d : F.FileDev <- nsay(~F.FileDev, x)
    r : F.FileDev & Result<&2, &2, D.DevError, B.Octets> <- F.FileDev.read_block(d, 1n)
    d : F.FileDev <- say(~F.FileDev, r)
    r : F.FileDev & Result<&2, &2, D.DevError, B.Octets> <- F.FileDev.read_block(d, 2n)
    d : F.FileDev <- say(~F.FileDev, r)
    r : F.FileDev & Result<&2, &2, D.DevError, B.Octets> <- F.FileDev.read_block(d, 3n)
    d : F.FileDev <- say(~F.FileDev, r)
    r : F.FileDev & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~F.FileDev, ~F.FileDev.block_size, ~F.FileDev.read_block, d, 2n, 7n)
    d : F.FileDev <- say(~F.FileDev, r)
    w : F.FileDev & Result<&2, &2, D.DevError, Unit> <- F.FileDev.write_block(d, 0n, B.Octets.of_string("WXYZ"))
    d : F.FileDev <- usay(~F.FileDev, w)
    s : F.FileDev & Result<&2, &2, D.DevError, Nat> <- V.IODev.fold_blocks(~Nat, ~F.FileDev, ~F.FileDev.read_block, ~sum_step, 3n, d, 0n, 0n)
    d : F.FileDev <- fsay(~F.FileDev, s)
    s : F.FileDev & Result<&2, &2, D.DevError, Nat> <- V.IODev.fold_blocks(~Nat, ~F.FileDev, ~F.FileDev.read_block, ~sum_step, 4n, d, 0n, 0n)
    d : F.FileDev <- fsay(~F.FileDev, s)
    F.FileDev.close(d)

# the same file, writable through an overlay: a write across blocks, a read
# back, a save to a new file
def ov_checks(o: O.IOOverlay<F.FileDev>) -> IO(Unit):
  do IO<Unit>:
    w : O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~O.IOOverlay<F.FileDev>, ~FO.FileOv.block_size, ~FO.FileOv.read_block, ~FO.FileOv.write_block, o, 3n, B.Octets.of_string("XYZW"))
    o : O.IOOverlay<F.FileDev> <- usay(~O.IOOverlay<F.FileDev>, w)
    w : O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, Unit> <- FO.FileOv.write_block(o, 0n, B.Octets.of_string("xyz"))
    o : O.IOOverlay<F.FileDev> <- usay(~O.IOOverlay<F.FileDev>, w)
    w : O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, Unit> <- FO.FileOv.write_block(o, 3n, B.Octets.of_string("abcd"))
    o : O.IOOverlay<F.FileDev> <- usay(~O.IOOverlay<F.FileDev>, w)
    r : O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~O.IOOverlay<F.FileDev>, ~FO.FileOv.block_size, ~FO.FileOv.read_block, o, 0n, 12n)
    o : O.IOOverlay<F.FileDev> <- say(~O.IOOverlay<F.FileDev>, r)
    w : O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, Unit> <- FO.FileOv.save(o, saved())
    o : O.IOOverlay<F.FileDev> <- usay(~O.IOOverlay<F.FileDev>, w)
    FO.FileOv.close(o)

# the saved file, read back with 6-byte blocks
def saved_checks(d: F.FileDev) -> IO(Unit):
  do IO<Unit>:
    x : F.FileDev & Nat <- F.FileDev.block_count(d)
    d : F.FileDev <- nsay(~F.FileDev, x)
    r : F.FileDev & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~F.FileDev, ~F.FileDev.block_size, ~F.FileDev.read_block, d, 0n, 12n)
    d : F.FileDev <- say(~F.FileDev, r)
    F.FileDev.close(d)

def opened(k: F.FileDev -> IO(Unit), r: Result<&1, &1, F.FileDevError, F.FileDev>) -> IO(Unit):
  match r:
    case Done{d}:
      k(d)
    case Fail{e}:
      IO.print(open_err(e))

def ov_opened(r: Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>>) -> IO(Unit):
  match r:
    case Done{o}:
      ov_checks(o)
    case Fail{e}:
      IO.print(open_err(e))

# the same file as a FileRW with the Base-only defaults (FileRW.base_*):
# reads on demand, writes refused; ref/ runs FileRW on fileio's effects
def rw_checks(d: R.FileRW) -> IO(Unit):
  do IO<Unit>:
    x : R.FileRW & Nat <- R.FileRW.block_count(d)
    d : R.FileRW <- nsay(~R.FileRW, x)
    r : R.FileRW & Result<&2, &2, D.DevError, B.Octets> <- R.FileRW.read_block(~R.FileRW.base_read_at, d, 2n)
    d : R.FileRW <- say(~R.FileRW, r)
    r : R.FileRW & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~R.FileRW, ~R.FileRW.block_size, ~R.FileRW.read_block(~R.FileRW.base_read_at), d, 2n, 7n)
    d : R.FileRW <- say(~R.FileRW, r)
    w : R.FileRW & Result<&2, &2, D.DevError, Unit> <- R.FileRW.write_block(~R.FileRW.base_write_at, d, 0n, B.Octets.of_string("WXYZ"))
    d : R.FileRW <- usay(~R.FileRW, w)
    w : R.FileRW & Result<&2, &2, D.DevError, Unit> <- R.FileRW.write_block(~R.FileRW.base_write_at, d, 0n, B.Octets.of_string("WXY"))
    d : R.FileRW <- usay(~R.FileRW, w)
    w : R.FileRW & Result<&2, &2, D.DevError, Unit> <- R.FileRW.write_block(~R.FileRW.base_write_at, d, 3n, B.Octets.of_string("WXYZ"))
    d : R.FileRW <- usay(~R.FileRW, w)
    w : R.FileRW & Result<&2, &2, D.DevError, Unit> <- R.FileRW.sync(~R.FileRW.base_sync, d)
    d : R.FileRW <- usay(~R.FileRW, w)
    R.FileRW.close(d)

def rw_opened(r: Result<&1, &1, F.FileDevError, R.FileRW>) -> IO(Unit):
  match r:
    case Done{d}:
      rw_checks(d)
    case Fail{e}:
      IO.print(open_err(e))

def dev() -> D.MemDev:
  D.MemDev.of_octets(4n, B.Octets.of_string("abcdefghij"))

def img() -> I.ImgDev:
  I.ImgDev.of_octets(1n, B.Octets.of_string("abcdefghij"))

def span_show(s: S.IOSpan) -> String:
  match s:
    case S.IOSpan{f, k, c, l}:
      Nat.show(f) ++ " " ++ Nat.show(k) ++ " " ++ Nat.show(c) ++ " " ++ Nat.show(l)

def adapter_checks() -> IO(Unit):
  do IO<Unit>:
    IO.print(span_show(S.IOSpan.of(4n, 6n, 7n)))
    IO.print(Nat.show(S.IOSpan.blocks(4n, 10n)))
    r : D.MemDev & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, dev(), 3n, 6n)
    m : D.MemDev <- say(~D.MemDev, r)
    w : D.MemDev & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, m, 1n, B.Octets.of_string("123456789"))
    m : D.MemDev <- usay(~D.MemDev, w)
    r : D.MemDev & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, m, 0n, 12n)
    m : D.MemDev <- say(~D.MemDev, r)
    w : D.MemDev & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, m, 10n, B.Octets.of_string("123"))
    m : D.MemDev <- usay(~D.MemDev, w)
    x : I.ImgDev & Nat <- M.IOImg.block_count(img())
    i : I.ImgDev <- nsay(~I.ImgDev, x)
    w : I.ImgDev & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~I.ImgDev, ~M.IOImg.block_size, ~M.IOImg.read_block, ~M.IOImg.write_block, i, 2n, B.Octets.of_string("ZZZ"))
    i : I.ImgDev <- usay(~I.ImgDev, w)
    r : I.ImgDev & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~I.ImgDev, ~M.IOImg.block_size, ~M.IOImg.read_block, i, 0n, 12n)
    i : I.ImgDev <- say(~I.ImgDev, r)
    IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    adapter_checks()
    make_file()
    a : Result<&1, &1, F.FileDevError, F.FileDev> <- F.FileDev.open(path(), 4n)
    opened(file_checks, a)
    b : Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>> <- FO.FileOv.open(path(), 4n)
    ov_opened(b)
    c : Result<&1, &1, F.FileDevError, F.FileDev> <- F.FileDev.open(saved(), 6n)
    opened(saved_checks, c)
    e : Result<&1, &1, F.FileDevError, F.FileDev> <- F.FileDev.open(path(), 0n)
    opened(saved_checks, e)
    g : Result<&1, &1, F.FileDevError, F.FileDev> <- F.FileDev.open("/nonexistent/bend-osdev-iodev.img", 4n)
    opened(saved_checks, g)
    h : Result<&1, &1, F.FileDevError, R.FileRW> <- R.FileRW.open(~R.FileRW.base_open, ~R.FileRW.base_size, path(), 4n)
    rw_opened(h)
    h : Result<&1, &1, F.FileDevError, R.FileRW> <- R.FileRW.open(~R.FileRW.base_open, ~R.FileRW.base_size, path(), 0n)
    rw_opened(h)
    h : Result<&1, &1, F.FileDevError, R.FileRW> <- R.FileRW.open(~R.FileRW.base_open, ~R.FileRW.base_size, "/nonexistent/bend-osdev-iodev.img", 4n)
    rw_opened(h)

#|1 2 3 3
#|3
#|ok 646566676869
#|ok
#|ok 613132333435363738390000
#|out of range 3
#|3
#|ok
#|ok 61625a5a5a666768696a0000
#|3
#|ok 65666768
#|ok 696a0000
#|out of range 3
#|ok 63646566676869
#|failed 30
#|ok 1015
#|out of range 3
#|ok
#|bad length 4 3
#|out of range 3
#|ok 61626358595a5768696a0000
#|ok
#|2
#|ok 61626358595a5768696a0000
#|bad block size 0
#|open failed 2
#|3
#|ok 696a0000
#|ok 63646566676869
#|failed 30
#|bad length 4 3
#|out of range 3
#|ok
#|bad block size 0
#|open failed 2
