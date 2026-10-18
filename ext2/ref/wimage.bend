# Test support for the writing tests (ref/wcases-*.bend): an image file
# loaded into a MemDev (its non-zero blocks, as gen_write.py lists them, each
# read from the file on its own), and a device printed back as its non-zero
# blocks, one line each ("blk N HEX"), for wgen.py to rebuild the image.
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D

def Ext2WImg.got(+n: Nat, res: Result<&1, &1, U32 & String, List<&2, U32>>, d: D.MemDev) -> D.MemDev:
  match res:
    case Done{xs}:
      D.MemDev.update(d, n, B.Octets.of_list(xs))
    case Fail{e}:
      d

def Ext2WImg.step(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, +n: Nat, d: D.MemDev) -> IO(File & D.MemDev):
  (f, res) = p
  IO.pure(File & D.MemDev, (f, Ext2WImg.got(n, res, d)))

def Ext2WImg.load.go(ns: List<&2, Nat>, st: File & D.MemDev, +bs: Nat) -> IO(File & D.MemDev):
  match ns:
    case Nil{}:
      IO.pure(File & D.MemDev, st)
    case Con{+n, t}:
      (f, d) = st
      do IO<File & D.MemDev>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, U32.from_nat(Nat.mul(n, bs)), U32.from_nat(bs))
        q : File & D.MemDev <- Ext2WImg.step(r, n, d)
        Ext2WImg.load.go(t, q, bs)

def Ext2WImg.fin(r: File & D.MemDev) -> IO(D.MemDev):
  (f, d) = r
  do IO<D.MemDev>:
    File.close(f)
    return d

# the image at path: count blocks of bs bytes, the blocks nonzero read from
# the file and the rest zeros
def Ext2WImg.load(path: String, +bs: Nat, +count: Nat, nonzero: List<&2, Nat>) -> IO(D.MemDev):
  do IO<D.MemDev>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & D.MemDev <- Ext2WImg.load.go(nonzero, (f, D.MemDev.blank(bs, count)), bs)
    Ext2WImg.fin(r)

def Ext2WImg.zero(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(U32.is_eq(x, 0), Ext2WImg.zero(t))

def Ext2WImg.line.go(zero: Bool, +n: Nat, o: B.Octets) -> IO(Unit):
  match zero:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print("blk " ++ Nat.show(n) ++ " " ++ B.Octets.hex(o))

def Ext2WImg.line(+n: Nat, r: Result<&2, &2, D.DevError, B.Octets>) -> IO(Unit):
  match r:
    case Done{+o}:
      Ext2WImg.line.go(Ext2WImg.zero(B.Octets.to_list(o)), n, o)
    case Fail{e}:
      IO.print("blk " ++ Nat.show(n) ++ " error")

# the device's non-zero blocks from block n on, count of them
def Ext2WImg.dump(count: Nat, +d: D.MemDev, +n: Nat) -> IO(Unit):
  match count:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+c:
      do IO<Unit>:
        Ext2WImg.line(n, D.MemDev.read_block(d, n))
        Ext2WImg.dump(c, d, Nat.add(n, 1n))
