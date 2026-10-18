# Test support for the ref/ case files: an image file as a MemDev, built
# from the file's listed (non-zero) blocks, each read on its own
# (File.read_at); every other block is a blank block. A MemDev, so
# recovery and commits can write to it.
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D

def Ext4Img.step(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, +n: Nat, d: D.MemDev) -> IO(File & D.MemDev):
  (f, res) = p
  match res:
    case Done{xs}:
      IO.pure(File & D.MemDev, (f, D.MemDev.update(d, n, B.Octets.of_list(xs))))
    case Fail{e}:
      IO.pure(File & D.MemDev, (f, d))

def Ext4Img.load(ns: List<&2, Nat>, st: File & D.MemDev, +bs: Nat) -> IO(File & D.MemDev):
  match ns:
    case Nil{}:
      IO.pure(File & D.MemDev, st)
    case Con{+n, t}:
      (f, d) = st
      do IO<File & D.MemDev>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, U32.from_nat(Nat.mul(n, bs)), U32.from_nat(bs))
        q : File & D.MemDev <- Ext4Img.step(r, n, d)
        Ext4Img.load(t, q, bs)

def Ext4Img.fin(r: File & D.MemDev) -> IO(D.MemDev):
  (f, d) = r
  do IO<D.MemDev>:
    File.close(f)
    return d

# the image file at path: count blocks of bs bytes, the blocks numbered in
# nonzero read from the file
def Ext4Img.open(path: String, +bs: Nat, +count: Nat, nonzero: List<&2, Nat>) -> IO(D.MemDev):
  do IO<D.MemDev>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & D.MemDev <- Ext4Img.load(nonzero, (f, D.MemDev.blank(bs, count)), bs)
    Ext4Img.fin(r)
