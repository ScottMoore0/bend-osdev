# Test support for ref/cases.bend: a device that holds an image file's
# non-zero blocks, each read from the file on its own (File.read_at), so no
# whole image is ever one Octets. Every other block reads as zeros. A block
# is kept as the list File.read_at answers (about 40 bytes of memory a byte,
# against an Octets' 940) and becomes an Octets when it is read.
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D

type Ext2ImgBlk is Data:
  Ext2ImgBlk{n: Nat, data: List<&2, U32>}

type Ext2ImgDev is Data:
  Ext2ImgDev{bs: Nat, count: Nat, blocks: List<&2, Ext2ImgBlk>}

def Ext2ImgDev.block_size(d: Ext2ImgDev) -> Nat:
  match d:
    case Ext2ImgDev{bs, c, l}:
      bs

def Ext2ImgDev.find.pick(hit: Bool, data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match hit:
    case True{}:
      Some{data}
    case False{}:
      None{}

# block n of the listed blocks, a tail call per block passed
def Ext2ImgDev.find(l: List<&2, Ext2ImgBlk>, +n: Nat, +bs: Nat, found: Maybe<&2, List<&2, U32>>) -> B.Octets:
  match l found:
    case _ Some{xs}:
      B.Octets.of_list(xs)
    case Nil{} None{}:
      B.Octets.zeros(bs)
    case Con{Ext2ImgBlk{k, data}, t} None{}:
      Ext2ImgDev.find(t, n, bs, Ext2ImgDev.find.pick(Nat.is_eq(k, n), data))

def Ext2ImgDev.read.pick(ok: Bool, +n: Nat, +bs: Nat, l: List<&2, Ext2ImgBlk>) -> Result<&2, &2, D.DevError, B.Octets>:
  match ok:
    case True{}:
      Done{Ext2ImgDev.find(l, n, bs, None{})}
    case False{}:
      Fail{D.DevOutOfRange{n}}

def Ext2ImgDev.read_block(d: Ext2ImgDev, n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  match d:
    case Ext2ImgDev{+bs, c, l}:
      +k = n
      Ext2ImgDev.read.pick(Nat.is_lt(k, c), k, bs, l)

def Ext2ImgDev.got(+n: Nat, res: Result<&1, &1, U32 & String, List<&2, U32>>, acc: List<&2, Ext2ImgBlk>) -> List<&2, Ext2ImgBlk>:
  match res:
    case Done{xs}:
      Con{Ext2ImgBlk{n, xs}, acc}
    case Fail{e}:
      acc

def Ext2ImgDev.step(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, +n: Nat, acc: List<&2, Ext2ImgBlk>) -> IO(File & List<&2, Ext2ImgBlk>):
  (f, res) = p
  IO.pure(File & List<&2, Ext2ImgBlk>, (f, Ext2ImgDev.got(n, res, acc)))

# the listed blocks of the file (gen.py lists the ones that are not all
# zeros), one read each
def Ext2ImgDev.load(ns: List<&2, Nat>, st: File & List<&2, Ext2ImgBlk>, +bs: Nat) -> IO(File & List<&2, Ext2ImgBlk>):
  match ns:
    case Nil{}:
      IO.pure(File & List<&2, Ext2ImgBlk>, st)
    case Con{+n, t}:
      (f, acc) = st
      do IO<File & List<&2, Ext2ImgBlk>>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, U32.from_nat(Nat.mul(n, bs)), U32.from_nat(bs))
        q : File & List<&2, Ext2ImgBlk> <- Ext2ImgDev.step(r, n, acc)
        Ext2ImgDev.load(t, q, bs)

def Ext2ImgDev.fin(+bs: Nat, +count: Nat, r: File & List<&2, Ext2ImgBlk>) -> IO(Ext2ImgDev):
  (f, l) = r
  do IO<Ext2ImgDev>:
    File.close(f)
    return Ext2ImgDev{bs, count, l}

# the image file at path, as count blocks of bs bytes, of which the blocks
# numbered in nonzero are read from the file and the rest are zeros
def Ext2ImgDev.open(path: String, +bs: Nat, +count: Nat, nonzero: List<&2, Nat>) -> IO(Ext2ImgDev):
  do IO<Ext2ImgDev>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & List<&2, Ext2ImgBlk> <- Ext2ImgDev.load(nonzero, (f, Nil{}), bs)
    Ext2ImgDev.fin(bs, count, r)
