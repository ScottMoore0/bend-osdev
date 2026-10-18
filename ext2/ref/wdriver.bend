# Test support for the writing tests (ref/wgen.py writes ref/wcases.bend,
# which runs a list of cases through Ext2WCase.run). A case is an image (read
# from a file, or made on a blank device by the package's mkfs) and a list of
# steps; each step's outcome is printed ("op K ok", or "op K err KIND:
# message"; a refused operation leaves the device as it was), then the tree
# as the package reads it back ("t PATH KIND SIZE LINKS CRC [TARGET]", hex
# paths and targets), then the final image's non-zero blocks ("blk N HEX"),
# for wgen.py to check against its model, e2fsck and debugfs.
import Base
import ../../bytes/bytes.bend as B
import ../../uuid/uuid.bend as U
import ../../crc/crc.bend as C
import ../../blockdev/blockdev.bend as D
import ./wimage.bend as W
import ../error.bend as E
import ../options.bend as O
import ../super.bend as S
import ../inode.bend as N
import ../file.bend as FL
import ../dir.bend as DR
import ../ext2.bend as X
import ../wopts.bend as WO
import ../meta.bend as T
import ../fsck.bend as FK
import ../ops.bend as P
import ../run.bend as RN
import ../mkfs.bend as MK

# A step: an operation, or a check of the whole filesystem
type Ext2WStep is Data:
  Ext2WOp{op: P.Ext2Op}
  Ext2WFsck{}

# where the image comes from
type Ext2WSource is Data:
  Ext2WFile{path: String, nonzero: List<&2, Nat>}
  Ext2WMkfs{opts: MK.Ext2MkfsOptions}

type Ext2WCase is Data:
  Ext2WCase{name: String, source: Ext2WSource, bs: Nat, count: Nat, opts: O.Ext2Options, wo: WO.Ext2WriteOptions, steps: List<&2, Ext2WStep>}

# n pseudo-random bytes from seed s (a linear congruential generator, as
# wgen.py computes them)
def Ext2WDrv.bytes.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      Ext2WDrv.bytes.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def Ext2WDrv.bytes(n: Nat, s: U32) -> B.Octets:
  B.Octets.of_list(Ext2WDrv.bytes.go(n, s, Nil{}))

def Ext2WDrv.hexval.pick(digit: Bool, +c: U32) -> U32:
  match digit:
    case True{}:
      U32.sub(c, 48)
    case False{}:
      U32.sub(c, 87)

def Ext2WDrv.hexval(+c: U32) -> U32:
  Ext2WDrv.hexval.pick(U32.is_lt(c, 58), c)

def Ext2WDrv.unhex.go(cs: String, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case SCon{Chr{a}, SCon{Chr{b}, t}}:
      Ext2WDrv.unhex.go(t, Con{U32.or(U32.shln(Ext2WDrv.hexval(a), 4n), Ext2WDrv.hexval(b)), acc})
    case _:
      List.reverse(&2, U32, acc)

# the bytes a lower-case hex string spells
def Ext2WDrv.hx(s: String) -> B.Octets:
  B.Octets.of_list(Ext2WDrv.unhex.go(s, Nil{}))

def Ext2WDrv.err(+e: E.Ext2Error) -> String:
  E.Ext2Error.kind(e) ++ ": " ++ E.Ext2Error.show(e)

def Ext2WDrv.show(+k: Nat, r: Result<&2, &2, E.Ext2Error, D.MemDev>) -> String:
  match r:
    case Done{d}:
      "op " ++ Nat.show(k) ++ " ok"
    case Fail{+e}:
      "op " ++ Nat.show(k) ++ " err " ++ Ext2WDrv.err(e)

def Ext2WDrv.keep(r: Result<&2, &2, E.Ext2Error, D.MemDev>, d: D.MemDev) -> D.MemDev:
  match r:
    case Done{d2}:
      d2
    case Fail{e}:
      d

def Ext2WDrv.fsck(+k: Nat, r: Result<&2, &2, E.Ext2Error, Unit>) -> String:
  match r:
    case Done{u}:
      "op " ++ Nat.show(k) ++ " fsck ok"
    case Fail{+e}:
      "op " ++ Nat.show(k) ++ " fsck err " ++ Ext2WDrv.err(e)

def Ext2WDrv.step(st: Ext2WStep, +d: D.MemDev, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +k: Nat) -> IO(D.MemDev):
  match st:
    case Ext2WOp{+op}:
      +r = RN.Ext2Op.run(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, op, d, fs, wo)
      do IO<D.MemDev>:
        IO.print(Ext2WDrv.show(k, r))
        return Ext2WDrv.keep(r, d)
    case Ext2WFsck{}:
      do IO<D.MemDev>:
        IO.print(Ext2WDrv.fsck(k, FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs)))
        return d

def Ext2WDrv.steps(xs: List<&2, Ext2WStep>, +d: D.MemDev, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +k: Nat) -> IO(D.MemDev):
  match xs:
    case Nil{}:
      IO.pure(D.MemDev, d)
    case Con{st, t}:
      do IO<D.MemDev>:
        d2 : D.MemDev <- Ext2WDrv.step(st, d, fs, wo, k)
        Ext2WDrv.steps(t, d2, fs, wo, Nat.add(k, 1n))

# The tree as the package reads it

def Ext2WDrv.crc(r: Result<&2, &2, E.Ext2Error, B.Octets>) -> String:
  match r:
    case Done{o}:
      U32.show(C.Crc32Spec.finish(C.crc32.spec(), C.Crc32Spec.update(C.crc32.spec(), C.Crc32Spec.start(C.crc32.spec()), o)))
    case Fail{e}:
      "err-" ++ E.Ext2Error.kind(e)

def Ext2WDrv.target(r: Result<&2, &2, E.Ext2Error, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      "err-" ++ E.Ext2Error.kind(e)

def Ext2WDrv.join(+dir: B.Octets, +name: B.Octets) -> B.Octets:
  B.Octets.append(dir, B.Octets.append(B.Octets.of_string("/"), name))

def Ext2WDrv.line.file(small: Bool, +d: D.MemDev, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> String:
  match small:
    case True{}:
      Ext2WDrv.crc(FL.Ext2File.read_all(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, i))
    case False{}:
      "big"

def Ext2WDrv.line.kind(k: N.Ext2Kind, +d: D.MemDev, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> String:
  match k:
    case N.Ext2Regular{}:
      Ext2WDrv.line.file(Nat.is_lt(N.Ext2Inode.size_nat(i), 1048576n), d, fs, i)
    case N.Ext2Symlink{}:
      "- " ++ Ext2WDrv.target(FL.Ext2File.readlink(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, i))
    case _:
      "-"

def Ext2WDrv.line(+path: B.Octets, +d: D.MemDev, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> String:
  "t " ++ B.Octets.hex(path) ++ " " ++ N.Ext2Kind.show(N.Ext2Inode.kind(i)) ++ " " ++ Nat.show(N.Ext2Inode.size_nat(i)) ++ " " ++ U32.show(N.Ext2Inode.links(i)) ++ " " ++ Ext2WDrv.line.kind(N.Ext2Inode.kind(i), d, fs, i)

# the directories still to walk: their paths and inodes
type Ext2WDir is Data:
  Ext2WDir{path: B.Octets, inode: N.Ext2Inode}

def Ext2WDrv.dots(es: List<&2, DR.Ext2Dirent>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{+e, t}:
      +n = DR.Ext2Dirent.name(e)
      Bool.or(B.Octets.is_eq(n, B.Octets.of_string(".")), B.Octets.is_eq(n, B.Octets.of_string("..")))

def Ext2WDrv.push(isdir: Bool, +p: B.Octets, +i: N.Ext2Inode, todo: List<&2, Ext2WDir>) -> List<&2, Ext2WDir>:
  match isdir:
    case True{}:
      Con{Ext2WDir{p, i}, todo}
    case False{}:
      todo

# the lines and the directories still to walk, after one entry
type Ext2WWalk is Data:
  Ext2WWalk{out: List<&2, String>, todo: List<&2, Ext2WDir>}

def Ext2WDrv.got(r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>, +p: B.Octets, +d: D.MemDev, +fs: S.Ext2Fs, w: Ext2WWalk) -> Ext2WWalk:
  match r w:
    case Done{+i} Ext2WWalk{out, todo}:
      Ext2WWalk{Con{Ext2WDrv.line(p, d, fs, i), out}, Ext2WDrv.push(N.Ext2Inode.is_dir(i), p, i, todo)}
    case Fail{e} Ext2WWalk{out, todo}:
      Ext2WWalk{Con{"t " ++ B.Octets.hex(p) ++ " err " ++ E.Ext2Error.kind(e), out}, todo}

def Ext2WDrv.entries(es: List<&2, DR.Ext2Dirent>, skip: Bool, +dir: B.Octets, +d: D.MemDev, +fs: S.Ext2Fs, w: Ext2WWalk) -> Ext2WWalk:
  match es skip:
    case Nil{} _:
      w
    case Con{e, +t} True{}:
      Ext2WDrv.entries(t, Ext2WDrv.dots(t), dir, d, fs, w)
    case Con{+e, +t} False{}:
      +p = Ext2WDrv.join(dir, DR.Ext2Dirent.name(e))
      Ext2WDrv.entries(t, Ext2WDrv.dots(t), dir, d, fs, Ext2WDrv.got(N.Ext2Inode.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, U32.to_nat(DR.Ext2Dirent.inode(e))), p, d, fs, w))

def Ext2WDrv.listed(r: Result<&2, &2, E.Ext2Error, List<&2, DR.Ext2Dirent>>, +dir: B.Octets, +d: D.MemDev, +fs: S.Ext2Fs, w: Ext2WWalk) -> Ext2WWalk:
  match r w:
    case Done{+es} _:
      Ext2WDrv.entries(es, Ext2WDrv.dots(es), dir, d, fs, w)
    case Fail{e} Ext2WWalk{out, todo}:
      Ext2WWalk{Con{"t " ++ B.Octets.hex(dir) ++ " err " ++ E.Ext2Error.kind(e), out}, todo}

def Ext2WDrv.walk(fuel: Nat, w: Ext2WWalk, +d: D.MemDev, +fs: S.Ext2Fs) -> List<&2, String>:
  match fuel w:
    case 0n Ext2WWalk{out, todo}:
      Con{"t walk out of fuel", out}
    case _ Ext2WWalk{out, Nil{}}:
      out
    case 1n+f Ext2WWalk{out, Con{Ext2WDir{+p, +i}, todo}}:
      Ext2WDrv.walk(f, Ext2WDrv.listed(DR.Ext2Dir.entries(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, i), p, d, fs, Ext2WWalk{out, todo}), d, fs)

def Ext2WDrv.tree(r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>, +d: D.MemDev, +fs: S.Ext2Fs) -> List<&2, String>:
  match r:
    case Done{i}:
      Ext2WDrv.walk(Nat.add(S.Ext2Fs.inodes_count(fs), 1n), Ext2WWalk{Nil{}, [Ext2WDir{B.Octets.empty(), i}]}, d, fs)
    case Fail{e}:
      ["t root err " ++ E.Ext2Error.kind(e)]

def Ext2WDrv.print_all(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{x, t}:
      do IO<Unit>:
        IO.print(x)
        Ext2WDrv.print_all(t)

# the tree read back through a fresh open of the result
def Ext2WDrv.reopened(r: Result<&2, &2, E.Ext2Error, S.Ext2Fs>, +d: D.MemDev) -> IO(Unit):
  match r:
    case Done{+fs}:
      Ext2WDrv.print_all(Ext2WDrv.tree(X.Ext2.root(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs), d, fs))
    case Fail{+e}:
      IO.print("t reopen err " ++ Ext2WDrv.err(e))

# A case

def Ext2WDrv.opened(r: Result<&2, &2, E.Ext2Error, S.Ext2Fs>, +d: D.MemDev, +wo: WO.Ext2WriteOptions, steps: List<&2, Ext2WStep>, +count: Nat, +opts: O.Ext2Options) -> IO(Unit):
  match r:
    case Done{+fs}:
      do IO<Unit>:
        +d2 : D.MemDev <- Ext2WDrv.steps(steps, d, fs, wo, 0n)
        Ext2WDrv.reopened(X.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, opts), d2)
        IO.print("image")
        W.Ext2WImg.dump(count, d2, 0n)
        IO.print("end")
    case Fail{+e}:
      do IO<Unit>:
        IO.print("open err " ++ Ext2WDrv.err(e))
        IO.print("end")

def Ext2WDrv.made(r: Result<&2, &2, E.Ext2Error, D.MemDev>, +wo: WO.Ext2WriteOptions, steps: List<&2, Ext2WStep>, +count: Nat, +opts: O.Ext2Options) -> IO(Unit):
  match r:
    case Done{+d}:
      do IO<Unit>:
        IO.print("mkfs ok")
        Ext2WDrv.opened(X.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, opts), d, wo, steps, count, opts)
    case Fail{+e}:
      do IO<Unit>:
        IO.print("mkfs err " ++ Ext2WDrv.err(e))
        IO.print("end")

def Ext2WCase.run(c: Ext2WCase) -> IO(Unit):
  match c:
    case Ext2WCase{name, Ext2WFile{path, nz}, +bs, +count, +opts, +wo, steps}:
      do IO<Unit>:
        +d : D.MemDev <- W.Ext2WImg.load(path, bs, count, nz)
        IO.print("== " ++ name)
        Ext2WDrv.opened(X.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, opts), d, wo, steps, count, opts)
    case Ext2WCase{name, Ext2WMkfs{mo}, +bs, +count, +opts, +wo, steps}:
      do IO<Unit>:
        IO.print("== " ++ name)
        Ext2WDrv.made(MK.Ext2Mkfs.make(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, D.MemDev.blank(bs, count), mo), wo, steps, count, opts)

def Ext2WCase.run_all(cs: List<&2, Ext2WCase>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{c, t}:
      do IO<Unit>:
        Ext2WCase.run(c)
        Ext2WCase.run_all(t)

# a UUID from 16 bytes in hex
def Ext2WDrv.uuid(s: String) -> U.Uuid:
  Maybe.default(&2, U.Uuid, U.Uuid.from_bytes_at(Ext2WDrv.hx(s), 0n), U.Uuid.nil())
