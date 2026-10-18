# The writing test's program: it reads the cases wgen.py wrote (a text file
# named on the command line, one directive a line, its first word a letter)
# and runs each through wdriver.bend's Ext2WCase.run as soon as its E line
# is read. Built once, run once, whatever the cases.
#
#   C NAME                          a case
#   F PATH BS COUNT                 its image file; Z N N ... lines list its
#                                   non-zero blocks
#   K PROFILE BLOCKS LOG ISZ RATIO BPG TIME UUIDHEX BS COUNT
#                                   or a mkfs on a blank device
#   W CHECK ALLOC CSUM EXTENTS TIME the write options (first letters)
#   c PATH MODE | m PATH MODE | s PATH TARGET | l TARGET PATH | u PATH |
#   r PATH | n FROM TO | w PATH OFF LEN SEED | a PATH LEN SEED |
#   t PATH SIZE | f                 its steps (paths and targets in hex)
#   E                               the end of the case: run it
import Base
import ../../bytes/bytes.bend as B
import ../../uuid/uuid.bend as U
import ../options.bend as O
import ../wopts.bend as WO
import ../ops.bend as P
import ../mkfs.bend as MK
import ./wdriver.bend as R

# Lines and words

def Ext2WMain.flush(cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cur:
    case Nil{}:
      acc
    case Con{h, t}:
      Con{List.reverse(&2, U32, Con{h, t}), acc}

def Ext2WMain.is_sep(xs: List<&2, U32>, +sep: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      U32.is_eq(x, sep)

def Ext2WMain.split.go(xs: List<&2, U32>, hit: Bool, +sep: U32, cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs hit:
    case Nil{} _:
      List.reverse(&2, List<&2, U32>, Ext2WMain.flush(cur, acc))
    case Con{x, +t} True{}:
      Ext2WMain.split.go(t, Ext2WMain.is_sep(t, sep), sep, Nil{}, Ext2WMain.flush(cur, acc))
    case Con{x, +t} False{}:
      Ext2WMain.split.go(t, Ext2WMain.is_sep(t, sep), sep, Con{x, cur}, acc)

# the pieces of xs between the separators (empty ones dropped)
def Ext2WMain.split(+xs: List<&2, U32>, +sep: U32) -> List<&2, List<&2, U32>>:
  Ext2WMain.split.go(xs, Ext2WMain.is_sep(xs, sep), sep, Nil{}, Nil{})

def Ext2WMain.nat.go(xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      Ext2WMain.nat.go(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(x, 48))))

def Ext2WMain.nat(xs: List<&2, U32>) -> Nat:
  Ext2WMain.nat.go(xs, 0n)

def Ext2WMain.u32(xs: List<&2, U32>) -> U32:
  U32.from_nat(Ext2WMain.nat(xs))

def Ext2WMain.hex(xs: List<&2, U32>) -> B.Octets:
  match xs:
    case Con{45, Nil{}}:
      B.Octets.empty()
    case _:
      R.Ext2WDrv.hx(B.to_string(xs))

def Ext2WMain.first(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      x

def Ext2WMain.at(xs: List<&2, U32>, n: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, xs, n), 0)

# What a line says

type Ext2WLine is Data:
  Ext2WLCase{name: String}
  Ext2WLFile{path: String, bs: Nat, count: Nat}
  Ext2WLNz{blocks: List<&2, Nat>}
  Ext2WLMkfs{opts: MK.Ext2MkfsOptions, bs: Nat, count: Nat}
  Ext2WLWo{wo: WO.Ext2WriteOptions}
  Ext2WLStep{step: R.Ext2WStep}
  Ext2WLEnd{}
  Ext2WLBad{}

def Ext2WMain.nats(ws: List<&2, List<&2, U32>>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{w, t}:
      Ext2WMain.nats(t, Con{Ext2WMain.nat(w), acc})

def Ext2WMain.check(c: U32) -> WO.Ext2CheckLevel:
  match c:
    case 110:
      WO.Ext2CheckNone{}
    case 102:
      WO.Ext2CheckFull{}
    case _:
      WO.Ext2CheckLocal{}

def Ext2WMain.alloc(c: U32) -> WO.Ext2AllocPolicy:
  match c:
    case 102:
      WO.Ext2AllocPolicy.first_fit()
    case _:
      WO.Ext2AllocPolicy.default()

def Ext2WMain.csum(c: U32) -> WO.Ext2CsumMode:
  match c:
    case 114:
      WO.Ext2CsumRefuse{}
    case _:
      WO.Ext2CsumUpdate{}

def Ext2WMain.wo(ws: List<&2, List<&2, U32>>) -> Ext2WLine:
  match ws:
    case Con{ck, Con{al, Con{cs, Con{ex, Con{tm, t}}}}}:
      +w0 = WO.Ext2WriteOptions.with_alloc(WO.Ext2WriteOptions.with_check(WO.Ext2WriteOptions.default(), Ext2WMain.check(Ext2WMain.first(ck))), Ext2WMain.alloc(Ext2WMain.first(al)))
      Ext2WLWo{WO.Ext2WriteOptions.with_time(WO.Ext2WriteOptions.with_extents(WO.Ext2WriteOptions.with_csum(w0, Ext2WMain.csum(Ext2WMain.first(cs))), U32.is_eq(Ext2WMain.first(ex), 49)), Ext2WMain.u32(tm))}
    case _:
      Ext2WLBad{}

def Ext2WMain.profile.pick(four: Bool, +blocks: Nat, +u: U.Uuid) -> MK.Ext2MkfsOptions:
  match four:
    case True{}:
      MK.Ext2MkfsOptions.ext4(blocks, u)
    case False{}:
      MK.Ext2MkfsOptions.ext2(blocks, u)

def Ext2WMain.profile(+p: List<&2, U32>, +blocks: Nat, +u: B.Octets) -> MK.Ext2MkfsOptions:
  Ext2WMain.profile.pick(U32.is_eq(Ext2WMain.at(p, 3n), 52), blocks, R.Ext2WDrv.uuid(B.Octets.hex(u)))

def Ext2WMain.mkfs(ws: List<&2, List<&2, U32>>) -> Ext2WLine:
  match ws:
    case Con{+pr, Con{bl, Con{lg, Con{isz, Con{ra, Con{bpg, Con{tm, Con{uu, Con{bs, Con{cnt, t}}}}}}}}}}:
      +o = MK.Ext2MkfsOptions.with_inodes(MK.Ext2MkfsOptions.with_block(Ext2WMain.profile(pr, Ext2WMain.nat(bl), Ext2WMain.hex(uu)), Ext2WMain.nat(lg)), Ext2WMain.nat(isz), Ext2WMain.nat(ra))
      Ext2WLMkfs{MK.Ext2MkfsOptions.with_time(MK.Ext2MkfsOptions.with_group(o, Ext2WMain.nat(bpg)), Ext2WMain.u32(tm)), Ext2WMain.nat(bs), Ext2WMain.nat(cnt)}
    case _:
      Ext2WLBad{}

def Ext2WMain.step(o: P.Ext2Op) -> Ext2WLine:
  Ext2WLStep{R.Ext2WOp{o}}

def Ext2WMain.op4(k: U32, a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>, d: List<&2, U32>) -> Ext2WLine:
  match k:
    case 119:
      Ext2WMain.step(P.Ext2OpWrite{Ext2WMain.hex(a), Ext2WMain.nat(b), R.Ext2WDrv.bytes(Ext2WMain.nat(c), Ext2WMain.u32(d))})
    case _:
      Ext2WLBad{}

def Ext2WMain.op3(k: U32, a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> Ext2WLine:
  match k:
    case 97:
      Ext2WMain.step(P.Ext2OpAppend{Ext2WMain.hex(a), R.Ext2WDrv.bytes(Ext2WMain.nat(b), Ext2WMain.u32(c))})
    case _:
      Ext2WLBad{}

def Ext2WMain.op2(k: U32, a: List<&2, U32>, b: List<&2, U32>) -> Ext2WLine:
  match k:
    case 99:
      Ext2WMain.step(P.Ext2OpCreate{Ext2WMain.hex(a), Ext2WMain.u32(b)})
    case 109:
      Ext2WMain.step(P.Ext2OpMkdir{Ext2WMain.hex(a), Ext2WMain.u32(b)})
    case 115:
      Ext2WMain.step(P.Ext2OpSymlink{Ext2WMain.hex(a), Ext2WMain.hex(b)})
    case 108:
      Ext2WMain.step(P.Ext2OpLink{Ext2WMain.hex(a), Ext2WMain.hex(b)})
    case 110:
      Ext2WMain.step(P.Ext2OpRename{Ext2WMain.hex(a), Ext2WMain.hex(b)})
    case 116:
      Ext2WMain.step(P.Ext2OpTruncate{Ext2WMain.hex(a), Ext2WMain.nat(b)})
    case _:
      Ext2WLBad{}

def Ext2WMain.op1(k: U32, a: List<&2, U32>) -> Ext2WLine:
  match k:
    case 117:
      Ext2WMain.step(P.Ext2OpUnlink{Ext2WMain.hex(a)})
    case 114:
      Ext2WMain.step(P.Ext2OpRmdir{Ext2WMain.hex(a)})
    case _:
      Ext2WLBad{}

def Ext2WMain.op(+k: U32, ws: List<&2, List<&2, U32>>) -> Ext2WLine:
  match ws:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Ext2WMain.op4(k, a, b, c, d)
    case Con{a, Con{b, Con{c, Nil{}}}}:
      Ext2WMain.op3(k, a, b, c)
    case Con{a, Con{b, Nil{}}}:
      Ext2WMain.op2(k, a, b)
    case Con{a, Nil{}}:
      Ext2WMain.op1(k, a)
    case _:
      Ext2WLStep{R.Ext2WFsck{}}

def Ext2WMain.file(ws: List<&2, List<&2, U32>>) -> Ext2WLine:
  match ws:
    case Con{p, Con{bs, Con{c, t}}}:
      Ext2WLFile{B.to_string(p), Ext2WMain.nat(bs), Ext2WMain.nat(c)}
    case _:
      Ext2WLBad{}

def Ext2WMain.line.key(+k: U32, args: List<&2, List<&2, U32>>) -> Ext2WLine:
  match k:
    case 67:
      Ext2WLCase{B.to_string(List.concat(&2, U32, args))}
    case 70:
      Ext2WMain.file(args)
    case 90:
      Ext2WLNz{Ext2WMain.nats(args, Nil{})}
    case 75:
      Ext2WMain.mkfs(args)
    case 87:
      Ext2WMain.wo(args)
    case 69:
      Ext2WLEnd{}
    case _:
      Ext2WMain.op(k, args)

def Ext2WMain.line(ws: List<&2, List<&2, U32>>) -> Ext2WLine:
  match ws:
    case Nil{}:
      Ext2WLBad{}
    case Con{key, args}:
      Ext2WMain.line.key(Ext2WMain.first(key), args)

# Building a case from its lines

type Ext2WBuild is Data:
  Ext2WBuild{name: String, src: R.Ext2WSource, bs: Nat, count: Nat, wo: WO.Ext2WriteOptions, nz: List<&2, Nat>, steps: List<&2, R.Ext2WStep>}

def Ext2WMain.empty() -> Ext2WBuild:
  Ext2WBuild{"", R.Ext2WFile{"", Nil{}}, 1024n, 0n, WO.Ext2WriteOptions.default(), Nil{}, Nil{}}

type Ext2WAct is Data:
  Ext2WGo{b: Ext2WBuild}
  Ext2WRun{c: R.Ext2WCase, b: Ext2WBuild}

def Ext2WMain.finish(src: R.Ext2WSource, nz: List<&2, Nat>) -> R.Ext2WSource:
  match src:
    case R.Ext2WFile{p, x}:
      R.Ext2WFile{p, List.reverse(&2, Nat, nz)}
    case R.Ext2WMkfs{o}:
      R.Ext2WMkfs{o}

def Ext2WMain.act(l: Ext2WLine, b: Ext2WBuild) -> Ext2WAct:
  match l b:
    case Ext2WLCase{n} _:
      Ext2WGo{Ext2WBuild{n, R.Ext2WFile{"", Nil{}}, 1024n, 0n, WO.Ext2WriteOptions.default(), Nil{}, Nil{}}}
    case Ext2WLFile{p, bs, c} Ext2WBuild{n, s, x, y, wo, nz, st}:
      Ext2WGo{Ext2WBuild{n, R.Ext2WFile{p, Nil{}}, bs, c, wo, nz, st}}
    case Ext2WLNz{ks} Ext2WBuild{n, s, bs, c, wo, nz, st}:
      Ext2WGo{Ext2WBuild{n, s, bs, c, wo, List.reverse.go(&2, Nat, ks, nz), st}}
    case Ext2WLMkfs{o, bs, c} Ext2WBuild{n, s, x, y, wo, nz, st}:
      Ext2WGo{Ext2WBuild{n, R.Ext2WMkfs{o}, bs, c, wo, nz, st}}
    case Ext2WLWo{w} Ext2WBuild{n, s, bs, c, wo, nz, st}:
      Ext2WGo{Ext2WBuild{n, s, bs, c, w, nz, st}}
    case Ext2WLStep{x} Ext2WBuild{n, s, bs, c, wo, nz, st}:
      Ext2WGo{Ext2WBuild{n, s, bs, c, wo, nz, Con{x, st}}}
    case Ext2WLEnd{} Ext2WBuild{n, s, bs, c, wo, nz, st}:
      Ext2WRun{R.Ext2WCase{n, Ext2WMain.finish(s, nz), bs, c, O.Ext2Options.default(), wo, List.reverse(&2, R.Ext2WStep, st)}, Ext2WMain.empty()}
    case Ext2WLBad{} _:
      Ext2WGo{b}

def Ext2WMain.go(ls: List<&2, List<&2, U32>>, a: Ext2WAct) -> IO(Unit):
  match ls a:
    case Nil{} Ext2WRun{c, b}:
      R.Ext2WCase.run(c)
    case Nil{} Ext2WGo{b}:
      IO.pure(Unit, Unit{})
    case Con{l, t} Ext2WRun{c, b}:
      do IO<Unit>:
        R.Ext2WCase.run(c)
        Ext2WMain.go(t, Ext2WMain.act(Ext2WMain.line(Ext2WMain.split(l, 32)), b))
    case Con{l, t} Ext2WGo{b}:
      Ext2WMain.go(t, Ext2WMain.act(Ext2WMain.line(Ext2WMain.split(l, 32)), b))

def Ext2WMain.size(p: File & Result<&1, &1, U32 & String, U32>) -> IO(File & U32):
  (f, r) = p
  IO.pure(File & U32, (f, Result.default(&1, &1, U32 & String, U32, r, 0)))

def Ext2WMain.close(q: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (f, r) = q
  do IO<List<&2, U32>>:
    File.close(f)
    return Result.default(&1, &1, U32 & String, List<&2, U32>, r, Nil{})

def Ext2WMain.read(p: File & U32) -> IO(List<&2, U32>):
  (f, n) = p
  do IO<List<&2, U32>>:
    q : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
    Ext2WMain.close(q)

def Ext2WMain.path(args: List<String>) -> String:
  match args:
    case Con{prog, Con{p, t}}:
      p
    case _:
      "cases.txt"

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    f : File <- IO.try(File, File.open(Ext2WMain.path(args), "r"))
    sz : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    fz : File & U32 <- Ext2WMain.size(sz)
    xs : List<&2, U32> <- Ext2WMain.read(fz)
    Ext2WMain.go(Ext2WMain.split(xs, 10), Ext2WGo{Ext2WMain.empty()})
