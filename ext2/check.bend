import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../crc/crc.bend as C
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./options.bend as O
import ./super.bend as S
import ./group.bend as G
import ./inode.bend as N
import ./file.bend as FL
import ./dir.bend as DR
import ./ext2.bend as X
import ./sample.bend as SM

# The sample image (sample.bend: ext4 with metadata_csum, made by mke2fs):
#   /hello.txt (16, "Hello, ext4!\n"), /docs (12), /docs/notes.txt (15,
#   5000 bytes), /docs/empty (13), /docs/long-link (14, 84 bytes, slow),
#   /sparse (18, 20100 bytes, two blocks and a hole), /link (17, fast, to
#   hello.txt), /up (19, fast, to docs)

def Ext2Check.p(s: String) -> B.Octets:
  B.Octets.of_string(s)

def Ext2Check.err(e: E.Ext2Error) -> String:
  "err " ++ E.Ext2Error.kind(e)

def Ext2Check.ents(es: List<&2, DR.Ext2Dirent>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{+e, t}:
      " " ++ B.Octets.to_string(DR.Ext2Dirent.name(e)) ++ ":" ++ U32.show(DR.Ext2Dirent.inode(e)) ++ ":" ++ U32.show(DR.Ext2Dirent.file_type(e)) ++ Ext2Check.ents(t)

def Ext2Check.ls(r: Result<&2, &2, E.Ext2Error, List<&2, DR.Ext2Dirent>>) -> String:
  match r:
    case Done{es}:
      "ls" ++ Ext2Check.ents(es)
    case Fail{e}:
      Ext2Check.err(e)

def Ext2Check.ino(r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      Nat.show(N.Ext2Inode.number_of(i)) ++ " " ++ N.Ext2Kind.show(N.Ext2Inode.kind(i)) ++ " " ++ W.W64.show(N.Ext2Inode.size(i))
    case Fail{e}:
      Ext2Check.err(e)

def Ext2Check.text(r: Result<&2, &2, E.Ext2Error, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      Ext2Check.err(e)

def Ext2Check.hex(r: Result<&2, &2, E.Ext2Error, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      Ext2Check.err(e)

def Ext2Check.blk(r: Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>) -> String:
  match r:
    case Done{Some{b}}:
      Nat.show(b)
    case Done{None{}}:
      "hole"
    case Fail{e}:
      Ext2Check.err(e)

# a file streamed a block at a time: blocks, bytes, CRC-32
def Ext2Check.stream.go(fuel: Nat, ch: Result<&2, &2, E.Ext2Error, FL.Ext2Chunk>, +d: D.MemDev, +fs: S.Ext2Fs, c: U32, n: Nat, len: Nat) -> String:
  match fuel ch:
    case 0n _:
      "fuel"
    case _ Fail{e}:
      Ext2Check.err(e)
    case 1n+f Done{FL.Ext2Eof{}}:
      Nat.show(n) ++ " blocks, " ++ Nat.show(len) ++ " bytes, crc32 " ++ U32.show(C.Crc32Spec.finish(C.crc32.spec(), c))
    case 1n+f Done{FL.Ext2Piece{+o, r}}:
      Ext2Check.stream.go(f, FL.Ext2File.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, r), d, fs, C.Crc32Spec.update(C.crc32.spec(), c, o), Nat.add(n, 1n), Nat.add(len, B.Octets.len(o)))

def Ext2Check.stream(+d: D.MemDev, +fs: S.Ext2Fs, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      Ext2Check.stream.go(Nat.add(FL.Ext2File.blocks_needed(fs, i), 1n), FL.Ext2File.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, FL.Ext2File.start(i)), d, fs, C.Crc32Spec.start(C.crc32.spec()), 0n, 0n)
    case Fail{e}:
      Ext2Check.err(e)

def Ext2Check.bmap(+d: D.MemDev, +fs: S.Ext2Fs, +l: Nat, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      Ext2Check.blk(FL.Ext2File.map(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, i, l))
    case Fail{e}:
      Ext2Check.err(e)

def Ext2Check.range(+d: D.MemDev, +fs: S.Ext2Fs, +off: Nat, +len: Nat, r: Result<&2, &2, E.Ext2Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      Ext2Check.hex(FL.Ext2File.read_range(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, i, off, len))
    case Fail{e}:
      Ext2Check.err(e)

def Ext2Check.look(+d: D.MemDev, +fs: S.Ext2Fs, +hops: Nat, path: String) -> String:
  Ext2Check.ino(X.Ext2.lookup(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, S.Ext2Fs.with_symlink_hops(fs, hops), Ext2Check.p(path)))

def Ext2Check.lookup(+d: D.MemDev, +fs: S.Ext2Fs, path: String) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  X.Ext2.lookup(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext2Check.p(path))

def Ext2Check.tests(+d: D.MemDev, +fs: S.Ext2Fs) -> List<String>:
  [Ext2Check.ls(X.Ext2.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext2Check.p("/"))),
   Ext2Check.ls(X.Ext2.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext2Check.p("/docs"))),
   Ext2Check.text(X.Ext2.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext2Check.p("/hello.txt"))),
   Ext2Check.stream(d, fs, Ext2Check.lookup(d, fs, "/docs/notes.txt")),
   Ext2Check.stream(d, fs, Ext2Check.lookup(d, fs, "/docs/empty")),
   Ext2Check.bmap(d, fs, 0n, Ext2Check.lookup(d, fs, "/sparse")) ++ " " ++ Ext2Check.bmap(d, fs, 1n, Ext2Check.lookup(d, fs, "/sparse")) ++ " " ++ Ext2Check.bmap(d, fs, 19n, Ext2Check.lookup(d, fs, "/sparse")) ++ " " ++ Ext2Check.bmap(d, fs, 20n, Ext2Check.lookup(d, fs, "/sparse")),
   Ext2Check.range(d, fs, 19996n, 12n, Ext2Check.lookup(d, fs, "/sparse")),
   Ext2Check.stream(d, fs, Ext2Check.lookup(d, fs, "/sparse")),
   Ext2Check.text(X.Ext2.readlink(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext2Check.p("/link"))),
   Ext2Check.text(X.Ext2.readlink(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext2Check.p("/docs/long-link"))),
   Ext2Check.look(d, fs, 0n, "/link") ++ ", " ++ Ext2Check.look(d, fs, 1n, "/link"),
   Ext2Check.look(d, fs, 0n, "/up/notes.txt") ++ ", " ++ Ext2Check.look(d, fs, 8n, "/up/notes.txt"),
   Ext2Check.look(d, fs, 8n, "/docs/long-link") ++ ", " ++ Ext2Check.look(d, fs, 8n, "/docs/../up/../hello.txt"),
   Ext2Check.look(d, fs, 0n, "/nope") ++ ", " ++ Ext2Check.look(d, fs, 0n, "/hello.txt/x"),
   Ext2Check.text(X.Ext2.readlink(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext2Check.p("/hello.txt")))]

def Ext2Check.opened(r: Result<&2, &2, E.Ext2Error, S.Ext2Fs>, +d: D.MemDev) -> List<String>:
  match r:
    case Done{+fs}:
      Con{"open " ++ Nat.show(S.Ext2Fs.block_size(fs)) ++ " " ++ Nat.show(S.Ext2Fs.blocks(fs)) ++ " " ++ Nat.show(S.Ext2Fs.groups(fs)) ++ " " ++ S.Ext2Super.label(S.Ext2Fs.sb(fs)), Ext2Check.tests(d, fs)}
    case Fail{e}:
      ["open " ++ Ext2Check.err(e)]

# Corruptions: one byte of one block changed

def Ext2Check.poke.block(r: Result<&2, &2, D.DevError, B.Octets>, +off: Nat, v: U32) -> B.Octets:
  match r:
    case Done{+o}:
      B.Octets.append(B.Octets.take(off, o), B.Octets.cons(v, B.Octets.drop(Nat.add(off, 1n), o)))
    case Fail{e}:
      B.Octets.empty()

def Ext2Check.poke(+d: D.MemDev, +n: Nat, +off: Nat, v: U32) -> D.MemDev:
  D.MemDev.update(d, n, Ext2Check.poke.block(D.MemDev.read_block(d, n), off, v))

def Ext2Check.open.kind(r: Result<&2, &2, E.Ext2Error, S.Ext2Fs>) -> String:
  match r:
    case Done{fs}:
      "open ok"
    case Fail{E.Ext2Unsupported{f}}:
      "open err Ext2Unsupported " ++ f
    case Fail{e}:
      "open " ++ Ext2Check.err(e)

def Ext2Check.open(+d: D.MemDev, +o: O.Ext2Options) -> String:
  Ext2Check.open.kind(X.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, o))

def Ext2Check.table(r: Result<&2, &2, E.Ext2Error, G.Ext2Group>) -> Nat:
  match r:
    case Done{g}:
      G.Ext2Group.inode_table(g)
    case Fail{e}:
      0n

def Ext2Check.corrupt(+d: D.MemDev, r: Result<&2, &2, E.Ext2Error, S.Ext2Fs>) -> List<String>:
  match r:
    case Done{+fs}:
      +it = Ext2Check.table(G.Ext2Group.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, 0n))
      +rootblk = Maybe.default(&2, Nat, Result.default(&2, &2, E.Ext2Error, Maybe<&2, Nat>, Result.bind(&2, &2, E.Ext2Error, N.Ext2Inode, Maybe<&2, Nat>, X.Ext2.root(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs), i => FL.Ext2File.map(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, i, 0n)), None{}), 0n)
      +noverify = O.Ext2Options.with_verify(O.Ext2Options.default(), False{})
      +bad = Ext2Check.poke(d, rootblk, 4n, 13)
      [Ext2Check.open(Ext2Check.poke(d, 1n, 56n, 0), O.Ext2Options.default()),
       Ext2Check.open(Ext2Check.poke(d, 1n, 120n, 88), O.Ext2Options.default()),
       Ext2Check.open(Ext2Check.poke(d, 1n, 120n, 88), noverify),
       Ext2Check.open(Ext2Check.poke(d, 1n, 97n, 130), O.Ext2Options.default()),
       Ext2Check.open(d, O.Ext2Options.with_incompat(O.Ext2Options.default(), O.Ext2Options.ext2_incompat())),
       Ext2Check.ino(N.Ext2Inode.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, Ext2Check.poke(d, Nat.add(it, 3n), 784n, 1), fs, 16n)),
       Ext2Check.ls(X.Ext2.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, Ext2Check.poke(d, rootblk, 9n, 1), fs, Ext2Check.p("/"))),
       Ext2Check.ls(Result.bind(&2, &2, E.Ext2Error, S.Ext2Fs, List<&2, DR.Ext2Dirent>, X.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, bad, noverify), f2 => X.Ext2.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, bad, f2, Ext2Check.p("/"))))]
    case Fail{e}:
      ["open " ++ Ext2Check.err(e)]

def Ext2Check.print_all(xs: List<String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{x, t}:
      do IO<Unit>:
        IO.print(x)
        Ext2Check.print_all(t)

def main() -> IO(Unit):
  +d = SM.Ext2Sample.dev()
  do IO<Unit>:
    Ext2Check.print_all(Ext2Check.opened(X.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, O.Ext2Options.default()), d))
    Ext2Check.print_all(Ext2Check.corrupt(d, X.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, O.Ext2Options.default())))

#|open 1024 256 1 sample
#|ls .:2:2 ..:2:2 lost+found:11:2 docs:12:2 hello.txt:16:1 link:17:7 sparse:18:1 up:19:7
#|ls .:12:2 ..:2:2 empty:13:1 long-link:14:7 notes.txt:15:1
#|Hello, ext4!
#|
#|5 blocks, 5000 bytes, crc32 1008702470
#|0 blocks, 0 bytes, crc32 0
#|28 hole 29 err Ext2PastEnd
#|000000007461696c7461696c
#|20 blocks, 20100 bytes, crc32 4079291647
#|hello.txt
#|../../../../../../../../../../../../../../../../../../../../../../../../../hello.txt
#|17 symlink 9, 16 file 13
#|err Ext2SymlinkInPath, 15 file 5000
#|16 file 13, 16 file 13
#|err Ext2NotFound, err Ext2NotDir
#|err Ext2NotSymlink
#|open err Ext2BadMagic
#|open err Ext2BadSuperCsum
#|open ok
#|open err Ext2Unsupported inline_data
#|open err Ext2Unsupported extent
#|err Ext2BadInodeCsum
#|err Ext2BadDirCsum
#|err Ext2BadDirent
