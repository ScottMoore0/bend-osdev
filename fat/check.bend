import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T
import ./dirent.bend as R
import ./dir.bend as Q
import ./file.bend as F
import ./fat.bend as M
import ../blockdev/imgdev.bend as G
import ./format.bend as K
import ./write.bend as X

# A FAT12 volume built by hand with the package's writers: 512-byte
# sectors, one sector per cluster, one reserved sector, one FAT of one
# sector, a root directory of 16 entries, 20 clusters (23 sectors).
#   root: README.TXT (600 bytes, clusters 2 and 4: fragmented), EFI/
#         (cluster 3), "Long File Name.txt" (cluster 7)
#   EFI/BOOT/ (cluster 5) holds BOOTX64.EFI (cluster 6)

# an entry of the FAT: cluster n holds v
type CheckLink is Data:
  CheckLink{n: U32, v: U32}

def chk.bpb(bps: U32) -> P.FatBpb:
  P.FatBpb{B.Octets.of_list([235, 60, 144]), B.Octets.of_string("BENDOSDV"), bps, 1, 1, 1, 16, 23, 248, 1, 63, 255, 0, 0, 0, 0, 0, 0, 0, 0, 43605}

def chk.boot(bps: U32) -> B.Octets:
  P.FatBpb.build(P.Fat12{}, chk.bpb(bps), P.FatBootExt{128, 41, 305419896, B.Octets.of_string("CHECK VOL"), B.Octets.of_string("FAT12")})

def chk.set_all(es: List<&2, CheckLink>, fat: B.Octets) -> B.Octets:
  match es:
    case Nil{}:
      fat
    case Con{CheckLink{n, v}, t}:
      chk.set_all(t, T.FatTable.set_in(P.Fat12{}, fat, n, v))

def chk.links() -> List<&2, CheckLink>:
  [CheckLink{0, 4088}, CheckLink{1, 4095}, CheckLink{2, 4}, CheckLink{3, 4095}, CheckLink{4, 4095}, CheckLink{5, 4095}, CheckLink{6, 4095}, CheckLink{7, 4095}]

def chk.fat(es: List<&2, CheckLink>) -> B.Octets:
  chk.set_all(es, B.Octets.zeros(512n))

def chk.entry(name: String, attr: U32, cluster: U32, size: U32) -> R.FatDirent:
  R.FatDirent{B.Octets.of_string(name), attr, 0, 0, 25692, 22621, 22621, 0, 25692, 22621, cluster, size}

def chk.sector(o: B.Octets) -> B.Octets:
  B.Octets.take(512n, B.Octets.append(o, B.Octets.zeros(512n)))

def chk.lfns(es: List<&2, R.FatLfn>) -> B.Octets:
  match es:
    case Nil{}:
      B.Octets.empty()
    case Con{h, t}:
      B.Octets.append(R.FatLfn.encode(h), chk.lfns(t))

def chk.long_name() -> String:
  "Long File Name.txt"

def chk.root() -> B.Octets:
  chk.sector(B.Octets.concat([R.FatDirent.encode(chk.entry("README  TXT", 32, 2, 600)), R.FatDirent.encode(chk.entry("EFI        ", 16, 3, 0)), chk.lfns(R.FatLfn.build(B.Octets.of_string("LONGFI~1TXT"), R.FatName.units(chk.long_name()))), R.FatDirent.encode(chk.entry("LONGFI~1TXT", 32, 7, 23))]))

def chk.dir(self: U32, parent: U32, e: R.FatDirent) -> B.Octets:
  chk.sector(B.Octets.concat([R.FatDirent.encode(chk.entry(".          ", 16, self, 0)), R.FatDirent.encode(chk.entry("..         ", 16, parent, 0)), R.FatDirent.encode(e)]))

def chk.readme() -> B.Octets:
  B.Octets.concat([B.Octets.of_string("FAT reading in Bend. "), B.Octets.zeros(500n), B.Octets.of_string("The end of README.TXT, in the second of its clusters (cluster 4, after 3)!!!!!!")])

def chk.image(es: List<&2, CheckLink>, bps: U32) -> D.MemDev:
  D.MemDev.of_octets(512n, B.Octets.concat([chk.boot(bps), chk.fat(es), chk.root(), B.Octets.take(512n, chk.readme()), chk.dir(3, 0, chk.entry("BOOT       ", 16, 5, 0)), chk.sector(B.Octets.drop(512n, chk.readme())), chk.dir(5, 3, chk.entry("BOOTX64 EFI", 32, 6, 18)), chk.sector(B.Octets.of_string("BOOTX64 says hello")), chk.sector(B.Octets.of_string("a file with a long name")), B.Octets.zeros(8192n)]))

def chk.dev() -> D.MemDev:
  chk.image(chk.links(), 512)

# Showing results

def chk.err(e: E.FatError) -> String:
  "error: " ++ E.FatError.show(e)

def chk.show_mount(r: Result<&2, &2, E.FatError, M.FatFs>) -> String:
  match r:
    case Done{+fs}:
      P.FatType.show(M.FatFs.kind(fs)) ++ ", " ++ U32.show(P.FatVolume.clusters(M.FatFs.volume(fs))) ++ " clusters"
    case Fail{e}:
      chk.err(e)

def chk.kind(dir: Bool) -> String:
  match dir:
    case True{}:
      "/"
    case False{}:
      ""

def chk.names(ns: List<&2, Q.FatNode>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{+n, Nil{}}:
      Q.FatNode.name(n) ++ chk.kind(Q.FatNode.is_dir(n))
    case Con{+n, t}:
      Q.FatNode.name(n) ++ chk.kind(Q.FatNode.is_dir(n)) ++ ", " ++ chk.names(t)

def chk.show_list(r: Result<&2, &2, E.FatError, List<&2, Q.FatNode>>) -> String:
  match r:
    case Done{ns}:
      chk.names(ns)
    case Fail{e}:
      chk.err(e)

def chk.show_text(r: Result<&2, &2, E.FatError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      chk.err(e)

def chk.show_len(r: Result<&2, &2, E.FatError, B.Octets>) -> String:
  match r:
    case Done{o}:
      Nat.show(B.Octets.len(o)) ++ " bytes"
    case Fail{e}:
      chk.err(e)

def chk.show_stat(r: Result<&2, &2, E.FatError, Q.FatPath>) -> String:
  match r:
    case Done{Q.FatPathRoot{}}:
      "the root"
    case Done{Q.FatPathNode{+n}}:
      Q.FatNode.name(n) ++ " (" ++ Q.FatNode.short_name(n) ++ "), " ++ U32.show(Q.FatNode.size(n)) ++ " bytes"
    case Fail{e}:
      chk.err(e)

def chk.show_walk(r: Result<&2, &2, E.FatError, List<&2, U32>>) -> String:
  match r:
    case Done{cs}:
      List.show(~&2, ~U32, ~U32.show, cs)
    case Fail{e}:
      chk.err(e)

# Operations on the image

def chk.mount(+d: D.MemDev) -> Result<&2, &2, E.FatError, M.FatFs>:
  M.Fat.mount(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, P.FatOptions.default())

def chk.ls(+d: D.MemDev, path: String) -> String:
  chk.show_list(do Result<&2, &2, E.FatError, List<&2, Q.FatNode>>:
    fs : M.FatFs <- chk.mount(d)
    M.Fat.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, path))

def chk.read(+d: D.MemDev, path: String, off: Nat, len: Nat) -> Result<&2, &2, E.FatError, B.Octets>:
  do Result<&2, &2, E.FatError, B.Octets>:
    fs : M.FatFs <- chk.mount(d)
    M.Fat.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, path, off, len)

def chk.stat(+d: D.MemDev, path: String) -> String:
  chk.show_stat(do Result<&2, &2, E.FatError, Q.FatPath>:
    fs : M.FatFs <- chk.mount(d)
    M.Fat.stat(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, path))

def chk.walk(+d: D.MemDev, c: U32) -> String:
  chk.show_walk(do Result<&2, &2, E.FatError, List<&2, U32>>:
    fs : M.FatFs <- chk.mount(d)
    T.FatChain.walk(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, M.FatFs.volume(fs), c))

# Streaming: the sizes of the pieces of a file

def chk.pieces.go(+d: D.MemDev, +fs: M.FatFs, fuel: Nat, r: Result<&2, &2, E.FatError, F.FatChunk>) -> String:
  match fuel:
    case 0n:
      "..."
    case 1n+p:
      match r:
        case Fail{e}:
          chk.err(e)
        case Done{F.FatChunk{o, None{}}}:
          Nat.show(B.Octets.len(o))
        case Done{F.FatChunk{o, Some{cur}}}:
          Nat.show(B.Octets.len(o)) ++ " + " ++ chk.pieces.go(d, fs, p, M.Fat.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, cur))

def chk.pieces.cursor(+d: D.MemDev, +fs: M.FatFs, r: Result<&2, &2, E.FatError, F.FatCursor>) -> String:
  match r:
    case Fail{e}:
      chk.err(e)
    case Done{cur}:
      chk.pieces.go(d, fs, 10n, M.Fat.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, cur))

def chk.pieces.open(+d: D.MemDev, +fs: M.FatFs, path: String) -> String:
  chk.pieces.cursor(d, fs, M.Fat.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, path))

def chk.pieces.mount(+d: D.MemDev, path: String, r: Result<&2, &2, E.FatError, M.FatFs>) -> String:
  match r:
    case Fail{e}:
      chk.err(e)
    case Done{+fs}:
      chk.pieces.open(d, fs, path)

def chk.pieces(+d: D.MemDev, path: String) -> String:
  chk.pieces.mount(d, path, chk.mount(d))

# A large volume, made up as it is read (so it costs no memory): FAT16,
# 512-byte sectors, one per cluster, one reserved sector, one FAT of 196
# sectors, a root directory of 16 entries, 50000 clusters, each linked to
# the next: one file, BIG.BIN, of 25,600,000 bytes from cluster 2. The device
# answers 2-byte blocks (so a FAT entry is one read): the boot sector, the
# FAT entries and the root entry, zeros elsewhere. Its chain is longer than
# the structural walk could follow (about 40,000 clusters).
type ChkBig is Data:
  ChkBig{boot: B.Octets, root: B.Octets}

def chk.big.bpb() -> P.FatBpb:
  P.FatBpb{B.Octets.of_list([235, 60, 144]), B.Octets.of_string("BENDOSDV"), 512, 1, 1, 1, 16, 50198, 248, 196, 63, 255, 0, 0, 0, 0, 0, 0, 0, 0, 43605}

def chk.big() -> ChkBig:
  ChkBig{P.FatBpb.build(P.Fat16{}, chk.big.bpb(), P.FatBootExt{128, 41, 1, B.Octets.of_string("BIG VOL"), B.Octets.of_string("FAT16")}), R.FatDirent.encode(chk.entry("BIG     BIN", 32, 2, 25600000))}

def ChkBig.block_size(d: ChkBig) -> Nat:
  2n

# the FAT entry of cluster k: the media and end marks, k + 1 up to the last
# cluster (50001), the end there, free after
def chk.big.entry.pick(low: Bool, more: Bool, last: Bool, +k: U32) -> U32:
  match low more last:
    case True{} _ _:
      U32.sub(65535, U32.mul(7, U32.sub(1, k)))
    case False{} True{} _:
      U32.add(k, 1)
    case False{} False{} True{}:
      65535
    case False{} False{} False{}:
      0

def chk.big.entry(+k: U32) -> U32:
  chk.big.entry.pick(U32.is_lt(k, 2), U32.is_lt(k, 50001), U32.is_eq(k, 50001), k)

def chk.big.read.go(boot: Bool, fat: Bool, root: Bool, d: ChkBig, +n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  match boot fat root d:
    case True{} _ _ ChkBig{b, r}:
      Done{B.Octets.slice(Nat.mul(n, 2n), 2n, b)}
    case False{} True{} _ _:
      Done{B.Octets.of_list(B.le16(chk.big.entry(U32.from_nat(Nat.sub(n, 256n)))))}
    case False{} False{} True{} ChkBig{b, r}:
      Done{B.Octets.slice(Nat.mul(Nat.sub(n, 50432n), 2n), 2n, r)}
    case False{} False{} False{} _:
      Done{B.Octets.zeros(2n)}

def chk.big.read(d: ChkBig, +n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  chk.big.read.go(Nat.is_lt(n, 256n), Nat.is_lt(n, 50432n), Nat.is_lt(n, 50448n), d, n)

def ChkBig.read_block(d: ChkBig, n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  chk.big.read(d, n)

def chk.big.count(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      chk.big.count(t, 1n+n)

def chk.big.show_walk(r: Result<&2, &2, E.FatError, List<&2, U32>>) -> String:
  match r:
    case Done{cs}:
      Nat.show(chk.big.count(cs, 0n)) ++ " clusters"
    case Fail{e}:
      chk.err(e)

# the walk of BIG.BIN's chain, and 100 KB of it near its end
def chk.big.run(+d: ChkBig) -> String:
  chk.big.show_walk(do Result<&2, &2, E.FatError, List<&2, U32>>:
    +fs : M.FatFs <- M.Fat.mount(~ChkBig, ~ChkBig.block_size, ~ChkBig.read_block, d, P.FatOptions.default())
    T.FatChain.walk(~ChkBig, ~ChkBig.block_size, ~ChkBig.read_block, d, M.FatFs.volume(fs), 2)) ++ ", " ++ chk.show_len(do Result<&2, &2, E.FatError, B.Octets>:
    +fs : M.FatFs <- M.Fat.mount(~ChkBig, ~ChkBig.block_size, ~ChkBig.read_block, d, P.FatOptions.default())
    M.Fat.read(~ChkBig, ~ChkBig.block_size, ~ChkBig.read_block, d, fs, "/big.bin", 25000000n, 102400n))

# Writing. A volume made by the package's format on a device, changed
# through the writer (write.bend), read back through the writer and through
# the reader. The devices are blockdev's array image (ImgDev, the owned
# interface) and a MemDev used through blockdev's adapters.

def cw.err(e: E.FatError) -> String:
  "error: " ++ E.FatError.show(e)

type CwOp is Data:
  CwMkdir{path: String}
  CwCreate{path: String}
  CwWrite{path: String, off: Nat, data: B.Octets}
  CwAppend{path: String, data: B.Octets}
  CwTrunc{path: String, size: Nat}
  CwUnlink{path: String}
  CwRmdir{path: String}
  CwRename{from: String, to: String}
  CwAttr{path: String, attr: U32}
  CwLs{path: String}
  CwRead{path: String}
  CwStat{path: String}

def cw.short(+n: Q.FatNode) -> String:
  Q.FatNode.name(n) ++ " (" ++ Q.FatNode.short_name(n) ++ ")" ++ chk.kind(Q.FatNode.is_dir(n))

def cw.names(ns: List<&2, Q.FatNode>) -> String:
  match ns:
    case Nil{}:
      "(empty)"
    case Con{+n, Nil{}}:
      cw.short(n)
    case Con{+n, t}:
      cw.short(n) ++ ", " ++ cw.names(t)

def cw.changed(r: G.ImgDev & Result<&2, &2, E.FatError, X.FatW>, +w0: X.FatW, k: G.ImgDev -> X.FatW -> String -> IO(G.ImgDev)) -> IO(G.ImgDev):
  (d, res) = r
  match res:
    case Done{+w}:
      k(d, w, "ok, " ++ Nat.show(X.FatW.free_clusters(w)) ++ " clusters free")
    case Fail{e}:
      k(d, w0, cw.err(e))

def cw.listed(r: G.ImgDev & Result<&2, &2, E.FatError, List<&2, Q.FatNode>>, k: G.ImgDev -> String -> IO(G.ImgDev)) -> IO(G.ImgDev):
  (d, res) = r
  match res:
    case Done{ns}:
      k(d, cw.names(ns))
    case Fail{e}:
      k(d, cw.err(e))

def cw.printable(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.and(U32.is_ge(h, 32), U32.is_lt(h, 127)), cw.printable(t))

def cw.text.pick(short: Bool, +o: B.Octets) -> String:
  match short:
    case True{}:
      B.Octets.to_string(o)
    case False{}:
      Nat.show(B.Octets.len(o)) ++ " bytes, ending " ++ B.Octets.hex(B.Octets.drop(Nat.sub(B.Octets.len(o), 6n), o))

# a file's bytes: as text when short and printable, else their count and
# the last few in hex
def cw.text(o: B.Octets) -> String:
  +x = o
  cw.text.pick(Bool.and(Nat.is_le(B.Octets.len(x), 80n), cw.printable(B.Octets.to_list(x))), x)

def cw.got(r: G.ImgDev & Result<&2, &2, E.FatError, B.Octets>, k: G.ImgDev -> String -> IO(G.ImgDev)) -> IO(G.ImgDev):
  (d, res) = r
  match res:
    case Done{o}:
      k(d, cw.text(o))
    case Fail{e}:
      k(d, cw.err(e))

def cw.stated(r: G.ImgDev & Result<&2, &2, E.FatError, Q.FatPath>, k: G.ImgDev -> String -> IO(G.ImgDev)) -> IO(G.ImgDev):
  (d, res) = r
  match res:
    case Done{Q.FatPathRoot{}}:
      k(d, "the root")
    case Done{Q.FatPathNode{+n}}:
      k(d, cw.short(n) ++ ", " ++ U32.show(Q.FatNode.size(n)) ++ " bytes, attributes " ++ U32.show(R.FatDirent.attr(Q.FatNode.entry(n))))
    case Fail{e}:
      k(d, cw.err(e))

def cw.say(+label: String, s: String) -> IO(Unit):
  IO.print(label ++ ": " ++ s)

# the operations run on an array image, one line each
def cw.run(ops: List<&2, CwOp>, d: G.ImgDev, +w: X.FatW) -> IO(G.ImgDev):
  match ops:
    case Nil{}:
      IO.pure(G.ImgDev, d)
    case Con{CwMkdir{+p}, t}:
      cw.changed(X.FatW.mkdir(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, p), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("mkdir " ++ p, s), u => cw.run(t, d2, w2)))
    case Con{CwCreate{+p}, t}:
      cw.changed(X.FatW.create(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, p), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("create " ++ p, s), u => cw.run(t, d2, w2)))
    case Con{CwWrite{+p, +off, o}, t}:
      cw.changed(X.FatW.write(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, p, off, o), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("write " ++ p ++ " at " ++ Nat.show(off), s), u => cw.run(t, d2, w2)))
    case Con{CwAppend{+p, o}, t}:
      cw.changed(X.FatW.append(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, p, o), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("append " ++ p, s), u => cw.run(t, d2, w2)))
    case Con{CwTrunc{+p, +n}, t}:
      cw.changed(X.FatW.truncate(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, p, n), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("truncate " ++ p ++ " to " ++ Nat.show(n), s), u => cw.run(t, d2, w2)))
    case Con{CwUnlink{+p}, t}:
      cw.changed(X.FatW.unlink(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, p), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("delete " ++ p, s), u => cw.run(t, d2, w2)))
    case Con{CwRmdir{+p}, t}:
      cw.changed(X.FatW.rmdir(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, p), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("rmdir " ++ p, s), u => cw.run(t, d2, w2)))
    case Con{CwRename{+a, +b}, t}:
      cw.changed(X.FatW.rename(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, a, b), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("rename " ++ a ++ " to " ++ b, s), u => cw.run(t, d2, w2)))
    case Con{CwAttr{+p, +a}, t}:
      cw.changed(X.FatW.set_attr(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, d, w, p, a), w, d2 => w2 => s => IO.bind(Unit, G.ImgDev, cw.say("attributes of " ++ p ++ " " ++ U32.show(a), s), u => cw.run(t, d2, w2)))
    case Con{CwLs{+p}, t}:
      cw.listed(X.FatW.list(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, d, w, p), d2 => s => IO.bind(Unit, G.ImgDev, cw.say("list " ++ p, s), u => cw.run(t, d2, w)))
    case Con{CwRead{+p}, t}:
      cw.got(X.FatW.read(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, d, w, p, 0n, 4294967295n), d2 => s => IO.bind(Unit, G.ImgDev, cw.say("read " ++ p, s), u => cw.run(t, d2, w)))
    case Con{CwStat{+p}, t}:
      cw.stated(X.FatW.stat(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, d, w, p), d2 => s => IO.bind(Unit, G.ImgDev, cw.say("stat " ++ p, s), u => cw.run(t, d2, w)))

def cw.text_of(s: String) -> B.Octets:
  B.Octets.of_string(s)

# bytes 0, 1, 2, ... (mod 251), n of them
def cw.pattern.go(n: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      cw.pattern.go(p, U32.add(i, 1), Con{U32.mod(i, 251), acc})

def cw.pattern(+n: Nat) -> B.Octets:
  B.Octets.of_list(B.rev(cw.pattern.go(n, 0, Nil{})))

def cw.ops() -> List<&2, CwOp>:
  [CwMkdir{"/EFI"}, CwMkdir{"/EFI/BOOT"}, CwCreate{"/EFI/BOOT/BOOTX64.EFI"}, CwWrite{"/EFI/BOOT/BOOTX64.EFI", 0n, cw.text_of("BOOTX64 says hello")}, CwCreate{"/Long File Name.txt"}, CwAppend{"/Long File Name.txt", cw.text_of("a file with")}, CwAppend{"/Long File Name.txt", cw.text_of(" a long name")}, CwCreate{"/readme.txt"}, CwWrite{"/readme.txt", 1500n, cw.text_of("past a gap of zeros")}, CwLs{"/"}, CwLs{"/EFI/BOOT"}, CwRead{"/efi/boot/bootx64.efi"}, CwRead{"/LONGFI~1.TXT"}, CwRead{"/readme.txt"}, CwCreate{"/README.TXT"}, CwCreate{"/bad:name"}, CwWrite{"/EFI", 0n, cw.text_of("x")}, CwRename{"/Long File Name.txt", "/EFI/Renamed, then moved.txt"}, CwRename{"/EFI", "/EFI/BOOT/inside"}, CwLs{"/EFI"}, CwTrunc{"/readme.txt", 10n}, CwRead{"/readme.txt"}, CwAttr{"/readme.txt", 1}, CwUnlink{"/readme.txt"}, CwAttr{"/readme.txt", 0}, CwUnlink{"/readme.txt"}, CwRmdir{"/EFI"}, CwUnlink{"/EFI/BOOT/BOOTX64.EFI"}, CwRmdir{"/EFI/BOOT"}, CwStat{"/EFI/Renamed, then moved.txt"}, CwCreate{"/big.bin"}, CwWrite{"/big.bin", 0n, cw.pattern(80000n)}, CwCreate{"/more"}, CwAppend{"/more", cw.pattern(80000n)}, CwAppend{"/more", cw.pattern(80000n)}, CwAppend{"/more", cw.pattern(80000n)}, CwAppend{"/more", cw.pattern(80000n)}, CwRead{"/big.bin"}, CwStat{"/more"}]

def cw.opened(r: G.ImgDev & Result<&2, &2, E.FatError, X.FatW>, k: G.ImgDev -> X.FatW -> IO(G.ImgDev)) -> IO(G.ImgDev):
  (d, res) = r
  match res:
    case Done{+w}:
      do IO<G.ImgDev>:
        IO.print("opened: " ++ P.FatType.show(X.FatW.kind(w)) ++ ", " ++ Nat.show(X.FatW.free_clusters(w)) ++ " clusters free")
        k(d, w)
    case Fail{e}:
      do IO<G.ImgDev>:
        IO.print("open: " ++ cw.err(e))
        IO.pure(G.ImgDev, d)

def cw.formatted(r: G.ImgDev & Result<&2, &2, E.FatError, K.FatLayout>, k: G.ImgDev -> IO(G.ImgDev)) -> IO(G.ImgDev):
  (d, res) = r
  match res:
    case Done{+l}:
      do IO<G.ImgDev>:
        IO.print("formatted: " ++ P.FatType.show(K.FatLayout.kind(l)) ++ ", " ++ Nat.show(K.FatLayout.clusters(l)) ++ " clusters")
        k(d)
    case Fail{e}:
      do IO<G.ImgDev>:
        IO.print("format: " ++ cw.err(e))
        k(d)

# the floppy, written: then the reader's view of it (the image copied into
# a MemDev)
def cw.floppy() -> IO(G.ImgDev):
  cw.formatted(K.FatFormat.format(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, G.ImgDev.blank(128n, 720n), P.Fat12{}, 720n, K.FatFormatOptions.default()), d =>
    cw.opened(X.FatW.open(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, d, P.FatOptions.default(), X.FatWOptions.default()), d2 => w => cw.run(cw.ops(), d2, w)))

def cw.reader(+d: D.MemDev) -> String:
  chk.ls(d, "/") ++ "; " ++ chk.ls(d, "/EFI") ++ "; " ++ chk.show_text(chk.read(d, "/efi/renamed, then moved.txt", 0n, 100n)) ++ "; " ++ chk.show_len(chk.read(d, "/BIG.BIN", 0n, 4294967295n))

def cw.mem.done(r: D.MemDev & Result<&2, &2, E.FatError, X.FatW>) -> String:
  (d, res) = r
  match res:
    case Done{+w}:
      Nat.show(X.FatW.free_clusters(w)) ++ " clusters free; the reader lists " ++ chk.ls(d, "/")
    case Fail{e}:
      cw.err(e)

# a format the size cannot hold, and FAT16 on a MemDev through blockdev's
# adapters (a pure device on the owned interface)
def cw.mem.opened(r: D.MemDev & Result<&2, &2, E.FatError, X.FatW>) -> String:
  (d, res) = r
  match res:
    case Done{+w}:
      cw.mem.done(X.FatW.create(~D.MemDev, ~D.MemDev.own_block_size, ~D.MemDev.own_read_block, ~D.MemDev.own_write_block, d, w, "/On a MemDev.txt"))
    case Fail{e}:
      cw.err(e)

def cw.mem.formatted(r: D.MemDev & Result<&2, &2, E.FatError, K.FatLayout>) -> String:
  (d, res) = r
  match res:
    case Done{+l}:
      P.FatType.show(K.FatLayout.kind(l)) ++ ", " ++ Nat.show(K.FatLayout.clusters(l)) ++ " clusters, " ++ cw.mem.opened(X.FatW.open(~D.MemDev, ~D.MemDev.own_block_size, ~D.MemDev.own_read_block, d, P.FatOptions.default(), X.FatWOptions.default()))
    case Fail{e}:
      cw.err(e)

def cw.mem() -> String:
  cw.mem.formatted(K.FatFormat.format(~D.MemDev, ~D.MemDev.own_block_size, ~D.MemDev.own_read_block, ~D.MemDev.own_write_block, D.MemDev.blank(512n, 20000n), P.Fat16{}, 20000n, K.FatFormatOptions.default()))

def cw.too_small(r: G.ImgDev & Result<&2, &2, E.FatError, K.FatLayout>) -> String:
  (d, res) = r
  match res:
    case Done{l}:
      "formatted"
    case Fail{e}:
      cw.err(e)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(chk.show_mount(chk.mount(chk.dev())))
    IO.print(chk.ls(chk.dev(), "/"))
    IO.print(chk.ls(chk.dev(), "/EFI/BOOT"))
    IO.print(chk.show_text(chk.read(chk.dev(), "/efi/boot/bootx64.efi", 0n, 100n)))
    IO.print(chk.show_text(chk.read(chk.dev(), "/Long File Name.txt", 0n, 100n)))
    IO.print(chk.show_text(chk.read(chk.dev(), "/LONG FILE NAME.TXT", 2n, 4n)))
    IO.print(chk.show_text(chk.read(chk.dev(), "/longfi~1.txt", 7n, 100n)))
    IO.print(chk.show_len(chk.read(chk.dev(), "/README.TXT", 0n, 4294967295n)))
    IO.print(chk.show_text(chk.read(chk.dev(), "/README.TXT", 521n, 100n)))
    IO.print(chk.show_text(chk.read(chk.dev(), "/README.TXT", 0n, 20n)))
    IO.print(chk.show_len(chk.read(chk.dev(), "/README.TXT", 600n, 10n)))
    IO.print(chk.pieces(chk.dev(), "/README.TXT"))
    IO.print(chk.walk(chk.dev(), 2))
    IO.print(chk.stat(chk.dev(), "/EFI/boot/BOOTX64.EFI"))
    IO.print(chk.stat(chk.dev(), "/"))
    IO.print(chk.stat(chk.dev(), "/EFI/nothing"))
    IO.print(chk.stat(chk.dev(), "/README.TXT/x"))
    IO.print(chk.show_text(chk.read(chk.dev(), "/EFI", 0n, 1n)))
    IO.print(chk.walk(chk.image([CheckLink{0, 4088}, CheckLink{1, 4095}, CheckLink{2, 4}, CheckLink{4, 2}], 512), 2))
    IO.print(chk.show_len(chk.read(chk.image([CheckLink{0, 4088}, CheckLink{1, 4095}, CheckLink{2, 0}], 512), "/README.TXT", 0n, 600n)))
    IO.print(chk.show_len(chk.read(chk.image([CheckLink{0, 4088}, CheckLink{1, 4095}, CheckLink{2, 4095}], 512), "/README.TXT", 0n, 600n)))
    IO.print(chk.show_len(chk.read(chk.image([CheckLink{0, 4088}, CheckLink{1, 4095}, CheckLink{2, 4000}], 512), "/README.TXT", 0n, 600n)))
    IO.print(chk.show_mount(chk.mount(chk.image(chk.links(), 500))))
    IO.print(chk.big.run(chk.big()))
    d : G.ImgDev <- cw.floppy()
    IO.print("the reader: " ++ cw.reader(G.ImgDev.freeze(d)))
    IO.print("FAT32 on 720 sectors: " ++ cw.too_small(K.FatFormat.format(~G.ImgDev, ~G.ImgDev.block_size, ~G.ImgDev.read_block, ~G.ImgDev.write_block, G.ImgDev.blank(128n, 720n), P.Fat32{}, 720n, K.FatFormatOptions.default())))
    IO.print("FAT16 on a MemDev: " ++ cw.mem())

#|FAT12, 20 clusters
#|README.TXT, EFI/, Long File Name.txt
#|BOOTX64.EFI
#|BOOTX64 says hello
#|a file with a long name
#|file
#|with a long name
#|600 bytes
#|The end of README.TXT, in the second of its clusters (cluster 4, after 3)!!!!!!
#|FAT reading in Bend.
#|0 bytes
#|512 + 88
#|[2, 4]
#|BOOTX64.EFI (BOOTX64.EFI), 18 bytes
#|the root
#|error: not found
#|error: not a directory
#|error: is a directory
#|error: chain loops
#|error: free cluster in chain 2
#|error: chain shorter than file
#|error: cluster out of range 4000
#|error: bad bytes per sector 500
#|50000 clusters, 102400 bytes
#|formatted: FAT12, 681 clusters
#|opened: FAT12, 681 clusters free
#|mkdir /EFI: ok, 680 clusters free
#|mkdir /EFI/BOOT: ok, 679 clusters free
#|create /EFI/BOOT/BOOTX64.EFI: ok, 679 clusters free
#|write /EFI/BOOT/BOOTX64.EFI at 0: ok, 678 clusters free
#|create /Long File Name.txt: ok, 678 clusters free
#|append /Long File Name.txt: ok, 677 clusters free
#|append /Long File Name.txt: ok, 677 clusters free
#|create /readme.txt: ok, 677 clusters free
#|write /readme.txt at 1500: ok, 674 clusters free
#|list /: EFI (EFI)/, Long File Name.txt (LONGFI~1.TXT), readme.txt (README.TXT)
#|list /EFI/BOOT: BOOTX64.EFI (BOOTX64.EFI)
#|read /efi/boot/bootx64.efi: BOOTX64 says hello
#|read /LONGFI~1.TXT: a file with a long name
#|read /readme.txt: 1519 bytes, ending 207a65726f73
#|create /README.TXT: error: name exists
#|create /bad:name: error: bad name
#|write /EFI at 0: error: is a directory
#|rename /Long File Name.txt to /EFI/Renamed, then moved.txt: ok, 674 clusters free
#|rename /EFI to /EFI/BOOT/inside: error: move into itself
#|list /EFI: BOOT (BOOT)/, Renamed, then moved.txt (RENAME~1.TXT)
#|truncate /readme.txt to 10: ok, 676 clusters free
#|read /readme.txt: 10 bytes, ending 000000000000
#|attributes of /readme.txt 1: ok, 676 clusters free
#|delete /readme.txt: error: read-only file
#|attributes of /readme.txt 0: ok, 676 clusters free
#|delete /readme.txt: ok, 677 clusters free
#|rmdir /EFI: error: directory not empty
#|delete /EFI/BOOT/BOOTX64.EFI: ok, 678 clusters free
#|rmdir /EFI/BOOT: ok, 679 clusters free
#|stat /EFI/Renamed, then moved.txt: Renamed, then moved.txt (RENAME~1.TXT), 23 bytes, attributes 32
#|create /big.bin: ok, 679 clusters free
#|write /big.bin at 0: ok, 522 clusters free
#|create /more: ok, 522 clusters free
#|append /more: ok, 365 clusters free
#|append /more: ok, 209 clusters free
#|append /more: ok, 53 clusters free
#|append /more: error: disk full
#|read /big.bin: 80000 bytes, ending b0b1b2b3b4b5
#|stat /more: more (MORE), 240000 bytes, attributes 32
#|the reader: EFI/, big.bin, more; Renamed, then moved.txt; a file with a long name; 80000 bytes
#|FAT32 on 720 sectors: error: cluster count 676 outside the FAT type
#|FAT16 on a MemDev: FAT16, 19811 clusters, 19811 clusters free; the reader lists On a MemDev.txt
