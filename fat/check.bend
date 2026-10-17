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
