import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as BD
import ./fields.bend as F
import ./joliet.bend as J
import ./dirrec.bend as R
import ./susp.bend as S
import ./volume.bend as V
import ./dir.bend as DR
import ./file.bend as FL
import ./iso9660.bend as I

# A small image built here with the package's own record writers: a
# primary and a Joliet hierarchy, Rock Ridge entries (SP, ER, PX, NM, SL),
# a file of two blocks in a subdirectory.
#   16 primary, 17 Joliet, 18 terminator, 19 root, 20 /sub (primary),
#   21 root, 22 /sub (Joliet), 23 hello.txt, 24..25 data.bin

def date() -> F.IsoDirDate:
  F.IsoDirDate{126, 10, 17, 12, 0, 0, 4}

def b32(+v: U32) -> List<&2, U32>:
  B.append(B.le32(v), B.be32(v))

def entry(a: U32, b: U32, data: List<&2, U32>) -> List<&2, U32>:
  +d = data
  Con{a, Con{b, Con{U32.add(4, U32.from_nat(B.len(d))), Con{1, d}}}}

def px(+mode: U32, +links: U32) -> List<&2, U32>:
  entry(80, 88, B.append(b32(mode), B.append(b32(links), B.append(b32(0), B.append(b32(0), b32(1))))))

def nm(s: String) -> List<&2, U32>:
  entry(78, 77, Con{0, B.of_string(s)})

def rec(ext: U32, size: U32, flags: U32, id: List<&2, U32>, su: List<&2, U32>) -> R.IsoDirRec:
  R.IsoDirRec{0, ext, size, date(), flags, 0, 0, 1, B.Octets.of_list(id), B.Octets.of_list(su)}

def sector.go(rs: List<&2, R.IsoDirRec>) -> B.Octets:
  match rs:
    case Nil{}:
      B.Octets.empty()
    case Con{r, t}:
      B.Octets.append(R.IsoDirRec.encode(r), sector.go(t))

def sector(rs: List<&2, R.IsoDirRec>) -> B.Octets:
  +o = sector.go(rs)
  B.Octets.append(o, B.Octets.zeros(Nat.sub(2048n, B.Octets.len(o))))

def u16(s: String) -> List<&2, U32>:
  B.Octets.to_list(J.Iso.ucs2_encode(s))

def root_p() -> B.Octets:
  sector([rec(19, 2048, 2, [0], B.append(entry(83, 80, [190, 239, 0]), entry(69, 82, B.append([10, 0, 0, 1], B.of_string("RRIP_1991A"))))), rec(19, 2048, 2, [1], Nil{}), rec(23, 11, 0, B.of_string("HELLO.TXT;1"), B.append(px(33188, 1), nm("hello.txt"))), rec(0, 0, 0, B.of_string("LINK.;1"), B.append(px(41471, 1), B.append(entry(83, 76, [0, 0, 9, 104, 101, 108, 108, 111, 46, 116, 120, 116]), nm("link")))), rec(20, 2048, 2, B.of_string("SUB"), B.append(px(16877, 2), nm("sub")))])

def sub_p() -> B.Octets:
  sector([rec(20, 2048, 2, [0], Nil{}), rec(19, 2048, 2, [1], Nil{}), rec(24, 3000, 0, B.of_string("DATA.BIN;1"), B.append(px(33188, 1), nm("data.bin")))])

def root_j() -> B.Octets:
  sector([rec(21, 2048, 2, [0], Nil{}), rec(21, 2048, 2, [1], Nil{}), rec(23, 11, 0, u16("hello.txt;1"), Nil{}), rec(22, 2048, 2, u16("sub"), Nil{})])

def sub_j() -> B.Octets:
  sector([rec(22, 2048, 2, [0], Nil{}), rec(21, 2048, 2, [1], Nil{}), rec(24, 3000, 0, u16("data.bin;1"), Nil{})])

def text(+n: Nat, s: String) -> B.Octets:
  +o = B.Octets.of_string(s)
  B.Octets.append(o, B.Octets.of_list(B.of_string(String.repeat(" ", Nat.sub(n, B.Octets.len(o))))))

def jtext(+n: Nat, s: String) -> B.Octets:
  +o = J.Iso.ucs2_encode(s)
  B.Octets.append(o, B.Octets.zeros(Nat.sub(n, B.Octets.len(o))))

def vdate() -> B.Octets:
  F.IsoVolDate.encode(F.IsoVolDate{2026n, 10n, 17n, 12n, 34n, 56n, 78n, 4})

def vd.text(j: Bool, +n: Nat, s: String) -> B.Octets:
  match j:
    case True{}:
      jtext(n, s)
    case False{}:
      text(n, s)

def vd.esc(j: Bool) -> B.Octets:
  match j:
    case True{}:
      B.Octets.append(B.Octets.of_list([37, 47, 69]), B.Octets.zeros(29n))
    case False{}:
      B.Octets.zeros(32n)

# a primary (kind 1) or Joliet (kind 2) descriptor, its root at block root
def vd(+kind: U32, root: U32, +space: B.Octets) -> B.Octets:
  +joliet = U32.is_eq(kind, 2)
  +head = B.Octets.concat([B.Octets.of_list([kind, 67, 68, 48, 48, 49, 1, 0]), vd.text(joliet, 32n, "BEND"), vd.text(joliet, 32n, "CHECK"), B.Octets.zeros(8n), space, vd.esc(joliet), F.Iso.both16_encode(1), F.Iso.both16_encode(1), F.Iso.both16_encode(2048), F.Iso.both32_encode(0), B.Octets.zeros(16n), R.IsoDirRec.encode(rec(root, 2048, 2, [0], Nil{})), B.Octets.zeros(623n), vdate(), vdate(), F.IsoVolDate.encode(F.IsoVolDate.unspecified()), F.IsoVolDate.encode(F.IsoVolDate.unspecified()), B.Octets.of_list([1])])
  B.Octets.append(head, B.Octets.zeros(Nat.sub(2048n, B.Octets.len(head))))

def terminator() -> B.Octets:
  B.Octets.append(B.Octets.of_list([255, 67, 68, 48, 48, 49, 1]), B.Octets.zeros(2041n))

def pattern(n: Nat, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{U32.mod(i, 251), pattern(p, U32.add(i, 1))}

def block(+o: B.Octets) -> B.Octets:
  B.Octets.append(o, B.Octets.zeros(Nat.sub(2048n, B.Octets.len(o))))

def image.with(space: B.Octets) -> BD.MemDev:
  +s = space
  BD.MemDev.update(BD.MemDev.update(BD.MemDev.update(BD.MemDev.update(BD.MemDev.update(BD.MemDev.update(BD.MemDev.update(BD.MemDev.update(BD.MemDev.update(BD.MemDev.update(BD.MemDev.blank(2048n, 26n), 16n, vd(1, 19, s)), 17n, vd(2, 21, s)), 18n, terminator()), 19n, root_p()), 20n, sub_p()), 21n, root_j()), 22n, sub_j()), 23n, block(B.Octets.of_string("hello, iso\n"))), 24n, B.Octets.of_list(pattern(2048n, 0))), 25n, block(B.Octets.of_list(pattern(952n, 2048))))

def image() -> BD.MemDev:
  image.with(F.Iso.both32_encode(26))

# the same image, its volume space size's halves disagreeing
def image.bad() -> BD.MemDev:
  image.with(F.Iso.both32_encode_pair(26, 27))

# Showing results

def show_items(xs: List<&2, I.IsoWalkItem>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, Nil{}}:
      I.IsoWalkItem.show(h)
    case Con{h, t}:
      I.IsoWalkItem.show(h) ++ "\n" ++ show_items(t)

def walked(r: Result<&2, &2, F.IsoError, List<&2, I.IsoWalkItem>>) -> String:
  match r:
    case Fail{e}:
      "walk: " ++ F.IsoError.show(e)
    case Done{items}:
      show_items(items)

def opts(nm: V.IsoNaming) -> V.IsoOptions:
  V.IsoOptions.with_naming(V.IsoOptions.default(), nm)

def walk.go(+d: BD.MemDev, r: Result<&2, &2, F.IsoError, V.IsoVolume>) -> String:
  match r:
    case Fail{e}:
      "open: " ++ F.IsoError.show(e)
    case Done{+v}:
      V.IsoNaming.show(V.IsoVolume.naming_of(v)) ++ " " ++ V.IsoPvd.volume_id_of(V.IsoVolume.pvd_of(v)) ++ "\n" ++ walked(I.Iso.walk(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, v))

def walk(+d: BD.MemDev, o: V.IsoOptions) -> String:
  walk.go(d, V.Iso.open(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, o))

def vol(+o: V.IsoOptions) -> V.IsoVolume:
  Result.default(&2, &2, F.IsoError, V.IsoVolume, V.Iso.open(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, image(), o), V.IsoVolume{o, V.IsoNamingPlain{}, V.IsoPvd{"", "", 0, 0, 0, 0, 0, 0, 0, rec(0, 0, 0, [0], Nil{}), "", "", "", "", "", "", "", B.Octets.empty(), B.Octets.empty(), B.Octets.empty(), B.Octets.empty(), 0}, rec(0, 0, 0, [0], Nil{}), 0n, 0n, None{}, Nil{}})

def bytes(r: Result<&2, &2, F.IsoError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      F.IsoError.show(e)

def read(path: String, +off: Nat, +len: Nat) -> String:
  bytes(I.Iso.read_path(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, image(), vol(V.IsoOptions.default()), path, off, len))

def piece.size(r: Result<&2, &2, F.IsoError, FL.IsoChunk>) -> String:
  match r:
    case Done{FL.IsoChunkEnd{}}:
      ""
    case Done{FL.IsoChunkData{o, c}}:
      Nat.show(B.Octets.len(o)) ++ " "
    case Fail{e}:
      F.IsoError.show(e) ++ " "

def piece.end(r: Result<&2, &2, F.IsoError, FL.IsoChunk>) -> Bool:
  match r:
    case Done{FL.IsoChunkData{o, c}}:
      False{}
    case _:
      True{}

def piece.next(r: Result<&2, &2, F.IsoError, FL.IsoChunk>) -> FL.IsoCursor:
  match r:
    case Done{FL.IsoChunkData{o, c}}:
      c
    case _:
      FL.IsoCursor{Nil{}, 0n, 0}

def pieces(fuel: Nat, stop: Bool, +d: BD.MemDev, c: FL.IsoCursor) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      match stop:
        case True{}:
          "end"
        case False{}:
          +r = FL.Iso.file_next(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, c)
          piece.size(r) ++ pieces(f, piece.end(r), d, piece.next(r))

def stream.go(+d: BD.MemDev, r: Result<&2, &2, F.IsoError, FL.IsoCursor>) -> String:
  match r:
    case Done{c}:
      pieces(10n, False{}, d, c)
    case Fail{e}:
      F.IsoError.show(e)

def stream(path: String) -> String:
  +d = image()
  stream.go(d, I.Iso.stream_path(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, vol(V.IsoOptions.default()), path))

def found(r: Result<&2, &2, F.IsoError, DR.IsoEntry>) -> String:
  match r:
    case Done{e}:
      "found " ++ DR.IsoEntry.name_of(e)
    case Fail{e}:
      F.IsoError.show(e)

def find(path: String) -> String:
  found(DR.Iso.find(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, image(), vol(V.IsoOptions.default()), path))

def listed(r: Result<&2, &2, F.IsoError, List<&2, DR.IsoEntry>>) -> String:
  match r:
    case Done{es}:
      Nat.show(List.length(&2, DR.IsoEntry, es)) ++ " entries"
    case Fail{e}:
      F.IsoError.show(e)

def descs.go(ds: List<&2, V.IsoDescriptor>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{V.IsoDescriptor.show(h), descs.go(t)}

def descs(r: Result<&2, &2, F.IsoError, List<&2, V.IsoDescriptor>>) -> String:
  match r:
    case Done{ds}:
      String.join(descs.go(ds), ", ")
    case Fail{e}:
      F.IsoError.show(e)

def u32r(r: Result<&2, &2, F.IsoError, U32>) -> String:
  match r:
    case Done{v}:
      U32.show(v)
    case Fail{e}:
      F.IsoError.show(e)

def vdate.show(r: Result<&2, &2, F.IsoError, F.IsoVolDate>) -> String:
  match r:
    case Done{d}:
      F.IsoVolDate.show(d)
    case Fail{e}:
      F.IsoError.show(e)

def recr(r: Result<&2, &2, F.IsoError, R.IsoDirRec>) -> String:
  match r:
    case Done{+x}:
      "record " ++ Nat.show(R.IsoDirRec.length(x)) ++ " " ++ B.Octets.to_string(R.IsoDirRec.ident_of(x))
    case Fail{e}:
      F.IsoError.show(e)

def susp(r: Result<&2, &2, F.IsoError, List<&2, S.IsoSuspEntry>>) -> String:
  match r:
    case Done{es}:
      Nat.show(List.length(&2, S.IsoSuspEntry, es)) ++ " entries"
    case Fail{e}:
      F.IsoError.show(e)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(descs(V.Iso.descriptors(~BD.MemDev, ~BD.MemDev.read_block, image(), V.IsoOptions.default())))
    IO.print(walk(image(), V.IsoOptions.default()))
    IO.print(walk(image(), opts(V.IsoNamingPlain{})))
    IO.print(walk(image(), opts(V.IsoNamingJoliet{})))
    IO.print(read("/sub/data.bin", 2040n, 12n))
    IO.print(read("/sub/data.bin", 2995n, 100n))
    IO.print(read("/hello.txt", 0n, 100n))
    IO.print(stream("/sub/data.bin"))
    IO.print(stream("/sub"))
    IO.print(find("/sub/nope"))
    IO.print(find("/hello.txt/x"))
    IO.print(find("/link"))
    IO.print(listed(DR.Iso.list_path(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, image(), vol(V.IsoOptions.default()), "/sub")))
    IO.print(walk(image.bad(), V.IsoOptions.default()))
    IO.print(walk(image.bad(), V.IsoOptions.with_endian(V.IsoOptions.default(), F.IsoEndianBig{})))
    IO.print(walk(BD.MemDev.blank(2048n, 20n), V.IsoOptions.default()))
    IO.print(walk(BD.MemDev.blank(512n, 20n), V.IsoOptions.default()))
    IO.print(u32r(F.Iso.both32_decode(F.IsoEndianCheck{}, F.Iso.both32_encode_pair(1, 2), 0n)))
    IO.print(u32r(F.Iso.both32_decode(F.IsoEndianBig{}, F.Iso.both32_encode_pair(1, 2), 0n)))
    IO.print(vdate.show(F.IsoVolDate.decode(vdate())))
    IO.print(vdate.show(F.IsoVolDate.decode(B.Octets.of_string("2026101712345x780"))))
    IO.print(F.IsoDirDate.show(date()))
    IO.print(recr(R.IsoDirRec.decode(F.IsoEndianCheck{}, R.IsoDirRec.encode(rec(24, 3000, 0, B.of_string("DATA.BIN;1"), nm("data.bin"))))))
    IO.print(recr(R.IsoDirRec.decode(F.IsoEndianCheck{}, B.Octets.take(40n, R.IsoDirRec.encode(rec(24, 3000, 0, B.of_string("DATA.BIN;1"), nm("data.bin")))))))
    IO.print(susp(S.Iso.susp_parse(B.Octets.of_list(B.append(px(1, 1), nm("x"))))))
    IO.print(susp(S.Iso.susp_parse(B.Octets.of_list([80, 88, 3, 1]))))
    IO.print(Nat.show(J.Iso.joliet_level(B.Octets.of_list([37, 47, 64]))))

#|primary, supplementary joliet 3, terminator
#|rockridge CHECK
#|f /hello.txt 11
#|l /link 0 -> hello.txt
#|d /sub 2048
#|f /sub/data.bin 3000
#|plain CHECK
#|f /HELLO.TXT 11
#|f /LINK 0
#|d /SUB 2048
#|f /SUB/DATA.BIN 3000
#|joliet CHECK
#|f /hello.txt 11
#|d /sub 2048
#|f /sub/data.bin 3000
#|202122232425262728292a2b
#|eaebecedee
#|68656c6c6f2c2069736f0a
#|2048 952 end
#|is a directory: sub
#|not found: nope
#|not a directory: hello.txt
#|found link
#|1 entries
#|open: both-endian halves differ at 80
#|rockridge CHECK
#|f /hello.txt 11
#|l /link 0 -> hello.txt
#|d /sub 2048
#|f /sub/data.bin 3000
#|open: no CD001 at sector 16
#|open: block size 512 is not 2048
#|both-endian halves differ at 0
#|2
#|2026-10-17 12:34:56.78 4
#|bad date
#|2026-10-17 12:00:00 4
#|record 57 DATA.BIN;1
#|truncated
#|2 entries
#|bad system use entry
#|1
