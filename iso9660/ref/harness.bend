import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as BD
import ../../crc/crc.bend as C
import ../fields.bend as F
import ../volume.bend as V
import ../dir.bend as DR
import ../file.bend as FL
import ../iso9660.bend as I

# The harness of the differential test (gen.py appends main): each case
# loads an image file a block at a time into a MemDev, opens it, walks it,
# streams every file a block at a time (CRC-32 of its bytes), reads some
# byte ranges, and prints the boot catalog.

type Rg is Data:
  Rg{path: String, off: Nat, len: Nat}

def esc.hex.pick(lt: Bool, d: U32) -> Char:
  match lt:
    case True{}:
      Chr{U32.add(48, d)}
    case False{}:
      Chr{U32.add(87, d)}

def esc.hexs(n: Nat, +c: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      esc.hexs(p, U32.shrn(c, 4n), SCon{esc.hex.pick(U32.is_lt(U32.and(c, 15), 10), U32.and(c, 15)), acc})

def esc.trim.pick(zero: Bool, c: Char, t: String) -> String:
  match zero:
    case True{}:
      t
    case False{}:
      SCon{c, t}

# leading zeros dropped (one digit kept)
def esc.trim(s: String) -> String:
  match s:
    case SCon{Chr{+c}, +t}:
      esc.trim.pick(Bool.and(U32.is_eq(c, 48), Bool.not(String.is_empty(t))), Chr{c}, t)
    case SNil{}:
      SNil{}

def show_name.one(odd: Bool, +c: U32) -> String:
  match odd:
    case True{}:
      SCon{Chr{92}, "u{" ++ esc.trim(esc.trim(esc.trim(esc.trim(esc.trim(esc.trim(esc.trim(esc.hexs(8n, c, "")))))))) ++ "}"}
    case False{}:
      SCon{Chr{c}, SNil{}}

# a name with non-printable characters and backslashes escaped as \u{hex}
def show_name(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, t}:
      show_name.one(Bool.or(Bool.or(U32.is_lt(c, 32), U32.is_gt(c, 126)), U32.is_eq(c, 92)), c) ++ show_name(t)

def hex8(c: U32) -> String:
  B.hex(B.be32(c))

def put(+i: Nat, d: BD.MemDev, res: Result<&1, &1, U32 & String, List<&2, U32>>) -> BD.MemDev:
  match res:
    case Done{xs}:
      BD.MemDev.update(d, i, B.Octets.of_list(xs))
    case Fail{e}:
      d

def step(+i: Nat, d: BD.MemDev, r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(File & BD.MemDev):
  (f2, res) = r
  IO.pure(File & BD.MemDev, (f2, put(i, d, res)))

def load(n: Nat, +i: Nat, st: File & BD.MemDev) -> IO(File & BD.MemDev):
  match n:
    case 0n:
      IO.pure(File & BD.MemDev, st)
    case 1n+p:
      (f, d) = st
      do IO<File & BD.MemDev>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, U32.mul(U32.from_nat(i), 2048), 2048)
        q : File & BD.MemDev <- step(i, d, r)
        load(p, Nat.add(i, 1n), q)

def lines(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, Nil{}}:
      h
    case Con{h, t}:
      h ++ "\n" ++ lines(t)

def item_line(i: I.IsoWalkItem) -> String:
  match i:
    case I.IsoWalkItem{p, e}:
      show_name(I.IsoWalkItem.show(I.IsoWalkItem{p, e}))

def item_lines(xs: List<&2, I.IsoWalkItem>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{item_line(h), item_lines(t)}

# the CRC-32 and length of a file, streamed a block at a time
type Sum is Data:
  Sum{crc: U32, len: Nat}

def chunk.end(k: FL.IsoChunk) -> Bool:
  match k:
    case FL.IsoChunkEnd{}:
      True{}
    case FL.IsoChunkData{o, c}:
      False{}

def chunk.next(k: FL.IsoChunk) -> FL.IsoCursor:
  match k:
    case FL.IsoChunkEnd{}:
      FL.IsoCursor{Nil{}, 0n, 0}
    case FL.IsoChunkData{o, c}:
      c

def chunk.add(k: FL.IsoChunk, acc: Sum) -> Sum:
  match k acc:
    case FL.IsoChunkEnd{} _:
      acc
    case FL.IsoChunkData{+o, c} Sum{x, n}:
      Sum{C.Crc32Spec.update(C.crc32.spec(), x, o), Nat.add(n, B.Octets.len(o))}

def stream(fuel: Nat, stop: Bool, +d: BD.MemDev, c: FL.IsoCursor, acc: Sum) -> Result<&2, &2, F.IsoError, Sum>:
  match fuel:
    case 0n:
      Done{acc}
    case 1n+f:
      match stop:
        case True{}:
          Done{acc}
        case False{}:
          do Result<&2, &2, F.IsoError, Sum>:
            +k : FL.IsoChunk <- FL.Iso.file_next(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, c)
            stream(f, chunk.end(k), d, chunk.next(k), chunk.add(k, acc))

def crc_of(+d: BD.MemDev, +e: DR.IsoEntry) -> Result<&2, &2, F.IsoError, Sum>:
  do Result<&2, &2, F.IsoError, Sum>:
    c : FL.IsoCursor <- FL.Iso.file_start(e)
    stream(100000n, False{}, d, c, Sum{C.Crc32Spec.start(C.crc32.spec()), 0n})

def sum_line(p: String, r: Result<&2, &2, F.IsoError, Sum>) -> String:
  match r:
    case Done{Sum{c, n}}:
      "crc " ++ show_name(p) ++ " " ++ hex8(C.Crc32Spec.finish(C.crc32.spec(), c)) ++ " " ++ Nat.show(n)
    case Fail{e}:
      "crc " ++ show_name(p) ++ " error " ++ F.IsoError.show(e)

def is_file(+e: DR.IsoEntry) -> Bool:
  Bool.and(Bool.not(DR.IsoEntry.is_dir_of(e)), Maybe.is_none(&2, String, DR.IsoEntry.link(e)))

def crc_lines.pick(f: Bool, +d: BD.MemDev, p: String, e: DR.IsoEntry, rest: List<&2, String>) -> List<&2, String>:
  match f:
    case True{}:
      Con{sum_line(p, crc_of(d, e)), rest}
    case False{}:
      rest

def crc_lines(+d: BD.MemDev, xs: List<&2, I.IsoWalkItem>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{I.IsoWalkItem{+p, +e}, t}:
      crc_lines.pick(is_file(e), d, p, e, crc_lines(d, t))

def range_line(+r: Rg, x: Result<&2, &2, F.IsoError, B.Octets>) -> String:
  match r x:
    case Rg{p, off, n} Done{+o}:
      "range " ++ show_name(p) ++ " " ++ Nat.show(off) ++ " " ++ Nat.show(n) ++ " " ++ hex8(C.crc32(o)) ++ " " ++ Nat.show(B.Octets.len(o))
    case Rg{p, off, n} Fail{e}:
      "range " ++ show_name(p) ++ " error " ++ F.IsoError.show(e)

def range_lines(+d: BD.MemDev, +v: V.IsoVolume, rs: List<&2, Rg>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Rg{+p, +off, +n}, t}:
      Con{range_line(Rg{p, off, n}, I.Iso.read_path(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, v, p, off, n)), range_lines(d, v, t)}

def boot.word(b: Bool) -> String:
  match b:
    case True{}:
      "bootable"
    case False{}:
      "not"

def boot_line(r: Result<&2, &2, F.IsoError, Maybe<&2, V.IsoBootCatalog>>, v: V.IsoVolume) -> List<&2, String>:
  match r v:
    case Done{Some{V.IsoBootCatalog{pl, id, V.IsoBootEntry{bt, mt, ls, st, sc, rba}}}} V.IsoVolume{o, n, p, rt, j, k, Some{c}, ds}:
      ["boot " ++ U32.show(c) ++ " " ++ boot.word(bt) ++ " " ++ U32.show(mt) ++ " " ++ U32.show(ls) ++ " " ++ U32.show(st) ++ " " ++ U32.show(sc) ++ " " ++ U32.show(rba)]
    case Done{None{}} _:
      Nil{}
    case Fail{e} _:
      ["boot: " ++ F.IsoError.show(e)]
    case _ _:
      Nil{}

def walked(+d: BD.MemDev, +v: V.IsoVolume, rs: List<&2, Rg>, r: Result<&2, &2, F.IsoError, List<&2, I.IsoWalkItem>>) -> List<&2, String>:
  match r:
    case Fail{e}:
      ["walk: " ++ F.IsoError.show(e)]
    case Done{+items}:
      Con{"naming " ++ V.IsoNaming.show(V.IsoVolume.naming_of(v)), List.append(&2, String, item_lines(items), List.append(&2, String, crc_lines(d, items), List.append(&2, String, range_lines(d, v, rs), boot_line(V.Iso.boot_catalog(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, v), v))))}

def opened(+d: BD.MemDev, rs: List<&2, Rg>, r: Result<&2, &2, F.IsoError, V.IsoVolume>) -> List<&2, String>:
  match r:
    case Fail{e}:
      ["open: " ++ F.IsoError.show(e)]
    case Done{+v}:
      walked(d, v, rs, I.Iso.walk(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, v))

def case_out(+d: BD.MemDev, nm: V.IsoNaming, en: F.IsoEndian, follow: Bool, rs: List<&2, Rg>) -> String:
  lines(opened(d, rs, V.Iso.open(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, V.IsoOptions.with_follow_relocation(V.IsoOptions.with_endian(V.IsoOptions.with_naming(V.IsoOptions.default(), nm), en), follow))))

def fin(label: String, nm: V.IsoNaming, en: F.IsoEndian, follow: Bool, rs: List<&2, Rg>, st: File & BD.MemDev) -> IO(Unit):
  (f, d) = st
  do IO<Unit>:
    File.close(f)
    IO.print("== " ++ label)
    IO.print(case_out(d, nm, en, follow, rs))

def run_case(label: String, path: String, +n: Nat, nm: V.IsoNaming, en: F.IsoEndian, follow: Bool, rs: List<&2, Rg>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "r"))
    st : File & BD.MemDev <- load(n, 0n, (f, BD.MemDev.blank(2048n, n)))
    fin(label, nm, en, follow, rs, st)
