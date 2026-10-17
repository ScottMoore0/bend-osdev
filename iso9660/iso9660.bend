# bend-osdev-iso9660: a read-only ISO 9660 reader, with Rock Ridge and
# Joliet, over blockdev's device interface (2048-byte blocks).
#
# This file is the entry concern: reading a volume by path. Open a volume
# (volume.bend: Iso.open), then find, list, walk and read by path; the
# pieces underneath are in their own files (fields, joliet, dirrec, susp,
# rockridge, volume, dir, file), listed in README.md.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../blockdev/blockdev.bend as BD
import ./fields.bend as F
import ./volume.bend as V
import ./dir.bend as DR
import ./file.bend as FL

# a volume opened with the default options (Rock Ridge, then Joliet, then
# plain names; both-endian halves checked)
def Iso.mount(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D) -> Result<&2, &2, F.IsoError, V.IsoVolume>:
  V.Iso.open(~D, ~block_size, ~read_block, d, V.IsoOptions.default())

# the bytes from off to off + len of the file at a path (fewer where it ends)
def Iso.read_path(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +v: V.IsoVolume, path: String, +off: Nat, +len: Nat) -> Result<&2, &2, F.IsoError, B.Octets>:
  Result.bind(&2, &2, F.IsoError, DR.IsoEntry, B.Octets, DR.Iso.find(~D, ~block_size, ~read_block, d, v, path), e => FL.Iso.file_read(~D, ~block_size, ~read_block, d, e, off, len))

# a stream over the file at a path
def Iso.stream_path(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +v: V.IsoVolume, path: String) -> Result<&2, &2, F.IsoError, FL.IsoCursor>:
  Result.bind(&2, &2, F.IsoError, DR.IsoEntry, FL.IsoCursor, DR.Iso.find(~D, ~block_size, ~read_block, d, v, path), e => FL.Iso.file_start(e))

# Walking the whole tree

# an entry and its path from the root
type IsoWalkItem is Data:
  IsoWalkItem{path: String, entry: DR.IsoEntry}

def iso.walk.kids(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, isdir: Bool, d: D, v: V.IsoVolume, e: DR.IsoEntry) -> Result<&2, &2, F.IsoError, List<&2, DR.IsoEntry>>:
  match isdir:
    case True{}:
      DR.Iso.list(~D, ~block_size, ~read_block, d, v, e)
    case False{}:
      Done{Nil{}}

def iso.walk.list(r: Result<&2, &2, F.IsoError, List<&2, DR.IsoEntry>>) -> List<&2, DR.IsoEntry>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{es}:
      es

def iso.walk.after(r: Result<&2, &2, F.IsoError, List<&2, DR.IsoEntry>>, acc: Result<&2, &2, F.IsoError, List<&2, IsoWalkItem>>) -> Result<&2, &2, F.IsoError, List<&2, IsoWalkItem>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{es}:
      acc

def iso.walk.rev(xs: List<&2, IsoWalkItem>, acc: List<&2, IsoWalkItem>) -> List<&2, IsoWalkItem>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      iso.walk.rev(t, Con{h, acc})

# the items under these entries (of the directory at prefix), depth-first,
# pushed onto r (the items so far, latest first, or the first error);
# fuel directory levels deep at most. It loops over the entries of a
# directory and recurses only into subdirectories.
def iso.walk.go(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +fuel: Nat, es: List<&2, DR.IsoEntry>, +d: D, +v: V.IsoVolume, +prefix: String, r: Result<&2, &2, F.IsoError, List<&2, IsoWalkItem>>) -> Result<&2, &2, F.IsoError, List<&2, IsoWalkItem>>:
  match fuel es r:
    case _ _ Fail{e}:
      Fail{e}
    case _ Nil{} Done{acc}:
      Done{acc}
    case 0n Con{+e, t} Done{acc}:
      +path = prefix ++ "/" ++ DR.IsoEntry.name_of(e)
      iso.walk.go(~D, ~block_size, ~read_block, fuel, t, d, v, prefix, Done{Con{IsoWalkItem{path, e}, acc}})
    case 1n+f Con{+e, t} Done{acc}:
      +path = prefix ++ "/" ++ DR.IsoEntry.name_of(e)
      +kids = iso.walk.kids(~D, ~block_size, ~read_block, DR.IsoEntry.is_dir_of(e), d, v, e)
      iso.walk.go(~D, ~block_size, ~read_block, fuel, t, d, v, prefix, iso.walk.go(~D, ~block_size, ~read_block, f, iso.walk.list(kids), d, v, path, iso.walk.after(kids, Done{Con{IsoWalkItem{path, e}, acc}})))

def iso.walk.fin(r: Result<&2, &2, F.IsoError, List<&2, IsoWalkItem>>) -> Result<&2, &2, F.IsoError, List<&2, IsoWalkItem>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{acc}:
      Done{iso.walk.rev(acc, Nil{})}

# every entry of the volume, depth-first, each directory before its entries
def Iso.walk(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +v: V.IsoVolume) -> Result<&2, &2, F.IsoError, List<&2, IsoWalkItem>>:
  match v:
    case V.IsoVolume{V.IsoOptions{nm, e, s, f, md, mc, +mx}, n, p, r, j, k, b, ds}:
      Result.bind(&2, &2, F.IsoError, List<&2, DR.IsoEntry>, List<&2, IsoWalkItem>, DR.Iso.list(~D, ~block_size, ~read_block, d, v, DR.Iso.root(v)), es => iso.walk.fin(iso.walk.go(~D, ~block_size, ~read_block, mx, es, d, v, "", Done{Nil{}})))

# One line per entry: "d" or "f", the path, the size, and " -> target" for a
# Rock Ridge symbolic link
def iso.walk.link(m: Maybe<&2, String>) -> String:
  match m:
    case Some{t}:
      " -> " ++ t
    case None{}:
      ""

def iso.walk.kind(isdir: Bool, link: Bool) -> String:
  match isdir link:
    case True{} _:
      "d"
    case False{} True{}:
      "l"
    case False{} False{}:
      "f"

def iso.walk.is_link(m: Maybe<&2, String>) -> Bool:
  match m:
    case Some{t}:
      True{}
    case None{}:
      False{}

def IsoWalkItem.show(i: IsoWalkItem) -> String:
  match i:
    case IsoWalkItem{p, +e}:
      +l = DR.IsoEntry.link(e)
      iso.walk.kind(DR.IsoEntry.is_dir_of(e), iso.walk.is_link(l)) ++ " " ++ p ++ " " ++ W.W64.show(DR.IsoEntry.size_of(e)) ++ iso.walk.link(l)
