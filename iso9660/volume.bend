# bend-osdev-iso9660, volume.bend: the volume descriptor set (ECMA-119, 4th
# edition, 8), the options a volume is read with, and opening a volume.
#
# The descriptor set starts at logical sector 16, one descriptor per 2048-
# byte sector: a type byte (0 boot record, 1 primary, 2 supplementary, 3
# partition, 255 terminator), the standard identifier "CD001" and a version
# byte (1; 2 for an enhanced volume descriptor). The primary and
# supplementary descriptors share their layout (8.4, 8.5):
#   8..39 system identifier, 40..71 volume identifier, 80..87 volume space
#   size (both-endian 32), 88..119 escape sequences (supplementary only),
#   120..123 volume set size, 124..127 volume sequence number, 128..131
#   logical block size (both-endian 16 each), 132..139 path table size,
#   140 and 144 type L path tables (little-endian), 148 and 152 type M path
#   tables (big-endian), 156..189 the root directory record, 190..317 volume
#   set identifier, 318..445 publisher, 446..573 data preparer, 574..701
#   application, 702..738 copyright file, 739..775 abstract file, 776..812
#   bibliographic file, 813, 830, 847 and 864 the creation, modification,
#   expiration and effective dates (17 bytes each), 881 file structure version.
# A boot record (8.2) of the El Torito specification (Phoenix and IBM, 1995)
# names "EL TORITO SPECIFICATION" at 7 and the boot catalog's sector at 71
# (little-endian 32).
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as BD
import ./fields.bend as F
import ./joliet.bend as J
import ./dirrec.bend as R
import ./susp.bend as S
import ./rockridge.bend as RR

# Options

# which names a volume's files are listed under
type IsoNaming is Data:
  # Rock Ridge if the volume has it, else Joliet if it has it, else plain
  IsoNamingAuto{}
  # the ISO 9660 file identifiers of the primary hierarchy
  IsoNamingPlain{}
  # the UCS-2 names of the Joliet hierarchy
  IsoNamingJoliet{}
  # the Rock Ridge NM names of the primary hierarchy
  IsoNamingRockRidge{}

type IsoOptions is Data:
  IsoOptions{naming: IsoNaming, endian: F.IsoEndian, strip_version: Bool, follow_relocation: Bool, max_descriptors: Nat, max_continuations: Nat, max_depth: Nat}

# Rock Ridge, then Joliet, then plain; both-endian halves checked; ";1"
# versions dropped; relocated directories followed; at most 32 volume
# descriptors, 16 continuation areas per record and 64 directory levels
def IsoOptions.default() -> IsoOptions:
  IsoOptions{IsoNamingAuto{}, F.IsoEndianCheck{}, True{}, True{}, 32n, 16n, 64n}

def IsoOptions.with_naming(o: IsoOptions, n: IsoNaming) -> IsoOptions:
  match o:
    case IsoOptions{a, e, s, f, md, mc, mx}:
      IsoOptions{n, e, s, f, md, mc, mx}

def IsoOptions.with_endian(o: IsoOptions, e: F.IsoEndian) -> IsoOptions:
  match o:
    case IsoOptions{a, x, s, f, md, mc, mx}:
      IsoOptions{a, e, s, f, md, mc, mx}

def IsoOptions.with_strip_version(o: IsoOptions, s: Bool) -> IsoOptions:
  match o:
    case IsoOptions{a, e, x, f, md, mc, mx}:
      IsoOptions{a, e, s, f, md, mc, mx}

def IsoOptions.with_follow_relocation(o: IsoOptions, f: Bool) -> IsoOptions:
  match o:
    case IsoOptions{a, e, s, x, md, mc, mx}:
      IsoOptions{a, e, s, f, md, mc, mx}

def IsoNaming.show(n: IsoNaming) -> String:
  match n:
    case IsoNamingAuto{}:
      "auto"
    case IsoNamingPlain{}:
      "plain"
    case IsoNamingJoliet{}:
      "joliet"
    case IsoNamingRockRidge{}:
      "rockridge"

# Volume descriptors

type IsoPvd is Data:
  IsoPvd{system_id: String, volume_id: String, space_size: U32, set_size: U32, seq_number: U32, block_size: U32, path_table_size: U32, path_table_l: U32, path_table_m: U32, root: R.IsoDirRec, volume_set_id: String, publisher_id: String, preparer_id: String, application_id: String, copyright_file: String, abstract_file: String, biblio_file: String, created: B.Octets, modified: B.Octets, expires: B.Octets, effective: B.Octets, file_structure: U32}

type IsoDescriptor is Data:
  IsoDescPrimary{pvd: IsoPvd}
  # flags, escape sequences, Joliet level (0 if not Joliet), the descriptor
  IsoDescSupplementary{flags: U32, escapes: B.Octets, joliet: Nat, svd: IsoPvd}
  # boot system identifier, boot catalog sector (El Torito)
  IsoDescBoot{system_id: String, catalog: U32}
  IsoDescPartition{}
  IsoDescUnknown{kind: U32}
  IsoDescTerminator{}

def IsoDescriptor.show(d: IsoDescriptor) -> String:
  match d:
    case IsoDescPrimary{p}:
      "primary"
    case IsoDescSupplementary{f, e, j, p}:
      "supplementary joliet " ++ Nat.show(j)
    case IsoDescBoot{s, c}:
      "boot " ++ s ++ " catalog " ++ U32.show(c)
    case IsoDescPartition{}:
      "partition"
    case IsoDescUnknown{k}:
      "unknown " ++ U32.show(k)
    case IsoDescTerminator{}:
      "terminator"

def iso.vd.text.go(joliet: Bool, o: B.Octets) -> String:
  match joliet:
    case True{}:
      J.Iso.ucs2_text(o)
    case False{}:
      F.Iso.text(o)

# an identifier field: a-/d-characters, or UCS-2 in a Joliet descriptor
def iso.vd.text(+joliet: Bool, +i: Nat, n: Nat, xs: List<&2, U32>) -> String:
  iso.vd.text.go(joliet, F.iso.slice(i, n, xs))

def iso.vd.root(+mode: F.IsoEndian, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, R.IsoDirRec>:
  R.iso.dirrec.list(mode, B.take(34n, B.drop(156n, xs)))

def iso.vd.pvd(+mode: F.IsoEndian, +joliet: Bool, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoPvd>:
  do Result<&2, &2, F.IsoError, IsoPvd>:
    space : U32 <- F.iso.both32.list(mode, B.drop(80n, xs), 80n)
    setsz : U32 <- F.iso.both16.list(mode, B.drop(120n, xs), 120n)
    seq : U32 <- F.iso.both16.list(mode, B.drop(124n, xs), 124n)
    bsz : U32 <- F.iso.both16.list(mode, B.drop(128n, xs), 128n)
    ptsz : U32 <- F.iso.both32.list(mode, B.drop(132n, xs), 132n)
    ptl : U32 <- F.iso.le32(xs, 140n)
    ptm : U32 <- F.iso.be32(xs, 148n)
    root : R.IsoDirRec <- iso.vd.root(mode, xs)
    fsv : U32 <- F.iso.u8(xs, 881n)
    return IsoPvd{iso.vd.text(joliet, 8n, 32n, xs), iso.vd.text(joliet, 40n, 32n, xs), space, setsz, seq, bsz, ptsz, ptl, ptm, root, iso.vd.text(joliet, 190n, 128n, xs), iso.vd.text(joliet, 318n, 128n, xs), iso.vd.text(joliet, 446n, 128n, xs), iso.vd.text(joliet, 574n, 128n, xs), iso.vd.text(joliet, 702n, 37n, xs), iso.vd.text(joliet, 739n, 37n, xs), iso.vd.text(joliet, 776n, 37n, xs), F.iso.slice(813n, 17n, xs), F.iso.slice(830n, 17n, xs), F.iso.slice(847n, 17n, xs), F.iso.slice(864n, 17n, xs), fsv}

def iso.vd.svd(+mode: F.IsoEndian, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDescriptor>:
  +esc = F.iso.slice(88n, 32n, xs)
  +level = J.Iso.joliet_level(esc)
  do Result<&2, &2, F.IsoError, IsoDescriptor>:
    fl : U32 <- F.iso.u8(xs, 7n)
    p : IsoPvd <- iso.vd.pvd(mode, Bool.not(Nat.is_eq(level, 0n)), xs)
    return IsoDescSupplementary{fl, esc, level, p}

def iso.vd.zstr.go(z: Bool, h: U32, rest: String) -> String:
  match z:
    case True{}:
      ""
    case False{}:
      SCon{Chr{h}, rest}

# a text field padded with zero bytes
def iso.vd.zstr(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+h, t}:
      iso.vd.zstr.go(U32.is_eq(h, 0), h, iso.vd.zstr(t))

def iso.vd.boot(+xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDescriptor>:
  do Result<&2, &2, F.IsoError, IsoDescriptor>:
    c : U32 <- F.iso.le32(xs, 71n)
    return IsoDescBoot{iso.vd.zstr(B.take(32n, B.drop(7n, xs))), c}

def iso.vd.kind(+mode: F.IsoEndian, k: Nat, +xs: List<&2, U32>, +ty: U32) -> Result<&2, &2, F.IsoError, IsoDescriptor>:
  match k:
    case 0n:
      iso.vd.boot(xs)
    case 1n:
      Result.map(&2, &2, F.IsoError, IsoPvd, IsoDescriptor, p => IsoDescPrimary{p}, iso.vd.pvd(mode, False{}, xs))
    case 2n:
      iso.vd.svd(mode, xs)
    case 3n:
      Done{IsoDescPartition{}}
    case 255n:
      Done{IsoDescTerminator{}}
    case _:
      Done{IsoDescUnknown{ty}}

def iso.vd.is_cd001(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{t, Con{a, Con{b, Con{c, Con{d, Con{e, Con{v, r}}}}}}}:
      Bool.and(Bool.and(U32.is_eq(a, 67), U32.is_eq(b, 68)), Bool.and(Bool.and(U32.is_eq(c, 48), U32.is_eq(d, 48)), U32.is_eq(e, 49)))
    case _:
      False{}

def iso.vd.version_ok(+ty: U32, v: Maybe<&2, U32>) -> Bool:
  match v:
    case Some{+x}:
      Bool.or(U32.is_eq(x, 1), Bool.and(U32.is_eq(ty, 2), U32.is_eq(x, 2)))
    case None{}:
      False{}

def iso.vd.check(id: Bool, ver: Bool, +sector: Nat, +mode: F.IsoEndian, +xs: List<&2, U32>, +ty: U32) -> Result<&2, &2, F.IsoError, IsoDescriptor>:
  match id ver:
    case False{} _:
      Fail{F.IsoNotIso{sector}}
    case True{} False{}:
      Fail{F.IsoBadDescriptorVersion{sector}}
    case True{} True{}:
      iso.vd.kind(mode, U32.to_nat(ty), xs, ty)

def iso.vd.parse.go(+sector: Nat, +mode: F.IsoEndian, +xs: List<&2, U32>, t: Maybe<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDescriptor>:
  match t:
    case Some{+ty}:
      iso.vd.check(iso.vd.is_cd001(xs), iso.vd.version_ok(ty, B.at(xs, 6n)), sector, mode, xs, ty)
    case None{}:
      Fail{F.IsoNotIso{sector}}

# the volume descriptor in a sector (sector is its number, for errors)
def Iso.descriptor_parse(mode: F.IsoEndian, sector: Nat, o: B.Octets) -> Result<&2, &2, F.IsoError, IsoDescriptor>:
  +xs = B.Octets.to_list(o)
  iso.vd.parse.go(sector, mode, xs, B.at(xs, 0n))

def iso.vd.is_term(d: IsoDescriptor) -> Bool:
  match d:
    case IsoDescTerminator{}:
      True{}
    case _:
      False{}

def iso.vd.end(stop: Bool) -> Result<&2, &2, F.IsoError, List<&2, IsoDescriptor>>:
  match stop:
    case True{}:
      Done{Nil{}}
    case False{}:
      Fail{F.IsoNoTerminator{}}

# the descriptors from sector n on, up to the terminator, at most fuel of
# them; stop: the terminator was just read, so nothing more is
def iso.vd.set(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, fuel: Nat, stop: Bool, +d: D, +mode: F.IsoEndian, +n: Nat) -> Result<&2, &2, F.IsoError, List<&2, IsoDescriptor>>:
  match fuel:
    case 0n:
      iso.vd.end(stop)
    case 1n+f:
      match stop:
        case True{}:
          Done{Nil{}}
        case False{}:
          do Result<&2, &2, F.IsoError, List<&2, IsoDescriptor>>:
            blk : B.Octets <- F.iso.read_sector(~D, ~read_block, d, n)
            +desc : IsoDescriptor <- Iso.descriptor_parse(mode, n, blk)
            rest : List<&2, IsoDescriptor> <- iso.vd.set(~D, ~read_block, f, iso.vd.is_term(desc), d, mode, 1n+n)
            return Con{desc, rest}

# the volume descriptor set, from sector 16 to its terminator
def Iso.descriptors(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, opts: IsoOptions) -> Result<&2, &2, F.IsoError, List<&2, IsoDescriptor>>:
  match opts:
    case IsoOptions{nm, e, s, f, md, mc, mx}:
      iso.vd.set(~D, ~read_block, md, False{}, d, e, 16n)

# El Torito: the boot catalog's validation entry (header 1, platform, ID,
# a checksum making its sixteen 16-bit words sum to 0, then 0x55 0xAA) and
# its initial/default entry (boot indicator 0x88 bootable or 0, media type,
# load segment, system type, sector count, load RBA)

type IsoBootEntry is Data:
  IsoBootEntry{bootable: Bool, media: U32, load_segment: U32, system_type: U32, sectors: U32, rba: U32}

type IsoBootCatalog is Data:
  IsoBootCatalog{platform: U32, id: String, initial: IsoBootEntry}

def iso.boot.sum(k: Nat, xs: List<&2, U32>, acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      +ys = xs
      iso.boot.sum(p, B.drop(2n, ys), U32.add(acc, Maybe.default(&2, U32, B.le16.head(ys), 0)))

def iso.boot.ok(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoBootCatalog>:
  match ok:
    case True{}:
      do Result<&2, &2, F.IsoError, IsoBootCatalog>:
        pl : U32 <- F.iso.u8(xs, 1n)
        bi : U32 <- F.iso.u8(xs, 32n)
        mt : U32 <- F.iso.u8(xs, 33n)
        ls : U32 <- F.iso.le16(xs, 34n)
        st : U32 <- F.iso.u8(xs, 36n)
        sc : U32 <- F.iso.le16(xs, 38n)
        rba : U32 <- F.iso.le32(xs, 40n)
        return IsoBootCatalog{pl, iso.vd.zstr(B.take(24n, B.drop(4n, xs))), IsoBootEntry{U32.is_eq(bi, 136), mt, ls, st, sc, rba}}
    case False{}:
      Fail{F.IsoBadBootCatalog{}}

def iso.boot.is(m: Maybe<&2, U32>, v: U32) -> Bool:
  match m:
    case Some{x}:
      U32.is_eq(x, v)
    case None{}:
      False{}

# the boot catalog in a sector
def Iso.boot_catalog_parse(o: B.Octets) -> Result<&2, &2, F.IsoError, IsoBootCatalog>:
  +xs = B.Octets.to_list(o)
  iso.boot.ok(Bool.and(Bool.and(iso.boot.is(B.at(xs, 0n), 1), U32.is_eq(U32.and(65535, iso.boot.sum(16n, xs, 0)), 0)), Bool.and(iso.boot.is(B.at(xs, 30n), 85), iso.boot.is(B.at(xs, 31n), 170))), xs)

# Opening a volume

type IsoVolume is Data:
  IsoVolume{opts: IsoOptions, naming: IsoNaming, pvd: IsoPvd, root: R.IsoDirRec, joliet: Nat, rr_skip: Nat, boot_catalog: Maybe<&2, U32>, descriptors: List<&2, IsoDescriptor>}

def iso.open.primary(ds: List<&2, IsoDescriptor>) -> Result<&2, &2, F.IsoError, IsoPvd>:
  match ds:
    case Nil{}:
      Fail{F.IsoNoPrimary{}}
    case Con{IsoDescPrimary{p}, t}:
      Done{p}
    case Con{h, t}:
      iso.open.primary(t)

# the Joliet descriptor with the highest level (0 and None if there is none)
type IsoJolietSvd is Data:
  IsoJolietSvd{level: Nat, svd: Maybe<&2, IsoPvd>}

def iso.open.joliet.pick(better: Bool, l: Nat, p: IsoPvd, rest: IsoJolietSvd) -> IsoJolietSvd:
  match better:
    case True{}:
      IsoJolietSvd{l, Some{p}}
    case False{}:
      rest

def iso.open.joliet.cmp(+l: Nat, p: IsoPvd, rest: IsoJolietSvd) -> IsoJolietSvd:
  match rest:
    case IsoJolietSvd{+rl, rp}:
      iso.open.joliet.pick(Nat.is_gt(l, rl), l, p, IsoJolietSvd{rl, rp})

def iso.open.joliet(ds: List<&2, IsoDescriptor>) -> IsoJolietSvd:
  match ds:
    case Nil{}:
      IsoJolietSvd{0n, None{}}
    case Con{IsoDescSupplementary{f, e, l, p}, t}:
      iso.open.joliet.cmp(l, p, iso.open.joliet(t))
    case Con{h, t}:
      iso.open.joliet(t)

def iso.open.boot(ds: List<&2, IsoDescriptor>) -> Maybe<&2, U32>:
  match ds:
    case Nil{}:
      None{}
    case Con{IsoDescBoot{s, c}, t}:
      Some{c}
    case Con{h, t}:
      iso.open.boot(t)

def IsoPvd.root_of(p: IsoPvd) -> R.IsoDirRec:
  match p:
    case IsoPvd{a, b, c, d, e, f, g, h, i, root, k, l, m, n, o, q, r, s, t, u, v, w}:
      root

def IsoPvd.block_size_of(p: IsoPvd) -> U32:
  match p:
    case IsoPvd{a, b, c, d, e, bs, g, h, i, root, k, l, m, n, o, q, r, s, t, u, v, w}:
      bs

def IsoPvd.space_size_of(p: IsoPvd) -> U32:
  match p:
    case IsoPvd{a, b, sp, d, e, bs, g, h, i, root, k, l, m, n, o, q, r, s, t, u, v, w}:
      sp

def IsoPvd.volume_id_of(p: IsoPvd) -> String:
  match p:
    case IsoPvd{a, vid, sp, d, e, bs, g, h, i, root, k, l, m, n, o, q, r, s, t, u, v, w}:
      vid

# Rock Ridge on the primary hierarchy: LEN_SKP when its root's "\0" record
# starts with an SP entry and its entries mark RRIP

def iso.open.rr.yes(yes: Bool, skip: Nat) -> Maybe<&2, Nat>:
  match yes:
    case True{}:
      Some{skip}
    case False{}:
      None{}

def iso.open.rr.got(+skip: Nat, es: List<&2, S.IsoSuspEntry>) -> Maybe<&2, Nat>:
  iso.open.rr.yes(RR.Iso.rr_present(es), skip)

def iso.open.rr.sp(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, mode: F.IsoEndian, fuel: Nat, m: Maybe<&2, Nat>, su: B.Octets) -> Result<&2, &2, F.IsoError, Maybe<&2, Nat>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{+skip}:
      Result.map(&2, &2, F.IsoError, List<&2, S.IsoSuspEntry>, Maybe<&2, Nat>, es => iso.open.rr.got(skip, es), S.Iso.susp_entries(~D, ~read_block, d, mode, fuel, 0n, su))

def iso.open.rr(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +mode: F.IsoEndian, fuel: Nat, root: R.IsoDirRec) -> Result<&2, &2, F.IsoError, Maybe<&2, Nat>>:
  do Result<&2, &2, F.IsoError, Maybe<&2, Nat>>:
    blk : B.Octets <- F.iso.read_sector(~D, ~read_block, d, U32.to_nat(R.IsoDirRec.extent_of(root)))
    +self : R.IsoDirRec <- R.IsoDirRec.decode(mode, blk)
    iso.open.rr.sp(~D, ~read_block, d, mode, fuel, S.Iso.susp_sp(R.IsoDirRec.system_use_of(self)), R.IsoDirRec.system_use_of(self))

# Rock Ridge is looked for unless plain or Joliet naming was asked for
def iso.open.rr.need(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, nm: IsoNaming, +d: D, +mode: F.IsoEndian, fuel: Nat, root: R.IsoDirRec) -> Result<&2, &2, F.IsoError, Maybe<&2, Nat>>:
  match nm:
    case IsoNamingPlain{}:
      Done{None{}}
    case IsoNamingJoliet{}:
      Done{None{}}
    case _:
      iso.open.rr(~D, ~read_block, d, mode, fuel, root)

def iso.open.choose(n: IsoNaming, rr: Maybe<&2, Nat>, j: IsoJolietSvd, opts: IsoOptions, +p: IsoPvd, ds: List<&2, IsoDescriptor>, boot: Maybe<&2, U32>) -> Result<&2, &2, F.IsoError, IsoVolume>:
  match n rr j:
    case IsoNamingAuto{} Some{k} _:
      Done{IsoVolume{opts, IsoNamingRockRidge{}, p, IsoPvd.root_of(p), 0n, k, boot, ds}}
    case IsoNamingAuto{} None{} IsoJolietSvd{l, Some{s}}:
      Done{IsoVolume{opts, IsoNamingJoliet{}, p, IsoPvd.root_of(s), l, 0n, boot, ds}}
    case IsoNamingAuto{} None{} IsoJolietSvd{l, None{}}:
      Done{IsoVolume{opts, IsoNamingPlain{}, p, IsoPvd.root_of(p), 0n, 0n, boot, ds}}
    case IsoNamingPlain{} _ _:
      Done{IsoVolume{opts, IsoNamingPlain{}, p, IsoPvd.root_of(p), 0n, 0n, boot, ds}}
    case IsoNamingRockRidge{} Some{k} _:
      Done{IsoVolume{opts, IsoNamingRockRidge{}, p, IsoPvd.root_of(p), 0n, k, boot, ds}}
    case IsoNamingRockRidge{} None{} _:
      Fail{F.IsoNoRockRidge{}}
    case IsoNamingJoliet{} _ IsoJolietSvd{l, Some{s}}:
      Done{IsoVolume{opts, IsoNamingJoliet{}, p, IsoPvd.root_of(s), l, 0n, boot, ds}}
    case IsoNamingJoliet{} _ IsoJolietSvd{l, None{}}:
      Fail{F.IsoNoJoliet{}}

def iso.open.bs(ok: Bool, +p: IsoPvd) -> Result<&2, &2, F.IsoError, IsoPvd>:
  match ok:
    case True{}:
      Done{p}
    case False{}:
      Fail{F.IsoBadLogicalBlockSize{IsoPvd.block_size_of(p)}}

def iso.open.go(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +opts: IsoOptions) -> Result<&2, &2, F.IsoError, IsoVolume>:
  match opts:
    case IsoOptions{+nm, +e, s, f, md, +mc, mx}:
      do Result<&2, &2, F.IsoError, IsoVolume>:
        +ds : List<&2, IsoDescriptor> <- Iso.descriptors(~D, ~read_block, d, opts)
        +p0 : IsoPvd <- iso.open.primary(ds)
        +p : IsoPvd <- iso.open.bs(U32.is_eq(IsoPvd.block_size_of(p0), 2048), p0)
        rr : Maybe<&2, Nat> <- iso.open.rr.need(~D, ~read_block, nm, d, e, mc, IsoPvd.root_of(p))
        iso.open.choose(nm, rr, iso.open.joliet(ds), opts, p, ds, iso.open.boot(ds))

def iso.open.dev(ok: Bool, +n: Nat, r: Result<&2, &2, F.IsoError, IsoVolume>) -> Result<&2, &2, F.IsoError, IsoVolume>:
  match ok:
    case True{}:
      r
    case False{}:
      Fail{F.IsoBadBlockSize{n}}

# a volume on a device of 2048-byte blocks: its descriptors, the hierarchy
# and naming chosen by opts, and where its boot catalog is
def Iso.open(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, opts: IsoOptions) -> Result<&2, &2, F.IsoError, IsoVolume>:
  +bs = block_size(d)
  iso.open.dev(Nat.is_eq(bs, 2048n), bs, iso.open.go(~D, ~read_block, d, opts))

# the boot catalog of a volume with an El Torito boot record
def Iso.boot_catalog(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, v: IsoVolume) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoBootCatalog>>:
  match v:
    case IsoVolume{o, n, p, r, j, k, Some{c}, ds}:
      do Result<&2, &2, F.IsoError, Maybe<&2, IsoBootCatalog>>:
        blk : B.Octets <- F.iso.read_sector(~D, ~read_block, d, U32.to_nat(c))
        cat : IsoBootCatalog <- Iso.boot_catalog_parse(blk)
        return Some{cat}
    case IsoVolume{o, n, p, r, j, k, None{}, ds}:
      Done{None{}}

def IsoVolume.naming_of(v: IsoVolume) -> IsoNaming:
  match v:
    case IsoVolume{o, n, p, r, j, k, b, ds}:
      n

def IsoVolume.pvd_of(v: IsoVolume) -> IsoPvd:
  match v:
    case IsoVolume{o, n, p, r, j, k, b, ds}:
      p
