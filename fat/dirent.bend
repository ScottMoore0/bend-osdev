# bend-osdev-fat, dirent.bend: directory entries. The 32-byte short entry
# (an 8.3 name, attributes, the first cluster, the size, times and dates) and
# the long-name entries before it (VFAT), with the short name's checksum.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000),
# section 6 ("FAT Directory Structure") and section 7 ("FAT Long Directory
# Entries").
#
# Short entry offsets: 0 DIR_Name (11: an 8-byte base and a 3-byte extension,
# padded with spaces), 11 DIR_Attr, 12 DIR_NTRes, 13 DIR_CrtTimeTenth,
# 14 DIR_CrtTime (2), 16 DIR_CrtDate (2), 18 DIR_LstAccDate (2),
# 20 DIR_FstClusHI (2), 22 DIR_WrtTime (2), 24 DIR_WrtDate (2),
# 26 DIR_FstClusLO (2), 28 DIR_FileSize (4). DIR_Name[0] is 0xE5 for a free
# (deleted) entry, 0x00 for a free entry with only free entries after it, and
# 0x05 for a name whose first byte really is 0xE5.
#
# Long entry offsets: 0 LDIR_Ord (its sequence number, 0x40 on the last),
# 1 LDIR_Name1 (5 UCS-2 characters), 11 LDIR_Attr (0x0F), 12 LDIR_Type (0),
# 13 LDIR_Chksum, 14 LDIR_Name2 (6 characters), 26 LDIR_FstClusLO (0),
# 28 LDIR_Name3 (2 characters). A name is split into pieces of 13
# characters, stored last piece first just before the short entry; a name
# that does not fill its last piece ends with 0x0000, then 0xFFFF padding.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bpb.bend as P

# Attributes (DIR_Attr)

def FatAttr.read_only() -> U32:
  1

def FatAttr.hidden() -> U32:
  2

def FatAttr.system() -> U32:
  4

def FatAttr.volume_id() -> U32:
  8

def FatAttr.directory() -> U32:
  16

def FatAttr.archive() -> U32:
  32

# ATTR_LONG_NAME: read-only, hidden, system and volume ID together
def FatAttr.long_name() -> U32:
  15

# Short entries

type FatDirent is Data:
  FatDirent{name: B.Octets, attr: U32, nt_res: U32, crt_tenth: U32, crt_time: U32, crt_date: U32, acc_date: U32, clus_hi: U32, wrt_time: U32, wrt_date: U32, clus_lo: U32, size: U32}

# the 11 name bytes an entry stores: name cut, or padded with spaces
def FatDirent.fit_name(name: B.Octets) -> B.Octets:
  B.Octets.of_list(P.Fat.fit(11n, 32, B.Octets.to_list(name)))

# an entry as it is stored: the name as fit_name, the 8-bit fields to 8 bits
# and the 16-bit fields to 16
def FatDirent.norm(d: FatDirent) -> FatDirent:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      FatDirent{FatDirent.fit_name(name), B.byte(attr), B.byte(nt), B.byte(tenth), B.low16(ctime), B.low16(cdate), B.low16(adate), B.low16(hi), B.low16(wtime), B.low16(wdate), B.low16(lo), size}

# bytes 11 to 31
def FatDirent.encode.tail(d: FatDirent) -> List<&2, U32>:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      List.concat(&2, U32, [[attr, nt, tenth], B.le16(ctime), B.le16(cdate), B.le16(adate), B.le16(hi), B.le16(wtime), B.le16(wdate), B.le16(lo), B.le32(size)])

def FatDirent.name(d: FatDirent) -> B.Octets:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      name

# the 32 bytes of a short entry
def FatDirent.encode(+d: FatDirent) -> B.Octets:
  B.Octets.of_list(B.append(P.Fat.fit(11n, 32, B.Octets.to_list(FatDirent.name(d))), FatDirent.encode.tail(d)))

def FatDirent.decode.fin(nm: B.Octets, attr: Maybe<&2, U32>, nt: Maybe<&2, U32>, tenth: Maybe<&2, U32>, ctime: Maybe<&2, U32>, cdate: Maybe<&2, U32>, adate: Maybe<&2, U32>, hi: Maybe<&2, U32>, wtime: Maybe<&2, U32>, wdate: Maybe<&2, U32>, lo: Maybe<&2, U32>, size: Maybe<&2, U32>) -> Result<&2, &2, E.FatError, FatDirent>:
  match attr nt tenth ctime cdate adate hi wtime wdate lo size:
    case Some{a} Some{b} Some{c} Some{e} Some{f} Some{g} Some{h} Some{i} Some{j} Some{k} Some{l}:
      Done{FatDirent{nm, a, b, c, e, f, g, h, i, j, k, l}}
    case _ _ _ _ _ _ _ _ _ _ _:
      Fail{E.FatTooShort{}}

# the fields after the name, from bytes 11 on
def FatDirent.decode.rest(nm: B.Octets, +r: List<&2, U32>) -> Result<&2, &2, E.FatError, FatDirent>:
  FatDirent.decode.fin(nm, B.at(r, 0n), B.at(r, 1n), B.at(r, 2n), B.le16_at(r, 3n), B.le16_at(r, 5n), B.le16_at(r, 7n), B.le16_at(r, 9n), B.le16_at(r, 11n), B.le16_at(r, 13n), B.le16_at(r, 15n), B.le32_at(r, 17n))

def FatDirent.decode.list(+xs: List<&2, U32>) -> Result<&2, &2, E.FatError, FatDirent>:
  FatDirent.decode.rest(B.Octets.of_list(B.take(11n, xs)), B.drop(11n, xs))

# the fields of a 32-byte short entry (FatTooShort if it is shorter)
def FatDirent.decode(o: B.Octets) -> Result<&2, &2, E.FatError, FatDirent>:
  FatDirent.decode.list(B.Octets.to_list(o))

# Fields

def FatDirent.attr(d: FatDirent) -> U32:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      attr

def FatDirent.size(d: FatDirent) -> U32:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      size

# the first cluster: DIR_FstClusHI and DIR_FstClusLO joined (on FAT12/16 the
# high word is 0)
def FatDirent.cluster(d: FatDirent) -> U32:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      U32.or(U32.shln(hi, 16n), lo)

def FatDirent.has_attr(d: FatDirent, a: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(a, FatDirent.attr(d)), 0))

def FatDirent.is_dir(d: FatDirent) -> Bool:
  FatDirent.has_attr(d, FatAttr.directory())

def FatDirent.is_volume_label(d: FatDirent) -> Bool:
  FatDirent.has_attr(d, FatAttr.volume_id())

# Times and dates. A time is hours (bits 11 to 15), minutes (5 to 10) and
# seconds / 2 (0 to 4); a date is years since 1980 (bits 9 to 15), the month
# (5 to 8, 1 to 12) and the day (0 to 4, 1 to 31).

type FatTime is Data:
  FatTime{hour: U32, minute: U32, second: U32}

type FatDate is Data:
  FatDate{year: U32, month: U32, day: U32}

def FatTime.of(+t: U32) -> FatTime:
  FatTime{U32.and(31, U32.shrn(t, 11n)), U32.and(63, U32.shrn(t, 5n)), U32.mul(U32.and(31, t), 2)}

def FatTime.encode(t: FatTime) -> U32:
  match t:
    case FatTime{h, m, s}:
      U32.or(U32.shln(U32.and(31, h), 11n), U32.or(U32.shln(U32.and(63, m), 5n), U32.and(31, U32.div(s, 2))))

def FatDate.of(+d: U32) -> FatDate:
  FatDate{U32.add(1980, U32.and(127, U32.shrn(d, 9n))), U32.and(15, U32.shrn(d, 5n)), U32.and(31, d)}

def FatDate.encode(d: FatDate) -> U32:
  match d:
    case FatDate{y, m, day}:
      U32.or(U32.shln(U32.and(127, U32.sub(y, 1980)), 9n), U32.or(U32.shln(U32.and(15, m), 5n), U32.and(31, day)))

def FatDirent.write_time(d: FatDirent) -> FatTime:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      FatTime.of(wtime)

def FatDirent.write_date(d: FatDirent) -> FatDate:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      FatDate.of(wdate)

def FatDirent.create_time(d: FatDirent) -> FatTime:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      FatTime.of(ctime)

def FatDirent.create_date(d: FatDirent) -> FatDate:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      FatDate.of(cdate)

def FatDirent.access_date(d: FatDirent) -> FatDate:
  match d:
    case FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      FatDate.of(adate)

# Short names

def FatName.first_byte.pick(kanji: Bool, +b: U32) -> U32:
  match kanji:
    case True{}:
      229
    case False{}:
      b

def FatName.pick_nat(c: Bool, a: Nat, b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

def FatName.pick_u32(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def FatName.chars(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      SCon{Char.from_u32(h), FatName.chars(t)}

def FatName.codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.to_u32(c), FatName.codes(t)}

# the length of xs without its trailing spaces (i: the position, best: the
# length so far)
def FatName.trim_len(xs: List<&2, U32>, +i: Nat, +best: Nat) -> Nat:
  match xs:
    case Nil{}:
      best
    case Con{+h, t}:
      FatName.trim_len(t, Nat.add(i, 1n), FatName.pick_nat(U32.is_eq(h, 32), best, Nat.add(i, 1n)))

def FatName.trim(+xs: List<&2, U32>) -> List<&2, U32>:
  B.take(FatName.trim_len(xs, 0n, 0n), xs)

# DIR_Name[0] = 0x05 stands for 0xE5
def FatName.kanji(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{FatName.pick_u32(U32.is_eq(h, 5), 229, h), t}

def FatName.text.ext(+ext: List<&2, U32>) -> String:
  match ext:
    case Nil{}:
      ""
    case Con{h, t}:
      "." ++ FatName.chars(ext)

# ASCII letters to lower case when c (Windows NT's case flags)
def FatName.lower.pick(c: Bool, +b: U32) -> U32:
  match c:
    case True{}:
      U32.add(b, U32.mul(Bool.to_u32(Bool.and(U32.is_ge(b, 65), U32.is_le(b, 90))), 32))
    case False{}:
      b

def FatName.lower_if(+c: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{FatName.lower.pick(c, h), FatName.lower_if(c, t)}

# an 11-byte short name as text, its base or extension in lower case when
# lower_base or lower_ext
def FatName.text_case(name: B.Octets, +lower_base: Bool, +lower_ext: Bool) -> String:
  +xs = FatName.kanji(B.Octets.to_list(name))
  FatName.chars(FatName.lower_if(lower_base, FatName.trim(B.take(8n, xs)))) ++ FatName.text.ext(FatName.lower_if(lower_ext, FatName.trim(B.take(3n, B.drop(8n, xs)))))

# an 11-byte short name as text: "BOOTX64.EFI", "README" (bytes above 127 as
# the code points of the same value: the OEM code page is not known)
def FatName.text(name: B.Octets) -> String:
  FatName.text_case(name, False{}, False{})

# ASCII letters to upper case (what short names store, and how names compare)
def FatName.upper(+b: U32) -> U32:
  U32.sub(b, U32.mul(Bool.to_u32(Bool.and(U32.is_ge(b, 97), U32.is_le(b, 122))), 32))

def FatName.upper_all(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{FatName.upper(h), FatName.upper_all(t)}

# a character a short name may hold: printable ASCII, not a space and none of
# " * + , . / : ; < = > ? [ \ ] |
def FatName.short_char(+c: U32) -> Bool:
  Bool.and(Bool.and(U32.is_gt(c, 32), U32.is_lt(c, 127)), Bool.not(P.Fat.u32_in(c, [34, 42, 43, 44, 46, 47, 58, 59, 60, 61, 62, 63, 91, 92, 93, 124])))

def FatName.all_short(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(FatName.short_char(h), FatName.all_short(t))

def FatName.last_dot.pick(dot: Bool, i: Nat, at: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match dot:
    case True{}:
      Some{i}
    case False{}:
      at

# the position of the last dot (i: the position, at: the last so far)
def FatName.last_dot(xs: List<&2, U32>, +i: Nat, at: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      at
    case Con{+h, t}:
      FatName.last_dot(t, Nat.add(i, 1n), FatName.last_dot.pick(U32.is_eq(h, 46), i, at))

def FatName.short_of.check(ok: Bool, base: List<&2, U32>, ext: List<&2, U32>) -> Maybe<&2, B.Octets>:
  match ok:
    case True{}:
      Some{B.Octets.of_list(B.append(P.Fat.fit(8n, 32, FatName.upper_all(base)), P.Fat.fit(3n, 32, FatName.upper_all(ext))))}
    case False{}:
      None{}

def FatName.short_of.parts(+base: List<&2, U32>, +ext: List<&2, U32>) -> Maybe<&2, B.Octets>:
  +n = B.len(base)
  FatName.short_of.check(Bool.and(Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, 8n)), Bool.and(Nat.is_le(B.len(ext), 3n), Bool.and(FatName.all_short(base), FatName.all_short(ext)))), base, ext)

def FatName.short_of.split(+xs: List<&2, U32>, at: Maybe<&2, Nat>) -> Maybe<&2, B.Octets>:
  match at:
    case None{}:
      FatName.short_of.parts(xs, Nil{})
    case Some{+i}:
      FatName.short_of.parts(B.take(i, xs), B.drop(Nat.add(i, 1n), xs))

def FatName.short_of.dots(dot: Bool, dotdot: Bool, +xs: List<&2, U32>) -> Maybe<&2, B.Octets>:
  match dot dotdot:
    case True{} _:
      Some{B.Octets.of_list(P.Fat.fit(11n, 32, [46]))}
    case False{} True{}:
      Some{B.Octets.of_list(P.Fat.fit(11n, 32, [46, 46]))}
    case False{} False{}:
      FatName.short_of.split(xs, FatName.last_dot(xs, 0n, None{}))

# the 11-byte short name a path component stands for, upper-cased ("efi" is
# "EFI        "), or None if it cannot be one (more than 8 + 3 characters,
# more than one dot, characters a short name cannot hold)
def FatName.short_of(+s: String) -> Maybe<&2, B.Octets>:
  FatName.short_of.dots(String.eq(s, "."), String.eq(s, ".."), FatName.codes(s))

def FatName.list_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, s} Con{b, t}:
      Bool.and(U32.is_eq(a, b), FatName.list_eq(s, t))
    case _ _:
      False{}

# whether two names are equal ignoring the case of ASCII letters
def FatName.same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  FatName.list_eq(FatName.upper_all(xs), FatName.upper_all(ys))

# Long names are UCS-2 code units (UTF-16: characters past U+FFFF as
# surrogate pairs)

def FatName.units.pick(bmp: Bool, +c: U32) -> List<&2, U32>:
  match bmp:
    case True{}:
      [c]
    case False{}:
      [U32.add(55296, U32.shrn(U32.sub(c, 65536), 10n)), U32.add(56320, U32.and(1023, U32.sub(c, 65536)))]

# the code units of a text
def FatName.units(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      +x = Char.to_u32(c)
      B.append(FatName.units.pick(U32.is_lt(x, 65536), x), FatName.units(t))

def FatName.is_high(+u: U32) -> Bool:
  Bool.and(U32.is_ge(u, 55296), U32.is_le(u, 56319))

def FatName.is_low(+u: U32) -> Bool:
  Bool.and(U32.is_ge(u, 56320), U32.is_le(u, 57343))

def FatName.text_of.emit.pending(low: Bool, high: Bool, +h: U32, +u: U32) -> String:
  match low high:
    case True{} _:
      SCon{Char.from_u32(U32.add(65536, U32.add(U32.shln(U32.sub(h, 55296), 10n), U32.sub(u, 56320)))), ""}
    case False{} True{}:
      SCon{Char.from_u32(h), ""}
    case False{} False{}:
      SCon{Char.from_u32(h), SCon{Char.from_u32(u), ""}}

def FatName.text_of.emit.alone(high: Bool, +u: U32) -> String:
  match high:
    case True{}:
      ""
    case False{}:
      SCon{Char.from_u32(u), ""}

# what one unit adds to the text, after the pending high surrogate (if any)
def FatName.text_of.emit(p: Maybe<&2, U32>, +u: U32) -> String:
  match p:
    case Some{+h}:
      FatName.text_of.emit.pending(FatName.is_low(u), FatName.is_high(u), h, u)
    case None{}:
      FatName.text_of.emit.alone(FatName.is_high(u), u)

def FatName.text_of.next.pick(keep: Bool, +u: U32) -> Maybe<&2, U32>:
  match keep:
    case True{}:
      Some{u}
    case False{}:
      None{}

# the high surrogate pending after one unit
def FatName.text_of.next(p: Maybe<&2, U32>, +u: U32) -> Maybe<&2, U32>:
  match p:
    case Some{h}:
      FatName.text_of.next.pick(Bool.and(Bool.not(FatName.is_low(u)), FatName.is_high(u)), u)
    case None{}:
      FatName.text_of.next.pick(FatName.is_high(u), u)

def FatName.text_of.flush(p: Maybe<&2, U32>) -> String:
  match p:
    case Some{h}:
      SCon{Char.from_u32(h), ""}
    case None{}:
      ""

def FatName.text_of.go(us: List<&2, U32>, +p: Maybe<&2, U32>) -> String:
  match us:
    case Nil{}:
      FatName.text_of.flush(p)
    case Con{+u, t}:
      FatName.text_of.emit(p, u) ++ FatName.text_of.go(t, FatName.text_of.next(p, u))

# the text of code units (surrogate pairs joined; a lone surrogate kept)
def FatName.text_of(us: List<&2, U32>) -> String:
  FatName.text_of.go(us, None{})

# Long-name entries

type FatLfn is Data:
  FatLfn{ord: U32, units: List<&2, U32>, chksum: U32}

def FatLfn.ord(e: FatLfn) -> U32:
  match e:
    case FatLfn{o, u, c}:
      o

def FatLfn.units(e: FatLfn) -> List<&2, U32>:
  match e:
    case FatLfn{o, u, c}:
      u

def FatLfn.chksum(e: FatLfn) -> U32:
  match e:
    case FatLfn{o, u, c}:
      c

def FatLfn.checksum.go(xs: List<&2, U32>, +sum: U32) -> U32:
  match xs:
    case Nil{}:
      sum
    case Con{h, t}:
      FatLfn.checksum.go(t, U32.and(255, U32.add(U32.add(U32.shln(U32.and(1, sum), 7n), U32.shrn(sum, 1n)), h)))

# the checksum of an 11-byte short name that its long-name entries carry
# (section 7.2: rotate the sum right by one bit, add the next byte, mod 256)
def FatLfn.checksum(name: B.Octets) -> U32:
  FatLfn.checksum.go(B.Octets.to_list(FatDirent.fit_name(name)), 0)

def FatLfn.le16s(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      B.append(B.le16(h), FatLfn.le16s(t))

# the 32 bytes of a long-name entry (its units cut, or padded with 0xFFFF, to
# 13)
def FatLfn.encode(e: FatLfn) -> B.Octets:
  match e:
    case FatLfn{o, u, c}:
      +us = P.Fat.fit(13n, 65535, u)
      B.Octets.of_list(List.concat(&2, U32, [[o], FatLfn.le16s(B.take(5n, us)), [15, 0, c], FatLfn.le16s(B.take(6n, B.drop(5n, us))), [0, 0], FatLfn.le16s(B.drop(11n, us))]))

def FatLfn.decode.go(+xs: List<&2, U32>) -> Maybe<&2, FatLfn>:
  do Maybe<&2, FatLfn>:
    o : U32 <- B.at(xs, 0n)
    c : U32 <- B.at(xs, 13n)
    u0 : U32 <- B.le16_at(xs, 1n)
    u1 : U32 <- B.le16_at(xs, 3n)
    u2 : U32 <- B.le16_at(xs, 5n)
    u3 : U32 <- B.le16_at(xs, 7n)
    u4 : U32 <- B.le16_at(xs, 9n)
    u5 : U32 <- B.le16_at(xs, 14n)
    u6 : U32 <- B.le16_at(xs, 16n)
    u7 : U32 <- B.le16_at(xs, 18n)
    u8 : U32 <- B.le16_at(xs, 20n)
    u9 : U32 <- B.le16_at(xs, 22n)
    u10 : U32 <- B.le16_at(xs, 24n)
    u11 : U32 <- B.le16_at(xs, 28n)
    u12 : U32 <- B.le16_at(xs, 30n)
    return FatLfn{o, [u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12], c}

def FatLfn.decode.fin(m: Maybe<&2, FatLfn>) -> Result<&2, &2, E.FatError, FatLfn>:
  match m:
    case Some{e}:
      Done{e}
    case None{}:
      Fail{E.FatTooShort{}}

def FatLfn.decode.check(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, E.FatError, FatLfn>:
  match ok:
    case True{}:
      FatLfn.decode.fin(FatLfn.decode.go(xs))
    case False{}:
      Fail{E.FatNotLongEntry{}}

def FatLfn.attr_is_long(m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{x}:
      U32.is_eq(U32.and(63, x), 15)
    case None{}:
      False{}

# whether 32 bytes are a long-name entry: (DIR_Attr & 0x3F) == 0x0F and the
# entry not free (DIR_Name[0] neither 0xE5 nor 0x00)
def FatLfn.is_long.list(+xs: List<&2, U32>) -> Bool:
  Bool.and(FatLfn.attr_is_long(B.at(xs, 11n)), Bool.not(Bool.or(P.Fat.byte_is(B.at(xs, 0n), 229), P.Fat.byte_is(B.at(xs, 0n), 0))))

def FatLfn.is_long(o: B.Octets) -> Bool:
  FatLfn.is_long.list(B.Octets.to_list(o))

# the fields of a long-name entry (FatNotLongEntry if it is not one)
def FatLfn.decode(o: B.Octets) -> Result<&2, &2, E.FatError, FatLfn>:
  +xs = B.Octets.to_list(o)
  FatLfn.decode.check(FatLfn.is_long.list(xs), xs)

# Building the long-name entries of a name

def FatLfn.piece.term(ended: Bool) -> U32:
  match ended:
    case True{}:
      65535
    case False{}:
      0

# n units of a name from its piece on: the name's units, then 0x0000 if it
# ends here, then 0xFFFF
def FatLfn.piece(n: Nat, us: List<&2, U32>, +ended: Bool) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match us:
        case Con{h, t}:
          Con{h, FatLfn.piece(p, t, False{})}
        case Nil{}:
          Con{FatLfn.piece.term(ended), FatLfn.piece(p, Nil{}, True{})}

def FatLfn.ord_of(+i: Nat, +k: Nat) -> U32:
  U32.or(U32.from_nat(i), U32.mul(Bool.to_u32(Nat.is_eq(i, k)), 64))

# entries i down to 1 of a name in k pieces
def FatLfn.build.go(+i: Nat, +k: Nat, +name: List<&2, U32>, +chk: U32) -> List<&2, FatLfn>:
  match i:
    case 0n:
      Nil{}
    case 1n+p:
      Con{FatLfn{FatLfn.ord_of(1n+p, k), FatLfn.piece(13n, B.drop(Nat.mul(p, 13n), name), False{}), chk}, FatLfn.build.go(p, k, name, chk)}

# the number of entries a name of n units needs
def FatLfn.count(+n: Nat) -> Nat:
  Nat.div(Nat.add(n, 12n), 13n)

# the long-name entries of a name (1 to 255 units) for the short name short,
# in the order they are stored: the last piece (ordinal 0x40 | k) first
def FatLfn.build(short: B.Octets, +name: List<&2, U32>) -> List<&2, FatLfn>:
  +k = FatLfn.count(B.len(name))
  FatLfn.build.go(k, k, name, FatLfn.checksum(short))

# whether every entry carries the checksum c
def FatLfn.carries(es: List<&2, FatLfn>, +c: U32) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{FatLfn{o, u, x}, t}:
      Bool.and(U32.is_eq(x, c), FatLfn.carries(t, c))

def FatLfn.cut.put(stop: Bool, h: U32, r: List<&2, U32>) -> List<&2, U32>:
  match stop:
    case True{}:
      Nil{}
    case False{}:
      Con{h, r}

# a name's units up to its 0x0000 terminator (the 0xFFFF padding after it
# dropped)
def FatLfn.cut.go(us: List<&2, U32>, +stop: Bool) -> List<&2, U32>:
  match us:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +s = Bool.or(stop, U32.is_eq(h, 0))
      FatLfn.cut.put(s, h, FatLfn.cut.go(t, s))

def FatLfn.cut(us: List<&2, U32>) -> List<&2, U32>:
  FatLfn.cut.go(us, False{})

# A short entry's name as text, with Windows NT's case flags applied: bit 3
# of DIR_NTRes for a lower-case base, bit 4 for a lower-case extension. The
# specification reserves DIR_NTRes; these flags are the convention Windows NT
# and later (and mtools) follow for a name that is all lower case.
def FatDirent.short_text(d: FatDirent) -> String:
  match d:
    case FatDirent{name, attr, +nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}:
      FatName.text_case(name, Bool.not(U32.is_eq(U32.and(8, nt), 0)), Bool.not(U32.is_eq(U32.and(16, nt), 0)))
