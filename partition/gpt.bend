# bend-osdev-partition, gpt.bend: the GUID Partition Table (UEFI
# Specification, chapter 5, "GUID Partition Table (GPT) Disk Layout").
#
# The header (section 5.3.2), at LBA 1 and, as a backup, at the last LBA:
#   0 "EFI PART"   8 revision   12 header size   16 header CRC32
#  20 reserved    24 my LBA    32 alternate LBA  40 first usable LBA
#  48 last usable LBA          56 disk GUID      72 partition entries LBA
#  80 number of entries        84 size of an entry   88 entries CRC32
# and zeros to the end of the block. Every field is little-endian; GUIDs are
# in the mixed-endian GUID layout. The header CRC32 (CRC-32/ISO-HDLC) covers
# the first header-size bytes with the CRC field itself taken as zero; the
# entries CRC32 covers number-of-entries times entry-size bytes of the array.
#
# A partition entry (section 5.3.3): type GUID (all zeros: unused), unique
# GUID, first and last LBA (inclusive), attributes, and the name, 36 UTF-16LE
# code units.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../crc/crc.bend as C
import ../uuid/uuid.bend as U

type GptHeader is Data:
  GptHeader{revision: U32, header_size: U32, header_crc: U32, my_lba: W.W64, alternate_lba: W.W64, first_usable: W.W64, last_usable: W.W64, disk_guid: U.Uuid, entries_lba: W.W64, entry_count: U32, entry_size: U32, entries_crc: U32}

# name: the 36 UTF-16 code units of the name field (GptEntry.name_text
# decodes them)
type GptEntry is Data:
  GptEntry{type_guid: U.Uuid, unique_guid: U.Uuid, first_lba: W.W64, last_lba: W.W64, attributes: W.W64, name: List<&2, U32>}

# The choices a new table is laid out with: the logical block size in bytes
# and the number of entries in the array
type GptLayout is Data:
  GptLayout{block_size: U32, entry_count: U32}

# why a header or an entry array was refused
type GptError is Data:
  GptTooShort{}
  GptBadSignature{}
  GptBadHeaderSize{}
  GptBadHeaderCrc{}
  GptBadEntrySize{}
  GptBadEntriesCrc{}

def GptError.show(e: GptError) -> String:
  match e:
    case GptTooShort{}:
      "too short"
    case GptBadSignature{}:
      "no EFI PART signature"
    case GptBadHeaderSize{}:
      "bad header size"
    case GptBadHeaderCrc{}:
      "bad header CRC"
    case GptBadEntrySize{}:
      "bad entry size"
    case GptBadEntriesCrc{}:
      "bad entries CRC"

# 512-byte blocks and 128 entries (16 KiB of entries), as partitioning tools
# create by default and the specification's minimum array size requires
def GptLayout.standard() -> GptLayout:
  GptLayout{512, 128}

# Internal helpers

def Gpt.signature() -> List<&2, U32>:
  [69, 70, 73, 32, 80, 65, 82, 84]

def Gpt.list_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, s} Con{b, t}:
      Bool.and(U32.is_eq(a, b), Gpt.list_eq(s, t))
    case _ _:
      False{}

# the four bytes of a word, least significant first, as a list whose shape
# does not depend on the word
def Gpt.le32s(+v: U32) -> List<&2, U32>:
  [B.byte(v), B.byte(U32.shrn(v, 8n)), B.byte(U32.shrn(v, 16n)), B.byte(U32.shrn(v, 24n))]

def Gpt.take_u32.pick(stop: Bool, h: U32, r: List<&2, U32>) -> List<&2, U32>:
  match stop:
    case True{}:
      Nil{}
    case False{}:
      Con{h, r}

# the first n bytes, n a U32 (no unary count is built)
def Gpt.take_u32(xs: List<&2, U32>, +n: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Gpt.take_u32.pick(U32.is_zero(n), h, Gpt.take_u32(t, U32.sub(n, 1)))

# the GUID read from 16 bytes in the GUID layout
def Gpt.guid_m(r: Result<&2, &2, U.UuidError, U.Uuid>) -> Maybe<&2, U.Uuid>:
  match r:
    case Done{g}:
      Some{g}
    case Fail{e}:
      None{}

def Gpt.guid_at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U.Uuid>:
  Gpt.guid_m(U.Uuid.from_guid_list(B.take(16n, B.drop(i, xs))))

def Gpt.u32_or0(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{x}:
      x
    case None{}:
      0

# Header CRC

# the header with its CRC field read as zero
def Gpt.zeroed(+s: List<&2, U32>) -> List<&2, U32>:
  B.append(B.take(16n, s), B.append(B.zeros(4n), B.drop(20n, s)))

# the bytes the header CRC covers
def Gpt.crc_input(+s: List<&2, U32>) -> List<&2, U32>:
  Gpt.take_u32(Gpt.zeroed(s), Gpt.u32_or0(B.le32_at(s, 12n)))

# the header CRC a header block should carry: CRC-32 of its first
# header-size bytes, the CRC field read as zero
def Gpt.header_crc(o: B.Octets) -> U32:
  C.crc32(B.Octets.of_list(Gpt.crc_input(B.Octets.to_list(o))))

def Gpt.crc_ok.list(+s: List<&2, U32>) -> Bool:
  Gpt.list_eq(B.take(4n, B.drop(16n, s)), Gpt.le32s(C.crc32(B.Octets.of_list(Gpt.crc_input(s)))))

# whether the stored header CRC is the one Gpt.header_crc computes
def Gpt.header_crc_ok(o: B.Octets) -> Bool:
  Gpt.crc_ok.list(B.Octets.to_list(o))

# Header: writing

def GptHeader.with_crc(h: GptHeader, c: U32) -> GptHeader:
  match h:
    case GptHeader{rev, size, old, my, alt, first, last, guid, elba, count, esize, ecrc}:
      GptHeader{rev, size, c, my, alt, first, last, guid, elba, count, esize, ecrc}

def GptHeader.with_entries_crc(h: GptHeader, c: U32) -> GptHeader:
  match h:
    case GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, old}:
      GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, c}

def GptHeader.entries_crc(h: GptHeader) -> U32:
  match h:
    case GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, ecrc}:
      ecrc

# the header block with header CRC field c, padded with pad zeros
def Gpt.header.encode(h: GptHeader, c: U32, pad: Nat) -> List<&2, U32>:
  match h:
    case GptHeader{rev, size, old, my, alt, first, last, guid, elba, count, esize, ecrc}:
      B.append(Gpt.signature(), B.append(B.le32(rev), B.append(B.le32(size), B.append(Gpt.le32s(c), B.append(B.le32(0), B.append(B.le64(my), B.append(B.le64(alt), B.append(B.le64(first), B.append(B.le64(last), B.append(U.Uuid.to_guid_list(guid), B.append(B.le64(elba), B.append(B.le32(count), B.append(B.le32(esize), B.append(B.le32(ecrc), B.zeros(pad)))))))))))))))

# the zeros after the 92 bytes of fields, to the end of a block
def Gpt.pad(l: GptLayout) -> Nat:
  match l:
    case GptLayout{block, count}:
      U32.to_nat(U32.sub(block, 92))

# the header CRC of h's header block
def Gpt.crc_of(+h: GptHeader, +pad: Nat) -> U32:
  Gpt.header_crc(B.Octets.of_list(Gpt.header.encode(h, 0, pad)))

# the header block of h, one block long, its header CRC computed (h's own
# header_crc field is ignored)
def Gpt.build_header_with(l: GptLayout, +h: GptHeader) -> B.Octets:
  +pad = Gpt.pad(l)
  B.Octets.of_list(Gpt.header.encode(h, Gpt.crc_of(h, pad), pad))

def Gpt.build_header(h: GptHeader) -> B.Octets:
  Gpt.build_header_with(GptLayout.standard(), h)

# h with the header CRC that Gpt.build_header writes
def GptHeader.seal(+h: GptHeader) -> GptHeader:
  GptHeader.with_crc(h, Gpt.crc_of(h, Gpt.pad(GptLayout.standard())))

# Header: reading

def Gpt.parse.fin(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, m3: Maybe<&2, W.W64>, m4: Maybe<&2, W.W64>, m5: Maybe<&2, W.W64>, m6: Maybe<&2, W.W64>, m7: Maybe<&2, U.Uuid>, m8: Maybe<&2, W.W64>, m9: Maybe<&2, U32>, m10: Maybe<&2, U32>, m11: Maybe<&2, U32>) -> Result<&2, &2, GptError, GptHeader>:
  match m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11:
    case Some{rev} Some{size} Some{crc} Some{my} Some{alt} Some{first} Some{last} Some{guid} Some{elba} Some{count} Some{esize} Some{ecrc}:
      Done{GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, ecrc}}
    case _ _ _ _ _ _ _ _ _ _ _ _:
      Fail{GptTooShort{}}

def Gpt.parse.sig(ok: Bool, +s: List<&2, U32>) -> Result<&2, &2, GptError, GptHeader>:
  match ok:
    case True{}:
      Gpt.parse.fin(B.le32_at(s, 8n), B.le32_at(s, 12n), B.le32_at(s, 16n), B.le64_at(s, 24n), B.le64_at(s, 32n), B.le64_at(s, 40n), B.le64_at(s, 48n), Gpt.guid_at(s, 56n), B.le64_at(s, 72n), B.le32_at(s, 80n), B.le32_at(s, 84n), B.le32_at(s, 88n))
    case False{}:
      Fail{GptBadSignature{}}

def Gpt.parse.list(+s: List<&2, U32>) -> Result<&2, &2, GptError, GptHeader>:
  Gpt.parse.sig(Gpt.list_eq(B.take(8n, s), Gpt.signature()), s)

# the fields of a header block (its CRC is not checked: Gpt.validate_header)
def Gpt.parse_header(o: B.Octets) -> Result<&2, &2, GptError, GptHeader>:
  Gpt.parse.list(B.Octets.to_list(o))

def Gpt.validate.crc(ok: Bool, h: GptHeader) -> Result<&2, &2, GptError, GptHeader>:
  match ok:
    case True{}:
      Done{h}
    case False{}:
      Fail{GptBadHeaderCrc{}}

def Gpt.validate.size(ok: Bool, +o: B.Octets, h: GptHeader) -> Result<&2, &2, GptError, GptHeader>:
  match ok:
    case True{}:
      Gpt.validate.crc(Gpt.header_crc_ok(o), h)
    case False{}:
      Fail{GptBadHeaderSize{}}

def Gpt.validate.go(r: Result<&2, &2, GptError, GptHeader>, +o: B.Octets) -> Result<&2, &2, GptError, GptHeader>:
  match r:
    case Done{GptHeader{rev, +size, crc, my, alt, first, last, guid, elba, count, esize, ecrc}}:
      Gpt.validate.size(Bool.and(U32.is_ge(size, 92), U32.is_le(size, U32.from_nat(B.Octets.len(o)))), o, GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, ecrc})
    case Fail{e}:
      Fail{e}

# the header of a header block, checked: the signature, a header size from
# 92 bytes to the block's size, and the header CRC
def Gpt.validate_header(+o: B.Octets) -> Result<&2, &2, GptError, GptHeader>:
  Gpt.validate.go(Gpt.parse_header(o), o)

# Partition entries

def GptEntry.unused() -> GptEntry:
  GptEntry{U.Uuid.nil(), U.Uuid.nil(), W.W64.zero(), W.W64.zero(), W.W64.zero(), Nil{}}

def GptEntry.is_used(e: GptEntry) -> Bool:
  match e:
    case GptEntry{t, u, first, last, attr, name}:
      Bool.not(U.Uuid.is_nil(t))

# n code units, little-endian, cut or padded with zeros
def Gpt.utf16_fit(n: Nat, us: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match us:
        case Nil{}:
          Con{0, Con{0, Gpt.utf16_fit(p, Nil{})}}
        case Con{u, t}:
          B.append(B.le16(u), Gpt.utf16_fit(p, t))

# the code units the name field holds: n of them, each masked to 16 bits
def Gpt.units_fit(n: Nat, us: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match us:
        case Nil{}:
          Con{0, Gpt.units_fit(p, Nil{})}
        case Con{u, t}:
          Con{B.low16(u), Gpt.units_fit(p, t)}

def Gpt.u16(a: U32, b: U32) -> U32:
  U32{W.W64.bits.cat(16n, 16n, W.W64.bits.cat(8n, 8n, B.bits8(a), B.bits8(b)), Word.zero(16n))}

# up to n little-endian code units
def Gpt.units(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Con{a, Con{b, t}}:
          Con{Gpt.u16(a, b), Gpt.units(p, t)}
        case _:
          Nil{}

# the entry as stored: its name cut or padded to 36 code units of 16 bits
def GptEntry.norm(e: GptEntry) -> GptEntry:
  match e:
    case GptEntry{t, u, first, last, attr, name}:
      GptEntry{t, u, first, last, attr, Gpt.units_fit(36n, name)}

def GptEntry.encode.list(e: GptEntry) -> List<&2, U32>:
  match e:
    case GptEntry{t, u, first, last, attr, name}:
      B.append(U.Uuid.to_guid_list(t), B.append(U.Uuid.to_guid_list(u), B.append(B.le64(first), B.append(B.le64(last), B.append(B.le64(attr), Gpt.utf16_fit(36n, name))))))

# the 128 bytes of an entry
def GptEntry.encode(e: GptEntry) -> B.Octets:
  B.Octets.of_list(GptEntry.encode.list(e))

def GptEntry.decode.fin(m0: Maybe<&2, U.Uuid>, m1: Maybe<&2, U.Uuid>, m2: Maybe<&2, W.W64>, m3: Maybe<&2, W.W64>, m4: Maybe<&2, W.W64>, name: List<&2, U32>) -> Result<&2, &2, GptError, GptEntry>:
  match m0 m1 m2 m3 m4:
    case Some{t} Some{u} Some{first} Some{last} Some{attr}:
      Done{GptEntry{t, u, first, last, attr, name}}
    case _ _ _ _ _:
      Fail{GptTooShort{}}

def GptEntry.decode.list(+xs: List<&2, U32>) -> Result<&2, &2, GptError, GptEntry>:
  GptEntry.decode.fin(Gpt.guid_at(xs, 0n), Gpt.guid_at(xs, 16n), B.le64_at(xs, 32n), B.le64_at(xs, 40n), B.le64_at(xs, 48n), Gpt.units(36n, B.drop(56n, xs)))

# the entry at the start of o
def GptEntry.decode(o: B.Octets) -> Result<&2, &2, GptError, GptEntry>:
  GptEntry.decode.list(B.Octets.to_list(o))

# Names: UTF-16 to and from text

def Gpt.utf16.until_nul.pick(stop: Bool, u: U32, r: List<&2, U32>) -> List<&2, U32>:
  match stop:
    case True{}:
      Nil{}
    case False{}:
      Con{u, r}

def Gpt.utf16.until_nul(us: List<&2, U32>) -> List<&2, U32>:
  match us:
    case Nil{}:
      Nil{}
    case Con{+u, t}:
      Gpt.utf16.until_nul.pick(U32.is_eq(u, 0), u, Gpt.utf16.until_nul(t))

def Gpt.utf16.in(+u: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(u, lo), U32.is_le(u, hi))

def Gpt.utf16.merge(pair: Bool, +u: U32, s: String) -> String:
  match pair:
    case True{}:
      match s:
        case SCon{Chr{v}, t}:
          SCon{Chr{U32.add(65536, U32.add(U32.shln(U32.sub(u, 55296), 10n), U32.sub(v, 56320)))}, t}
        case SNil{}:
          SCon{Chr{u}, SNil{}}
    case False{}:
      SCon{Chr{u}, s}

def Gpt.utf16.low_head(s: String) -> Bool:
  match s:
    case SCon{Chr{+v}, t}:
      Gpt.utf16.in(v, 56320, 57343)
    case SNil{}:
      False{}

def Gpt.utf16.decode(us: List<&2, U32>) -> String:
  match us:
    case Nil{}:
      SNil{}
    case Con{+u, t}:
      +s = Gpt.utf16.decode(t)
      Gpt.utf16.merge(Bool.and(Gpt.utf16.in(u, 55296, 56319), Gpt.utf16.low_head(s)), u, s)

# the name as text, up to its first NUL (surrogate pairs combined)
def GptEntry.name_text(e: GptEntry) -> String:
  match e:
    case GptEntry{t, u, first, last, attr, name}:
      Gpt.utf16.decode(Gpt.utf16.until_nul(name))

def Gpt.utf16.encode.pick(small: Bool, +x: U32, r: List<&2, U32>) -> List<&2, U32>:
  match small:
    case True{}:
      Con{x, r}
    case False{}:
      +y = U32.sub(x, 65536)
      Con{U32.add(55296, U32.shrn(y, 10n)), Con{U32.add(56320, U32.and(1023, y)), r}}

# the UTF-16 code units of a text (a name field for GptEntry)
def Gpt.name_units(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{+x}, t}:
      Gpt.utf16.encode.pick(U32.is_lt(x, 65536), x, Gpt.name_units(t))

# Entry arrays

def Gpt.entries_list(es: List<&2, GptEntry>) -> List<&2, U32>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      B.append(GptEntry.encode.list(e), Gpt.entries_list(t))

# the entry array of these entries, 128 bytes each
def Gpt.entries_encode(es: List<&2, GptEntry>) -> B.Octets:
  B.Octets.of_list(Gpt.entries_list(es))

def Gpt.entries.rev(es: List<&2, GptEntry>, acc: List<&2, GptEntry>) -> List<&2, GptEntry>:
  match es:
    case Nil{}:
      acc
    case Con{e, t}:
      Gpt.entries.rev(t, Con{e, acc})

# an entry pushed onto the entries so far (reversed); once one fails to
# decode, Fail holds the entries before it, in order: the answer
def Gpt.entries.push(r: Result<&2, &2, GptError, GptEntry>, acc: List<&2, GptEntry>) -> Result<&2, &2, List<&2, GptEntry>, List<&2, GptEntry>>:
  match r:
    case Done{e}:
      Done{Con{e, acc}}
    case Fail{e}:
      Fail{Gpt.entries.rev(acc, Nil{})}

# n entries size bytes apart, each decoded from its first 128 bytes (so that
# only those become a list), up to the first that does not decode;
# tail-recursive, so an array can have any number of entries
def Gpt.entries.go(n: Nat, st: Result<&2, &2, List<&2, GptEntry>, List<&2, GptEntry>>, +size: Nat, +o: B.Octets) -> List<&2, GptEntry>:
  match n:
    case 0n:
      match st:
        case Done{acc}:
          Gpt.entries.rev(acc, Nil{})
        case Fail{es}:
          es
    case 1n+p:
      match st:
        case Done{acc}:
          Gpt.entries.go(p, Gpt.entries.push(GptEntry.decode(B.Octets.take(128n, o)), acc), size, B.Octets.drop(size, o))
        case Fail{es}:
          es

def Gpt.entries.size(ok: Bool, +h: GptHeader, +o: B.Octets) -> Result<&2, &2, GptError, List<&2, GptEntry>>:
  match ok:
    case True{}:
      match h:
        case GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, +esize, ecrc}:
          +n = U32.min(count, U32.div(U32.from_nat(B.Octets.len(o)), esize))
          Done{Gpt.entries.go(U32.to_nat(n), Done{Nil{}}, U32.to_nat(esize), o)}
    case False{}:
      Fail{GptBadEntrySize{}}

def GptHeader.entry_size(h: GptHeader) -> U32:
  match h:
    case GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, ecrc}:
      esize

def GptHeader.entry_count(h: GptHeader) -> U32:
  match h:
    case GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, ecrc}:
      count

# the entries of an entry array, as many as the header says (fewer if the
# array ends first); unused entries included (GptEntry.is_used)
def Gpt.entries(+h: GptHeader, +o: B.Octets) -> Result<&2, &2, GptError, List<&2, GptEntry>>:
  Gpt.entries.size(U32.is_ge(GptHeader.entry_size(h), 128), h, o)

def Gpt.entries_crc_ok.go(enough: Bool, +h: GptHeader, +o: B.Octets) -> Bool:
  match enough:
    case True{}:
      U32.is_eq(GptHeader.entries_crc(h), C.crc32(B.Octets.take(U32.to_nat(U32.mul(GptHeader.entry_count(h), GptHeader.entry_size(h))), o)))
    case False{}:
      False{}

# whether the header's entries CRC is the CRC-32 of the array's first
# count * size bytes
def Gpt.entries_crc_ok(+h: GptHeader, +o: B.Octets) -> Bool:
  Gpt.entries_crc_ok.go(W.W64.is_le(W.W64.mul(W.W64.from_u32(GptHeader.entry_count(h)), W.W64.from_u32(GptHeader.entry_size(h))), W.W64.from_nat(B.Octets.len(o))), h, o)

# the header block of h for these entries: its entries CRC is the CRC-32 of
# Gpt.entries_encode(es), and its header CRC is computed
def Gpt.build(h: GptHeader, es: List<&2, GptEntry>) -> B.Octets:
  Gpt.build_header(GptHeader.with_entries_crc(h, C.crc32(Gpt.entries_encode(es))))

# Laying out a new disk

def Gpt.entry_blocks.of(+block: U32, count: U32) -> U32:
  U32.div(U32.add(U32.mul(count, 128), U32.sub(block, 1)), block)

# the blocks the entry array of a layout takes
def Gpt.entry_blocks(l: GptLayout) -> U32:
  match l:
    case GptLayout{block, count}:
      Gpt.entry_blocks.of(block, count)

# the primary header of a disk of disk_blocks blocks: entries from LBA 2,
# the backup header in the last block and its entries just before it
def GptHeader.standard(l: GptLayout, +disk_blocks: W.W64, guid: U.Uuid) -> GptHeader:
  match l:
    case GptLayout{block, +count}:
      +eb = W.W64.from_u32(Gpt.entry_blocks.of(block, count))
      +last = W.W64.sub(disk_blocks, W.W64.one())
      GptHeader{65536, 92, 0, W.W64.one(), last, W.W64.add(W.W64.from_u32(2), eb), W.W64.sub(W.W64.sub(last, W.W64.one()), eb), guid, W.W64.from_u32(2), count, 128, 0}

# the backup header of a primary one: my and alternate LBAs swapped, its
# entries just after the last usable LBA
def GptHeader.backup(h: GptHeader) -> GptHeader:
  match h:
    case GptHeader{rev, size, crc, my, alt, first, +last, guid, elba, count, esize, ecrc}:
      GptHeader{rev, size, crc, alt, my, first, last, guid, W.W64.add(last, W.W64.one()), count, esize, ecrc}
