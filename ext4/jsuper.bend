# bend-osdev-ext4: the jbd2 journal's superblock, version 1 and 2 (the jbd2
# documentation, "Journal (jbd2)": "Super Block"), and the geometry the
# journal's other blocks are read with.
#
# Every journal field is big-endian. The superblock is the journal's block
# 0: header (h_magic 0xC03B3998, h_blocktype 3 for v1 or 4 for v2,
# h_sequence), then s_blocksize (0x0C), s_maxlen (0x10, the journal's
# blocks), s_first (0x14, the first block of the log), s_sequence (0x18,
# the first transaction expected), s_start (0x1C, where the log starts; 0
# when the journal is empty), s_errno (0x20). Version 2 adds the features
# (compat 0x24, incompat 0x28, ro_compat 0x2C), s_uuid (0x30),
# s_checksum_type (0x50, 4 = crc32c) and s_checksum (0xFC): crc32c from ~0
# over the 1024-byte superblock with s_checksum zeroed.
#
# Incompat features: revoke (1), 64bit (2, 64-bit block numbers in tags and
# revoke records), async_commit (4), csum_v2 (8), csum_v3 (16), fast_commit
# (32, refused: fast commit blocks are not replayed). Compat: checksum (1,
# the old per-transaction crc32 in commit blocks, read but not checked).
import Base
import ../bytes/bytes.bend as B
import ../ext2/csum.bend as K
import ./error.bend as E
import ./options.bend as O

def Jbd2.magic() -> U32:
  3225106840

def Jbd2.u8(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, i), 0)

def Jbd2.be32(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.be32_at(o, i), 0)

def Jbd2.nat(o: B.Octets, i: Nat) -> Nat:
  U32.to_nat(Jbd2.be32(o, i))

# o with the big-endian field at byte i replaced by v
def Jbd2.patch32(+o: B.Octets, +i: Nat, v: U32) -> B.Octets:
  B.Octets.append(B.Octets.take(i, o), B.Octets.append(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o)))

def Jbd2.has(+flags: U32, bit: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(flags, bit), 0))

type Jbd2Super is Data:
  Jbd2Super{blocktype: U32, block_size: Nat, maxlen: Nat, first: Nat, sequence: U32, start: Nat, errno: U32, compat: U32, incompat: U32, ro_compat: U32, uuid: B.Octets, csum_type: U32, checksum: U32}

def Jbd2Super.blocktype(s: Jbd2Super) -> U32:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      t

def Jbd2Super.block_size(s: Jbd2Super) -> Nat:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      bs

def Jbd2Super.maxlen(s: Jbd2Super) -> Nat:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      ml

def Jbd2Super.first(s: Jbd2Super) -> Nat:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      f

def Jbd2Super.sequence(s: Jbd2Super) -> U32:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      sq

def Jbd2Super.start(s: Jbd2Super) -> Nat:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      st

def Jbd2Super.errno(s: Jbd2Super) -> U32:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      er

def Jbd2Super.compat(s: Jbd2Super) -> U32:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      c

def Jbd2Super.incompat(s: Jbd2Super) -> U32:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      i

def Jbd2Super.ro_compat(s: Jbd2Super) -> U32:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      r

def Jbd2Super.uuid(s: Jbd2Super) -> B.Octets:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      u

def Jbd2Super.csum_type(s: Jbd2Super) -> U32:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      ct

def Jbd2Super.checksum(s: Jbd2Super) -> U32:
  match s:
    case Jbd2Super{t, bs, ml, f, sq, st, er, c, i, r, u, ct, ck}:
      ck

# Feature bits

def Jbd2Super.incompat_revoke() -> U32:
  1

def Jbd2Super.incompat_64bit() -> U32:
  2

def Jbd2Super.incompat_async_commit() -> U32:
  4

def Jbd2Super.incompat_csum_v2() -> U32:
  8

def Jbd2Super.incompat_csum_v3() -> U32:
  16

def Jbd2Super.incompat_fast_commit() -> U32:
  32

def Jbd2Super.compat_checksum() -> U32:
  1

# the incompat features this package reads: revoke, 64bit, async_commit,
# csum_v2, csum_v3
def Jbd2Super.known_incompat() -> U32:
  31

def Jbd2Super.v2_field(v2: Bool, +o: B.Octets, i: Nat) -> U32:
  match v2:
    case True{}:
      Jbd2.be32(o, i)
    case False{}:
      0

def Jbd2Super.v2_byte(v2: Bool, +o: B.Octets, i: Nat) -> U32:
  match v2:
    case True{}:
      Jbd2.u8(o, i)
    case False{}:
      0

def Jbd2Super.parse.go(+v2: Bool, +o: B.Octets) -> Jbd2Super:
  Jbd2Super{Jbd2.be32(o, 4n), Jbd2.nat(o, 12n), Jbd2.nat(o, 16n), Jbd2.nat(o, 20n), Jbd2.be32(o, 24n), Jbd2.nat(o, 28n), Jbd2.be32(o, 32n), Jbd2Super.v2_field(v2, o, 36n), Jbd2Super.v2_field(v2, o, 40n), Jbd2Super.v2_field(v2, o, 44n), B.Octets.slice(48n, 16n, o), Jbd2Super.v2_byte(v2, o, 80n), Jbd2Super.v2_field(v2, o, 252n)}

# the fields of a journal superblock (no checks; a v1 superblock's feature
# fields read as 0)
def Jbd2Super.parse(+o: B.Octets) -> Jbd2Super:
  Jbd2Super.parse.go(U32.is_eq(Jbd2.be32(o, 4n), 4), o)

# the superblock's checksum, over its first 1024 bytes with s_checksum
# zeroed
def Jbd2Super.csum(+o: B.Octets) -> U32:
  K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(4294967295, B.Octets.take(252n, o)), B.Octets.zeros(4n)), B.Octets.slice(256n, 768n, o))

def Jbd2Super.has_incompat(+s: Jbd2Super, bit: U32) -> Bool:
  Jbd2.has(Jbd2Super.incompat(s), bit)

# whether the journal has checksums (csum_v2 or csum_v3)
def Jbd2Super.has_csum(+s: Jbd2Super) -> Bool:
  Bool.or(Jbd2Super.has_incompat(s, Jbd2Super.incompat_csum_v2()), Jbd2Super.has_incompat(s, Jbd2Super.incompat_csum_v3()))

def Jbd2Super.incompat_name.pick(fc: Bool, +m: U32) -> String:
  match fc:
    case True{}:
      "fast_commit"
    case False{}:
      "journal incompat bits " ++ U32.show(m)

# a name for unknown incompat bits m
def Jbd2Super.incompat_name(+m: U32) -> String:
  Jbd2Super.incompat_name.pick(Jbd2.has(m, 32), m)

def Jbd2Super.csum_ok(on: Bool, +o: B.Octets, +s: Jbd2Super) -> Result<&2, &2, E.Ext4Error, Unit>:
  match on:
    case True{}:
      +c = Jbd2Super.csum(o)
      do Result<&2, &2, E.Ext4Error, Unit>:
        E.Ext4.require(U32.is_eq(Jbd2Super.csum_type(s), 4), E.Ext4JournalUnsupported{"checksum type " ++ U32.show(Jbd2Super.csum_type(s))})
        E.Ext4.require(U32.is_eq(c, Jbd2Super.checksum(s)), E.Ext4BadJournalCsum{Jbd2Super.checksum(s), c})
    case False{}:
      Done{Unit{}}

# the journal superblock in o (the journal's block 0), checked: the magic,
# the version, the block size (bs, the filesystem's), the log's bounds
# within the journal's blocks (blocks: how many the journal has), the
# features, and with csum_v2 or csum_v3 the checksum (when opts verify)
def Jbd2Super.check(+o: B.Octets, +bs: Nat, +blocks: Nat, +opts: O.Jbd2Options) -> Result<&2, &2, E.Ext4Error, Jbd2Super>:
  +s = Jbd2Super.parse(o)
  +t = Jbd2Super.blocktype(s)
  +ml = Jbd2Super.maxlen(s)
  +f = Jbd2Super.first(s)
  +st = Jbd2Super.start(s)
  +inc = Jbd2Super.incompat(s)
  +bad = U32.and(inc, U32.not(Jbd2Super.known_incompat()))
  do Result<&2, &2, E.Ext4Error, Jbd2Super>:
    E.Ext4.require(U32.is_eq(Jbd2.be32(o, 0n), Jbd2.magic()), E.Ext4BadJournalMagic{Jbd2.be32(o, 0n)})
    E.Ext4.require(Bool.or(U32.is_eq(t, 3), U32.is_eq(t, 4)), E.Ext4BadJournalType{t})
    E.Ext4.require(Nat.is_eq(Jbd2Super.block_size(s), bs), E.Ext4BadJournal{"the journal's block size is not the filesystem's"})
    E.Ext4.require(Bool.and(Nat.is_lt(0n, f), Bool.and(Nat.is_lt(f, ml), Nat.is_le(ml, blocks))), E.Ext4BadJournal{"the log's bounds are outside the journal"})
    E.Ext4.require(Bool.or(Nat.is_eq(st, 0n), Bool.and(Nat.is_le(f, st), Nat.is_lt(st, ml))), E.Ext4BadJournal{"the log's start is outside the log"})
    E.Ext4.require(U32.is_eq(bad, 0), E.Ext4JournalUnsupported{Jbd2Super.incompat_name(bad)})
    E.Ext4.require(U32.is_eq(Jbd2Super.ro_compat(s), 0), E.Ext4JournalUnsupported{"journal ro_compat bits " ++ U32.show(Jbd2Super.ro_compat(s))})
    E.Ext4.require(Bool.not(Bool.and(Jbd2.has(inc, 8), Jbd2.has(inc, 16))), E.Ext4BadJournal{"both csum_v2 and csum_v3"})
    Jbd2Super.csum_ok(Bool.and(O.Jbd2Options.verify(opts), Jbd2Super.has_csum(s)), o, s)
    return s

# The geometry: how the log's blocks are read

type Jbd2Geom is Data:
  Jbd2Geom{bs: Nat, wide: Bool, csum: Nat, seed: U32, first: Nat, maxlen: Nat}

def Jbd2Geom.bs(g: Jbd2Geom) -> Nat:
  match g:
    case Jbd2Geom{bs, w, c, s, f, m}:
      bs

def Jbd2Geom.wide(g: Jbd2Geom) -> Bool:
  match g:
    case Jbd2Geom{bs, w, c, s, f, m}:
      w

# 0 (no checksums), 2 (csum_v2) or 3 (csum_v3)
def Jbd2Geom.csum(g: Jbd2Geom) -> Nat:
  match g:
    case Jbd2Geom{bs, w, c, s, f, m}:
      c

def Jbd2Geom.seed(g: Jbd2Geom) -> U32:
  match g:
    case Jbd2Geom{bs, w, c, s, f, m}:
      s

def Jbd2Geom.first(g: Jbd2Geom) -> Nat:
  match g:
    case Jbd2Geom{bs, w, c, s, f, m}:
      f

def Jbd2Geom.maxlen(g: Jbd2Geom) -> Nat:
  match g:
    case Jbd2Geom{bs, w, c, s, f, m}:
      m

def Jbd2Geom.csum.pick(v3: Bool, v2: Bool) -> Nat:
  match v3 v2:
    case True{} _:
      3n
    case False{} True{}:
      2n
    case False{} False{}:
      0n

# the seed of the journal's checksums: crc32c from ~0 over its UUID
def Jbd2Super.seed(+s: Jbd2Super) -> U32:
  K.Ext2Csum.crc32c(4294967295, Jbd2Super.uuid(s))

def Jbd2Super.geom(+s: Jbd2Super) -> Jbd2Geom:
  Jbd2Geom{Jbd2Super.block_size(s), Jbd2Super.has_incompat(s, Jbd2Super.incompat_64bit()), Jbd2Geom.csum.pick(Jbd2Super.has_incompat(s, Jbd2Super.incompat_csum_v3()), Jbd2Super.has_incompat(s, Jbd2Super.incompat_csum_v2())), Jbd2Super.seed(s), Jbd2Super.first(s), Jbd2Super.maxlen(s)}

def Jbd2Geom.has_csum(+g: Jbd2Geom) -> Bool:
  Nat.is_lt(0n, Jbd2Geom.csum(g))

def Jbd2Geom.tag.pick(v: Nat, wide: Bool) -> Nat:
  match v wide:
    case 3n _:
      16n
    case 2n True{}:
      14n
    case 2n False{}:
      10n
    case _ True{}:
      12n
    case _ False{}:
      8n

# a descriptor tag's bytes: 16 with csum_v3; otherwise 8, 4 more with
# 64bit, 2 more with csum_v2 (seen in the journals e2fsprogs writes: the
# documentation's tables give the fields, not this padding)
def Jbd2Geom.tag_size(+g: Jbd2Geom) -> Nat:
  Jbd2Geom.tag.pick(Jbd2Geom.csum(g), Jbd2Geom.wide(g))

def Jbd2Geom.tail.pick(c: Bool) -> Nat:
  match c:
    case True{}:
      4n
    case False{}:
      0n

# the checksum tail at the end of descriptor and revoke blocks: 4 bytes with
# csum_v2 or csum_v3
def Jbd2Geom.tail(+g: Jbd2Geom) -> Nat:
  Jbd2Geom.tail.pick(Jbd2Geom.has_csum(g))

def Jbd2Geom.next.pick(wrap: Bool, +f: Nat, +n: Nat) -> Nat:
  match wrap:
    case True{}:
      f
    case False{}:
      n

# the log block after p: the log runs from s_first to s_maxlen - 1, then
# wraps to s_first
def Jbd2Geom.next(+g: Jbd2Geom, p: Nat) -> Nat:
  +n = Nat.add(p, 1n)
  Jbd2Geom.next.pick(Nat.is_le(Jbd2Geom.maxlen(g), n), Jbd2Geom.first(g), n)

def Jbd2Super.reseal(csum: Bool, +o: B.Octets) -> B.Octets:
  match csum:
    case True{}:
      Jbd2.patch32(o, 252n, Jbd2Super.csum(o))
    case False{}:
      o

# the superblock o with s_start and s_sequence set, its checksum
# recomputed when the journal has checksums
def Jbd2Super.with_log(+o: B.Octets, +start: Nat, +seq: U32) -> B.Octets:
  Jbd2Super.reseal(Jbd2Super.has_csum(Jbd2Super.parse(o)), Jbd2.patch32(Jbd2.patch32(o, 24n, seq), 28n, U32.from_nat(start)))
