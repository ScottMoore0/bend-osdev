# bend-osdev-ext4: extended attributes, in the inode body and in an
# attribute block (the ext4 disk-layout documentation, "Extended
# Attributes").
#
# Both places hold the same entries: e_name_len (u8), e_name_index (u8),
# e_value_offs (le16), e_value_inum (le32), e_value_size (le32), e_hash
# (le32), the name, padded to 4 bytes; the list ends at four zero bytes.
# In the inode body the area after i_extra_isize starts with the magic
# 0xEA020000 and value offsets count from the first entry; an attribute
# block (i_file_acl) has a 32-byte header (magic, refcount, h_blocks = 1,
# h_hash, h_checksum) and offsets count from the block's start. With the
# ea_inode feature a large value lives in an inode of its own
# (e_value_inum), whose i_atime holds crc32c(seed, value).
#
# Hashes: an entry's hash folds the name's bytes in (each step: hash << 5
# xor hash >> 27 xor byte), then the value's little-endian words (each
# step: hash << 16 xor hash >> 16 xor word), or for an EA inode value the
# one word crc32c(seed, value); the block hash folds the entries' hashes
# the second way. The documentation does not give these; they were fixed
# by experiment against the hashes e2fsprogs and debugfs write (README.md).
# A stored hash of 0 means none was computed (e2fsprogs writes 0 for
# entries in the inode body), and is not checked; names are hashed as
# unsigned bytes, or as signed ones (older writers), either is accepted.
# Checksum (metadata_csum): crc32c from the filesystem's seed over the
# block number (le64), then the block with h_checksum zeroed.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../blockdev/blockdev.bend as D
import ../ext2/super.bend as XS
import ../ext2/inode.bend as N
import ../ext2/file.bend as FL
import ../ext2/csum.bend as K
import ./error.bend as E
import ./super.bend as S
import ./inode.bend as I

type Ext4Xattr is Data:
  Ext4Xattr{index: U32, name: B.Octets, value: B.Octets, inum: Nat, size: Nat, hash: U32}

def Ext4Xattr.index(x: Ext4Xattr) -> U32:
  match x:
    case Ext4Xattr{i, n, v, q, s, h}:
      i

def Ext4Xattr.name(x: Ext4Xattr) -> B.Octets:
  match x:
    case Ext4Xattr{i, n, v, q, s, h}:
      n

def Ext4Xattr.value(x: Ext4Xattr) -> B.Octets:
  match x:
    case Ext4Xattr{i, n, v, q, s, h}:
      v

def Ext4Xattr.inum(x: Ext4Xattr) -> Nat:
  match x:
    case Ext4Xattr{i, n, v, q, s, h}:
      q

def Ext4Xattr.size(x: Ext4Xattr) -> Nat:
  match x:
    case Ext4Xattr{i, n, v, q, s, h}:
      s

def Ext4Xattr.hash(x: Ext4Xattr) -> U32:
  match x:
    case Ext4Xattr{i, n, v, q, s, h}:
      h

# the prefix a name index stands for
def Ext4Xattr.prefix(i: Nat) -> String:
  match i:
    case 1n:
      "user."
    case 2n:
      "system.posix_acl_access"
    case 3n:
      "system.posix_acl_default"
    case 4n:
      "trusted."
    case 6n:
      "security."
    case 7n:
      "system."
    case 8n:
      "system.richacl"
    case _:
      ""

# the attribute's full name: its index's prefix and its own name
def Ext4Xattr.full_name(+x: Ext4Xattr) -> B.Octets:
  B.Octets.append(B.Octets.of_string(Ext4Xattr.prefix(U32.to_nat(Ext4Xattr.index(x)))), Ext4Xattr.name(x))

# Hashes

def Ext4Xattr.sext.pick(neg: Bool, +b: U32) -> U32:
  match neg:
    case True{}:
      U32.or(b, 4294967040)
    case False{}:
      b

def Ext4Xattr.sext(signed: Bool, +b: U32) -> U32:
  match signed:
    case True{}:
      Ext4Xattr.sext.pick(U32.is_le(128, b), b)
    case False{}:
      b

def Ext4Xattr.step5(+h: U32, x: U32) -> U32:
  U32.xor(U32.xor(U32.shln(h, 5n), U32.shrn(h, 27n)), x)

def Ext4Xattr.step16(+h: U32, x: U32) -> U32:
  U32.xor(U32.xor(U32.shln(h, 16n), U32.shrn(h, 16n)), x)

def Ext4Xattr.name_hash(xs: List<&2, U32>, +signed: Bool, h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{c, t}:
      Ext4Xattr.name_hash(t, signed, Ext4Xattr.step5(h, Ext4Xattr.sext(signed, U32.and(c, 255))))

def Ext4Xattr.word(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n)))

# the value's little-endian words folded in (a short last word padded with
# zeros)
def Ext4Xattr.value_hash(xs: List<&2, U32>, h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{a, Nil{}}:
      Ext4Xattr.step16(h, Ext4Xattr.word(a, 0, 0, 0))
    case Con{a, Con{b, Nil{}}}:
      Ext4Xattr.step16(h, Ext4Xattr.word(a, b, 0, 0))
    case Con{a, Con{b, Con{c, Nil{}}}}:
      Ext4Xattr.step16(h, Ext4Xattr.word(a, b, c, 0))
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Ext4Xattr.value_hash(t, Ext4Xattr.step16(h, Ext4Xattr.word(a, b, c, d)))

# an entry's hash, its value held in the entry's area
def Ext4Xattr.entry_hash(signed: Bool, name: B.Octets, value: B.Octets) -> U32:
  Ext4Xattr.value_hash(B.Octets.to_list(value), Ext4Xattr.name_hash(B.Octets.to_list(name), signed, 0))

# an entry's hash, its value in an EA inode whose value hash is vh
def Ext4Xattr.inode_hash(signed: Bool, name: B.Octets, vh: U32) -> U32:
  Ext4Xattr.step16(Ext4Xattr.name_hash(B.Octets.to_list(name), signed, 0), vh)

def Ext4Xattr.fold16(xs: List<&2, Ext4Xattr>, h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      Ext4Xattr.fold16(t, Ext4Xattr.step16(h, Ext4Xattr.hash(x)))

def Ext4Xattr.any_zero(xs: List<&2, Ext4Xattr>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.or(U32.is_eq(Ext4Xattr.hash(x), 0), Ext4Xattr.any_zero(t))

def Ext4Xattr.block_hash.pick(zero: Bool, xs: List<&2, Ext4Xattr>) -> U32:
  match zero:
    case True{}:
      0
    case False{}:
      Ext4Xattr.fold16(xs, 0)

# the block hash: the entries' hashes folded in; 0 if any entry's is 0
def Ext4Xattr.block_hash(+xs: List<&2, Ext4Xattr>) -> U32:
  Ext4Xattr.block_hash.pick(Ext4Xattr.any_zero(xs), xs)


# Entries

type Ext4XaStep is Data:
  Ext4XaEnd{}
  Ext4XaBad{why: String}
  Ext4XaEnt{x: Ext4Xattr, size: Nat}

def Ext4Xattr.u8(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, i), 0)

def Ext4Xattr.u16(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le16_at(o, i), 0)

def Ext4Xattr.u32(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le32_at(o, i), 0)

def Ext4Xattr.value.of(inline: Bool, off: Nat, +len: Nat, base: B.Octets) -> B.Octets:
  match inline:
    case True{}:
      B.Octets.slice(off, len, base)
    case False{}:
      B.Octets.empty()

def Ext4Xattr.make(ok: Bool, +o: B.Octets, +base: B.Octets, +size: Nat) -> Ext4XaStep:
  match ok:
    case False{}:
      Ext4XaBad{"value outside the attribute area"}
    case True{}:
      +nl = U32.to_nat(Ext4Xattr.u8(o, 0n))
      +inum = U32.to_nat(Ext4Xattr.u32(o, 4n))
      +vs = U32.to_nat(Ext4Xattr.u32(o, 8n))
      Ext4XaEnt{Ext4Xattr{Ext4Xattr.u8(o, 1n), B.Octets.slice(16n, nl, o), Ext4Xattr.value.of(Nat.is_eq(inum, 0n), U32.to_nat(Ext4Xattr.u16(o, 2n)), vs, base), inum, vs, Ext4Xattr.u32(o, 12n)}, size}

# an entry whose value is in the area: inside it
def Ext4Xattr.fits(+o: B.Octets, +base: B.Octets) -> Bool:
  +inum = Ext4Xattr.u32(o, 4n)
  Bool.or(Bool.not(U32.is_eq(inum, 0)), Nat.is_le(Nat.add(U32.to_nat(Ext4Xattr.u16(o, 2n)), U32.to_nat(Ext4Xattr.u32(o, 8n))), B.Octets.len(base)))

def Ext4Xattr.step.entry(room: Bool, named: Bool, +o: B.Octets, +base: B.Octets, +size: Nat) -> Ext4XaStep:
  match room named:
    case False{} _:
      Ext4XaBad{"entry past the end of the area"}
    case True{} False{}:
      Ext4XaBad{"an entry with an empty name"}
    case True{} True{}:
      Ext4Xattr.make(Ext4Xattr.fits(o, base), o, base, size)

def Ext4Xattr.step.go(end: Bool, header: Bool, +o: B.Octets, +avail: Nat, +base: B.Octets) -> Ext4XaStep:
  match end header:
    case True{} _:
      Ext4XaEnd{}
    case False{} False{}:
      Ext4XaBad{"entry header past the end of the area"}
    case False{} True{}:
      +nl = U32.to_nat(Ext4Xattr.u8(o, 0n))
      +size = Nat.mul(Nat.div(Nat.add(nl, 19n), 4n), 4n)
      Ext4Xattr.step.entry(Nat.is_le(size, avail), Nat.is_lt(0n, nl), o, base, size)

# what is at the start of o, avail bytes of the area left: the end (four
# zero bytes, or no room for them), or an entry and the bytes it takes
def Ext4Xattr.step(+o: B.Octets, +avail: Nat, +base: B.Octets) -> Ext4XaStep:
  Ext4Xattr.step.go(Bool.or(Nat.is_lt(avail, 4n), U32.is_eq(Ext4Xattr.u32(o, 0n), 0)), Nat.is_le(16n, avail), o, avail, base)

# the entries from o on (avail bytes of the area), a tail call each; values
# are read from base at their offsets
def Ext4Xattr.walk(fuel: Nat, st: Ext4XaStep, o: B.Octets, +avail: Nat, +base: B.Octets, acc: List<&2, Ext4Xattr>) -> Result<&2, &2, String, List<&2, Ext4Xattr>>:
  match fuel st:
    case 0n _:
      Fail{"too many entries"}
    case 1n+f Ext4XaEnd{}:
      Done{List.reverse(&2, Ext4Xattr, acc)}
    case 1n+f Ext4XaBad{w}:
      Fail{w}
    case 1n+f Ext4XaEnt{x, +size}:
      +rest = B.Octets.drop(size, o)
      +left = Nat.sub(avail, size)
      Ext4Xattr.walk(f, Ext4Xattr.step(rest, left, base), rest, left, base, Con{x, acc})

# the entries of an area (the entries start at o's start; values are at
# offsets into base)
def Ext4Xattr.entries(+o: B.Octets, +base: B.Octets) -> Result<&2, &2, String, List<&2, Ext4Xattr>>:
  +n = B.Octets.len(o)
  Ext4Xattr.walk(Nat.add(Nat.div(n, 16n), 1n), Ext4Xattr.step(o, n, base), o, n, base, Nil{})

# Checking entry hashes

def Ext4Xattr.hash_ok(+x: Ext4Xattr) -> Bool:
  +h = Ext4Xattr.hash(x)
  Bool.or(U32.is_eq(h, 0), Bool.or(Bool.not(Nat.is_eq(Ext4Xattr.inum(x), 0n)), Bool.or(U32.is_eq(h, Ext4Xattr.entry_hash(False{}, Ext4Xattr.name(x), Ext4Xattr.value(x))), U32.is_eq(h, Ext4Xattr.entry_hash(True{}, Ext4Xattr.name(x), Ext4Xattr.value(x))))))

def Ext4Xattr.bad.pick(ok: Bool, x: Ext4Xattr) -> Maybe<&2, Ext4Xattr>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{x}

# the first entry whose stored hash is neither 0 nor the hash of its name
# and value
def Ext4Xattr.first_bad(xs: List<&2, Ext4Xattr>, found: Maybe<&2, Ext4Xattr>) -> Maybe<&2, Ext4Xattr>:
  match xs found:
    case _ Some{x}:
      Some{x}
    case Nil{} None{}:
      None{}
    case Con{+x, t} None{}:
      Ext4Xattr.first_bad(t, Ext4Xattr.bad.pick(Ext4Xattr.hash_ok(x), x))

def Ext4Xattr.report(m: Maybe<&2, Ext4Xattr>, +ino: Nat) -> Result<&2, &2, E.Ext4Error, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{+x}:
      Fail{E.Ext4BadXattrHash{ino, Ext4Xattr.hash(x), Ext4Xattr.entry_hash(False{}, Ext4Xattr.name(x), Ext4Xattr.value(x))}}

def Ext4Xattr.check_hashes(on: Bool, +xs: List<&2, Ext4Xattr>, +ino: Nat) -> Result<&2, &2, E.Ext4Error, Unit>:
  match on:
    case True{}:
      Ext4Xattr.report(Ext4Xattr.first_bad(xs, None{}), ino)
    case False{}:
      Done{Unit{}}

def Ext4Xattr.lift(r: Result<&2, &2, String, List<&2, Ext4Xattr>>, +ino: Nat) -> Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
  match r:
    case Done{xs}:
      Done{xs}
    case Fail{w}:
      Fail{E.Ext4BadXattr{ino, w}}

# The inode body

def Ext4Xattr.ibody.go(has: Bool, +raw: B.Octets, +off: Nat, +ino: Nat, +check: Bool) -> Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
  match has:
    case False{}:
      Done{Nil{}}
    case True{}:
      +area = B.Octets.drop(Nat.add(off, 4n), raw)
      do Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
        +xs : List<&2, Ext4Xattr> <- Ext4Xattr.lift(Ext4Xattr.entries(area, area), ino)
        Ext4Xattr.check_hashes(check, xs, ino)
        return xs

# the attributes in an inode's body, from its raw record (none if the area
# does not start with the magic)
def Ext4Xattr.ibody(+raw: B.Octets, +ino: Nat, +check: Bool) -> Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
  +off = I.Ext4Inode.ea_offset(raw)
  Ext4Xattr.ibody.go(Bool.and(Nat.is_le(Nat.add(off, 4n), B.Octets.len(raw)), U32.is_eq(Ext4Xattr.u32(raw, off), 3925999616)), raw, off, ino, check)

# The attribute block

def Ext4Xattr.block_csum(+seed: U32, +n: Nat, +blk: B.Octets) -> U32:
  K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(seed, B.Octets.le64(W.W64.from_nat(n))), B.Octets.take(16n, blk)), B.Octets.zeros(4n)), B.Octets.drop(20n, blk))

def Ext4Xattr.csum_check(on: Bool, +seed: U32, +n: Nat, +blk: B.Octets) -> Result<&2, &2, E.Ext4Error, Unit>:
  match on:
    case True{}:
      +c = Ext4Xattr.block_csum(seed, n, blk)
      +st = Ext4Xattr.u32(blk, 16n)
      E.Ext4.require(U32.is_eq(c, st), E.Ext4BadXattrCsum{n, st, c})
    case False{}:
      Done{Unit{}}

# the attributes of attribute block n (blk: its bytes), checked: the header,
# the checksum (metadata_csum), the entries and their hashes, and the block
# hash when it is stored
def Ext4Xattr.block_of(+fs: S.Ext4Fs, +n: Nat, +blk: B.Octets, +ino: Nat) -> Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
  +check = S.Ext4Fs.verify(fs)
  +bh = Ext4Xattr.u32(blk, 12n)
  do Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
    E.Ext4.require(U32.is_eq(Ext4Xattr.u32(blk, 0n), 3925999616), E.Ext4BadXattrBlock{n, "bad magic"})
    E.Ext4.require(U32.is_eq(Ext4Xattr.u32(blk, 8n), 1), E.Ext4BadXattrBlock{n, "h_blocks is not 1"})
    Ext4Xattr.csum_check(S.Ext4Fs.verify_meta(fs), S.Ext4Fs.seed(fs), n, blk)
    +xs : List<&2, Ext4Xattr> <- Ext4Xattr.lift(Ext4Xattr.entries(B.Octets.drop(32n, blk), blk), ino)
    Ext4Xattr.check_hashes(check, xs, ino)
    E.Ext4.require(Bool.or(Bool.not(check), Bool.or(U32.is_eq(bh, 0), U32.is_eq(bh, Ext4Xattr.block_hash(xs)))), E.Ext4BadXattrBlock{n, "bad block hash"})
    return xs

def Ext4Xattr.block.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, none: Bool, +d: Dv, +fs: S.Ext4Fs, +n: Nat, +ino: Nat) -> Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
  match none:
    case True{}:
      Done{Nil{}}
    case False{}:
      +f = S.Ext4Fs.ext2(fs)
      do Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
        E.Ext4.require(Nat.is_lt(n, XS.Ext2Fs.blocks(f)), E.Ext4BadXattrBlock{n, "outside the filesystem"})
        blk : B.Octets <- E.Ext4Error.lift(B.Octets, XS.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, f, n))
        Ext4Xattr.block_of(fs, n, blk, ino)

# the attributes in inode i's attribute block, if it has one
def Ext4Xattr.block(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
  +n = W.W64.to_nat(N.Ext2Inode.file_acl(i))
  Ext4Xattr.block.go(~Dv, ~block_size, ~read_block, Nat.is_eq(n, 0n), d, fs, n, N.Ext2Inode.number_of(i))

# every attribute of inode i: those in its body, then those in its block
def Ext4Xattr.list(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
  +n = N.Ext2Inode.number_of(i)
  do Result<&2, &2, E.Ext4Error, List<&2, Ext4Xattr>>:
    raw : B.Octets <- I.Ext4Inode.raw(~Dv, ~block_size, ~read_block, d, fs, n)
    a : List<&2, Ext4Xattr> <- Ext4Xattr.ibody(raw, n, S.Ext4Fs.verify(fs))
    b : List<&2, Ext4Xattr> <- Ext4Xattr.block(~Dv, ~block_size, ~read_block, d, fs, i)
    return List.append(&2, Ext4Xattr, a, b)

# Values

def Ext4Xattr.find.pick(hit: Bool, x: Ext4Xattr) -> Maybe<&2, Ext4Xattr>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      None{}

# the first attribute with the full name n
def Ext4Xattr.find(xs: List<&2, Ext4Xattr>, +n: B.Octets, found: Maybe<&2, Ext4Xattr>) -> Maybe<&2, Ext4Xattr>:
  match xs found:
    case _ Some{x}:
      Some{x}
    case Nil{} None{}:
      None{}
    case Con{+x, t} None{}:
      Ext4Xattr.find(t, n, Ext4Xattr.find.pick(B.Octets.is_eq(Ext4Xattr.full_name(x), n), x))

def Ext4Xattr.ea_check(on: Bool, +x: Ext4Xattr, +vh: U32, +stored: U32, +ino: Nat) -> Result<&2, &2, E.Ext4Error, Unit>:
  match on:
    case True{}:
      +h = Ext4Xattr.hash(x)
      do Result<&2, &2, E.Ext4Error, Unit>:
        E.Ext4.require(U32.is_eq(vh, stored), E.Ext4BadXattrHash{ino, stored, vh})
        E.Ext4.require(Bool.or(U32.is_eq(h, 0), Bool.or(U32.is_eq(h, Ext4Xattr.inode_hash(False{}, Ext4Xattr.name(x), vh)), U32.is_eq(h, Ext4Xattr.inode_hash(True{}, Ext4Xattr.name(x), vh)))), E.Ext4BadXattrHash{ino, h, Ext4Xattr.inode_hash(False{}, Ext4Xattr.name(x), vh)})
    case False{}:
      Done{Unit{}}

# a value kept in EA inode x.inum: the inode's data, checked against the
# hash the inode and the entry store
def Ext4Xattr.ea_value(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +x: Ext4Xattr, +ino: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  +q = Ext4Xattr.inum(x)
  +f = S.Ext4Fs.ext2(fs)
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    +ea : N.Ext2Inode <- E.Ext4Error.lift(N.Ext2Inode, N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, f, q))
    E.Ext4.require(N.Ext2Inode.has_flag(ea, I.Ext4Inode.flag_ea_inode()), E.Ext4BadXattr{ino, "the value's inode is not an EA inode"})
    +v : B.Octets <- E.Ext4Error.lift(B.Octets, FL.Ext2File.read_all(~Dv, ~block_size, ~read_block, d, f, ea))
    E.Ext4.require(Nat.is_eq(B.Octets.len(v), Ext4Xattr.size(x)), E.Ext4BadXattr{ino, "the EA inode's size is not the value's"})
    raw : B.Octets <- I.Ext4Inode.raw(~Dv, ~block_size, ~read_block, d, fs, q)
    Ext4Xattr.ea_check(S.Ext4Fs.verify(fs), x, K.Ext2Csum.crc32c(S.Ext4Fs.seed(fs), v), I.Ext4Inode.atime(raw), ino)
    return v

def Ext4Xattr.value_of.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, inline: Bool, +d: Dv, +fs: S.Ext4Fs, +x: Ext4Xattr, +ino: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match inline:
    case True{}:
      Done{Ext4Xattr.value(x)}
    case False{}:
      Ext4Xattr.ea_value(~Dv, ~block_size, ~read_block, d, fs, x, ino)

def Ext4Xattr.value_of(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, m: Maybe<&2, Ext4Xattr>, +d: Dv, +fs: S.Ext4Fs, +n: B.Octets, +ino: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match m:
    case None{}:
      Fail{E.Ext4NoXattr{B.Octets.to_string(n)}}
    case Some{+x}:
      Ext4Xattr.value_of.go(~Dv, ~block_size, ~read_block, Nat.is_eq(Ext4Xattr.inum(x), 0n), d, fs, x, ino)

# the value of inode i's attribute with the full name n ("user.x",
# "trusted.y", ...), from wherever it is kept; Ext4NoXattr if there is none
def Ext4Xattr.get(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +n: B.Octets) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    xs : List<&2, Ext4Xattr> <- Ext4Xattr.list(~Dv, ~block_size, ~read_block, d, fs, i)
    Ext4Xattr.value_of(~Dv, ~block_size, ~read_block, Ext4Xattr.find(xs, n, None{}), d, fs, n, N.Ext2Inode.number_of(i))
