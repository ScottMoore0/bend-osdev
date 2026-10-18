# bend-osdev-ext2: directories (Poirier, "Directories"; the ext4 disk-layout
# documentation, "Directory Entries").
#
# A directory's data is a sequence of blocks, each a chain of entries: inode
# (4 bytes), rec_len (2), name_len (1), file_type (1, with the filetype
# feature; without it name_len is 2 bytes), then the name, padded to rec_len.
# An entry with inode 0 is unused. With metadata_csum each block ends in a
# 12-byte tail (inode 0, rec_len 12, name_len 0, file_type 0xDE) holding the
# block's checksum.
#
# Hash-indexed (htree) directories are read linearly: their index blocks
# look like a single unused entry covering the block (and the root's index
# lies inside ".."'s rec_len), so a linear walk sees exactly the entries.
# The checksums of the index blocks themselves are not verified.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./csum.bend as K
import ./super.bend as S
import ./inode.bend as N
import ./file.bend as FL

type Ext2Dirent is Data:
  Ext2Dirent{inode: U32, rec_len: U32, name_len: U32, file_type: U32, name: B.Octets}

def Ext2Dirent.inode(e: Ext2Dirent) -> U32:
  match e:
    case Ext2Dirent{i, r, n, f, nm}:
      i

def Ext2Dirent.rec_len(e: Ext2Dirent) -> U32:
  match e:
    case Ext2Dirent{i, r, n, f, nm}:
      r

def Ext2Dirent.name_len(e: Ext2Dirent) -> U32:
  match e:
    case Ext2Dirent{i, r, n, f, nm}:
      n

def Ext2Dirent.file_type(e: Ext2Dirent) -> U32:
  match e:
    case Ext2Dirent{i, r, n, f, nm}:
      f

def Ext2Dirent.name(e: Ext2Dirent) -> B.Octets:
  match e:
    case Ext2Dirent{i, r, n, f, nm}:
      nm

# an entry as the disk stores it: rec_len to 16 bits, name_len and file_type
# to 8
def Ext2Dirent.norm(e: Ext2Dirent) -> Ext2Dirent:
  match e:
    case Ext2Dirent{i, r, n, f, nm}:
      Ext2Dirent{i, B.low16(r), B.byte(n), B.byte(f), nm}

# The codec. An entry's bytes are its 8-byte header (inode, rec_len, then
# name_len and file_type), the name, and zeros up to rec_len.

def Ext2Dirent.header(+inode: U32, +rec_len: U32, name_len: U32, file_type: U32) -> B.Octets:
  B.Octets.append(B.Octets.le32(inode), B.Octets.append(B.Octets.le16(rec_len), B.Octets.of_list([name_len, file_type])))

# an entry's rec_len bytes (the filetype layout)
def Ext2Dirent.encode(e: Ext2Dirent) -> B.Octets:
  match e:
    case Ext2Dirent{+i, +r, n, f, +nm}:
      B.Octets.append(Ext2Dirent.header(i, r, n, f), B.Octets.append(nm, B.Octets.zeros(Nat.sub(U32.to_nat(r), Nat.add(8n, B.Octets.len(nm))))))

def Ext2Dirent.decode.make(filetype: Bool, inode: U32, rec_len: U32, nf: List<&2, U32>, +rest: B.Octets) -> Ext2Dirent:
  match filetype nf:
    case True{} Con{+a6, Con{+a7, t}}:
      Ext2Dirent{inode, rec_len, a6, a7, B.Octets.take(U32.to_nat(a6), rest)}
    case False{} Con{+a6, Con{+a7, t}}:
      +nl = Maybe.default(&2, U32, B.le16_at([a6, a7], 0n), 0)
      Ext2Dirent{inode, rec_len, nl, 0, B.Octets.take(U32.to_nat(nl), rest)}
    case _ _:
      Ext2Dirent{inode, rec_len, 0, 0, B.Octets.empty()}

def Ext2Dirent.decode.go(+filetype: Bool, ok: Bool, +hdr: B.Octets, +rest: B.Octets) -> Maybe<&2, Ext2Dirent>:
  match ok:
    case True{}:
      Some{Ext2Dirent.decode.make(filetype, Maybe.default(&2, U32, B.Octets.le32_at(B.Octets.take(4n, hdr), 0n), 0), Maybe.default(&2, U32, B.Octets.le16_at(B.Octets.take(2n, B.Octets.drop(4n, hdr)), 0n), 0), B.Octets.to_list(B.Octets.drop(2n, B.Octets.drop(4n, hdr))), rest)}
    case False{}:
      None{}

# the entry at the start of o; filetype: the filetype feature's layout
# (name_len 1 byte, then file_type), else name_len is 2 bytes and file_type
# reads as 0. None if o is shorter than a header; the name is the name_len
# bytes after it, fewer if o ends first. No other checks: see
# Ext2Dirent.check.
def Ext2Dirent.decode(+filetype: Bool, +o: B.Octets) -> Maybe<&2, Ext2Dirent>:
  +hdr = B.Octets.take(8n, o)
  Ext2Dirent.decode.go(filetype, Nat.is_eq(B.Octets.len(hdr), 8n), hdr, B.Octets.drop(8n, o))

# Validation

# the shortest rec_len an entry with a name of n bytes may have: 8 + n,
# rounded up to a multiple of 4
def Ext2Dirent.min_rec_len(n: Nat) -> Nat:
  Nat.mul(Nat.div(Nat.add(n, 11n), 4n), 4n)

def Ext2Dirent.why(ok: Bool, why: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{why}

# why an entry is malformed, if it is, when avail bytes of its block are
# left from its start and the filesystem has inodes inodes: rec_len a
# multiple of 4, long enough for the header and the name, and within the
# block; the inode number in range; a used entry has a name
def Ext2Dirent.check(e: Ext2Dirent, +avail: Nat, +inodes: Nat) -> Maybe<&2, String>:
  match e:
    case Ext2Dirent{+i, +r, +n, f, nm}:
      +rec = U32.to_nat(r)
      Ext2Dirent.why(Nat.is_eq(Nat.mod(rec, 4n), 0n), "rec_len is not a multiple of 4", Ext2Dirent.why(Nat.is_le(Ext2Dirent.min_rec_len(U32.to_nat(n)), rec), "rec_len too short for the entry", Ext2Dirent.why(Nat.is_le(rec, avail), "rec_len past the end of the block", Ext2Dirent.why(Nat.is_le(U32.to_nat(i), inodes), "inode number out of range", Ext2Dirent.why(Bool.or(U32.is_eq(i, 0), Bool.not(U32.is_eq(n, 0))), "a used entry with an empty name", None{})))))

# Walking one block

type Ext2DirStep is Data:
  Ext2DirEnd{}
  Ext2DirBad{why: String}
  Ext2DirEntry{entry: Ext2Dirent, rec_len: Nat}

def Ext2Dir.step.checked(why: Maybe<&2, String>, +e: Ext2Dirent) -> Ext2DirStep:
  match why:
    case None{}:
      Ext2DirEntry{e, U32.to_nat(Ext2Dirent.rec_len(e))}
    case Some{w}:
      Ext2DirBad{w}

def Ext2Dir.step.decoded(m: Maybe<&2, Ext2Dirent>, +avail: Nat, +inodes: Nat) -> Ext2DirStep:
  match m:
    case None{}:
      Ext2DirBad{"entry header past the end of the block"}
    case Some{+e}:
      Ext2Dir.step.checked(Ext2Dirent.check(e, avail, inodes), e)

def Ext2Dir.step.pick(done: Bool, room: Bool, +filetype: Bool, +xs: B.Octets, +avail: Nat, +inodes: Nat) -> Ext2DirStep:
  match done room:
    case True{} _:
      Ext2DirEnd{}
    case False{} False{}:
      Ext2DirBad{"entry header past the end of the block"}
    case False{} True{}:
      Ext2Dir.step.decoded(Ext2Dirent.decode(filetype, xs), avail, inodes)

# what is at byte pos of a block region of limit bytes (xs: the block's
# bytes from pos on)
def Ext2Dir.step(+filetype: Bool, +xs: B.Octets, +pos: Nat, +limit: Nat, +inodes: Nat) -> Ext2DirStep:
  +avail = Nat.sub(limit, pos)
  Ext2Dir.step.pick(Nat.is_le(limit, pos), Nat.is_le(8n, avail), filetype, xs, avail, inodes)

def Ext2Dir.keep.pick(unused: Bool, e: Ext2Dirent, acc: List<&2, Ext2Dirent>) -> List<&2, Ext2Dirent>:
  match unused:
    case True{}:
      acc
    case False{}:
      Con{e, acc}

# the entries kept: the used ones (inode not 0)
def Ext2Dir.keep(+e: Ext2Dirent, acc: List<&2, Ext2Dirent>) -> List<&2, Ext2Dirent>:
  Ext2Dir.keep.pick(U32.is_eq(Ext2Dirent.inode(e), 0), e, acc)

# the used entries of a block region, from byte pos on (st: what is there,
# xs: the region's bytes from pos); base is the block's offset in the
# directory, for messages. Each step moves on by its rec_len, at least 8.
def Ext2Dir.walk(fuel: Nat, st: Ext2DirStep, +filetype: Bool, xs: B.Octets, +pos: Nat, +limit: Nat, +inodes: Nat, +ino: Nat, +base: Nat, acc: List<&2, Ext2Dirent>) -> Result<&2, &2, E.Ext2Error, List<&2, Ext2Dirent>>:
  match fuel st:
    case 0n _:
      Fail{E.Ext2BadDirent{ino, Nat.add(base, pos), "too many entries"}}
    case 1n+f Ext2DirEnd{}:
      Done{List.reverse(&2, Ext2Dirent, acc)}
    case 1n+f Ext2DirBad{w}:
      Fail{E.Ext2BadDirent{ino, Nat.add(base, pos), w}}
    case 1n+f Ext2DirEntry{e, +rec}:
      +ys = B.Octets.drop(rec, xs)
      +next = Nat.add(pos, rec)
      Ext2Dir.walk(f, Ext2Dir.step(filetype, ys, next, limit, inodes), filetype, ys, next, limit, inodes, ino, base, Ext2Dir.keep(e, acc))

# the used entries of a block of bs bytes, of which the first limit hold
# entries
def Ext2Dir.parse_block(+filetype: Bool, +blk: B.Octets, +limit: Nat, +inodes: Nat, +ino: Nat, +base: Nat) -> Result<&2, &2, E.Ext2Error, List<&2, Ext2Dirent>>:
  Ext2Dir.walk(Nat.add(Nat.div(limit, 8n), 2n), Ext2Dir.step(filetype, blk, 0n, limit, inodes), filetype, blk, 0n, limit, inodes, ino, base, Nil{})

# The checksum tail (metadata_csum)

# whether a block of bs bytes ends in a checksum tail
def Ext2Dir.has_tail(+blk: B.Octets, +bs: Nat) -> Bool:
  Bool.and(U32.is_eq(F.Ext2Field.u32(blk, Nat.sub(bs, 12n)), 0), Bool.and(U32.is_eq(F.Ext2Field.u16(blk, Nat.sub(bs, 8n)), 12), Bool.and(U32.is_eq(F.Ext2Field.u8(blk, Nat.sub(bs, 6n)), 0), U32.is_eq(F.Ext2Field.u8(blk, Nat.sub(bs, 5n)), 222))))

def Ext2Dir.tail.pick(tail: Bool, indexed: Bool, +iseed: U32, +blk: B.Octets, +bs: Nat, +ino: Nat, +k: Nat) -> Result<&2, &2, E.Ext2Error, Nat>:
  match tail indexed:
    case True{} _:
      +stored = F.Ext2Field.u32(blk, Nat.sub(bs, 4n))
      +c = K.Ext2Csum.dir_block(iseed, blk, bs)
      do Result<&2, &2, E.Ext2Error, Nat>:
        S.Ext2.require(U32.is_eq(c, stored), E.Ext2BadDirCsum{ino, k, stored, c})
        return Nat.sub(bs, 12n)
    case False{} True{}:
      Done{bs}
    case False{} False{}:
      Fail{E.Ext2NoDirTail{ino, k}}

# how many bytes of block k hold entries, its checksum verified: all of
# them, or with metadata_csum all but the tail (an htree index block has no
# tail and is taken whole)
def Ext2Dir.region(on: Bool, +fs: S.Ext2Fs, +i: N.Ext2Inode, +blk: B.Octets, +k: Nat) -> Result<&2, &2, E.Ext2Error, Nat>:
  match on:
    case True{}:
      +bs = S.Ext2Fs.block_size(fs)
      +n = N.Ext2Inode.number_of(i)
      Ext2Dir.tail.pick(Ext2Dir.has_tail(blk, bs), N.Ext2Inode.has_flag(i, N.Ext2Inode.flag_index()), K.Ext2Csum.inode_seed(S.Ext2Fs.seed(fs), U32.from_nat(n), N.Ext2Inode.generation(i)), blk, bs, n, k)
    case False{}:
      Done{S.Ext2Fs.block_size(fs)}

# Reading a directory, a block at a time

# the used entries of block k of directory i
def Ext2Dir.block(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +k: Nat) -> Result<&2, &2, E.Ext2Error, List<&2, Ext2Dirent>>:
  +bs = S.Ext2Fs.block_size(fs)
  +n = N.Ext2Inode.number_of(i)
  do Result<&2, &2, E.Ext2Error, List<&2, Ext2Dirent>>:
    +blk : B.Octets <- FL.Ext2File.read_block(~Dv, ~block_size, ~read_block, d, fs, i, k)
    S.Ext2.require(Nat.is_eq(B.Octets.len(blk), bs), E.Ext2BadDirent{n, Nat.mul(k, bs), "the directory's size is not a whole number of blocks"})
    limit : Nat <- Ext2Dir.region(S.Ext2Fs.verify_meta(fs), fs, i, blk, k)
    Ext2Dir.parse_block(S.Ext2Fs.has_incompat(fs, S.Ext2Super.incompat_filetype()), blk, limit, S.Ext2Fs.inodes_count(fs), n, Nat.mul(k, bs))

# the used entries of count blocks from block k on, a tail call per block:
# r is the read of the block before k (Done{Nil} at the start), acc the
# entries before it, last first. The first failure is the answer.
def Ext2Dir.all(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, List<&2, Ext2Dirent>>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +k: Nat, acc: List<&2, Ext2Dirent>) -> Result<&2, &2, E.Ext2Error, List<&2, Ext2Dirent>>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{es}:
      Done{List.reverse(&2, Ext2Dirent, List.reverse.go(&2, Ext2Dirent, es, acc))}
    case 1n+c Done{es}:
      Ext2Dir.all(~Dv, ~block_size, ~read_block, c, Ext2Dir.block(~Dv, ~block_size, ~read_block, d, fs, i, k), d, fs, i, Nat.add(k, 1n), List.reverse.go(&2, Ext2Dirent, es, acc))

# every used entry of directory i (with "." and ".."), in the order the
# blocks hold them; Ext2NotDir for any other inode
def Ext2Dir.entries(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext2Error, List<&2, Ext2Dirent>>:
  do Result<&2, &2, E.Ext2Error, List<&2, Ext2Dirent>>:
    S.Ext2.require(N.Ext2Inode.is_dir(i), E.Ext2NotDir{N.Ext2Inode.number_of(i)})
    Ext2Dir.all(~Dv, ~block_size, ~read_block, FL.Ext2File.blocks_needed(fs, i), Done{Nil{}}, d, fs, i, 0n, Nil{})

# Looking a name up

def Ext2Dir.find_in.pick(hit: Bool, e: Ext2Dirent) -> Maybe<&2, Ext2Dirent>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      None{}

# the first entry of es named name (found: what the entries before es gave)
def Ext2Dir.find_in(es: List<&2, Ext2Dirent>, +name: B.Octets, found: Maybe<&2, Ext2Dirent>) -> Maybe<&2, Ext2Dirent>:
  match es found:
    case _ Some{e}:
      Some{e}
    case Nil{} None{}:
      None{}
    case Con{+e, t} None{}:
      Ext2Dir.find_in(t, name, Ext2Dir.find_in.pick(B.Octets.is_eq(Ext2Dirent.name(e), name), e))

def Ext2Dir.find.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, found: Maybe<&2, Ext2Dirent>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +name: B.Octets, +k: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Ext2Dirent>>:
  match count found:
    case _ Some{e}:
      Done{Some{e}}
    case 0n None{}:
      Done{None{}}
    case 1n+c None{}:
      do Result<&2, &2, E.Ext2Error, Maybe<&2, Ext2Dirent>>:
        es : List<&2, Ext2Dirent> <- Ext2Dir.block(~Dv, ~block_size, ~read_block, d, fs, i, k)
        Ext2Dir.find.go(~Dv, ~block_size, ~read_block, c, Ext2Dir.find_in(es, name, None{}), d, fs, i, name, Nat.add(k, 1n))

# the entry named name in directory i, if any; reads the directory's blocks
# only up to the one that holds it
def Ext2Dir.find(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Ext2Dirent>>:
  do Result<&2, &2, E.Ext2Error, Maybe<&2, Ext2Dirent>>:
    S.Ext2.require(N.Ext2Inode.is_dir(i), E.Ext2NotDir{N.Ext2Inode.number_of(i)})
    Ext2Dir.find.go(~Dv, ~block_size, ~read_block, FL.Ext2File.blocks_needed(fs, i), None{}, d, fs, i, name, 0n)
