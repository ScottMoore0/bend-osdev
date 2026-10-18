# bend-osdev-ext4: the index blocks of hashed (htree) directories, their
# codec and their checksum (the ext4 disk-layout documentation, "Hash Tree
# Directories").
#
# Block 0 of an indexed directory is the dx_root: a "." entry (12 bytes),
# a ".." entry whose rec_len covers the rest of the block, then at byte 24
# dx_root_info (reserved_zero le32, hash_version, info_length = 8,
# indirect_levels, unused_flags), then at byte 32 the index: limit (le16),
# count (le16) and the first entry's block (le32), followed by count - 1
# entries of (hash le32, block le32). An interior node (dx_node) is a fake
# entry (inode 0, rec_len = the block) and the same index at byte 8. Index
# entries are sorted by hash; entry 0 covers every hash below entry 1's.
# With metadata_csum the last 8 bytes of the index area (at count_offset +
# limit * 8) are a dx_tail (dt_reserved, dt_checksum), so limit is one
# less; dt_checksum is crc32c from the inode's seed over the block up to
# the end of the count entries, then dt_reserved, then four zero bytes.
import Base
import ../bytes/bytes.bend as B
import ../ext2/csum.bend as K
import ./error.bend as E

type Ext4DxEntry is Data:
  Ext4DxEntry{hash: U32, block: U32}

def Ext4DxEntry.hash(e: Ext4DxEntry) -> U32:
  match e:
    case Ext4DxEntry{h, b}:
      h

def Ext4DxEntry.block(e: Ext4DxEntry) -> U32:
  match e:
    case Ext4DxEntry{h, b}:
      b

# the root: the inode numbers of "." and "..", the hash version, the index
# levels below the root, the limit, and the entries (entry 0's hash is 0)
type Ext4DxRoot is Data:
  Ext4DxRoot{dot: U32, dotdot: U32, version: U32, levels: U32, limit: U32, entries: List<&2, Ext4DxEntry>}

type Ext4DxNode is Data:
  Ext4DxNode{limit: U32, entries: List<&2, Ext4DxEntry>}

def Ext4DxRoot.version(r: Ext4DxRoot) -> U32:
  match r:
    case Ext4DxRoot{a, b, v, l, m, es}:
      v

def Ext4DxRoot.levels(r: Ext4DxRoot) -> U32:
  match r:
    case Ext4DxRoot{a, b, v, l, m, es}:
      l

def Ext4DxRoot.entries(r: Ext4DxRoot) -> List<&2, Ext4DxEntry>:
  match r:
    case Ext4DxRoot{a, b, v, l, m, es}:
      es

def Ext4DxRoot.dot(r: Ext4DxRoot) -> U32:
  match r:
    case Ext4DxRoot{a, b, v, l, m, es}:
      a

def Ext4DxRoot.dotdot(r: Ext4DxRoot) -> U32:
  match r:
    case Ext4DxRoot{a, b, v, l, m, es}:
      b

def Ext4DxNode.entries(n: Ext4DxNode) -> List<&2, Ext4DxEntry>:
  match n:
    case Ext4DxNode{m, +es}:
      es

def Ext4Dx.u8(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, i), 0)

def Ext4Dx.u16(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le16_at(o, i), 0)

def Ext4Dx.u32(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le32_at(o, i), 0)

# the most entries an index of a bs-byte block holds from byte off on
# (one fewer with a checksum tail)
def Ext4Dx.limit.tail(tail: Bool, +n: Nat) -> Nat:
  match tail:
    case True{}:
      Nat.sub(n, 1n)
    case False{}:
      n

def Ext4Dx.limit(+bs: Nat, +off: Nat, tail: Bool) -> Nat:
  Ext4Dx.limit.tail(tail, Nat.div(Nat.sub(bs, off), 8n))

# count entries of an index whose count field is at byte off (entry 0's
# block at off + 4, the others from off + 8), a tail call each
def Ext4Dx.entries.go(n: Nat, o: B.Octets, acc: List<&2, Ext4DxEntry>) -> List<&2, Ext4DxEntry>:
  match n:
    case 0n:
      List.reverse(&2, Ext4DxEntry, acc)
    case 1n+p:
      +x = o
      Ext4Dx.entries.go(p, B.Octets.drop(8n, x), Con{Ext4DxEntry{Ext4Dx.u32(x, 0n), Ext4Dx.u32(x, 4n)}, acc})

def Ext4Dx.entries(+blk: B.Octets, +off: Nat, +count: Nat) -> List<&2, Ext4DxEntry>:
  Con{Ext4DxEntry{0, Ext4Dx.u32(blk, Nat.add(off, 4n))}, Ext4Dx.entries.go(Nat.sub(count, 1n), B.Octets.drop(Nat.add(off, 8n), blk), Nil{})}

# The checksum (dx_tail)

def Ext4Dx.csum(+iseed: U32, +blk: B.Octets, +off: Nat, +count: Nat, +limit: Nat) -> U32:
  +t = Nat.add(off, Nat.mul(limit, 8n))
  K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(iseed, B.Octets.take(Nat.add(off, Nat.mul(count, 8n)), blk)), B.Octets.slice(t, 4n, blk)), B.Octets.zeros(4n))

def Ext4Dx.stored(+blk: B.Octets, +off: Nat, +limit: Nat) -> U32:
  Ext4Dx.u32(blk, Nat.add(Nat.add(off, Nat.mul(limit, 8n)), 4n))

# a checksum, when asked for (Some{iseed}): equal to the stored one
def Ext4Dx.verify(check: Maybe<&2, U32>, +blk: B.Octets, +off: Nat, +count: Nat, +limit: Nat, +ino: Nat, +k: Nat) -> Result<&2, &2, E.Ext4Error, Unit>:
  match check:
    case None{}:
      Done{Unit{}}
    case Some{+s}:
      +c = Ext4Dx.csum(s, blk, off, count, limit)
      +st = Ext4Dx.stored(blk, off, limit)
      E.Ext4.require(U32.is_eq(c, st), E.Ext4BadDxCsum{ino, k, st, c})

def Ext4Dx.is_some(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# Parsing

def Ext4Dx.why(ok: Bool, why: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{why}

# the index's own checks: the limit the block size gives, and 0 < count <=
# limit
def Ext4Dx.index_why(+count: Nat, +limit: Nat, +want: Nat) -> Maybe<&2, String>:
  Ext4Dx.why(Nat.is_eq(limit, want), "limit does not match the block size", Ext4Dx.why(Nat.is_lt(0n, count), "an empty index", Ext4Dx.why(Nat.is_le(count, limit), "count above limit", None{})))

# rec_len of an entry covering the rest of a block from byte off: the
# 16-bit field holds 65536 as 0 or 65535
def Ext4Dx.rec_len_ok(+rec: U32, +bs: Nat, +off: Nat) -> Bool:
  +want = Nat.sub(bs, off)
  Bool.or(Nat.is_eq(U32.to_nat(rec), want), Bool.and(Nat.is_eq(want, 65536n), Bool.or(U32.is_eq(rec, 0), U32.is_eq(rec, 65535))))

def Ext4DxRoot.why(+blk: B.Octets, +bs: Nat, +tail: Bool) -> Maybe<&2, String>:
  Ext4Dx.why(Nat.is_eq(B.Octets.len(blk), bs), "not a whole block", Ext4Dx.why(Bool.and(U32.is_eq(Ext4Dx.u16(blk, 4n), 12), Bool.and(U32.is_eq(Ext4Dx.u8(blk, 6n), 1), U32.is_eq(Ext4Dx.u8(blk, 8n), 46))), "no \".\" entry", Ext4Dx.why(Bool.and(Ext4Dx.rec_len_ok(Ext4Dx.u16(blk, 16n), bs, 12n), Bool.and(U32.is_eq(Ext4Dx.u8(blk, 18n), 2), Bool.and(U32.is_eq(Ext4Dx.u8(blk, 20n), 46), U32.is_eq(Ext4Dx.u8(blk, 21n), 46)))), "no \"..\" entry", Ext4Dx.why(U32.is_eq(Ext4Dx.u32(blk, 24n), 0), "reserved_zero is not zero", Ext4Dx.why(U32.is_eq(Ext4Dx.u8(blk, 29n), 8), "info_length is not 8", Ext4Dx.index_why(U32.to_nat(Ext4Dx.u16(blk, 34n)), U32.to_nat(Ext4Dx.u16(blk, 32n)), Ext4Dx.limit(bs, 32n, tail)))))))

def Ext4DxRoot.parse.go(why: Maybe<&2, String>, +blk: B.Octets, +ino: Nat) -> Result<&2, &2, E.Ext4Error, Ext4DxRoot>:
  match why:
    case Some{w}:
      Fail{E.Ext4BadDxRoot{ino, w}}
    case None{}:
      Done{Ext4DxRoot{Ext4Dx.u32(blk, 0n), Ext4Dx.u32(blk, 12n), Ext4Dx.u8(blk, 28n), Ext4Dx.u8(blk, 30n), Ext4Dx.u16(blk, 32n), Ext4Dx.entries(blk, 32n, U32.to_nat(Ext4Dx.u16(blk, 34n)))}}

def Ext4DxRoot.depth(ok: Bool, +levels: Nat, +ino: Nat) -> Result<&2, &2, E.Ext4Error, Unit>:
  E.Ext4.require(ok, E.Ext4DxTooDeep{ino, levels})

# the root of directory ino from its block 0 (bs bytes), checked: the "."
# and ".." entries, dx_root_info, the index (tail: whether the filesystem
# has metadata_csum, so the index ends in a dx_tail), fewer than max index
# levels, and the checksum when check is Some{inode seed}
def Ext4DxRoot.parse(+blk: B.Octets, +bs: Nat, +tail: Bool, +check: Maybe<&2, U32>, +max: Nat, +ino: Nat) -> Result<&2, &2, E.Ext4Error, Ext4DxRoot>:
  +levels = U32.to_nat(Ext4Dx.u8(blk, 30n))
  do Result<&2, &2, E.Ext4Error, Ext4DxRoot>:
    r : Ext4DxRoot <- Ext4DxRoot.parse.go(Ext4DxRoot.why(blk, bs, tail), blk, ino)
    Ext4DxRoot.depth(Nat.is_lt(levels, max), levels, ino)
    Ext4Dx.verify(check, blk, 32n, U32.to_nat(Ext4Dx.u16(blk, 34n)), U32.to_nat(Ext4Dx.u16(blk, 32n)), ino, 0n)
    return r

def Ext4DxNode.why(+blk: B.Octets, +bs: Nat, +tail: Bool) -> Maybe<&2, String>:
  Ext4Dx.why(Nat.is_eq(B.Octets.len(blk), bs), "not a whole block", Ext4Dx.why(Bool.and(U32.is_eq(Ext4Dx.u32(blk, 0n), 0), Bool.and(Ext4Dx.rec_len_ok(Ext4Dx.u16(blk, 4n), bs, 0n), U32.is_eq(Ext4Dx.u8(blk, 6n), 0))), "no empty entry covering the block", Ext4Dx.index_why(U32.to_nat(Ext4Dx.u16(blk, 10n)), U32.to_nat(Ext4Dx.u16(blk, 8n)), Ext4Dx.limit(bs, 8n, tail))))

def Ext4DxNode.parse.go(why: Maybe<&2, String>, +blk: B.Octets, +ino: Nat, +k: Nat) -> Result<&2, &2, E.Ext4Error, Ext4DxNode>:
  match why:
    case Some{w}:
      Fail{E.Ext4BadDxNode{ino, k, w}}
    case None{}:
      Done{Ext4DxNode{Ext4Dx.u16(blk, 8n), Ext4Dx.entries(blk, 8n, U32.to_nat(Ext4Dx.u16(blk, 10n)))}}

# an interior node of directory ino, from its logical block k, checked
def Ext4DxNode.parse(+blk: B.Octets, +bs: Nat, +tail: Bool, +check: Maybe<&2, U32>, +ino: Nat, +k: Nat) -> Result<&2, &2, E.Ext4Error, Ext4DxNode>:
  do Result<&2, &2, E.Ext4Error, Ext4DxNode>:
    n : Ext4DxNode <- Ext4DxNode.parse.go(Ext4DxNode.why(blk, bs, tail), blk, ino, k)
    Ext4Dx.verify(check, blk, 8n, U32.to_nat(Ext4Dx.u16(blk, 10n)), U32.to_nat(Ext4Dx.u16(blk, 8n)), ino, k)
    return n

# Encoding (for the htree writer)

def Ext4Dx.entry_bytes(es: List<&2, Ext4DxEntry>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match es:
    case Nil{}:
      List.reverse(&2, B.Octets, acc)
    case Con{Ext4DxEntry{h, b}, t}:
      Ext4Dx.entry_bytes(t, Con{B.Octets.append(B.Octets.le32(h), B.Octets.le32(b)), acc})

# an index: limit, count, entry 0's block, the other entries
def Ext4Dx.index_bytes(+limit: Nat, es: List<&2, Ext4DxEntry>) -> B.Octets:
  match es:
    case Nil{}:
      B.Octets.append(B.Octets.le16(U32.from_nat(limit)), B.Octets.zeros(6n))
    case Con{Ext4DxEntry{h, b}, +t}:
      +n = U32.from_nat(1n+List.length(&2, Ext4DxEntry, t))
      B.Octets.append(B.Octets.le16(U32.from_nat(limit)), B.Octets.append(B.Octets.le16(n), B.Octets.append(B.Octets.le32(b), B.Octets.concat(Ext4Dx.entry_bytes(t, Nil{})))))

def Ext4Dx.finish.tail(check: Maybe<&2, U32>, +body: B.Octets, +off: Nat, +count: Nat, +limit: Nat) -> B.Octets:
  match check:
    case None{}:
      body
    case Some{+s}:
      +z = B.Octets.append(body, B.Octets.zeros(4n))
      B.Octets.append(z, B.Octets.le32(Ext4Dx.csum(s, B.Octets.append(z, B.Octets.zeros(4n)), off, count, limit)))

# an index block: head (the entries before the index) and the index, padded
# to the end of the index area, the tail added when check is Some{seed},
# padded to bs bytes
def Ext4Dx.finish(+bs: Nat, check: Maybe<&2, U32>, +head: B.Octets, +off: Nat, +count: Nat, +limit: Nat, idx: B.Octets) -> B.Octets:
  +area = Nat.add(off, Nat.mul(limit, 8n))
  +x = B.Octets.append(head, idx)
  +body = B.Octets.append(x, B.Octets.zeros(Nat.sub(area, B.Octets.len(x))))
  +blk = Ext4Dx.finish.tail(check, body, off, count, limit)
  B.Octets.append(blk, B.Octets.zeros(Nat.sub(bs, B.Octets.len(blk))))

# a root block of bs bytes; ft is the file type stored in the "." and ".."
# entries (2 with the filetype feature, else 0)
def Ext4DxRoot.encode(+bs: Nat, check: Maybe<&2, U32>, +ft: U32, r: Ext4DxRoot) -> B.Octets:
  match r:
    case Ext4DxRoot{dot, dotdot, v, l, m, +es}:
      +limit = U32.to_nat(m)
      +count = List.length(&2, Ext4DxEntry, es)
      +d1 = B.Octets.append(B.Octets.le32(dot), B.Octets.append(B.Octets.le16(12), B.Octets.append(B.Octets.of_list([1, ft, 46, 0, 0, 0]), B.Octets.empty())))
      +d2 = B.Octets.append(B.Octets.le32(dotdot), B.Octets.append(B.Octets.le16(U32.from_nat(Nat.sub(bs, 12n))), B.Octets.of_list([2, ft, 46, 46, 0, 0])))
      +info = B.Octets.append(B.Octets.zeros(4n), B.Octets.of_list([v, 8, l, 0]))
      Ext4Dx.finish(bs, check, B.Octets.append(d1, B.Octets.append(d2, info)), 32n, count, limit, Ext4Dx.index_bytes(limit, es))

# an interior node block of bs bytes
def Ext4DxNode.encode(+bs: Nat, check: Maybe<&2, U32>, n: Ext4DxNode) -> B.Octets:
  match n:
    case Ext4DxNode{m, +es}:
      +limit = U32.to_nat(m)
      +count = List.length(&2, Ext4DxEntry, es)
      +head = B.Octets.append(B.Octets.zeros(4n), B.Octets.append(B.Octets.le16(U32.from_nat(Nat.mod(bs, 65536n))), B.Octets.zeros(2n)))
      Ext4Dx.finish(bs, check, head, 8n, count, limit, Ext4Dx.index_bytes(limit, es))
