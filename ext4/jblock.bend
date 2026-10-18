# bend-osdev-ext4: the blocks of a jbd2 log, their codec and their
# checksums (the jbd2 documentation: "Block Header", "Descriptor Block",
# "Data Block", "Revocation Block", "Commit Block").
#
# Every log block but a data block starts with the 12-byte header (h_magic,
# h_blocktype, h_sequence: the transaction's ID). Block types: 1
# descriptor, 2 commit, 5 revoke.
#
# Descriptor: the header, then tags, each followed by a 16-byte UUID unless
# its flags have SAME_UUID (2); LAST_TAG (8) ends the list; ESCAPE (1) says
# the data block's first four bytes were the magic number and are stored as
# zeros. A tag is t_blocknr, then (csum_v3) t_flags, t_blocknr_high,
# t_checksum, all be32 (16 bytes), or (otherwise) t_checksum (be16, the low
# 16 bits, csum_v2 only), t_flags (be16), and t_blocknr_high (be32, 64bit
# only). The data blocks follow the descriptor in the log, one per tag.
# With csum_v2/v3 a descriptor ends in a 4-byte tail: crc32c from the
# journal's seed over the block with the tail zeroed; a tag's checksum is
# crc32c from the seed over the transaction's ID (be32) and the data block.
#
# Revoke: the header, r_count (be32: the bytes used, header included), then
# block numbers (be64 with 64bit, else be32), and the same tail as a
# descriptor. Commit: the header, h_chksum_type, h_chksum_size, two bytes
# of padding, h_chksum[8] (be32 each), h_commit_sec (be64), h_commit_nsec
# (be32); with csum_v2/v3, h_chksum[0] is crc32c from the seed over the
# whole block with h_chksum[0] zeroed.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../ext2/csum.bend as K
import ./jsuper.bend as J

def Jbd2.kind_desc() -> U32:
  1

def Jbd2.kind_commit() -> U32:
  2

def Jbd2.kind_revoke() -> U32:
  5

def Jbd2.flag_escape() -> U32:
  1

def Jbd2.flag_same_uuid() -> U32:
  2

def Jbd2.flag_last() -> U32:
  8

def Jbd2.be16(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.be16_at(o, i), 0)

def Jbd2.two32() -> Nat:
  Nat.mul(65536n, 65536n)

# a 48-bit block number from its halves (64bit: the high half's low 16
# bits count; Nat holds 48 bits, as ext4's block numbers)
def Jbd2.join(wide: Bool, hi: U32, lo: U32) -> Nat:
  match wide:
    case True{}:
      Nat.add(Nat.mul(U32.to_nat(U32.and(hi, 65535)), Jbd2.two32()), U32.to_nat(lo))
    case False{}:
      U32.to_nat(lo)

def Jbd2.lo(+n: Nat) -> U32:
  U32.from_nat(Nat.mod(n, Jbd2.two32()))

def Jbd2.hi(+n: Nat) -> U32:
  U32.from_nat(Nat.div(n, Jbd2.two32()))

def Jbd2.header(kind: U32, seq: U32) -> B.Octets:
  B.Octets.append(B.Octets.be32(J.Jbd2.magic()), B.Octets.append(B.Octets.be32(kind), B.Octets.be32(seq)))

# whether blk is a log block of this kind for transaction seq
def Jbd2Block.is(+blk: B.Octets, +kind: U32, +seq: U32) -> Bool:
  Bool.and(U32.is_eq(J.Jbd2.be32(blk, 0n), J.Jbd2.magic()), Bool.and(U32.is_eq(J.Jbd2.be32(blk, 4n), kind), U32.is_eq(J.Jbd2.be32(blk, 8n), seq)))

# a log block's type, if it has the magic number and transaction seq (0
# for anything else: the end of the log)
def Jbd2Block.kind.pick(ok: Bool, +blk: B.Octets) -> U32:
  match ok:
    case True{}:
      J.Jbd2.be32(blk, 4n)
    case False{}:
      0

def Jbd2Block.kind(+blk: B.Octets, +seq: U32) -> U32:
  Jbd2Block.kind.pick(Bool.and(U32.is_eq(J.Jbd2.be32(blk, 0n), J.Jbd2.magic()), U32.is_eq(J.Jbd2.be32(blk, 8n), seq)), blk)

# A tail checksum (descriptor and revoke blocks): crc32c over the block
# with its last four bytes zeroed

def Jbd2Block.tail_csum(+g: J.Jbd2Geom, +blk: B.Octets) -> U32:
  +bs = J.Jbd2Geom.bs(g)
  K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), B.Octets.take(Nat.sub(bs, 4n), blk)), B.Octets.zeros(4n))

def Jbd2Block.tail_ok(+check: Bool, +g: J.Jbd2Geom, +blk: B.Octets) -> Bool:
  Bool.or(Bool.not(Bool.and(check, J.Jbd2Geom.has_csum(g))), U32.is_eq(Jbd2Block.tail_csum(g, blk), J.Jbd2.be32(blk, Nat.sub(J.Jbd2Geom.bs(g), 4n))))

# body (bs - tail bytes) with its tail added when the journal has
# checksums
def Jbd2Block.seal(csum: Bool, +g: J.Jbd2Geom, +body: B.Octets) -> B.Octets:
  match csum:
    case True{}:
      B.Octets.append(body, B.Octets.be32(Jbd2Block.tail_csum(g, B.Octets.append(body, B.Octets.zeros(4n)))))
    case False{}:
      body

def Jbd2Block.pad(+g: J.Jbd2Geom, +body: B.Octets) -> B.Octets:
  B.Octets.append(body, B.Octets.zeros(Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g)), B.Octets.len(body))))

# Tags

type Jbd2Tag is Data:
  Jbd2Tag{block: Nat, flags: U32, csum: U32}

def Jbd2Tag.block(t: Jbd2Tag) -> Nat:
  match t:
    case Jbd2Tag{b, f, c}:
      b

def Jbd2Tag.flags(t: Jbd2Tag) -> U32:
  match t:
    case Jbd2Tag{b, f, c}:
      f

def Jbd2Tag.csum(t: Jbd2Tag) -> U32:
  match t:
    case Jbd2Tag{b, f, c}:
      c

def Jbd2Tag.parse.go(v3: Bool, +wide: Bool, +o: B.Octets) -> Jbd2Tag:
  match v3:
    case True{}:
      Jbd2Tag{Jbd2.join(wide, J.Jbd2.be32(o, 8n), J.Jbd2.be32(o, 0n)), J.Jbd2.be32(o, 4n), J.Jbd2.be32(o, 12n)}
    case False{}:
      Jbd2Tag{Jbd2.join(wide, J.Jbd2.be32(o, 8n), J.Jbd2.be32(o, 0n)), Jbd2.be16(o, 6n), Jbd2.be16(o, 4n)}

# the tag at the start of o
def Jbd2Tag.parse(+g: J.Jbd2Geom, +o: B.Octets) -> Jbd2Tag:
  Jbd2Tag.parse.go(Nat.is_eq(J.Jbd2Geom.csum(g), 3n), J.Jbd2Geom.wide(g), o)

def Jbd2Tag.encode.go(v: Nat, wide: Bool, +b: Nat, +f: U32, +c: U32) -> B.Octets:
  match v wide:
    case 3n _:
      B.Octets.append(B.Octets.be32(Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(Jbd2.hi(b)), B.Octets.be32(c))))
    case 2n True{}:
      B.Octets.append(B.Octets.be32(Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(Jbd2.hi(b)), B.Octets.zeros(2n)))))
    case 2n False{}:
      B.Octets.append(B.Octets.be32(Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.zeros(2n))))
    case _ True{}:
      B.Octets.append(B.Octets.be32(Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.be32(Jbd2.hi(b)))))
    case _ False{}:
      B.Octets.append(B.Octets.be32(Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.be16(f)))

def Jbd2Tag.encode(+g: J.Jbd2Geom, t: Jbd2Tag) -> B.Octets:
  match t:
    case Jbd2Tag{b, f, c}:
      Jbd2Tag.encode.go(J.Jbd2Geom.csum(g), J.Jbd2Geom.wide(g), b, f, c)

# Descriptor blocks

type Jbd2TagStep is Data:
  Jbd2TagEnd{}
  Jbd2TagAt{tag: Jbd2Tag, size: Nat, last: Bool}

def Jbd2Tag.uuid.pick(same: Bool) -> Nat:
  match same:
    case True{}:
      0n
    case False{}:
      16n

def Jbd2Tag.step.go(room: Bool, +g: J.Jbd2Geom, +o: B.Octets, +avail: Nat) -> Jbd2TagStep:
  match room:
    case False{}:
      Jbd2TagEnd{}
    case True{}:
      +t = Jbd2Tag.parse(g, o)
      +f = Jbd2Tag.flags(t)
      +size = Nat.add(J.Jbd2Geom.tag_size(g), Jbd2Tag.uuid.pick(J.Jbd2.has(f, Jbd2.flag_same_uuid())))
      Jbd2TagAt{t, size, Bool.or(J.Jbd2.has(f, Jbd2.flag_last()), Nat.is_lt(avail, Nat.add(size, J.Jbd2Geom.tag_size(g))))}

# the tag at the start of o, avail bytes of the tag area left
def Jbd2Tag.step(+g: J.Jbd2Geom, +o: B.Octets, +avail: Nat) -> Jbd2TagStep:
  Jbd2Tag.step.go(Nat.is_le(J.Jbd2Geom.tag_size(g), avail), g, o, avail)

def Jbd2Desc.walk(fuel: Nat, st: Jbd2TagStep, o: B.Octets, +avail: Nat, +g: J.Jbd2Geom, acc: List<&2, Jbd2Tag>) -> List<&2, Jbd2Tag>:
  match fuel st:
    case 0n _:
      List.reverse(&2, Jbd2Tag, acc)
    case 1n+f Jbd2TagEnd{}:
      List.reverse(&2, Jbd2Tag, acc)
    case 1n+f Jbd2TagAt{t, +size, last}:
      match last:
        case True{}:
          List.reverse(&2, Jbd2Tag, Con{t, acc})
        case False{}:
          +rest = B.Octets.drop(size, o)
          +left = Nat.sub(avail, size)
          Jbd2Desc.walk(f, Jbd2Tag.step(g, rest, left), rest, left, g, Con{t, acc})

def Jbd2Desc.tags(+g: J.Jbd2Geom, +blk: B.Octets) -> List<&2, Jbd2Tag>:
  +area = B.Octets.drop(12n, blk)
  +n = Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), 12n), J.Jbd2Geom.tail(g))
  Jbd2Desc.walk(Nat.add(Nat.div(n, 8n), 1n), Jbd2Tag.step(g, area, n), area, n, g, Nil{})

def Jbd2Desc.decode.go(ok: Bool, +g: J.Jbd2Geom, +blk: B.Octets) -> Maybe<&2, List<&2, Jbd2Tag>>:
  match ok:
    case True{}:
      Some{Jbd2Desc.tags(g, blk)}
    case False{}:
      None{}

# a descriptor block's tags, or None if its tail checksum fails (when
# checked)
def Jbd2Desc.decode(+check: Bool, +g: J.Jbd2Geom, +blk: B.Octets) -> Maybe<&2, List<&2, Jbd2Tag>>:
  Jbd2Desc.decode.go(Jbd2Block.tail_ok(check, g, blk), g, blk)

def Jbd2Desc.tag_uuid(same: Bool, uuid: B.Octets) -> B.Octets:
  match same:
    case True{}:
      B.Octets.empty()
    case False{}:
      uuid

def Jbd2Desc.tag_bytes(+g: J.Jbd2Geom, ts: List<&2, Jbd2Tag>, +uuid: B.Octets, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match ts:
    case Nil{}:
      List.reverse(&2, B.Octets, acc)
    case Con{+t, rest}:
      Jbd2Desc.tag_bytes(g, rest, uuid, Con{Jbd2Desc.tag_uuid(J.Jbd2.has(Jbd2Tag.flags(t), Jbd2.flag_same_uuid()), uuid), Con{Jbd2Tag.encode(g, t), acc}})

# a descriptor block for transaction seq: the header, the tags (each
# followed by uuid unless it has SAME_UUID), padding, and the tail
def Jbd2Desc.encode(+g: J.Jbd2Geom, +seq: U32, ts: List<&2, Jbd2Tag>, +uuid: B.Octets) -> B.Octets:
  Jbd2Block.seal(J.Jbd2Geom.has_csum(g), g, Jbd2Block.pad(g, B.Octets.append(Jbd2.header(Jbd2.kind_desc(), seq), B.Octets.concat(Jbd2Desc.tag_bytes(g, ts, uuid, Nil{})))))

# how many tags a descriptor holds when only the first carries a UUID
def Jbd2Desc.capacity(+g: J.Jbd2Geom) -> Nat:
  Nat.div(Nat.sub(Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), 12n), J.Jbd2Geom.tail(g)), 16n), J.Jbd2Geom.tag_size(g))

# Data blocks: escaping, and the tag checksum

# whether a data block starts with the magic number, and must be escaped
def Jbd2.needs_escape(+data: B.Octets) -> Bool:
  B.list_eq(B.Octets.to_list(B.Octets.take(4n, data)), B.be32(J.Jbd2.magic()))

def Jbd2.escape.pick(esc: Bool, +data: B.Octets) -> B.Octets:
  match esc:
    case True{}:
      B.Octets.append(B.Octets.zeros(4n), B.Octets.drop(4n, data))
    case False{}:
      data

# a block as the log stores it (its first four bytes zeroed if they are the
# magic number)
def Jbd2.escape(+data: B.Octets) -> B.Octets:
  Jbd2.escape.pick(Jbd2.needs_escape(data), data)

# a block as the log stored it, back as it was (esc: its tag's ESCAPE flag)
def Jbd2.unescape(esc: Bool, +data: B.Octets) -> B.Octets:
  match esc:
    case True{}:
      B.Octets.append(B.Octets.be32(J.Jbd2.magic()), B.Octets.drop(4n, data))
    case False{}:
      data

# the checksum a tag holds for a data block of transaction seq
def Jbd2.data_csum(+g: J.Jbd2Geom, seq: U32, data: B.Octets) -> U32:
  K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), B.Octets.be32(seq)), data)

def Jbd2.data_csum.cmp(v: Nat, +stored: U32, +c: U32) -> Bool:
  match v:
    case 3n:
      U32.is_eq(stored, c)
    case 2n:
      U32.is_eq(stored, U32.and(c, 65535))
    case _:
      True{}

# whether a data block's tag checksum holds (always, without checksums)
def Jbd2.data_ok(+check: Bool, +g: J.Jbd2Geom, +seq: U32, +data: B.Octets, +stored: U32) -> Bool:
  Bool.or(Bool.not(check), Jbd2.data_csum.cmp(J.Jbd2Geom.csum(g), stored, Jbd2.data_csum(g, seq, data)))

# the checksum field a tag stores (the low 16 bits with csum_v2, nothing
# without checksums)
def Jbd2.tag_csum(v: Nat, +g: J.Jbd2Geom, +seq: U32, +data: B.Octets) -> U32:
  match v:
    case 3n:
      Jbd2.data_csum(g, seq, data)
    case 2n:
      U32.and(Jbd2.data_csum(g, seq, data), 65535)
    case _:
      0

# Revoke blocks

def Jbd2Revoke.entry_size(wide: Bool) -> Nat:
  match wide:
    case True{}:
      8n
    case False{}:
      4n

def Jbd2Revoke.read(+wide: Bool, +o: B.Octets) -> Nat:
  Jbd2.join(wide, J.Jbd2.be32(o, 0n), J.Jbd2.be32(o, Nat.sub(Jbd2Revoke.entry_size(wide), 4n)))

def Jbd2Revoke.walk(n: Nat, o: B.Octets, +wide: Bool, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      List.reverse(&2, Nat, acc)
    case 1n+p:
      +x = o
      Jbd2Revoke.walk(p, B.Octets.drop(Jbd2Revoke.entry_size(wide), x), wide, Con{Jbd2Revoke.read(wide, x), acc})

def Jbd2Revoke.decode.go(ok: Bool, +g: J.Jbd2Geom, +blk: B.Octets, +count: Nat) -> Maybe<&2, List<&2, Nat>>:
  match ok:
    case True{}:
      +wide = J.Jbd2Geom.wide(g)
      Some{Jbd2Revoke.walk(Nat.div(Nat.sub(count, 16n), Jbd2Revoke.entry_size(wide)), B.Octets.drop(16n, blk), wide, Nil{})}
    case False{}:
      None{}

# a revoke block's block numbers, or None if its tail checksum fails (when
# checked) or r_count is outside the block
def Jbd2Revoke.decode(+check: Bool, +g: J.Jbd2Geom, +blk: B.Octets) -> Maybe<&2, List<&2, Nat>>:
  +count = J.Jbd2.nat(blk, 12n)
  Jbd2Revoke.decode.go(Bool.and(Jbd2Block.tail_ok(check, g, blk), Bool.and(Nat.is_le(16n, count), Nat.is_le(count, Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))))), g, blk, count)

def Jbd2Revoke.entry(+wide: Bool, +b: Nat) -> B.Octets:
  match wide:
    case True{}:
      B.Octets.append(B.Octets.be32(Jbd2.hi(b)), B.Octets.be32(Jbd2.lo(b)))
    case False{}:
      B.Octets.be32(Jbd2.lo(b))

def Jbd2Revoke.entries(bs: List<&2, Nat>, +wide: Bool, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match bs:
    case Nil{}:
      List.reverse(&2, B.Octets, acc)
    case Con{b, t}:
      Jbd2Revoke.entries(t, wide, Con{Jbd2Revoke.entry(wide, b), acc})

# a revoke block for transaction seq revoking the blocks bs
def Jbd2Revoke.encode(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>) -> B.Octets:
  +wide = J.Jbd2Geom.wide(g)
  +count = Nat.add(16n, Nat.mul(List.length(&2, Nat, bs), Jbd2Revoke.entry_size(wide)))
  Jbd2Block.seal(J.Jbd2Geom.has_csum(g), g, Jbd2Block.pad(g, B.Octets.append(Jbd2.header(Jbd2.kind_revoke(), seq), B.Octets.append(B.Octets.be32(U32.from_nat(count)), B.Octets.concat(Jbd2Revoke.entries(bs, wide, Nil{}))))))

# how many block numbers a revoke block holds
def Jbd2Revoke.capacity(+g: J.Jbd2Geom) -> Nat:
  Nat.div(Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), 16n), J.Jbd2Geom.tail(g)), Jbd2Revoke.entry_size(J.Jbd2Geom.wide(g)))

# Commit blocks

def Jbd2Commit.csum(+g: J.Jbd2Geom, +blk: B.Octets) -> U32:
  K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), B.Octets.take(16n, blk)), B.Octets.zeros(4n)), B.Octets.drop(20n, blk))

# whether a commit block's checksum holds (always, without checksums or
# when not checked)
def Jbd2Commit.ok(+check: Bool, +g: J.Jbd2Geom, +blk: B.Octets) -> Bool:
  Bool.or(Bool.not(Bool.and(check, J.Jbd2Geom.has_csum(g))), U32.is_eq(Jbd2Commit.csum(g, blk), J.Jbd2.be32(blk, 16n)))

def Jbd2Commit.seal(csum: Bool, +g: J.Jbd2Geom, +blk: B.Octets) -> B.Octets:
  match csum:
    case True{}:
      J.Jbd2.patch32(blk, 16n, Jbd2Commit.csum(g, blk))
    case False{}:
      blk

# a commit block for transaction seq, stamped with a time (seconds and
# nanoseconds)
def Jbd2Commit.encode(+g: J.Jbd2Geom, seq: U32, sec: U32, nsec: U32) -> B.Octets:
  +bs = J.Jbd2Geom.bs(g)
  +body = B.Octets.append(Jbd2.header(Jbd2.kind_commit(), seq), B.Octets.append(B.Octets.zeros(36n), B.Octets.append(B.Octets.be64(W.W64.from_parts(0, sec)), B.Octets.be32(nsec))))
  Jbd2Commit.seal(J.Jbd2Geom.has_csum(g), g, B.Octets.append(body, B.Octets.zeros(Nat.sub(bs, B.Octets.len(body)))))
