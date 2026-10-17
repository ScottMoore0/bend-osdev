# bend-osdev-lz4, the frame format (LZ4 Frame Format Description,
# lz4_Frame_format.md, from the LZ4 project): one LZ4 frame.
#
# A frame is the magic number 0x184D2204, a descriptor (FLG, BD, the content
# size if FLG says so, the dictionary ID if FLG says so), the header checksum
# (the second byte of the descriptor's XXH32), data blocks, the end mark (a
# block size of 0), and the content checksum if FLG says so. Checksums are
# XXH32 with seed 0, from bend-kit-hash.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import bend-kit-hash@0.2.0.0/hash.bend as H
import ./block.bend as K

# Options

# max: the most bytes decompression may produce (it fails with
# Lz4OutputTooLarge past it); verify: check the block and content checksums
# (the header checksum is always checked); dict: the dictionary every frame
# starts after (empty for none; the frame's dictionary ID names it)
type Lz4Options is Data:
  Lz4Options{max: U32, verify: Bool, dict: B.Octets}

# 64 MiB at most, checksums verified, no dictionary
def Lz4Options.default() -> Lz4Options:
  Lz4Options{67108864, True{}, B.Octets.empty()}

# A frame's descriptor: blocks independent (or each may refer to the ones
# before); block checksums; content checksum; content size; dictionary ID;
# block maximum size (65536, 262144, 1048576 or 4194304)
type Lz4FrameInfo is Data:
  Lz4FrameInfo{indep: Bool, block_sum: Bool, content_sum: Bool, size: Maybe<&2, W.W64>, dict_id: Maybe<&2, U32>, block_max: U32}

# a decoded frame: its content, and the input after it
type Lz4Frame is Data:
  Lz4Frame{content: B.Octets, rest: B.Octets}

# Checksums

def frm.xxh32(xs: List<&2, U32>) -> U32:
  H.xxh32.str(B.to_string(xs), 0)

# XXH32 with seed 0: the frame format's checksum
def frame_checksum(o: B.Octets) -> U32:
  H.xxh32.str(B.Octets.to_string(o), 0)

# Helpers

def frm.need(m: Maybe<&2, U32>) -> Result<&2, &2, K.Lz4Error, U32>:
  match m:
    case None{}:
      Fail{K.Lz4Truncated{}}
    case Some{v}:
      Done{v}

def frm.need64(m: Maybe<&2, W.W64>) -> Result<&2, &2, K.Lz4Error, W.W64>:
  match m:
    case None{}:
      Fail{K.Lz4Truncated{}}
    case Some{v}:
      Done{v}

def frm.check(ok: Bool, e: K.Lz4Error) -> Result<&2, &2, K.Lz4Error, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

def frm.bit(b: U32, k: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(b, k), 0))

def frm.n(on: Bool, k: Nat) -> Nat:
  match on:
    case True{}:
      k
    case False{}:
      0n

# The header

def frm.bmax.pick(ok: Bool, code: U32) -> Result<&2, &2, K.Lz4Error, U32>:
  match ok:
    case True{}:
      Done{U32.shln(1, U32.to_nat(U32.add(U32.mul(code, 2), 8)))}
    case False{}:
      Fail{K.Lz4BadDescriptor{}}

# BD: bits 7 and 3 to 0 are reserved (0); bits 6 to 4 give the block maximum
# size, 4 to 7 (0 to 3 are reserved)
def frm.bmax(+bd: U32) -> Result<&2, &2, K.Lz4Error, U32>:
  +code = U32.shrn(bd, 4n)
  frm.bmax.pick(Bool.and(U32.is_eq(U32.and(bd, 143), 0), U32.is_le(4, code)), code)

def frm.opt64(on: Bool, xs: List<&2, U32>, i: Nat) -> Result<&2, &2, K.Lz4Error, Maybe<&2, W.W64>>:
  match on:
    case True{}:
      do Result<&2, &2, K.Lz4Error, Maybe<&2, W.W64>>:
        v : W.W64 <- frm.need64(B.le64_at(xs, i))
        return Some{v}
    case False{}:
      Done{None{}}

def frm.opt32(on: Bool, xs: List<&2, U32>, i: Nat) -> Result<&2, &2, K.Lz4Error, Maybe<&2, U32>>:
  match on:
    case True{}:
      do Result<&2, &2, K.Lz4Error, Maybe<&2, U32>>:
        v : U32 <- frm.need(B.le32_at(xs, i))
        return Some{v}
    case False{}:
      Done{None{}}

# a frame's descriptor, and the input after its header
type Lz4Hd is Data:
  Lz4Hd{info: Lz4FrameInfo, rest: List<&2, U32>}

# FLG: bits 7 and 6 are the version (01), bit 5 block independence, 4 block
# checksums, 3 content size, 2 content checksum, 1 reserved (0), 0
# dictionary ID
def frm.header(+xs: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Hd>:
  do Result<&2, &2, K.Lz4Error, Lz4Hd>:
    magic : U32 <- frm.need(B.le32_at(xs, 0n))
    ok1 : Unit <- frm.check(U32.is_eq(magic, 407708164), K.Lz4BadMagic{})
    +flg : U32 <- frm.need(B.at(xs, 4n))
    bd : U32 <- frm.need(B.at(xs, 5n))
    ok2 : Unit <- frm.check(U32.is_eq(U32.and(flg, 192), 64), K.Lz4BadVersion{})
    ok3 : Unit <- frm.check(U32.is_eq(U32.and(flg, 2), 0), K.Lz4BadDescriptor{})
    bmax : U32 <- frm.bmax(bd)
    +csize : Bool = frm.bit(flg, 8)
    +hasdict : Bool = frm.bit(flg, 1)
    +dlen : Nat = Nat.add(2n, Nat.add(frm.n(csize, 8n), frm.n(hasdict, 4n)))
    +desc : List<&2, U32> = B.take(dlen, B.drop(4n, xs))
    hc : U32 <- frm.need(B.at(xs, Nat.add(4n, dlen)))
    ok4 : Unit <- frm.check(U32.is_eq(hc, U32.and(U32.shrn(frm.xxh32(desc), 8n), 255)), K.Lz4BadHeaderChecksum{})
    size : Maybe<&2, W.W64> <- frm.opt64(csize, desc, 2n)
    did : Maybe<&2, U32> <- frm.opt32(hasdict, desc, Nat.add(2n, frm.n(csize, 8n)))
    return Lz4Hd{Lz4FrameInfo{frm.bit(flg, 32), frm.bit(flg, 16), frm.bit(flg, 4), size, did, bmax}, B.drop(Nat.add(5n, dlen), xs)}

def frm.info(r: Result<&2, &2, K.Lz4Error, Lz4Hd>) -> Result<&2, &2, K.Lz4Error, Lz4FrameInfo>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Lz4Hd{info, rest}}:
      Done{info}

# the descriptor of the LZ4 frame at the start of src
def frame_header(src: B.Octets) -> Result<&2, &2, K.Lz4Error, Lz4FrameInfo>:
  frm.info(frm.header(B.Octets.to_list(src)))

# Data blocks

# what every block of a frame shares: block checksums, independence, the
# block maximum size, whether to verify checksums, the dictionary (reversed)
type Lz4Cfg is Data:
  Lz4Cfg{bsum: Bool, indep: Bool, bmax: U32, verify: Bool, dict: List<&2, U32>}

# where the walk over a frame's blocks stands: acc is the frame's output so
# far, reversed, after the dictionary (reversed)
type Lz4Blocks is Data:
  Lz4More{acc: List<&2, U32>, room: U32, rest: List<&2, U32>}
  Lz4Ended{acc: List<&2, U32>, room: U32, rest: List<&2, U32>}
  Lz4Broken{e: K.Lz4Error}

# an uncompressed block
def frm.raw(ok: Bool, +data: List<&2, U32>, +n: U32, acc: List<&2, U32>, +room: U32, rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match ok:
    case True{}:
      Done{Lz4More{K.blk.push(data, acc), U32.sub(room, n), rest}}
    case False{}:
      Fail{K.Lz4OutputTooLarge{}}

# a block that may refer back into the frame's output and the dictionary
def frm.linked(r: Result<&2, &2, K.Lz4Error, K.Lz4Out>, +rb: Nat, +room: U32, rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{K.Lz4Out{acc, left}}:
      Done{Lz4More{acc, U32.sub(room, U32.from_nat(Nat.sub(rb, left))), rest}}

# an independent block (decoded after the dictionary alone): its bytes go on
# top of the frame's output
def frm.indep(r: Result<&2, &2, K.Lz4Error, K.Lz4Out>, +rb: Nat, acc: List<&2, U32>, +room: U32, rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{K.Lz4Out{out, left}}:
      +k = Nat.sub(rb, left)
      Done{Lz4More{B.append(B.take(k, out), acc), U32.sub(room, U32.from_nat(k)), rest}}

def frm.lz4(indep: Bool, +rb: Nat, dict: List<&2, U32>, data: List<&2, U32>, +acc: List<&2, U32>, +room: U32, rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match indep:
    case True{}:
      frm.indep(K.blk.run(data, dict, rb), rb, acc, room, rest)
    case False{}:
      frm.linked(K.blk.run(data, acc, rb), rb, room, rest)

# a compressed block decodes into at most the block maximum size and the
# room left; and (as each byte of a block gives at most 255 bytes of output)
# into at most 256 times its size plus one, which keeps the count small
def frm.put(unc: Bool, +c: Lz4Cfg, +n: U32, +data: List<&2, U32>, +acc: List<&2, U32>, +room: U32, rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match unc:
    case True{}:
      frm.raw(U32.is_le(n, room), data, n, acc, room, rest)
    case False{}:
      match c:
        case Lz4Cfg{bsum, indep, bmax, verify, dict}:
          +rb = U32.min(U32.min(room, bmax), U32.mul(U32.add(n, 1), 256))
          frm.lz4(indep, U32.to_nat(rb), dict, data, acc, room, rest)

def frm.bsum.verify(verify: Bool, s: U32, data: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Unit>:
  match verify:
    case True{}:
      frm.check(U32.is_eq(s, frm.xxh32(data)), K.Lz4BadBlockChecksum{})
    case False{}:
      Done{Unit{}}

# the block checksum, when the frame has them: XXH32 of the block's data as
# stored
def frm.bsum(on: Bool, verify: Bool, data: List<&2, U32>, +rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, List<&2, U32>>:
  match on:
    case True{}:
      do Result<&2, &2, K.Lz4Error, List<&2, U32>>:
        s : U32 <- frm.need(B.le32_at(rest, 0n))
        ok : Unit <- frm.bsum.verify(verify, s, data)
        return B.drop(4n, rest)
    case False{}:
      Done{rest}

def frm.after(r: Result<&2, &2, K.Lz4Error, List<&2, U32>>, unc: Bool, +c: Lz4Cfg, +n: U32, +data: List<&2, U32>, +acc: List<&2, U32>, +room: U32) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rest}:
      frm.put(unc, c, n, data, acc, room, rest)

# a block: its size never passes the block maximum size, and its data (and
# checksum) are all there
def frm.data(+c: Lz4Cfg, unc: Bool, +n: U32, +acc: List<&2, U32>, +room: U32, +rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match c:
    case Lz4Cfg{+bsum, +indep, +bmax, +verify, +dict}:
      do Result<&2, &2, K.Lz4Error, Lz4Blocks>:
        ok1 : Unit <- frm.check(U32.is_le(n, bmax), K.Lz4BlockTooLarge{})
        +k : Nat = U32.to_nat(n)
        +data : List<&2, U32> = B.take(k, rest)
        ok2 : Unit <- frm.check(Nat.is_eq(B.len(data), k), K.Lz4Truncated{})
        frm.after(frm.bsum(bsum, verify, data, B.drop(k, rest)), unc, Lz4Cfg{bsum, indep, bmax, verify, dict}, n, data, acc, room)

# the block size field: 0 is the end mark; the high bit marks an uncompressed
# block; the other 31 bits are the size of its data
def frm.head(end: Bool, +w: U32, +c: Lz4Cfg, +acc: List<&2, U32>, +room: U32, +rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match end:
    case True{}:
      Done{Lz4Ended{acc, room, rest}}
    case False{}:
      frm.data(c, frm.bit(w, 2147483648), U32.and(w, 2147483647), acc, room, rest)

def frm.block.at(r: Result<&2, &2, K.Lz4Error, U32>, +c: Lz4Cfg, +acc: List<&2, U32>, +room: U32, +rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Lz4Blocks>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+w}:
      frm.head(U32.is_eq(w, 0), w, c, acc, room, rest)

def frm.lift(r: Result<&2, &2, K.Lz4Error, Lz4Blocks>) -> Lz4Blocks:
  match r:
    case Fail{e}:
      Lz4Broken{e}
    case Done{b}:
      b

def frm.block(+c: Lz4Cfg, +acc: List<&2, U32>, +room: U32, +xs: List<&2, U32>) -> Lz4Blocks:
  frm.lift(frm.block.at(frm.need(B.le32_at(xs, 0n)), c, acc, room, B.drop(4n, xs)))

# every block reads 4 bytes or more, so fuel of the input's length + 1 always
# reaches the end mark or a failure
def frm.blocks(fuel: Nat, s: Lz4Blocks, +c: Lz4Cfg) -> Lz4Blocks:
  match fuel:
    case 0n:
      Lz4Broken{K.Lz4Truncated{}}
    case 1n+f:
      match s:
        case Lz4More{acc, room, rest}:
          frm.blocks(f, frm.block(c, acc, room, rest), c)
        case Lz4Ended{acc, room, rest}:
          Lz4Ended{acc, room, rest}
        case Lz4Broken{e}:
          Lz4Broken{e}

# The frame

# a decoded frame: its content, the room left, the input after it
type Lz4Got is Data:
  Lz4Got{out: List<&2, U32>, room: U32, rest: List<&2, U32>}

def frm.csum.verify(verify: Bool, s: U32, out: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Unit>:
  match verify:
    case True{}:
      frm.check(U32.is_eq(s, frm.xxh32(out)), K.Lz4BadContentChecksum{})
    case False{}:
      Done{Unit{}}

# the content checksum, when the frame has one: XXH32 of the content
def frm.csum(on: Bool, verify: Bool, out: List<&2, U32>, +rest: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, List<&2, U32>>:
  match on:
    case True{}:
      do Result<&2, &2, K.Lz4Error, List<&2, U32>>:
        s : U32 <- frm.need(B.le32_at(rest, 0n))
        ok : Unit <- frm.csum.verify(verify, s, out)
        return B.drop(4n, rest)
    case False{}:
      Done{rest}

# the content size, when the frame has one, is the content's
def frm.csize(m: Maybe<&2, W.W64>, out: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{s}:
      frm.check(W.W64.is_eq(s, W.W64.from_nat(B.len(out))), K.Lz4BadContentSize{})

def frm.ended(b: Lz4Blocks, +k: Nat, verify: Bool, csum: Bool, size: Maybe<&2, W.W64>) -> Result<&2, &2, K.Lz4Error, Lz4Got>:
  match b:
    case Lz4Ended{acc, left, after}:
      +out = B.drop(k, K.blk.rev(acc))
      do Result<&2, &2, K.Lz4Error, Lz4Got>:
        ok : Unit <- frm.csize(size, out)
        rest : List<&2, U32> <- frm.csum(csum, verify, out, after)
        return Lz4Got{out, left, rest}
    case Lz4Broken{e}:
      Fail{e}
    case Lz4More{acc, left, after}:
      Fail{K.Lz4Truncated{}}

def frm.frame.go(r: Result<&2, &2, K.Lz4Error, Lz4Hd>, +verify: Bool, +dict: List<&2, U32>, room: U32) -> Result<&2, &2, K.Lz4Error, Lz4Got>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Lz4Hd{Lz4FrameInfo{indep, bsum, csum, size, did, bmax}, +rest}}:
      +rdict = K.blk.rev(dict)
      frm.ended(frm.blocks(Nat.add(B.len(rest), 1n), Lz4More{rdict, room, rest}, Lz4Cfg{bsum, indep, bmax, verify, rdict}), B.len(dict), verify, csum, size)

# the LZ4 frame at the start of xs, after the dictionary dict, with room
# bytes of output at most
def frm.frame(+xs: List<&2, U32>, +verify: Bool, +dict: List<&2, U32>, room: U32) -> Result<&2, &2, K.Lz4Error, Lz4Got>:
  frm.frame.go(frm.header(xs), verify, dict, room)

def frm.out(r: Result<&2, &2, K.Lz4Error, Lz4Got>) -> Result<&2, &2, K.Lz4Error, Lz4Frame>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Lz4Got{out, room, rest}}:
      Done{Lz4Frame{B.Octets.of_list(out), B.Octets.of_list(rest)}}

# The public interface

# the LZ4 frame at the start of src: its content, and the input after it
def frame_decompress(opts: Lz4Options, src: B.Octets) -> Result<&2, &2, K.Lz4Error, Lz4Frame>:
  match opts:
    case Lz4Options{max, verify, dict}:
      frm.out(frm.frame(B.Octets.to_list(src), verify, B.Octets.to_list(dict), max))
