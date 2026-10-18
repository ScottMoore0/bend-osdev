# bend-osdev-lzo, the lzop file container, written from the lzop file-format
# notes (the layout of a .lzo file: magic, header, blocks, checksums); no
# lzop or LZO source code was read (see README.md for what each field rests
# on, and what is not yet checked against the lzop tool).
#
# A file is a header, then blocks, then four zero bytes. All numbers are
# big-endian.
#
#   magic          89 4C 5A 4F 00 0D 0A 1A 0A
#   version        16 bits (0x0940 or later here)
#   lib_version    16 bits
#   need           16 bits: the version needed to extract
#   method, level  8 bits each (methods 1, 2, 3: LZO1X streams)
#   flags          32 bits
#   mode           32 bits
#   mtime          32 bits low, 32 bits high
#   name           8-bit length, then the bytes
#   checksum       32 bits: Adler-32 (CRC-32 with flag 0x1000) of the
#                  header from version to the end of the name
#
# A block is its size uncompressed (32 bits; 0 ends the file), its size as
# stored (32 bits; equal: stored as it is, smaller: an LZO1X stream, larger:
# malformed), the checksums its flags ask for (Adler-32 0x1, then CRC-32
# 0x100, of the uncompressed bytes; then, for a compressed block only,
# Adler-32 0x2 and CRC-32 0x200 of the stored bytes), then the stored bytes.
import Base
import ../bytes/bytes.bend as B
import ../crc/crc.bend as CR
import ../crc/table.bend as CT
import ./error.bend as E
import ./decode.bend as D
import ./encode.bend as C
import ./adler32.bend as A

# Checksums, over lists of bytes

def lzp.adler(xs: List<&2, U32>) -> U32:
  A.Adler32.finish(A.adl.go(xs, A.Adler32.start()))

def lzp.crc(xs: List<&2, U32>) -> U32:
  CT.Crc32Spec.compute_fast(CR.crc32.spec(), B.Octets.of_list(xs))

def lzp.sum(crc: Bool, xs: List<&2, U32>) -> U32:
  match crc:
    case True{}:
      lzp.crc(xs)
    case False{}:
      lzp.adler(xs)

def lzp.has(+flags: U32, +bit: U32) -> Bool:
  U32.is_eq(U32.and(flags, bit), bit)

def lzp.magic() -> List<&2, U32>:
  [137, 76, 90, 79, 0, 13, 10, 26, 10]

# Reading

def lzp.need(m: Maybe<&2, U32>) -> Result<&2, &2, E.LzoError, U32>:
  match m:
    case None{}:
      Fail{E.LzoTruncated{}}
    case Some{v}:
      Done{v}

def lzp.ensure(ok: Bool, e: E.LzoError) -> Result<&2, &2, E.LzoError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# the header's fields (flags: the 32 flag bits; name: the stored name)
type LzopHeader is Data:
  LzopHeader{version: U32, lib_version: U32, need: U32, method: U32, level: U32, flags: U32, mode: U32, mtime_low: U32, mtime_high: U32, name: B.Octets}

# a header and where the blocks start
type LzopHead is Data:
  LzopHead{h: LzopHeader, pos: Nat}

def lzp.method_ok(+m: U32) -> Bool:
  Bool.and(U32.is_le(1, m), U32.is_le(m, 3))

def lzp.header(+xs: List<&2, U32>) -> Result<&2, &2, E.LzoError, LzopHead>:
  do Result<&2, &2, E.LzoError, LzopHead>:
    m : Unit <- lzp.ensure(B.list_eq.fast(B.take.fast(9n, xs), lzp.magic()), E.LzoBadMagic{})
    +version : U32 <- lzp.need(B.be16_at(xs, 9n))
    v : Unit <- lzp.ensure(U32.is_le(2368, version), E.LzoBadVersion{})
    +lib : U32 <- lzp.need(B.be16_at(xs, 11n))
    +need : U32 <- lzp.need(B.be16_at(xs, 13n))
    n : Unit <- lzp.ensure(U32.is_le(need, 4160), E.LzoBadVersion{})
    +method : U32 <- lzp.need(B.at(xs, 15n))
    mo : Unit <- lzp.ensure(lzp.method_ok(method), E.LzoBadMethod{})
    +level : U32 <- lzp.need(B.at(xs, 16n))
    +flags : U32 <- lzp.need(B.be32_at(xs, 17n))
    f : Unit <- lzp.ensure(U32.is_eq(U32.and(flags, 3136), 0), E.LzoUnsupported{})
    +mode : U32 <- lzp.need(B.be32_at(xs, 21n))
    +lo : U32 <- lzp.need(B.be32_at(xs, 25n))
    +hi : U32 <- lzp.need(B.be32_at(xs, 29n))
    +nl : U32 <- lzp.need(B.at(xs, 33n))
    +sum : U32 <- lzp.need(B.be32_at(xs, Nat.add(34n, U32.to_nat(nl))))
    s : Unit <- lzp.ensure(U32.is_eq(sum, lzp.sum(lzp.has(flags, 4096), B.take.fast(Nat.add(25n, U32.to_nat(nl)), B.drop(9n, xs)))), E.LzoBadHeaderChecksum{})
    return LzopHead{LzopHeader{version, lib, need, method, level, flags, mode, lo, hi, B.Octets.of_list(B.take.fast(U32.to_nat(nl), B.drop(34n, xs)))}, Nat.add(38n, U32.to_nat(nl))}

# an optional 32-bit checksum field at p, and the position after it
type LzopField is Data:
  LzopField{v: Maybe<&2, U32>, p: Nat}

def lzp.field(on: Bool, +xs: List<&2, U32>, +p: Nat) -> Result<&2, &2, E.LzoError, LzopField>:
  match on:
    case True{}:
      do Result<&2, &2, E.LzoError, LzopField>:
        v : U32 <- lzp.need(B.be32_at(xs, p))
        return LzopField{Some{v}, Nat.add(p, 4n)}
    case False{}:
      Done{LzopField{None{}, p}}

def lzp.field.v(f: LzopField) -> Maybe<&2, U32>:
  match f:
    case LzopField{v, p}:
      v

def lzp.field.p(f: LzopField) -> Nat:
  match f:
    case LzopField{v, p}:
      p

# a checksum field agrees with the bytes (or is absent)
def lzp.agrees(m: Maybe<&2, U32>, crc: Bool, xs: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{v}:
      U32.is_eq(v, lzp.sum(crc, xs))

def lzp.check(on: Bool, +ad: Maybe<&2, U32>, +cd: Maybe<&2, U32>, +xs: List<&2, U32>) -> Result<&2, &2, E.LzoError, Unit>:
  match on:
    case True{}:
      lzp.ensure(Bool.and(lzp.agrees(ad, False{}, xs), lzp.agrees(cd, True{}, xs)), E.LzoBadChecksum{})
    case False{}:
      Done{Unit{}}

# what a block holds: its bytes, and the input after it; or the end
type LzopStep is Data:
  LzopMore{raw: List<&2, U32>, rest: List<&2, U32>}
  LzopLast{}

def lzp.unpack.out(r: Result<&2, &2, E.LzoError, D.LzoOut>) -> Result<&2, &2, E.LzoError, List<&2, U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{D.LzoOut{acc, room}}:
      match room:
        case 0n:
          Done{B.rev(acc)}
        case 1n+r:
          Fail{E.LzoBadBlockSize{}}

# the block's bytes: stored, or an LZO1X stream of exactly dst bytes
def lzp.unpack(comp: Bool, +data: List<&2, U32>, +dst: U32) -> Result<&2, &2, E.LzoError, List<&2, U32>>:
  match comp:
    case True{}:
      lzp.unpack.out(D.dec.run_list(data, U32.to_nat(dst)))
    case False{}:
      Done{data}

def lzp.block.data(+dst: U32, +rest: List<&2, U32>, +flags: U32, +verify: Bool, +room: U32) -> Result<&2, &2, E.LzoError, LzopStep>:
  do Result<&2, &2, E.LzoError, LzopStep>:
    a : Unit <- lzp.ensure(U32.is_le(dst, 67108864), E.LzoBadBlockSize{})
    b : Unit <- lzp.ensure(U32.is_le(dst, room), E.LzoOutputTooLarge{})
    +src : U32 <- lzp.need(B.be32_at(rest, 4n))
    c : Unit <- lzp.ensure(U32.is_le(src, dst), E.LzoBadBlockSize{})
    +comp : Bool = U32.is_lt(src, dst)
    +ad : LzopField <- lzp.field(lzp.has(flags, 1), rest, 8n)
    +cd : LzopField <- lzp.field(lzp.has(flags, 256), rest, lzp.field.p(ad))
    +ac : LzopField <- lzp.field(Bool.and(comp, lzp.has(flags, 2)), rest, lzp.field.p(cd))
    +cc : LzopField <- lzp.field(Bool.and(comp, lzp.has(flags, 512)), rest, lzp.field.p(ac))
    +p : Nat = lzp.field.p(cc)
    +n : Nat = U32.to_nat(src)
    d : Unit <- lzp.ensure(Nat.is_le(Nat.add(p, n), B.len.fast(rest)), E.LzoTruncated{})
    +data : List<&2, U32> = B.take.fast(n, B.drop(p, rest))
    e : Unit <- lzp.check(Bool.and(verify, comp), lzp.field.v(ac), lzp.field.v(cc), data)
    +out : List<&2, U32> <- lzp.unpack(comp, data, dst)
    g : Unit <- lzp.check(verify, lzp.field.v(ad), lzp.field.v(cd), out)
    return LzopMore{out, B.drop(Nat.add(p, n), rest)}

# the end of the file: nothing may follow it
def lzp.end(xs: List<&2, U32>) -> Result<&2, &2, E.LzoError, LzopStep>:
  match xs:
    case Nil{}:
      Done{LzopLast{}}
    case _:
      Fail{E.LzoTrailing{}}

def lzp.block.at(last: Bool, +dst: U32, +rest: List<&2, U32>, +flags: U32, +verify: Bool, +room: U32) -> Result<&2, &2, E.LzoError, LzopStep>:
  match last:
    case True{}:
      lzp.end(B.drop(4n, rest))
    case False{}:
      lzp.block.data(dst, rest, flags, verify, room)

def lzp.block(+rest: List<&2, U32>, +flags: U32, +verify: Bool, +room: U32) -> Result<&2, &2, E.LzoError, LzopStep>:
  do Result<&2, &2, E.LzoError, LzopStep>:
    +dst : U32 <- lzp.need(B.be32_at(rest, 0n))
    lzp.block.at(U32.is_eq(dst, 0), dst, rest, flags, verify, room)

# every block reads 4 bytes or more, so fuel of the input's length + 1
# reaches the end or a failure; out: the content so far, reversed
def lzp.loop(fuel: Nat, s: Result<&2, &2, E.LzoError, LzopStep>, +flags: U32, +verify: Bool, +room: U32, out: List<&2, U32>) -> Result<&2, &2, E.LzoError, List<&2, U32>>:
  match fuel:
    case 0n:
      Fail{E.LzoTruncated{}}
    case 1n+f:
      match s:
        case Fail{e}:
          Fail{e}
        case Done{LzopLast{}}:
          Done{B.rev(out)}
        case Done{LzopMore{+raw, next}}:
          +left = U32.sub(room, U32.from_nat(B.len.fast(raw)))
          lzp.loop(f, lzp.block(next, flags, verify, left), flags, verify, left, B.rev_onto(raw, out))

# max: the most bytes the content may have; verify: check the blocks'
# checksums (the header's is always checked)
type LzopOptions is Data:
  LzopOptions{max: U32, verify: Bool}

# 64 MiB, verified
def LzopOptions.default() -> LzopOptions:
  LzopOptions{67108864, True{}}

def lzp.flags(h: LzopHeader) -> U32:
  match h:
    case LzopHeader{version, lib, need, method, level, flags, mode, lo, hi, name}:
      flags

def lzp.body(hd: LzopHead, +xs: List<&2, U32>, +max: U32, +verify: Bool) -> Result<&2, &2, E.LzoError, B.Octets>:
  match hd:
    case LzopHead{h, pos}:
      +flags = lzp.flags(h)
      +rest = B.drop(pos, xs)
      Result.map(&2, &2, E.LzoError, List<&2, U32>, B.Octets, B.Octets.of_list, lzp.loop(1n+B.len.fast(rest), lzp.block(rest, flags, verify, max), flags, verify, max, Nil{}))

def lzp.head.at(r: Result<&2, &2, E.LzoError, LzopHead>) -> Result<&2, &2, E.LzoError, LzopHeader>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{LzopHead{h, pos}}:
      Done{h}

# The public interface: reading

# the header of the lzop file src
def lzop_header(src: B.Octets) -> Result<&2, &2, E.LzoError, LzopHeader>:
  lzp.head.at(lzp.header(B.Octets.to_list(src)))

# the content of the lzop file src
def lzop_decompress(opts: LzopOptions, src: B.Octets) -> Result<&2, &2, E.LzoError, B.Octets>:
  match opts:
    case LzopOptions{+max, +verify}:
      +xs = B.Octets.to_list(src)
      do Result<&2, &2, E.LzoError, B.Octets>:
        hd : LzopHead <- lzp.header(xs)
        lzp.body(hd, xs, max, verify)

# Writing

# block_size: where the content is cut into blocks (1 to 64 MiB; 0, or
# more, means 256 KiB); the checksums to write: Adler-32 and CRC-32 of each
# block's uncompressed bytes (adler_d, crc_d) and of its compressed bytes
# (adler_c, crc_c); header_crc: CRC-32 for the header (else Adler-32); the
# method and level to record (1 to 3 are LZO1X); the file's name, mode and
# modification time; the compressor's options
type LzopWriteOptions is Data:
  LzopWriteOptions{block_size: U32, adler_d: Bool, crc_d: Bool, adler_c: Bool, crc_c: Bool, header_crc: Bool, method: U32, level: U32, name: B.Octets, mode: U32, mtime: U32, lzo: C.LzoCompressOptions}

# 256 KiB blocks, Adler-32 of the uncompressed bytes only, method 1
# (LZO1X-1), no name
def LzopWriteOptions.default() -> LzopWriteOptions:
  LzopWriteOptions{262144, True{}, False{}, False{}, False{}, False{}, 1, 1, B.Octets.empty(), 0, 0, C.LzoCompressOptions.default()}

def lzp.bit(on: Bool, v: U32) -> U32:
  match on:
    case True{}:
      v
    case False{}:
      0

def lzp.u8(v: U32) -> List<&2, U32>:
  [U32.and(v, 255)]

# the header: magic, then the fields (version 0x1030, library 0x2080, need
# 0x0940), then their checksum
def lzp.whead(opts: LzopWriteOptions) -> List<&2, U32>:
  match opts:
    case LzopWriteOptions{bs, +ad, +cd, +ac, +cc, +hc, method, level, name, mode, mtime, lzo}:
      +flags = U32.or(U32.or(lzp.bit(ad, 1), lzp.bit(ac, 2)), U32.or(U32.or(lzp.bit(cd, 256), lzp.bit(cc, 512)), lzp.bit(hc, 4096)))
      +nm = B.take.fast(255n, B.Octets.to_list(name))
      +fields = B.append.fast(B.append.fast(B.append.fast(B.be16(4144), B.append.fast(B.be16(8320), B.be16(2368))), B.append.fast(lzp.u8(method), B.append.fast(lzp.u8(level), B.be32(flags)))), B.append.fast(B.append.fast(B.be32(mode), B.append.fast(B.be32(mtime), B.be32(0))), Con{U32.from_nat(B.len.fast(nm)), nm}))
      B.append.fast(lzp.magic(), B.append.fast(fields, B.be32(lzp.sum(hc, fields))))

def lzp.wsum(on: Bool, crc: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match on:
    case True{}:
      B.be32(lzp.sum(crc, xs))
    case False{}:
      Nil{}

# a compressed block (comp) or a stored one
def lzp.wblock.pick(opts: LzopWriteOptions, comp: Bool, +c: List<&2, U32>, +raw: List<&2, U32>) -> List<&2, U32>:
  match opts:
    case LzopWriteOptions{bs, ad, cd, ac, cc, hc, method, level, name, mode, mtime, lzo}:
      match comp:
        case True{}:
          B.append.fast(B.be32(U32.from_nat(B.len.fast(raw))), B.append.fast(B.be32(U32.from_nat(B.len.fast(c))), B.append.fast(B.append.fast(lzp.wsum(ad, False{}, raw), lzp.wsum(cd, True{}, raw)), B.append.fast(B.append.fast(lzp.wsum(ac, False{}, c), lzp.wsum(cc, True{}, c)), c))))
        case False{}:
          B.append.fast(B.be32(U32.from_nat(B.len.fast(raw))), B.append.fast(B.be32(U32.from_nat(B.len.fast(raw))), B.append.fast(B.append.fast(lzp.wsum(ad, False{}, raw), lzp.wsum(cd, True{}, raw)), raw)))

def lzp.lzo(opts: LzopWriteOptions) -> C.LzoCompressOptions:
  match opts:
    case LzopWriteOptions{bs, ad, cd, ac, cc, hc, method, level, name, mode, mtime, lzo}:
      lzo

# a block: compressed when that is smaller, else stored as it is
def lzp.wblock(+opts: LzopWriteOptions, +raw: List<&2, U32>) -> List<&2, U32>:
  +c = C.enc.checked(lzp.lzo(opts), raw)
  lzp.wblock.pick(opts, Nat.is_lt(B.len.fast(c), B.len.fast(raw)), c, raw)

def lzp.bsize.pick(ok: Bool, +bs: U32) -> Nat:
  match ok:
    case True{}:
      U32.to_nat(bs)
    case False{}:
      262144n

def lzp.bsize(opts: LzopWriteOptions) -> Nat:
  match opts:
    case LzopWriteOptions{+bs, ad, cd, ac, cc, hc, method, level, name, mode, mtime, lzo}:
      lzp.bsize.pick(Bool.and(U32.is_lt(0, bs), U32.is_le(bs, 67108864)), bs)

# the first n bytes of a list, the rest, and whether there were n of them
type LzopCut is Data:
  LzopCut{head: List<&2, U32>, rest: List<&2, U32>, full: Bool}

def lzp.split.go(n: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> LzopCut:
  match n:
    case 0n:
      LzopCut{B.rev(acc), xs, True{}}
    case 1n+p:
      match xs:
        case Nil{}:
          LzopCut{B.rev(acc), Nil{}, False{}}
        case Con{h, t}:
          lzp.split.go(p, t, Con{h, acc})

# blocks of bsz bytes, while there are bsz bytes (all: the last, shorter
# one too); acc: the bytes out so far, reversed. Answers the bytes left
# over, and acc.
type LzopFlushed is Data:
  LzopFlushed{pending: List<&2, U32>, bytes: List<&2, U32>}

def lzp.cut.full(c: LzopCut) -> Bool:
  match c:
    case LzopCut{head, rest, full}:
      full

# go: this block goes out (it is full, or every block does)
def lzp.blocks(fuel: Nat, c: LzopCut, go: Bool, +all: Bool, +opts: LzopWriteOptions, +bsz: Nat, acc: List<&2, U32>) -> LzopFlushed:
  match fuel:
    case 0n:
      match c:
        case LzopCut{raw, rest, full}:
          LzopFlushed{B.append.fast(raw, rest), acc}
    case 1n+f:
      match c go:
        case LzopCut{Nil{}, rest, full} _:
          LzopFlushed{Nil{}, acc}
        case LzopCut{Con{h, t}, rest, full} True{}:
          +nc = lzp.split.go(bsz, rest, Nil{})
          lzp.blocks(f, nc, Bool.or(lzp.cut.full(nc), all), all, opts, bsz, B.rev_onto(lzp.wblock(opts, Con{h, t}), acc))
        case LzopCut{Con{h, t}, rest, full} False{}:
          LzopFlushed{Con{h, B.append.fast(t, rest)}, acc}

def lzp.flushed.bytes(r: LzopFlushed) -> List<&2, U32>:
  match r:
    case LzopFlushed{pending, bytes}:
      B.rev(bytes)

# The public interface: writing

# an lzop file holding o
def lzop_compress(+opts: LzopWriteOptions, o: B.Octets) -> B.Octets:
  +xs = B.Octets.to_list(o)
  +bsz = lzp.bsize(opts)
  +body = lzp.flushed.bytes(lzp.blocks(1n+B.len.fast(xs), lzp.split.go(bsz, xs, Nil{}), True{}, True{}, opts, bsz, Nil{}))
  B.Octets.of_list(B.append.fast(lzp.whead(opts), B.append.fast(body, [0, 0, 0, 0])))

# Streaming: start, then feed the content in pieces, then finish; each
# answers the file's next bytes. Blocks are independent, and their
# checksums are per block, so the writer keeps only the bytes not yet in a
# block.

type LzopWriter is Data:
  LzopWriter{opts: LzopWriteOptions, pending: List<&2, U32>}

type LzopWritten is Data:
  LzopWritten{writer: LzopWriter, bytes: B.Octets}

def lzop_start(+opts: LzopWriteOptions) -> LzopWritten:
  LzopWritten{LzopWriter{opts, Nil{}}, B.Octets.of_list(lzp.whead(opts))}

def lzp.fed(r: LzopFlushed, opts: LzopWriteOptions) -> LzopWritten:
  match r:
    case LzopFlushed{pending, bytes}:
      LzopWritten{LzopWriter{opts, pending}, B.Octets.of_list(B.rev(bytes))}

def lzop_feed(w: LzopWriter, o: B.Octets) -> LzopWritten:
  match w:
    case LzopWriter{+opts, pending}:
      +p = B.append.fast(pending, B.Octets.to_list(o))
      +bsz = lzp.bsize(opts)
      +c = lzp.split.go(bsz, p, Nil{})
      lzp.fed(lzp.blocks(1n+B.len.fast(p), c, lzp.cut.full(c), False{}, opts, bsz, Nil{}), opts)

# the last block and the end of the file
def lzop_finish(w: LzopWriter) -> B.Octets:
  match w:
    case LzopWriter{+opts, +pending}:
      +bsz = lzp.bsize(opts)
      B.Octets.of_list(B.append.fast(lzp.flushed.bytes(lzp.blocks(1n+B.len.fast(pending), lzp.split.go(bsz, pending, Nil{}), True{}, True{}, opts, bsz, Nil{})), [0, 0, 0, 0]))

def lzp.feed_all(ps: List<&2, B.Octets>, r: LzopWritten, acc: B.Octets) -> B.Octets:
  match ps:
    case Nil{}:
      match r:
        case LzopWritten{w, bytes}:
          B.Octets.append(B.Octets.append(acc, bytes), lzop_finish(w))
    case Con{p, t}:
      match r:
        case LzopWritten{w, bytes}:
          lzp.feed_all(t, lzop_feed(w, p), B.Octets.append(acc, bytes))

# the file a writer gives for content fed in these pieces
def lzop_stream(opts: LzopWriteOptions, ps: List<&2, B.Octets>) -> B.Octets:
  lzp.feed_all(ps, lzop_start(opts), B.Octets.empty())
