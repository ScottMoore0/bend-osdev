# bend-osdev-bzip2: streams (Tsai, "BZip2 Format Specification", section 2;
# the bzip2 manual, version 1.0.8, on concatenated streams and block sizes).
#
# A stream is "BZh", a block size digit 1 to 9 (blocks of at most 100,000
# times that many bytes before the BWT), its blocks, and its end: the magic
# 0x177245385090 and the combined CRC, then 0 bits to a whole byte. Each
# block's CRC is CRC-32/BZIP2 (polynomial 0x04C11DB7, most significant bit
# first, initial value and final XOR 0xFFFFFFFF) of its bytes; the combined
# CRC is, block by block, the last one rotated left by one bit, XOR the
# block's CRC.
#
# A file may hold several streams back to back; its content is theirs in
# order. What follows the last stream, if it does not start a stream, is
# ignored (as the bzip2 tool and Python's bz2 module do), unless the options
# say to refuse it. An input that ends inside a stream header ("BZ") is cut
# short, wherever it is.
import Base
import ../bytes/bytes.bend as B
import ../crc/crc.bend as C
import ../crc/table.bend as T
import ./list.bend as L
import ./error.bend as E
import ./bits.bend as K
import ./block.bend as D

# The decoding options: the most output allowed, and whether bytes after the
# last stream that do not start a stream are ignored (True) or refused
# (Bzip2TrailingData)
type Bzip2Options is Data:
  Bzip2Options{max: U32, ignore_trailing: Bool}

# 64 MiB at most; trailing bytes ignored
def Bzip2Options.default() -> Bzip2Options:
  Bzip2Options{67108864, True{}}

def Bzip2Options.max(o: Bzip2Options) -> U32:
  match o:
    case Bzip2Options{max, t}:
      max

# CRC-32/BZIP2, in the crc package's parameter model
def bzip2_crc.spec() -> C.Crc32Spec:
  C.Crc32Spec{32n, 79764919, 4294967295, False{}, 4294967295}

# a block's CRC
def bzip2_crc(o: B.Octets) -> U32:
  T.Crc32Spec.compute_fast(bzip2_crc.spec(), o)

# the combined CRC after one more block
def bzip2_combine(+c: U32, b: U32) -> U32:
  U32.xor(U32.or(U32.shl(c), U32.shrn(c, 31n)), b)

# The stream header: the block size, in bytes

type Bzip2Head is Data:
  Bzip2Head{bmax: Nat, rest: List<&2, U32>}

def hdr.digit(ok: Bool, +d: U32, t: List<&2, U32>) -> Result<&2, &2, E.Bzip2Error, Bzip2Head>:
  match ok:
    case True{}:
      Done{Bzip2Head{Nat.mul(U32.to_nat(U32.sub(d, 48)), 100000n), t}}
    case False{}:
      Fail{E.Bzip2BadBlockSize{}}

def hdr.level(xs: List<&2, U32>) -> Result<&2, &2, E.Bzip2Error, Bzip2Head>:
  match xs:
    case Nil{}:
      Fail{E.Bzip2Truncated{}}
    case Con{h, t}:
      +d = B.byte(h)
      hdr.digit(Bool.and(U32.is_le(49, d), U32.is_le(d, 57)), d, t)

# the magic bytes want, then the level digit (ok: whether the byte before
# matched)
def hdr.magic(want: List<&2, U32>, ok: Bool, xs: List<&2, U32>) -> Result<&2, &2, E.Bzip2Error, Bzip2Head>:
  match want:
    case Nil{}:
      match ok:
        case True{}:
          hdr.level(xs)
        case False{}:
          Fail{E.Bzip2BadMagic{}}
    case Con{w, wt}:
      match ok:
        case False{}:
          Fail{E.Bzip2BadMagic{}}
        case True{}:
          match xs:
            case Nil{}:
              Fail{E.Bzip2Truncated{}}
            case Con{h, t}:
              hdr.magic(wt, U32.is_eq(B.byte(h), w), t)

# "BZh" and the block size digit, at the front of xs
def stream_header(xs: List<&2, U32>) -> Result<&2, &2, E.Bzip2Error, Bzip2Head>:
  hdr.magic([66, 90, 104], True{}, xs)

# The decoder: expecting a stream header (first: none read yet), or inside a
# stream; out: the blocks' bytes so far, reversed; room: how many more bytes
# the output may take

type Bzip2Dec is Data:
  Bzip2DecHead{rest: List<&2, U32>, first: Bool, room: Nat, out: List<&2, B.Octets>}
  Bzip2DecBlock{r: K.Bzip2Bits, bmax: Nat, comb: U32, room: Nat, out: List<&2, B.Octets>}
  Bzip2DecDone{out: List<&2, B.Octets>}
  Bzip2DecBad{e: E.Bzip2Error}

def dec.data(ok: Bool, r: K.Bzip2Bits, +bmax: Nat, +comb: U32, +crc: U32, +o: B.Octets, +n: Nat, room: Nat, out: List<&2, B.Octets>) -> Bzip2Dec:
  match ok:
    case True{}:
      Bzip2DecBlock{r, bmax, bzip2_combine(comb, crc), Nat.sub(room, n), Con{o, out}}
    case False{}:
      Bzip2DecBad{E.Bzip2BadBlockCrc{}}

def dec.data.o(+o: B.Octets, r: K.Bzip2Bits, +bmax: Nat, +comb: U32, +crc: U32, +n: Nat, room: Nat, out: List<&2, B.Octets>) -> Bzip2Dec:
  dec.data(U32.is_eq(bzip2_crc(o), crc), r, bmax, comb, crc, o, n, room, out)

def dec.end(ok: Bool, r: K.Bzip2Bits, +room: Nat, out: List<&2, B.Octets>) -> Bzip2Dec:
  match ok:
    case True{}:
      Bzip2DecHead{K.bits.rest(K.bits.align(r)), False{}, room, out}
    case False{}:
      Bzip2DecBad{E.Bzip2BadStreamCrc{}}

def dec.block(b: D.Bzip2Blk, +bmax: Nat, +comb: U32, +room: Nat, out: List<&2, B.Octets>) -> Bzip2Dec:
  match b:
    case D.Bzip2BlkData{r, crc, +bytes}:
      dec.data.o(B.Octets.of_list(bytes), r, bmax, comb, crc, L.bz.len(bytes), room, out)
    case D.Bzip2BlkEnd{r, crc}:
      dec.end(U32.is_eq(crc, comb), r, room, out)
    case D.Bzip2BlkBad{e}:
      Bzip2DecBad{e}

def dec.trail(ignore: Bool, out: List<&2, B.Octets>) -> Bzip2Dec:
  match ignore:
    case True{}:
      Bzip2DecDone{out}
    case False{}:
      Bzip2DecBad{E.Bzip2TrailingData{}}

def dec.head.err(first: Bool, +ignore: Bool, e: E.Bzip2Error, out: List<&2, B.Octets>) -> Bzip2Dec:
  match first:
    case True{}:
      Bzip2DecBad{e}
    case False{}:
      match e:
        case E.Bzip2Truncated{}:
          Bzip2DecBad{E.Bzip2Truncated{}}
        case _:
          dec.trail(ignore, out)

def dec.head(h: Result<&2, &2, E.Bzip2Error, Bzip2Head>, first: Bool, +ignore: Bool, room: Nat, out: List<&2, B.Octets>) -> Bzip2Dec:
  match h:
    case Done{hd}:
      match hd:
        case Bzip2Head{bmax, rest}:
          Bzip2DecBlock{K.bits.start(rest), bmax, 0, room, out}
    case Fail{e}:
      dec.head.err(first, ignore, e, out)

# a stream header, if there is anything left
def dec.at(rest: List<&2, U32>, first: Bool, +ignore: Bool, room: Nat, out: List<&2, B.Octets>) -> Bzip2Dec:
  match rest:
    case Nil{}:
      match first:
        case True{}:
          Bzip2DecBad{E.Bzip2Truncated{}}
        case False{}:
          Bzip2DecDone{out}
    case Con{h, t}:
      dec.head(stream_header(Con{h, t}), first, ignore, room, out)

# every step reads at least one byte, so fuel of the input's length (and a
# little) reaches the end
def dec.go(fuel: Nat, st: Bzip2Dec, +ignore: Bool) -> Bzip2Dec:
  match fuel:
    case 0n:
      Bzip2DecBad{E.Bzip2Truncated{}}
    case 1n+f:
      match st:
        case Bzip2DecHead{rest, first, room, out}:
          dec.go(f, dec.at(rest, first, ignore, room, out), ignore)
        case Bzip2DecBlock{r, +bmax, +comb, +room, out}:
          dec.go(f, dec.block(D.block_read(r, bmax, room), bmax, comb, room, out), ignore)
        case Bzip2DecDone{out}:
          Bzip2DecDone{out}
        case Bzip2DecBad{e}:
          Bzip2DecBad{e}

def dec.result(st: Bzip2Dec) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  match st:
    case Bzip2DecDone{out}:
      Done{B.Octets.concat(List.reverse(&2, B.Octets, out))}
    case Bzip2DecBad{e}:
      Fail{e}
    case _:
      Fail{E.Bzip2Truncated{}}

# The final guard: an output longer than the maximum is refused (the decoder
# already stops at the maximum; this makes the bound plain)
def stm.bound.pick(ok: Bool, o: B.Octets) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  match ok:
    case True{}:
      Done{o}
    case False{}:
      Fail{E.Bzip2OutputTooLarge{}}

def stm.bound(+max: U32, r: Result<&2, &2, E.Bzip2Error, B.Octets>) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+o}:
      stm.bound.pick(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o)

def stm.run(+xs: List<&2, U32>, +max: U32, +ignore: Bool) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  stm.bound(max, dec.result(dec.go(1n+1n+L.bz.len(xs), Bzip2DecHead{xs, True{}, U32.to_nat(max), Nil{}}, ignore)))

# the content of the bzip2 file src (one stream or more), with these options
def stream_decode(opts: Bzip2Options, src: B.Octets) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  match opts:
    case Bzip2Options{+max, ignore}:
      stm.run(B.Octets.to_list(src), max, ignore)
