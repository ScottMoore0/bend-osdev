# bend-osdev-lz4: LZ4 decompression, from the LZ4 project's specifications
# (lz4_Frame_format.md and lz4_Block_format.md).
#
# This file is the main concern: decompressing an LZ4 stream, as the lz4 tool
# writes it. A stream is one frame or more, back to back: LZ4 frames (see
# frame.bend, whose blocks are in block.bend) and skippable frames (a magic
# number 0x184D2A50 to 0x184D2A5F, a 32-bit size, and that many bytes, all
# ignored). Its content is the content of its LZ4 frames, in order.
import Base
import ../bytes/bytes.bend as B
import ./block.bend as K
import ./frame.bend as F

# out: the content so far, reversed
type Lz4Stream is Data:
  Lz4Go{out: List<&2, U32>, room: U32, rest: List<&2, U32>}
  Lz4Stop{out: List<&2, U32>}
  Lz4Err{e: K.Lz4Error}

def lz4.got(r: Result<&2, &2, K.Lz4Error, F.Lz4Got>, out: List<&2, U32>) -> Lz4Stream:
  match r:
    case Fail{e}:
      Lz4Err{e}
    case Done{F.Lz4Got{o, room, rest}}:
      Lz4Go{B.rev_onto(o, out), room, rest}

def lz4.skip.fits(ok: Bool, +k: Nat, out: List<&2, U32>, room: U32, +rest: List<&2, U32>) -> Lz4Stream:
  match ok:
    case True{}:
      Lz4Go{out, room, B.drop(k, rest)}
    case False{}:
      Lz4Err{K.Lz4Truncated{}}

# a skippable frame: its size, then that many bytes
def lz4.skip(m: Maybe<&2, U32>, out: List<&2, U32>, room: U32, +rest: List<&2, U32>) -> Lz4Stream:
  match m:
    case None{}:
      Lz4Err{K.Lz4Truncated{}}
    case Some{n}:
      +k = Nat.add(8n, U32.to_nat(n))
      lz4.skip.fits(Nat.is_le(k, B.len.fast(rest)), k, out, room, rest)

def lz4.next.skip(skip: Bool, out: List<&2, U32>, room: U32, +rest: List<&2, U32>) -> Lz4Stream:
  match skip:
    case True{}:
      lz4.skip(B.le32_at(rest, 4n), out, room, rest)
    case False{}:
      Lz4Err{K.Lz4BadMagic{}}

def lz4.next.pick(lz4: Bool, +skip: Bool, +verify: Bool, +dict: List<&2, U32>, out: List<&2, U32>, +room: U32, +rest: List<&2, U32>) -> Lz4Stream:
  match lz4:
    case True{}:
      lz4.got(F.frm.frame(rest, verify, dict, room), out)
    case False{}:
      lz4.next.skip(skip, out, room, rest)

def lz4.next.at(m: Maybe<&2, U32>, +verify: Bool, +dict: List<&2, U32>, out: List<&2, U32>, +room: U32, +rest: List<&2, U32>) -> Lz4Stream:
  match m:
    case None{}:
      Lz4Err{K.Lz4Truncated{}}
    case Some{+magic}:
      lz4.next.pick(U32.is_eq(magic, 407708164), U32.is_eq(U32.and(magic, 4294967280), 407710288), verify, dict, out, room, rest)

# the next frame of a stream, if there is one
def lz4.next(rest: List<&2, U32>, +verify: Bool, +dict: List<&2, U32>, out: List<&2, U32>, room: U32) -> Lz4Stream:
  match rest:
    case Nil{}:
      Lz4Stop{out}
    case Con{h, t}:
      +xs = {Con{h, t} : List<&2, U32>}
      lz4.next.at(B.le32_at(xs, 0n), verify, dict, out, room, xs)

# every frame reads 8 bytes or more, so fuel of the input's length + 1 always
# reaches the end of the input or a failure
def lz4.stream(fuel: Nat, s: Lz4Stream, +verify: Bool, +dict: List<&2, U32>) -> Lz4Stream:
  match fuel:
    case 0n:
      Lz4Err{K.Lz4Truncated{}}
    case 1n+f:
      match s:
        case Lz4Go{out, room, rest}:
          lz4.stream(f, lz4.next(rest, verify, dict, out, room), verify, dict)
        case Lz4Stop{out}:
          Lz4Stop{out}
        case Lz4Err{e}:
          Lz4Err{e}

def lz4.result(s: Lz4Stream) -> Result<&2, &2, K.Lz4Error, B.Octets>:
  match s:
    case Lz4Stop{out}:
      Done{B.Octets.of_list(B.rev(out))}
    case Lz4Err{e}:
      Fail{e}
    case Lz4Go{out, room, rest}:
      Fail{K.Lz4Truncated{}}

def lz4.start(xs: List<&2, U32>, max: U32, +verify: Bool, +dict: List<&2, U32>) -> Result<&2, &2, K.Lz4Error, B.Octets>:
  match xs:
    case Nil{}:
      Fail{K.Lz4Truncated{}}
    case Con{h, t}:
      +s = {Con{h, t} : List<&2, U32>}
      lz4.result(lz4.stream(Nat.add(B.len.fast(s), 1n), Lz4Go{Nil{}, max, s}, verify, dict))

# The public interface

# the content of the stream src (one frame or more), with these options
def decompress_with(opts: F.Lz4Options, src: B.Octets) -> Result<&2, &2, K.Lz4Error, B.Octets>:
  match opts:
    case F.Lz4Options{max, verify, dict}:
      lz4.start(B.Octets.to_list(src), max, verify, B.Octets.to_list(dict))

# the content of the stream src, with the default options (64 MiB at most,
# checksums verified, no dictionary)
def decompress(src: B.Octets) -> Result<&2, &2, K.Lz4Error, B.Octets>:
  decompress_with(F.Lz4Options.default(), src)
