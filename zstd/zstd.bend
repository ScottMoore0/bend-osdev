# bend-osdev-zstd: Zstandard decompression (RFC 8878, "Zstandard Compression
# and the 'application/zstd' Media Type", Y. Collet and M. Kucherawy,
# February 2021).
#
# This file is the main concern: decompressing a stream of frames, given
# whole or in pieces, with options or the defaults. The frames are
# frame.bend's, their blocks block.bend's (literals.bend, sequences.bend,
# huffman.bend, fse.bend, bits.bend), the content checksum xxh64.bend's,
# dictionaries dict.bend's; compression is in compress.bend.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./dict.bend as D
import ./block.bend as K
import ./frame.bend as F

# limit: the most bytes to produce (or none); verify: whether to check
# content checksums; dict: the dictionary every frame starts with (raw
# content, or a formatted dictionary; empty: none); max_window: the largest
# window size accepted
type ZstdOptions is Data:
  ZstdOptions{limit: F.ZstdLimit, verify: Bool, dict: B.Octets, max_window: U32}

# 64 MiB at most, checksums verified, no dictionary, windows up to 128 MiB
def ZstdOptions.default() -> ZstdOptions:
  ZstdOptions{F.ZstdLimit{67108864}, True{}, B.Octets.empty(), 134217728}

# the same without a limit on the output, for trusted input
def ZstdOptions.unlimited() -> ZstdOptions:
  ZstdOptions{F.ZstdNoLimit{}, True{}, B.Octets.empty(), 134217728}

def zstd.room(l: F.ZstdLimit) -> F.ZsRoom:
  match l:
    case F.ZstdNoLimit{}:
      F.ZsRoomAny{}
    case F.ZstdLimit{max}:
      F.ZsRoomN{U32.to_nat(max)}

def zstd.start(r: Result<&2, &2, E.ZstdError, D.ZstdDict>, verify: Bool, max_window: U32, room: F.ZsRoom) -> F.ZstdDecoder:
  match r:
    case Fail{e}:
      F.ZstdDecoder{F.ZsPhBad{e}, F.frm.none(), Nil{}, room, F.ZsCfg{D.ZstdDict.none(), 0n, verify, max_window}, K.ZstdWin.new(0n)}
    case Done{+d}:
      F.ZstdFrame.new(F.ZsCfg{d, B.len.fast(D.ZstdDict.content(d)), verify, max_window}, room)

# The public interface: streaming

# a decoder at the start of a stream (a malformed dictionary makes every
# later step fail with ZstdBadDictionary)
def Zstd.start(opts: ZstdOptions) -> F.ZstdDecoder:
  match opts:
    case ZstdOptions{limit, verify, dict, max_window}:
      zstd.start(D.ZstdDict.parse(dict), verify, max_window, zstd.room(limit))

# the decoder after the next piece of input
def Zstd.feed(d: F.ZstdDecoder, o: B.Octets) -> F.ZstdDecoder:
  F.ZstdFrame.run(B.Octets.to_list(o), d)

# the output decoded so far and not yet taken, and the decoder without it
type ZstdPiece is Type:
  ZstdPiece{dec: F.ZstdDecoder, out: B.Octets}

def zstd.piece(t: F.ZstdTaken) -> ZstdPiece:
  match t:
    case F.ZstdTaken{dec, bytes}:
      ZstdPiece{dec, B.Octets.of_list(bytes)}

def Zstd.take(d: F.ZstdDecoder) -> ZstdPiece:
  zstd.piece(F.ZstdFrame.take(d))

def zstd.fin(r: Result<&2, &2, E.ZstdError, List<&2, U32>>) -> Result<&2, &2, E.ZstdError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{xs}:
      Done{B.Octets.of_list(xs)}

# the output not yet taken, if the input ended between frames; else the
# failure (ZstdTruncated if it ended inside a frame)
def Zstd.finish(d: F.ZstdDecoder) -> Result<&2, &2, E.ZstdError, B.Octets>:
  zstd.fin(F.ZstdFrame.finish(d))

# The public interface: one call

def zstd.fits(ok: Bool, o: B.Octets) -> Result<&2, &2, E.ZstdError, B.Octets>:
  match ok:
    case True{}:
      Done{o}
    case False{}:
      Fail{E.ZstdOutputTooLarge{}}

# the result, held to the limit (the decoder stops at the limit as it
# goes; this makes the bound plain, for LAWS.bend)
def zstd.guard(l: F.ZstdLimit, r: Result<&2, &2, E.ZstdError, B.Octets>) -> Result<&2, &2, E.ZstdError, B.Octets>:
  match l:
    case F.ZstdNoLimit{}:
      r
    case F.ZstdLimit{max}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{+o}:
          zstd.fits(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o)

def zstd.limit(opts: ZstdOptions) -> F.ZstdLimit:
  match opts:
    case ZstdOptions{limit, verify, dict, max_window}:
      limit

# the content of the stream src (zero or more frames, Zstandard and
# skippable), with these options
def decompress_with(+opts: ZstdOptions, src: B.Octets) -> Result<&2, &2, E.ZstdError, B.Octets>:
  zstd.guard(zstd.limit(opts), Zstd.finish(Zstd.feed(Zstd.start(opts), src)))

# the same with ZstdOptions.default()
def decompress(src: B.Octets) -> Result<&2, &2, E.ZstdError, B.Octets>:
  decompress_with(ZstdOptions.default(), src)
