# bend-osdev-deflate: the zlib format (RFC 1950): a two-byte header, a raw
# DEFLATE stream, and the Adler-32 of the data, most significant byte first.
#
# RFC 1950, 2.2: CMF holds CM (8: deflate) and CINFO ("the base-2 logarithm
# of the LZ77 window size, minus eight"; "Values of CINFO above 7 are not
# allowed"); FLG holds FCHECK ("CMF and FLG, when viewed as a 16-bit unsigned
# integer stored in MSB order (CMF*256 + FLG), is a multiple of 31"), FDICT
# (a preset dictionary, named by its Adler-32, DICTID) and FLEVEL (0 fastest
# to 3 maximum compression; "not needed for decompression"). 2.3: "A
# compliant decompressor must check CMF, FLG, and ADLER32, and provide an
# error indication if any of these have incorrect values."
#
# What the RFC leaves to the decoder, decided as zlib 1.3 decides it
# (Python's zlib module, as a black box): FCHECK is checked first, then CM,
# then CINFO; a window size smaller than 32K is not enforced; FDICT without
# a matching dictionary is refused; bytes after ADLER32 are ignored (or
# refused, DeflateTrailingData, with InflateOptions' ignore False).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./eq.bend as Q
import ./window.bend as W
import ./adler32.bend as A
import ./inflate.bend as I
import ./deflate.bend as D

# The writer

# FLEVEL (2.2): which kind of compressor wrote the stream

type DflFlevel is Data:
  DflFlevelFastest{}
  DflFlevelFast{}
  DflFlevelDefault{}
  DflFlevelMax{}

type ZlibOptions is Data:
  ZlibOptions{deflate: D.DeflateOptions, flevel: DflFlevel}

def zl.flevel.at(fastest: Bool, fast: Bool, dflt: Bool) -> DflFlevel:
  match fastest:
    case True{}:
      DflFlevelFastest{}
    case False{}:
      match fast:
        case True{}:
          DflFlevelFast{}
        case False{}:
          match dflt:
            case True{}:
              DflFlevelDefault{}
            case False{}:
              DflFlevelMax{}

def zl.flevel(+l: U32) -> DflFlevel:
  zl.flevel.at(U32.is_le(l, 1), U32.is_le(l, 5), U32.is_eq(l, 6))

# level l (0 to 9), its FLEVEL: 0 and 1 fastest, 2 to 5 fast, 6 default,
# 7 to 9 maximum
def ZlibOptions.level(+l: U32) -> ZlibOptions:
  ZlibOptions{D.DeflateOptions.level(l), zl.flevel(l)}

def ZlibOptions.default() -> ZlibOptions:
  ZlibOptions.level(6)

# CMF 0x78 (CM 8, CINFO 7: a 32K window), then FLG: FLEVEL in its top two
# bits, FDICT 0, FCHECK making CMF * 256 + FLG a multiple of 31
def zl.header(f: DflFlevel) -> List<&2, U32>:
  match f:
    case DflFlevelFastest{}:
      [120, 1]
    case DflFlevelFast{}:
      [120, 94]
    case DflFlevelDefault{}:
      [120, 156]
    case DflFlevelMax{}:
      [120, 218]

# o in the zlib format
def zlib_compress_with(zo: ZlibOptions, +o: B.Octets) -> B.Octets:
  match zo:
    case ZlibOptions{dopts, f}:
      B.Octets.append(B.Octets.of_list(zl.header(f)), B.Octets.append(D.deflate_with(dopts, o), B.Octets.be32(A.adler32(o))))

def zlib_compress(+o: B.Octets) -> B.Octets:
  zlib_compress_with(ZlibOptions.default(), o)

# The reader

def zl.none(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

def zl.check.rest(none: Bool, +out: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match none:
    case True{}:
      Done{out}
    case False{}:
      Fail{E.DeflateTrailingData{}}

def zl.check(ok: Bool, +out: B.Octets, +rest: B.Octets, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match ok:
    case True{}:
      match ignore:
        case True{}:
          Done{out}
        case False{}:
          zl.check.rest(zl.none(Nat.sub(B.Octets.len(rest), 4n)), out)
    case False{}:
      Fail{E.DeflateZlibBadChecksum{}}

# the trailer: ADLER32 (a: the data's), then nothing (unless ignored); the
# answer is out
def zl.trail(m: Maybe<&2, U32>, +a: U32, +out: B.Octets, +rest: B.Octets, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match m:
    case None{}:
      Fail{E.DeflateTruncated{}}
    case Some{v}:
      zl.check(Q.eq.u32(v, a), out, rest, ignore)

def zl.trailer(m: Maybe<&2, U32>, +out: B.Octets, +rest: B.Octets, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  zl.trail(m, A.adler32(out), out, rest, ignore)

def zl.guard(ok: Bool, +out: B.Octets, +rest: B.Octets, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match ok:
    case True{}:
      zl.trailer(B.Octets.be32_at(rest, 0n), out, rest, ignore)
    case False{}:
      Fail{E.DeflateOutputTooLarge{}}

def zl.body(r: Result<&2, &2, E.DeflateError, I.DflOutRest>, +max: U32, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{I.DflOutRest{+out, rest}}:
      zl.guard(Nat.is_le(B.Octets.len(out), U32.to_nat(max)), out, B.Octets.of_list(rest), ignore)

def zl.inflate(+win: W.DflWin, +max: U32, ignore: Bool, xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, B.Octets>:
  zl.body(I.inf.run.out(win, U32.to_nat(max), xs), max, ignore)

# The header: the window the stream starts after, and the bytes after the
# header

type DflZlibHead is Data:
  DflZlibHead{win: W.DflWin, rest: List<&2, U32>}

def zl.dict.match(ok: Bool, +dict: B.Octets, xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflZlibHead>:
  match ok:
    case True{}:
      Done{DflZlibHead{W.win.of(B.Octets.to_list(dict)), xs}}
    case False{}:
      Fail{E.DeflateZlibBadDictId{}}

def zl.dict.have(none: Bool, +id: U32, +dict: B.Octets, xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflZlibHead>:
  match none:
    case True{}:
      Fail{E.DeflateZlibNeedDict{}}
    case False{}:
      zl.dict.match(Q.eq.u32(id, A.adler32(dict)), dict, xs)

# FDICT: the next four bytes are DICTID
def zl.dict(m: Maybe<&2, U32>, +dict: B.Octets, xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflZlibHead>:
  match m:
    case None{}:
      Fail{E.DeflateTruncated{}}
    case Some{id}:
      zl.dict.have(zl.none(B.Octets.len(dict)), id, dict, B.drop(4n, xs))

def zl.fdict(fdict: Bool, +dict: B.Octets, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflZlibHead>:
  match fdict:
    case True{}:
      zl.dict(B.be32_at(xs, 0n), dict, xs)
    case False{}:
      Done{DflZlibHead{W.win.empty(), xs}}

def zl.cinfo(ok: Bool, +flg: U32, +dict: B.Octets, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflZlibHead>:
  match ok:
    case True{}:
      zl.fdict(U32.is_eq(U32.and(flg, 32), 32), dict, xs)
    case False{}:
      Fail{E.DeflateZlibBadWindow{}}

def zl.cm(ok: Bool, +cmf: U32, +flg: U32, +dict: B.Octets, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflZlibHead>:
  match ok:
    case True{}:
      zl.cinfo(U32.is_le(U32.shrn(cmf, 4n), 7), flg, dict, xs)
    case False{}:
      Fail{E.DeflateZlibBadMethod{}}

def zl.fcheck(ok: Bool, +cmf: U32, +flg: U32, +dict: B.Octets, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflZlibHead>:
  match ok:
    case True{}:
      zl.cm(U32.is_eq(U32.and(cmf, 15), 8), cmf, flg, dict, xs)
    case False{}:
      Fail{E.DeflateZlibBadHeader{}}

# CMF, FLG (and DICTID) at the start of xs, checked (2.2, 2.3); a
# dictionary is used only if FDICT asks for one
def zl.head(xs: List<&2, U32>, +dict: B.Octets) -> Result<&2, &2, E.DeflateError, DflZlibHead>:
  match xs:
    case Con{+cmf, Con{+flg, rest}}:
      zl.fcheck(U32.is_eq(U32.mod(U32.add(U32.shln(cmf, 8n), flg), 31), 0), cmf, flg, dict, rest)
    case _:
      Fail{E.DeflateTruncated{}}

def zl.after(r: Result<&2, &2, E.DeflateError, DflZlibHead>, +max: U32, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{DflZlibHead{win, rest}}:
      zl.inflate(win, max, ignore, rest)

def zl.decode(xs: List<&2, U32>, opts: I.InflateOptions) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match opts:
    case I.InflateOptions{+max, dict, ignore}:
      zl.after(zl.head(xs, dict), max, ignore)

# the data of the zlib stream src (src must hold exactly one stream; bytes
# after it are ignored or refused, as opts says)
def zlib_decompress_with(opts: I.InflateOptions, src: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  zl.decode(B.Octets.to_list(src), opts)

def zlib_decompress(src: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  zlib_decompress_with(I.InflateOptions.default(), src)

# The streaming writer: the header with the first bytes, ADLER32 at the end

type ZlibWriter is Data:
  ZlibWriter{d: D.Deflater, adler: A.Adler32, head: List<&2, U32>}

type DflZlibWritten is Data:
  DflZlibWritten{writer: ZlibWriter, bytes: B.Octets}

def zlib_start(zo: ZlibOptions) -> ZlibWriter:
  match zo:
    case ZlibOptions{dopts, f}:
      ZlibWriter{D.deflate_start(dopts), A.Adler32.start(), zl.header(f)}

def zl.fed(r: D.DflDeflated, a: A.Adler32, head: List<&2, U32>) -> DflZlibWritten:
  match r:
    case D.DflDeflated{d, bytes}:
      DflZlibWritten{ZlibWriter{d, a, Nil{}}, B.Octets.append(B.Octets.of_list(head), bytes)}

# more data: answers the bytes it completes
def zlib_feed(w: ZlibWriter, +o: B.Octets) -> DflZlibWritten:
  match w:
    case ZlibWriter{d, a, head}:
      zl.fed(D.deflate_feed(d, o), A.Adler32.update(a, o), head)

# the end of the data: the rest of the stream
def zlib_finish(w: ZlibWriter) -> B.Octets:
  match w:
    case ZlibWriter{d, a, head}:
      B.Octets.append(B.Octets.of_list(head), B.Octets.append(D.deflate_finish(d), B.Octets.be32(A.Adler32.finish(a))))

# The streaming reader: the header (held until it is whole), then the
# inflater, the data's Adler-32 kept as it comes out

type ZlibInflater is Data:
  ZlibInHead{buf: List<&2, U32>, opts: I.InflateOptions}
  ZlibInBody{inf: I.Inflater, adler: A.Adler32}
  ZlibInBad{e: E.DeflateError}

type DflZlibFed is Data:
  DflZlibFed{inflater: ZlibInflater, out: B.Octets}

def zlib_inflate_start(opts: I.InflateOptions) -> ZlibInflater:
  ZlibInHead{Nil{}, opts}

def zl.in.fed(r: I.DflFed, a: A.Adler32) -> DflZlibFed:
  match r:
    case I.DflFed{i, +out}:
      DflZlibFed{ZlibInBody{i, A.Adler32.update(a, out)}, out}

def zl.in.wait(e: E.DeflateError, +buf: List<&2, U32>, +opts: I.InflateOptions) -> DflZlibFed:
  match e:
    case E.DeflateTruncated{}:
      DflZlibFed{ZlibInHead{buf, opts}, B.Octets.empty()}
    case _:
      DflZlibFed{ZlibInBad{e}, B.Octets.empty()}

def zl.in.head(r: Result<&2, &2, E.DeflateError, DflZlibHead>, +buf: List<&2, U32>, +opts: I.InflateOptions) -> DflZlibFed:
  match r:
    case Fail{e}:
      zl.in.wait(e, buf, opts)
    case Done{DflZlibHead{win, rest}}:
      match opts:
        case I.InflateOptions{+max, dict, ignore}:
          zl.in.fed(I.inflate_feed(I.inf.start(win, U32.to_nat(max), max, ignore), B.Octets.of_list(rest)), A.Adler32.start())

# more of the stream: answers the data it completes
def zlib_inflate_feed(z: ZlibInflater, o: B.Octets) -> DflZlibFed:
  match z:
    case ZlibInHead{buf, +opts}:
      +all = B.append.fast(buf, B.Octets.to_list(o))
      zl.in.head(zl.head(all, I.InflateOptions.dict(opts)), all, opts)
    case ZlibInBody{i, a}:
      zl.in.fed(I.inflate_feed(i, o), a)
    case ZlibInBad{e}:
      DflZlibFed{ZlibInBad{e}, B.Octets.empty()}

def zl.in.end(r: Result<&2, &2, E.DeflateError, I.DflInflated>, a: A.Adler32, +ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{I.DflInflated{+out, +rest}}:
      zl.trail(B.Octets.be32_at(rest, 0n), A.Adler32.finish(A.Adler32.update(a, out)), out, rest, ignore)

def zl.in.ignore(i: I.Inflater) -> Bool:
  match i:
    case I.Inflater{d, max, ignore}:
      ignore

def zl.in.after(r: Result<&2, &2, E.DeflateError, DflZlibHead>) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{h}:
      Fail{E.DeflateTruncated{}}

# the end of the stream: the data not yet handed out, or the failure
def zlib_inflate_finish(z: ZlibInflater) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match z:
    case ZlibInHead{buf, opts}:
      zl.in.after(zl.head(buf, I.InflateOptions.dict(opts)))
    case ZlibInBody{+i, a}:
      zl.in.end(I.inflate_finish(i), a, zl.in.ignore(i))
    case ZlibInBad{e}:
      Fail{e}
