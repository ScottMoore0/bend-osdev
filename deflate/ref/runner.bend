# The differential test's runner (see gen.py). Its arguments come in
# threes: an action, an input file and a name.
#   d F FILE NAME   decode FILE as format F (r raw DEFLATE, z zlib, g gzip);
#                   print "NAME LEN CRC32" (the zlib CRC-32 of the output, by
#                   the crc package) or "NAME error KIND"
#   p F FILE NAME   the same through the format's streaming decoder, fed in
#                   pieces
#                   (three, or single bytes for files under 4 KB)
#   c F S L FILE NAME  compress FILE as format F, strategy S, level L into
#                   NAME.out; print "NAME written"
# Strategies: d the level's matcher, f the fast greedy matcher, r run-length,
# h Huffman only, F fixed blocks only, D dynamic blocks only, S stored
# blocks only, s the level's matcher through the format's streaming writer
# fed in three pieces.
import Base
import ../../bytes/bytes.bend as B
import ../../crc/crc.bend as CR
import ../../crc/table.bend as CT
import ../error.bend as E
import ../inflate.bend as I
import ../deflate.bend as D
import ../match.bend as M
import ../block.bend as L
import ../zlib.bend as Z
import ../gzip.bend as G

def crc(o: B.Octets) -> U32:
  CT.Crc32Spec.compute_fast(CR.crc32.spec(), o)

def report(+name: String, r: Result<&2, &2, E.DeflateError, B.Octets>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(name ++ " error " ++ E.DeflateError.show(e))
    case Done{+o}:
      IO.print(name ++ " " ++ Nat.show(B.Octets.len(o)) ++ " " ++ U32.show(crc(o)))

def opts() -> I.InflateOptions:
  I.InflateOptions{4000000000, B.Octets.empty(), True{}}

def chr1(c: Char) -> U32:
  match c:
    case Chr{v}:
      v

def chr(s: String) -> U32:
  match s:
    case SCon{c, t}:
      match c:
        case Chr{v}:
          v
    case SNil{}:
      0

def dec.pick(raw: Bool, zl: Bool, +o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match raw:
    case True{}:
      I.inflate_with(opts(), o)
    case False{}:
      match zl:
        case True{}:
          Z.zlib_decompress_with(opts(), o)
        case False{}:
          G.gzip_decompress_with(opts(), o)

# Streaming raw decoding: the pieces, then the end

def decode(+f: U32, +o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  dec.pick(U32.is_eq(f, 114), U32.is_eq(f, 122), o)

def bytes1(k: Nat, +o: B.Octets, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match k:
    case 0n:
      List.reverse(&2, B.Octets, acc)
    case 1n+j:
      bytes1(j, B.Octets.drop(1n, o), Con{B.Octets.take(1n, o), acc})

def pieces.pick(small: Bool, +n: Nat, +o: B.Octets) -> List<&2, B.Octets>:
  match small:
    case True{}:
      bytes1(n, o, Nil{})
    case False{}:
      +a = Nat.div(n, 3n)
      [B.Octets.take(a, o), B.Octets.slice(a, a, o), B.Octets.drop(Nat.add(a, a), o)]

def pieces(+o: B.Octets) -> List<&2, B.Octets>:
  +n = B.Octets.len(o)
  pieces.pick(Nat.is_lt(n, 4096n), n, o)

type Acc is Data:
  Acc{inf: I.Inflater, out: List<&2, B.Octets>}

def feed.one(r: I.DflFed, out: List<&2, B.Octets>) -> Acc:
  match r:
    case I.DflFed{i, o}:
      Acc{i, Con{o, out}}

def feed.all(ps: List<&2, B.Octets>, a: Acc) -> Acc:
  match ps:
    case Nil{}:
      a
    case Con{p, rest}:
      match a:
        case Acc{i, out}:
          feed.all(rest, feed.one(I.inflate_feed(i, p), out))

def stream.end(r: Result<&2, &2, E.DeflateError, I.DflInflated>, out: List<&2, B.Octets>) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{I.DflInflated{o, rest}}:
      Done{B.Octets.concat(List.reverse(&2, B.Octets, Con{o, out}))}

def stream.fin(a: Acc) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match a:
    case Acc{i, out}:
      stream.end(I.inflate_finish(i), out)

def stream(+o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  stream.fin(feed.all(pieces(o), Acc{I.inflate_start(opts()), Nil{}}))

# Streaming zlib and gzip decoding, in the same pieces

type ZAcc is Data:
  ZAcc{inf: Z.ZlibInflater, out: List<&2, B.Octets>}

def zfeed.one(r: Z.DflZlibFed, out: List<&2, B.Octets>) -> ZAcc:
  match r:
    case Z.DflZlibFed{i, o}:
      ZAcc{i, Con{o, out}}

def zfeed.all(ps: List<&2, B.Octets>, a: ZAcc) -> ZAcc:
  match ps:
    case Nil{}:
      a
    case Con{p, rest}:
      match a:
        case ZAcc{i, out}:
          zfeed.all(rest, zfeed.one(Z.zlib_inflate_feed(i, p), out))

def zstream.end(r: Result<&2, &2, E.DeflateError, B.Octets>, out: List<&2, B.Octets>) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Done{B.Octets.concat(List.reverse(&2, B.Octets, Con{o, out}))}

def zstream.fin(a: ZAcc) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match a:
    case ZAcc{i, out}:
      zstream.end(Z.zlib_inflate_finish(i), out)

def zstream(+o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  zstream.fin(zfeed.all(pieces(o), ZAcc{Z.zlib_inflate_start(opts()), Nil{}}))

type GAcc is Data:
  GAcc{inf: G.GzipInflater, out: List<&2, B.Octets>}

def gfeed.one(r: G.DflGzipFed, out: List<&2, B.Octets>) -> GAcc:
  match r:
    case G.DflGzipFed{i, o}:
      GAcc{i, Con{o, out}}

def gfeed.all(ps: List<&2, B.Octets>, a: GAcc) -> GAcc:
  match ps:
    case Nil{}:
      a
    case Con{p, rest}:
      match a:
        case GAcc{i, out}:
          gfeed.all(rest, gfeed.one(G.gzip_inflate_feed(i, p), out))

def gstream.fin(a: GAcc) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match a:
    case GAcc{i, out}:
      zstream.end(G.gzip_inflate_finish(i), out)

def gstream(+o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  gstream.fin(gfeed.all(pieces(o), GAcc{G.gzip_inflate_start(opts()), Nil{}}))

def streamf.pick(raw: Bool, zl: Bool, +o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match raw:
    case True{}:
      stream(o)
    case False{}:
      match zl:
        case True{}:
          zstream(o)
        case False{}:
          gstream(o)

def streamf(+f: U32, +o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  streamf.pick(U32.is_eq(f, 114), U32.is_eq(f, 122), o)

# Streaming zlib and gzip writing, in thirds

type ZWAcc is Data:
  ZWAcc{w: Z.ZlibWriter, out: List<&2, B.Octets>}

def zwfeed.one(r: Z.DflZlibWritten, out: List<&2, B.Octets>) -> ZWAcc:
  match r:
    case Z.DflZlibWritten{w, o}:
      ZWAcc{w, Con{o, out}}

def zwfeed.all(ps: List<&2, B.Octets>, a: ZWAcc) -> ZWAcc:
  match ps:
    case Nil{}:
      a
    case Con{p, rest}:
      match a:
        case ZWAcc{w, out}:
          zwfeed.all(rest, zwfeed.one(Z.zlib_feed(w, p), out))

def zwfin(a: ZWAcc) -> B.Octets:
  match a:
    case ZWAcc{w, out}:
      B.Octets.concat(List.reverse(&2, B.Octets, Con{Z.zlib_finish(w), out}))

type GWAcc is Data:
  GWAcc{w: G.GzipWriter, out: List<&2, B.Octets>}

def gwfeed.one(r: G.DflGzipWritten, out: List<&2, B.Octets>) -> GWAcc:
  match r:
    case G.DflGzipWritten{w, o}:
      GWAcc{w, Con{o, out}}

def gwfeed.all(ps: List<&2, B.Octets>, a: GWAcc) -> GWAcc:
  match ps:
    case Nil{}:
      a
    case Con{p, rest}:
      match a:
        case GWAcc{w, out}:
          gwfeed.all(rest, gwfeed.one(G.gzip_feed(w, p), out))

def gwfin(a: GWAcc) -> B.Octets:
  match a:
    case GWAcc{w, out}:
      B.Octets.concat(List.reverse(&2, B.Octets, Con{G.gzip_finish(w), out}))

# Compression

def strat.blocks.pick(fx: Bool, dy: Bool, st: Bool, d: D.DeflateOptions) -> D.DeflateOptions:
  match fx:
    case True{}:
      D.DeflateOptions.with_blocks(d, L.DflBlockFixed{})
    case False{}:
      match dy:
        case True{}:
          D.DeflateOptions.with_blocks(d, L.DflBlockDynamic{})
        case False{}:
          match st:
            case True{}:
              D.DeflateOptions.with_blocks(d, L.DflBlockStored{})
            case False{}:
              d

def strat.blocks(+s: U32, d: D.DeflateOptions) -> D.DeflateOptions:
  strat.blocks.pick(U32.is_eq(s, 70), U32.is_eq(s, 68), U32.is_eq(s, 83), d)

def strat.match.pick(fast: Bool, rle: Bool, huff: Bool, d: D.DeflateOptions) -> D.DeflateOptions:
  match fast:
    case True{}:
      D.DeflateOptions.with_matcher(d, M.DflStratChains{M.DflMatchParams.fast()})
    case False{}:
      match rle:
        case True{}:
          D.DeflateOptions.with_matcher(d, M.DflStratRle{})
        case False{}:
          match huff:
            case True{}:
              D.DeflateOptions.with_matcher(d, M.DflStratHuffman{})
            case False{}:
              d

def strat(+s: U32, +l: U32) -> D.DeflateOptions:
  strat.blocks(s, strat.match.pick(U32.is_eq(s, 102), U32.is_eq(s, 114), U32.is_eq(s, 104), D.DeflateOptions.level(l)))

type WAcc is Data:
  WAcc{d: D.Deflater, out: List<&2, B.Octets>}

def wfeed.one(r: D.DflDeflated, out: List<&2, B.Octets>) -> WAcc:
  match r:
    case D.DflDeflated{d, o}:
      WAcc{d, Con{o, out}}

def wfeed.all(ps: List<&2, B.Octets>, a: WAcc) -> WAcc:
  match ps:
    case Nil{}:
      a
    case Con{p, rest}:
      match a:
        case WAcc{d, out}:
          wfeed.all(rest, wfeed.one(D.deflate_feed(d, p), out))

def wfin(a: WAcc) -> B.Octets:
  match a:
    case WAcc{d, out}:
      B.Octets.concat(List.reverse(&2, B.Octets, Con{D.deflate_finish(d), out}))

def thirds(+o: B.Octets) -> List<&2, B.Octets>:
  +n = B.Octets.len(o)
  +a = Nat.div(n, 3n)
  [B.Octets.take(a, o), B.Octets.slice(a, a, o), B.Octets.drop(Nat.add(a, a), o)]

def raw.pick(streamed: Bool, +s: U32, +l: U32, +o: B.Octets) -> B.Octets:
  match streamed:
    case True{}:
      wfin(wfeed.all(thirds(o), WAcc{D.deflate_start(D.DeflateOptions.level(l)), Nil{}}))
    case False{}:
      D.deflate_with(strat(s, l), o)

# raw DEFLATE: the streaming writer (s) gives deflate_unchecked_with's bytes
def raw(+s: U32, +l: U32, +o: B.Octets) -> B.Octets:
  raw.pick(U32.is_eq(s, 115), s, l, o)

def comp.zl(streamed: Bool, +s: U32, +l: U32, +o: B.Octets) -> B.Octets:
  match streamed:
    case True{}:
      zwfin(zwfeed.all(thirds(o), ZWAcc{Z.zlib_start(Z.ZlibOptions.level(l)), Nil{}}))
    case False{}:
      Z.zlib_compress_with(Z.ZlibOptions{strat(s, l), Z.zl.flevel(l)}, o)

def comp.gz(streamed: Bool, +s: U32, +l: U32, +o: B.Octets) -> B.Octets:
  match streamed:
    case True{}:
      gwfin(gwfeed.all(thirds(o), GWAcc{G.gzip_start(G.GzipOptions{D.DeflateOptions.level(l), G.GzipHeader.default()}), Nil{}}))
    case False{}:
      G.gzip_compress_with(G.GzipOptions{strat(s, l), G.GzipHeader.default()}, o)

def comp.pick(rw: Bool, zl: Bool, +s: U32, +l: U32, +o: B.Octets) -> B.Octets:
  match rw:
    case True{}:
      raw(s, l, o)
    case False{}:
      match zl:
        case True{}:
          comp.zl(U32.is_eq(s, 115), s, l, o)
        case False{}:
          comp.gz(U32.is_eq(s, 115), s, l, o)

def compress(+f: U32, +s: U32, +l: U32, +o: B.Octets) -> B.Octets:
  comp.pick(U32.is_eq(f, 114), U32.is_eq(f, 122), s, l, o)

def save(+name: String, o: B.Octets) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(name ++ ".out", "w"))
    fr : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, B.Octets.to_list(o))
    IO.print(name ++ " written")

# The actions

def act.comp(+rest: String, +name: String, +o: B.Octets) -> IO(Unit):
  match rest:
    case SCon{f, SCon{s, SCon{l, t}}}:
      save(name, compress(chr1(f), chr1(s), U32.sub(chr1(l), 48), o))
    case _:
      IO.print(name ++ " bad action")

def act.kind(dec: Bool, str: Bool, +rest: String, +name: String, +o: B.Octets) -> IO(Unit):
  match dec:
    case True{}:
      report(name, decode(chr(rest), o))
    case False{}:
      match str:
        case True{}:
          report(name, streamf(chr(rest), o))
        case False{}:
          act.comp(rest, name, o)

# a: "d", "p" or "c" and its letters
def act.on(+a: String, +name: String, xs: List<&2, U32>) -> IO(Unit):
  match a:
    case SCon{k, rest}:
      match k:
        case Chr{+kv}:
          act.kind(U32.is_eq(kv, 100), U32.is_eq(kv, 112), rest, name, B.Octets.of_list(xs))
    case SNil{}:
      IO.print(name ++ " bad action")

def act.read(r: Result<&1, &1, U32 & String, List<&2, U32>>, +a: String, +name: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(name ++ " unreadable")
    case Done{xs}:
      act.on(a, name, xs)

def act.got(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>, +a: String, +name: String) -> IO(Unit):
  (f, r) = fr
  act.read(r, a, name)

def act(+a: String, file: String, +name: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(file, "r"))
    fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 4000000000)
    act.got(fr, a, name)

def run(args: List<&1, String>) -> IO(Unit):
  match args:
    case Con{+a, Con{+file, Con{+name, rest}}}:
      do IO<Unit>:
        act(a, file, name)
        run(rest)
    case _:
      IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args
    run(List.tail(&1, String, args))
