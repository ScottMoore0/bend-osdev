# The streaming forms equal the one-shot forms, for every split of the
# input.
#
# inflate_streaming: the streaming inflater (inflate_start, inflate_feed,
# inflate_finish), fed a raw DEFLATE stream in any pieces, answers what
# inflate_split answers for the pieces joined: the same failure, or the
# same output (every feed's output and the finish's, joined) and the same
# bytes after the stream. So it also never answers more than the maximum,
# and refuses what the one-shot form refuses, at the same point.
#
# zlib_streaming: the same for the streaming zlib reader (zlib_inflate_start,
# zlib_inflate_feed, zlib_inflate_finish) and zlib_decompress_with: the
# header may arrive in any pieces, and the Adler-32 kept piece by piece is
# the one the one-shot form computes.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./inflate.bend as I
import ./zlib.bend as Z

# the pieces joined, in order
def stream_join(ps: List<&2, B.Octets>) -> B.Octets:
  match ps:
    case Nil{}:
      B.Octets.empty()
    case Con{p, t}:
      B.Octets.append(p, stream_join(t))

# the finish's answer, after the output out the feeds handed out
def stream_last(r: Result<&2, &2, E.DeflateError, I.DflInflated>, out: B.Octets) -> Result<&2, &2, E.DeflateError, I.DflInflated>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{I.DflInflated{o, rest}}:
      Done{I.DflInflated{B.Octets.append(out, o), rest}}

# the inflater after a feed that answered f, then fed the pieces ps in
# turn and finished; out: the output handed out before f
def inflate_pieces.go(ps: List<&2, B.Octets>, f: I.DflFed, out: B.Octets) -> Result<&2, &2, E.DeflateError, I.DflInflated>:
  match ps:
    case Nil{}:
      match f:
        case I.DflFed{i, o}:
          stream_last(I.inflate_finish(i), B.Octets.append(out, o))
    case Con{p, t}:
      match f:
        case I.DflFed{i, o}:
          inflate_pieces.go(t, I.inflate_feed(i, p), B.Octets.append(out, o))

# a streaming inflater with these options, fed the pieces ps in turn and
# finished: everything it answers
def inflate_pieces(opts: I.InflateOptions, ps: List<&2, B.Octets>) -> Result<&2, &2, E.DeflateError, I.DflInflated>:
  inflate_pieces.go(ps, I.DflFed{I.inflate_start(opts), B.Octets.empty()}, B.Octets.empty())

law inflate_streaming:
  for +opts: I.InflateOptions
  for +ps: List<&2, B.Octets>
  {inflate_pieces(opts, ps) == I.inflate_split(opts, stream_join(ps)) : Result<&2, &2, E.DeflateError, I.DflInflated>}

# the zlib reader's answer at its finish, after the output out
def zlib_last(r: Result<&2, &2, E.DeflateError, B.Octets>, out: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Done{B.Octets.append(out, o)}

# the zlib reader after a feed that answered f, then fed the pieces ps in
# turn and finished; out: the output handed out before f
def zlib_pieces.go(ps: List<&2, B.Octets>, f: Z.DflZlibFed, out: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match ps:
    case Nil{}:
      match f:
        case Z.DflZlibFed{z, o}:
          zlib_last(Z.zlib_inflate_finish(z), B.Octets.append(out, o))
    case Con{p, t}:
      match f:
        case Z.DflZlibFed{z, o}:
          zlib_pieces.go(t, Z.zlib_inflate_feed(z, p), B.Octets.append(out, o))

# a streaming zlib reader with these options, fed the pieces ps in turn and
# finished: everything it answers
def zlib_pieces(opts: I.InflateOptions, ps: List<&2, B.Octets>) -> Result<&2, &2, E.DeflateError, B.Octets>:
  zlib_pieces.go(ps, Z.DflZlibFed{Z.zlib_inflate_start(opts), B.Octets.empty()}, B.Octets.empty())

law zlib_streaming:
  for +opts: I.InflateOptions
  for +ps: List<&2, B.Octets>
  {zlib_pieces(opts, ps) == Z.zlib_decompress_with(opts, stream_join(ps)) : Result<&2, &2, E.DeflateError, B.Octets>}
