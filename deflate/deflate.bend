# bend-osdev-deflate: the entry file: raw DEFLATE (RFC 1951) compression and
# decompression. inflate is the inflater's (inflate.bend), re-exported in
# name only: Bend imports do not re-export, so import inflate.bend for the
# decoder's types and options.
#
# The deflater cuts its input into segments (64 KB by default; the matcher
# reaches back into the 32 KB before each), turns each into tokens with the
# matcher (match.bend), and writes the tokens as blocks (block.bend), the
# last block final. Every choice is a parameter (DeflateOptions), with the
# levels 0 to 9 as named defaults.
#
# deflate_with checks its own output: it inflates it and compares, and
# should they differ (no test has ever seen it) it answers stored_stream(o)
# instead, a stream whose round trip is proved for every input. So
# inflate(deflate_with(opts, o)) == o is a law for every input and every
# option (LAWS.bend); deflate_unchecked_with skips the check.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bits.bend as K
import ./window.bend as W
import ./eq.bend as Q
import ./match.bend as M
import ./block.bend as L
import ./inflate.bend as I

# The options

# matcher: how tokens are found; blocks: which block types are written;
# block_tokens: the most tokens a block holds; segment: how many input bytes
# the matcher works on at a time (and the unit the streaming writer emits)
type DeflateOptions is Data:
  DeflateOptions{matcher: M.DflStrategy, blocks: L.DflBlockStrategy, block_tokens: Nat, segment: Nat}

def dfl.lv(zero: Bool, +l: U32) -> DeflateOptions:
  match zero:
    case True{}:
      DeflateOptions{M.DflStratHuffman{}, L.DflBlockStored{}, 16384n, 65536n}
    case False{}:
      DeflateOptions{M.DflStratChains{M.DflMatchParams.level(l)}, L.DflBlockAuto{}, 16384n, 65536n}

# level 0: stored blocks only; 1 to 9: the matcher's levels (match.bend),
# blocks of 16384 tokens, each the smallest type
def DeflateOptions.level(+l: U32) -> DeflateOptions:
  dfl.lv(U32.is_eq(l, 0), l)

# level 6
def DeflateOptions.default() -> DeflateOptions:
  DeflateOptions.level(6)

# the fast greedy matcher (DflMatchParams.fast)
def DeflateOptions.fast() -> DeflateOptions:
  DeflateOptions{M.DflStratChains{M.DflMatchParams.fast()}, L.DflBlockAuto{}, 16384n, 65536n}

def DeflateOptions.with_matcher(o: DeflateOptions, +m: M.DflStrategy) -> DeflateOptions:
  match o:
    case DeflateOptions{matcher, blocks, bt, seg}:
      DeflateOptions{m, blocks, bt, seg}

def DeflateOptions.with_blocks(o: DeflateOptions, +b: L.DflBlockStrategy) -> DeflateOptions:
  match o:
    case DeflateOptions{matcher, blocks, bt, seg}:
      DeflateOptions{matcher, b, bt, seg}

# The segments

# the streaming writer's state: the options, the last 32768 input bytes
# before the pending ones, the input not yet compressed, the bits written
type Deflater is Data:
  Deflater{opts: DeflateOptions, hist: List<&2, U32>, pending: List<&2, U32>, w: K.DflOut}

def dfl.keep32k(+xs: List<&2, U32>) -> List<&2, U32>:
  B.drop(Nat.sub(B.len.fast(xs), 32768n), xs)

# one segment, compressed after hist (final: the stream's last)
def dfl.segment(opts: DeflateOptions, +final: Bool, +hist: List<&2, U32>, +seg: List<&2, U32>, w: K.DflOut) -> K.DflOut:
  match opts:
    case DeflateOptions{matcher, blocks, bt, sz}:
      L.blocks_write(w, final, blocks, bt, M.match_tokens(matcher, hist, seg), seg)

def dfl.seg.size(opts: DeflateOptions) -> Nat:
  match opts:
    case DeflateOptions{matcher, blocks, bt, sz}:
      Nat.max(sz, 1n)

def dfl.empty(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def dfl.opts(d: Deflater) -> DeflateOptions:
  match d:
    case Deflater{opts, hist, pending, w}:
      opts

# whether anything has been compressed yet (a segment, or history)
def dfl.started(d: Deflater) -> Bool:
  match d:
    case Deflater{opts, hist, pending, w}:
      Bool.not(dfl.empty(hist))

# the first segment of the pending input compressed (final if nothing is
# left after it and final)
def dfl.seg.one(+fin: Bool, d: Deflater) -> Deflater:
  match d:
    case Deflater{+opts, +hist, +pending, w}:
      +n = dfl.seg.size(opts)
      +seg = B.take.fast(n, pending)
      +rest = B.drop(n, pending)
      Deflater{opts, dfl.keep32k(B.append.fast(hist, seg)), rest, dfl.segment(opts, Bool.and(fin, dfl.empty(rest)), hist, seg, w)}

def dfl.pending.len(d: Deflater) -> Nat:
  match d:
    case Deflater{opts, hist, pending, w}:
      B.len.fast(pending)

def dfl.ready(+d: Deflater) -> Bool:
  Nat.is_lt(dfl.seg.size(dfl.opts(d)), dfl.pending.len(d))

# while more than a segment is pending: a segment that is surely not the
# last
def dfl.feed.go(fuel: Nat, go: Bool, +d: Deflater) -> Deflater:
  match fuel:
    case 0n:
      d
    case 1n+f:
      match go:
        case True{}:
          +d2 = dfl.seg.one(False{}, d)
          dfl.feed.go(f, dfl.ready(d2), d2)
        case False{}:
          d

def dfl.pending.none(d: Deflater) -> Bool:
  match d:
    case Deflater{opts, hist, pending, w}:
      dfl.empty(pending)

# at the end: every pending segment, the last final
def dfl.finish.go(fuel: Nat, done: Bool, +d: Deflater) -> Deflater:
  match fuel:
    case 0n:
      d
    case 1n+f:
      match done:
        case True{}:
          d
        case False{}:
          +d2 = dfl.seg.one(True{}, d)
          dfl.finish.go(f, dfl.pending.none(d2), d2)

# The streaming writer

def deflate_start(opts: DeflateOptions) -> Deflater:
  Deflater{opts, Nil{}, Nil{}, K.out.new()}

# the deflater and the whole bytes written so far
type DflDeflated is Data:
  DflDeflated{deflater: Deflater, bytes: B.Octets}

def dfl.take.of(t: K.DflOutTake, +opts: DeflateOptions, +hist: List<&2, U32>, +pending: List<&2, U32>) -> DflDeflated:
  match t:
    case K.DflOutTake{bytes, w2}:
      DflDeflated{Deflater{opts, hist, pending, w2}, B.Octets.of_list(bytes)}

def dfl.take(d: Deflater) -> DflDeflated:
  match d:
    case Deflater{opts, hist, pending, w}:
      dfl.take.of(K.out.take(w), opts, hist, pending)

def dfl.add(d: Deflater, o: B.Octets) -> Deflater:
  match d:
    case Deflater{opts, hist, pending, w}:
      Deflater{opts, hist, B.append.fast(pending, B.Octets.to_list(o)), w}

# more input: answers the bytes it completes (whole segments are compressed
# once more than a segment's worth is pending)
def deflate_feed(d: Deflater, o: B.Octets) -> DflDeflated:
  +d1 = dfl.add(d, o)
  +n = dfl.pending.len(d1)
  dfl.take(dfl.feed.go(n, dfl.ready(d1), d1))

def dfl.fin.of(d: Deflater) -> B.Octets:
  match d:
    case Deflater{opts, hist, pending, w}:
      B.Octets.of_list(K.out.finish(w))

def dfl.fin.empty(none: Bool, +d: Deflater) -> Deflater:
  match none:
    case True{}:
      match d:
        case Deflater{+opts, hist, pending, w}:
          Deflater{opts, hist, pending, dfl.segment(opts, True{}, hist, Nil{}, w)}
    case False{}:
      d

# the end of the input: the rest of the stream (the final block's last
# byte padded with zero bits). A stream with no input at all is one empty
# final block.
def deflate_finish(+d: Deflater) -> B.Octets:
  +n = dfl.pending.len(d)
  +started = dfl.started(d)
  dfl.fin.of(dfl.fin.empty(Bool.and(Nat.is_eq(n, 0n), Bool.not(started)), dfl.finish.go(1n+n, dfl.pending.none(d), d)))

# The one-shot forms

# o compressed, without the self-check: exactly what the streaming writer
# writes for o fed in any pieces
def dfl.whole(r: DflDeflated) -> B.Octets:
  match r:
    case DflDeflated{d, bytes}:
      B.Octets.append(bytes, deflate_finish(d))

def deflate_unchecked_with(+opts: DeflateOptions, o: B.Octets) -> B.Octets:
  dfl.whole(deflate_feed(deflate_start(opts), o))

# The fallback: stored blocks of at most 255 bytes, then an empty final
# stored block. It is never the shortest stream, but its round trip is
# proved for every input (PROOF.bend), each block's LEN being a single byte.

# min(len(xs), cap)
def fb.count(cap: Nat, xs: List<&2, U32>) -> Nat:
  match cap:
    case 0n:
      0n
    case 1n+c:
      match xs:
        case Nil{}:
          0n
        case Con{h, t}:
          1n+fb.count(c, t)

# a non-final stored block's header for n bytes (n from 1 to 255): BFINAL 0,
# BTYPE 00, then LEN = n and NLEN = 65535 - n, least significant byte first
def fb.hdr(+n: Nat) -> List<&2, U32>:
  +v = U32.from_nat(n)
  [0, v, 0, U32.xor(v, 255), 255]

# xs as stored blocks; k: how many bytes are left in the current block
def fb.go(xs: List<&2, U32>, k: Nat) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [1, 0, 0, 255, 255]
    case Con{h, +t}:
      match k:
        case 0n:
          +n = fb.count(254n, t)
          B.append(fb.hdr(1n+n), Con{h, fb.go(t, n)})
        case 1n+j:
          Con{h, fb.go(t, j)}

# o as stored blocks of at most 255 bytes
def stored_stream(o: B.Octets) -> B.Octets:
  B.Octets.of_list(fb.go(B.Octets.to_list(o), 0n))

# The self-check

def dfl.keep(ok: Bool, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match ok:
    case True{}:
      c
    case False{}:
      stored_stream(o)

def dfl.check.st(st: I.DflSt, em: List<&2, U32>, +acc: List<&2, U32>, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match st:
    case I.DflEnd{rest}:
      match rest:
        case Nil{}:
          match em:
            case Nil{}:
              dfl.keep(Q.eq.list(B.rev(acc), B.Octets.to_list(o)), c, o)
            case Con{x, y}:
              stored_stream(o)
        case Con{h, t}:
          stored_stream(o)
    case _:
      stored_stream(o)

# c, if inflating it gives o back exactly (and it ends where the stream
# ends); else the fallback
def dfl.check(r: I.DflDrv, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match r:
    case I.DflFull{}:
      stored_stream(o)
    case I.DflRun{core, acc, room}:
      match core:
        case I.DflCore{st, win, em}:
          dfl.check.st(st, em, acc, c, o)

# o compressed with these options, checked by inflating it
def deflate_with(+opts: DeflateOptions, +o: B.Octets) -> B.Octets:
  +c = deflate_unchecked_with(opts, o)
  dfl.check(I.drv.go(B.Octets.to_list(c), I.drv.start(W.win.empty(), B.Octets.len(o))), c, o)

# o compressed at the default level (6)
def deflate(+o: B.Octets) -> B.Octets:
  deflate_with(DeflateOptions.default(), o)

# o compressed at level l (0 to 9)
def deflate_level(+l: U32, +o: B.Octets) -> B.Octets:
  deflate_with(DeflateOptions.level(l), o)

# the output of the raw DEFLATE stream src (inflate.bend's inflate)
def inflate(src: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  I.inflate(src)

def inflate_with(+opts: I.InflateOptions, src: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  I.inflate_with(opts, src)
