# bend-osdev-lz4, compression: a block compressor and a frame writer, from the
# LZ4 project's specifications (lz4_Block_format.md, lz4_Frame_format.md).
#
# The block compressor is a greedy LZ77 matcher with a single-entry hash
# table: at each position it looks up the last position whose next four bytes
# hashed the same, extends the match as far as the end-of-block rules allow
# (a match starts 12 bytes or more before the end and ends 5 bytes or more
# before it), and emits literals and matches as LZ4 sequences.
#
# block_compress checks its own output: it decodes it and, should that not
# give the input back, answers the literal-only block instead. So a law can
# say, for every input, that what it writes decodes to the input.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./block.bend as K
import ./frame.bend as F

# The matcher

# a table slot: a position + 1 (0: empty) and the input from there on
type Lz4Cand is Data:
  Lz4Cand{pos: U32, suf: List<&2, U32>}

# the matcher's state: the table; the input from position i on; the last
# position a match may start at (lim) and the last it may reach (end); the
# literals since the last match (reversed); the output so far (reversed)
type Lz4Enc is Type:
  Lz4EncGo{tab: Array<Lz4Cand>, cur: List<&2, U32>, i: U32, lim: U32, end: U32, lits: List<&2, U32>, out: List<&2, U32>}
  Lz4EncDone{out: List<&2, U32>}

# 12 bits of a hash of the next four bytes
def cmp.hash(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      U32.shrn(U32.mul(U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n))), 2654435761), 20n)
    case _:
      0

def cmp.inc_if(ok: Bool, n: Nat) -> Nat:
  match ok:
    case True{}:
      1n+n
    case False{}:
      n

# how many bytes a and b share from their starts, k at most; live: the bytes
# so far agree
def cmp.common(a: List<&2, U32>, live: Bool, b: List<&2, U32>, +k: U32, n: Nat) -> Nat:
  match a live:
    case Con{x, s} True{}:
      match b:
        case Nil{}:
          n
        case Con{y, t}:
          +ok = Bool.and(U32.is_lt(0, k), U32.is_eq(x, y))
          cmp.common(s, ok, t, U32.sub(k, 1), cmp.inc_if(ok, n))
    case _ _:
      n

# the low nibble of a length: the length itself below 15, else 15
def cmp.nib(+n: Nat) -> U32:
  U32.from_nat(Nat.min(n, 15n))

def cmp.ext.pick(more: Bool, +n: Nat) -> List<&2, U32>:
  match more:
    case True{}:
      K.lit.ext(Nat.sub(n, 15n), 254n)
    case False{}:
      Nil{}

# the length bytes after a nibble of 15
def cmp.ext(+n: Nat) -> List<&2, U32>:
  cmp.ext.pick(Nat.is_le(15n, n), n)

# a sequence (literals, then a match at offset off of length ml), pushed onto
# the reversed output
def cmp.seq(+lits: List<&2, U32>, +off: U32, +ml: Nat, out: List<&2, U32>) -> List<&2, U32>:
  +l = B.len(lits)
  +m = Nat.sub(ml, 4n)
  +tok = U32.or(U32.shln(cmp.nib(l), 4n), cmp.nib(m))
  K.blk.push(cmp.ext(m), Con{U32.shrn(off, 8n), Con{U32.and(off, 255), K.blk.push(lits, K.blk.push(cmp.ext(l), Con{tok, out}))}})

# the last sequence: literals only
def cmp.last(+lits: List<&2, U32>, out: List<&2, U32>) -> List<&2, U32>:
  +l = B.len(lits)
  K.blk.push(lits, K.blk.push(cmp.ext(l), Con{U32.shln(cmp.nib(l), 4n), out}))

def cmp.done(lits: List<&2, U32>, cur: List<&2, U32>, out: List<&2, U32>) -> Lz4Enc:
  Lz4EncDone{cmp.last(B.append(K.blk.rev(lits), cur), out)}

# a match of ml bytes, or (shorter than 4) one more literal
def cmp.emit(ok: Bool, tab: Array<Lz4Cand>, +cur: List<&2, U32>, +i: U32, +ml: Nat, +off: U32, lim: U32, end: U32, +lits: List<&2, U32>, out: List<&2, U32>) -> Lz4Enc:
  match ok:
    case True{}:
      Lz4EncGo{tab, B.drop(ml, cur), U32.add(i, U32.from_nat(ml)), lim, end, Nil{}, cmp.seq(K.blk.rev(lits), off, ml, out)}
    case False{}:
      match cur:
        case Nil{}:
          cmp.done(lits, Nil{}, out)
        case Con{b, t}:
          Lz4EncGo{tab, t, U32.add(i, 1), lim, end, Con{b, lits}, out}

def cmp.found(valid: Bool, +suf: List<&2, U32>, +cur: List<&2, U32>, +k: U32) -> Nat:
  match valid:
    case True{}:
      cmp.common(suf, True{}, cur, k, 0n)
    case False{}:
      0n

# the slot for this position: its old entry is the candidate, which must be
# 65535 bytes back at most and agree on 4 bytes or more
def cmp.cand(r: Array<Lz4Cand> & Lz4Cand, +h: U32, +cur: List<&2, U32>, +i: U32, lim: U32, +end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4Enc:
  (tab, c) = r
  match c:
    case Lz4Cand{+pos, suf}:
      +off = U32.sub(U32.add(i, 1), pos)
      +ml = cmp.found(Bool.and(U32.is_lt(0, pos), U32.is_le(off, 65535)), suf, cur, U32.sub(end, i))
      cmp.emit(Nat.is_le(4n, ml), Array.set(Lz4Cand, tab, h, Lz4Cand{U32.add(i, 1), cur}), cur, i, ml, off, lim, end, lits, out)

def cmp.step.at(go: Bool, tab: Array<Lz4Cand>, +cur: List<&2, U32>, +i: U32, lim: U32, end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4Enc:
  match go:
    case True{}:
      +h = cmp.hash(cur)
      cmp.cand(Array.get(Lz4Cand, tab, h), h, cur, i, lim, end, lits, out)
    case False{}:
      cmp.done(lits, cur, out)

# one position: past the last place a match may start, the rest are literals
def cmp.step(tab: Array<Lz4Cand>, cur: List<&2, U32>, +i: U32, +lim: U32, end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4Enc:
  cmp.step.at(U32.is_le(i, lim), tab, cur, i, lim, end, lits, out)

# every step moves on a byte or more, so fuel of the input's length + 1
# reaches the end
def cmp.loop(fuel: Nat, st: Lz4Enc) -> List<&2, U32>:
  match fuel:
    case 0n:
      match st:
        case Lz4EncGo{tab, cur, i, lim, end, lits, out}:
          K.blk.rev(cmp.last(B.append(K.blk.rev(lits), cur), out))
        case Lz4EncDone{out}:
          K.blk.rev(out)
    case 1n+f:
      match st:
        case Lz4EncGo{tab, cur, i, lim, end, lits, out}:
          cmp.loop(f, cmp.step(tab, cur, i, lim, end, lits, out))
        case Lz4EncDone{out}:
          K.blk.rev(out)

# the dictionary's positions go into the table first
def cmp.seed(n: Nat, tab: Array<Lz4Cand>, +xs: List<&2, U32>, +i: U32) -> Array<Lz4Cand>:
  match n:
    case 0n:
      tab
    case 1n+p:
      match xs:
        case Nil{}:
          tab
        case Con{h, t}:
          cmp.seed(p, Array.set(Lz4Cand, tab, cmp.hash(xs), Lz4Cand{U32.add(i, 1), xs}), t, U32.add(i, 1))

def cmp.start(big: Bool, +dict: List<&2, U32>, +xs: List<&2, U32>, +total: U32) -> List<&2, U32>:
  match big:
    case True{}:
      +all = B.append(dict, xs)
      +base = B.len(dict)
      tab = cmp.seed(base, Array.new(Lz4Cand, 12n, Lz4Cand{0, Nil{}}), all, 0)
      cmp.loop(Nat.add(B.len(xs), 1n), Lz4EncGo{tab, B.drop(base, all), U32.from_nat(base), U32.sub(total, 12), U32.sub(total, 5), Nil{}, Nil{}})
    case False{}:
      K.blk.rev(cmp.last(xs, Nil{}))

# the block for xs, after the history dict (at most its last 65535 bytes)
def cmp.block(+dict: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  +d = B.drop(Nat.sub(B.len(dict), 65535n), dict)
  +total = U32.from_nat(Nat.add(B.len(d), B.len(xs)))
  cmp.start(U32.is_le(13, total), d, xs, total)

# Checking a block: decode it and compare

def cmp.weq(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          Bool.and(Bool.not(Bool.xor(x, y)), cmp.weq(p, s, t))

def cmp.u32_eq(a: U32, b: U32) -> Bool:
  match a b:
    case U32{x} U32{y}:
      cmp.weq(32n, x, y)

# the same bytes, in the same order
def cmp.same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, s} Con{b, t}:
      Bool.and(cmp.u32_eq(a, b), cmp.same(s, t))
    case _ _:
      False{}

def cmp.keep(ok: Bool, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match ok:
    case True{}:
      c
    case False{}:
      K.block_literals(o)

# the block c if it decodes to o, else the literal-only block
def cmp.check(r: Result<&2, &2, K.Lz4Error, B.Octets>, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match r:
    case Fail{e}:
      K.block_literals(o)
    case Done{d}:
      cmp.keep(cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)), c, o)

def cmp.check_dict(r: Result<&2, &2, K.Lz4Error, B.Octets>, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match r:
    case Fail{e}:
      K.block_literals(o)
    case Done{d}:
      cmp.keep(cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)), c, o)

# The public interface: blocks

# the matcher's block for o, unchecked
def block_compress_unchecked(o: B.Octets) -> B.Octets:
  B.Octets.of_list(cmp.block(Nil{}, B.Octets.to_list(o)))

# a block for o: the matcher's, checked by decoding it
def block_compress(+o: B.Octets) -> B.Octets:
  +c = block_compress_unchecked(o)
  cmp.check(K.block_decompress(c, B.Octets.len(o)), c, o)

# a block for o that may refer back into dict (the bytes before it), checked
def block_compress_dict(+dict: B.Octets, +o: B.Octets) -> B.Octets:
  +c = B.Octets.of_list(cmp.block(B.Octets.to_list(dict), B.Octets.to_list(o)))
  cmp.check_dict(K.block_decompress_dict(dict, c, B.Octets.len(o)), c, o)

# The frame writer

type Lz4BlockMax is Data:
  Lz4Max64KB{}
  Lz4Max256KB{}
  Lz4Max1MB{}
  Lz4Max4MB{}

# block_max: the block maximum size the header declares; block_size: where
# the content is cut into blocks (at most block_max; 0 means block_max);
# indep: blocks independent (or each may refer back into the ones before);
# block_sum: a checksum after every block; content_sum: a checksum of the
# content; content_size: the content's size in the header (one-shot writing
# only)
type Lz4FrameOptions is Data:
  Lz4FrameOptions{block_max: Lz4BlockMax, block_size: U32, indep: Bool, block_sum: Bool, content_sum: Bool, content_size: Bool}

# what the lz4 tool writes by default: 64 KB independent blocks and a
# content checksum (FLG 0x64, BD 0x40)
def Lz4FrameOptions.default() -> Lz4FrameOptions:
  Lz4FrameOptions{Lz4Max64KB{}, 65536, True{}, False{}, True{}, False{}}

def wr.code(m: Lz4BlockMax) -> U32:
  match m:
    case Lz4Max64KB{}:
      4
    case Lz4Max256KB{}:
      5
    case Lz4Max1MB{}:
      6
    case Lz4Max4MB{}:
      7

def wr.bmax(m: Lz4BlockMax) -> U32:
  match m:
    case Lz4Max64KB{}:
      65536
    case Lz4Max256KB{}:
      262144
    case Lz4Max1MB{}:
      1048576
    case Lz4Max4MB{}:
      4194304

def wr.bit(on: Bool, v: U32) -> U32:
  match on:
    case True{}:
      v
    case False{}:
      0

def wr.size(m: Maybe<&2, Nat>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{n}:
      B.le64(W.W64.from_nat(n))

# the header: magic, FLG, BD, the content size if known, header checksum
def wr.header(opts: Lz4FrameOptions, +size: Maybe<&2, Nat>) -> List<&2, U32>:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize}:
      +flg = U32.or(64, U32.or(wr.bit(indep, 32), U32.or(wr.bit(bsum, 16), U32.or(wr.bit(csum, 4), wr.bit(Maybe.is_some(&2, Nat, size), 8)))))
      +desc = {Con{flg, Con{U32.shln(wr.code(bmax), 4n), wr.size(size)}} : List<&2, U32>}
      B.append(B.le32(407708164), B.append(desc, [U32.and(U32.shrn(F.frm.xxh32(desc), 8n), 255)]))

def wr.sum(on: Bool, data: List<&2, U32>) -> List<&2, U32>:
  match on:
    case True{}:
      B.le32(F.frm.xxh32(data))
    case False{}:
      Nil{}

# a block: compressed when that is smaller, else stored as it is
def wr.stored(small: Bool, +bsum: Bool, +comp: List<&2, U32>, +raw: List<&2, U32>) -> List<&2, U32>:
  match small:
    case True{}:
      B.append(B.le32(U32.from_nat(B.len(comp))), B.append(comp, wr.sum(bsum, comp)))
    case False{}:
      B.append(B.le32(U32.or(U32.from_nat(B.len(raw)), 2147483648)), B.append(raw, wr.sum(bsum, raw)))

def wr.comp(indep: Bool, +hist: List<&2, U32>, +raw: List<&2, U32>) -> List<&2, U32>:
  match indep:
    case True{}:
      B.Octets.to_list(block_compress(B.Octets.of_list(raw)))
    case False{}:
      B.Octets.to_list(block_compress_dict(B.Octets.of_list(hist), B.Octets.of_list(raw)))

# the bytes of one block of raw, after the history hist
def wr.block(+opts: Lz4FrameOptions, +hist: List<&2, U32>, +raw: List<&2, U32>) -> List<&2, U32>:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize}:
      +comp = wr.comp(indep, hist, raw)
      wr.stored(Nat.is_lt(B.len(comp), B.len(raw)), bsum, comp, raw)

def wr.keep(+xs: List<&2, U32>) -> List<&2, U32>:
  B.drop(Nat.sub(B.len(xs), 65535n), xs)

# the first n bytes of a list, the rest, and whether there were n of them
# (counted in U32: a Nat block size would be a long chain of successors)
type Lz4Cut is Data:
  Lz4Cut{head: List<&2, U32>, rest: List<&2, U32>, full: Bool}

def wr.split.go(xs: List<&2, U32>, more: Bool, +n: U32, acc: List<&2, U32>) -> Lz4Cut:
  match xs more:
    case Con{h, t} True{}:
      wr.split.go(t, U32.is_lt(1, n), U32.sub(n, 1), Con{h, acc})
    case Con{h, t} False{}:
      Lz4Cut{K.blk.rev(acc), Con{h, t}, True{}}
    case Nil{} True{}:
      Lz4Cut{K.blk.rev(acc), Nil{}, False{}}
    case Nil{} False{}:
      Lz4Cut{K.blk.rev(acc), Nil{}, True{}}

def wr.split(xs: List<&2, U32>, +n: U32) -> Lz4Cut:
  wr.split.go(xs, U32.is_lt(0, n), n, Nil{})

# blocks of the block size, the last one shorter; c: the next block and
# the rest; acc: the frame's bytes so far
def wr.blocks(fuel: Nat, c: Lz4Cut, +opts: Lz4FrameOptions, +bsz: U32, +hist: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match c:
        case Lz4Cut{+raw, rest, full}:
          match raw:
            case Nil{}:
              acc
            case Con{h, t}:
              wr.blocks(f, wr.split(rest, bsz), opts, bsz, wr.keep(B.append(hist, raw)), B.append(acc, wr.block(opts, hist, raw)))

def wr.end(opts: Lz4FrameOptions, content: List<&2, U32>) -> List<&2, U32>:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize}:
      B.append(B.le32(0), wr.sum(csum, content))

def wr.size_of(on: Bool, +xs: List<&2, U32>) -> Maybe<&2, Nat>:
  match on:
    case True{}:
      Some{B.len(xs)}
    case False{}:
      None{}

def wr.cut.pick(ok: Bool, bmax: U32, bsize: U32) -> U32:
  match ok:
    case True{}:
      bsize
    case False{}:
      bmax

def wr.cut(+bmax: U32, +bsize: U32) -> U32:
  wr.cut.pick(Bool.and(U32.is_lt(0, bsize), U32.is_le(bsize, bmax)), bmax, bsize)

# where blocks are cut: the block size, if it is 1 to the block maximum size,
# else the block maximum size
def wr.opts.bmax(opts: Lz4FrameOptions) -> U32:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize}:
      wr.cut(wr.bmax(bmax), bsize)

def wr.opts.csize(opts: Lz4FrameOptions) -> Bool:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize}:
      csize

# The public interface: frames

# a frame holding o
def frame_compress(+opts: Lz4FrameOptions, o: B.Octets) -> B.Octets:
  +xs = B.Octets.to_list(o)
  +hd = wr.header(opts, wr.size_of(wr.opts.csize(opts), xs))
  +bsz = wr.opts.bmax(opts)
  B.Octets.of_list(B.append(hd, B.append(wr.blocks(Nat.add(B.len(xs), 1n), wr.split(xs, bsz), opts, bsz, Nil{}, Nil{}), wr.end(opts, xs))))

# a frame holding o, with the default options
def compress(o: B.Octets) -> B.Octets:
  frame_compress(Lz4FrameOptions.default(), o)

# Streaming: start, then feed the content in pieces, then finish. Each call
# answers the frame's next bytes. A streamed frame has no content size, and
# the writer keeps the content for the content checksum (XXH32 here is one
# shot).

# the options, the bytes not yet in a block, the history (linked blocks),
# the content so far (reversed)
type Lz4Writer is Data:
  Lz4Writer{opts: Lz4FrameOptions, pending: List<&2, U32>, hist: List<&2, U32>, content: List<&2, U32>}

type Lz4Written is Data:
  Lz4Written{writer: Lz4Writer, bytes: B.Octets}

def wr.no_size(opts: Lz4FrameOptions) -> Lz4FrameOptions:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize}:
      Lz4FrameOptions{bmax, bsize, indep, bsum, csum, False{}}

def frame_start(opts: Lz4FrameOptions) -> Lz4Written:
  +o = wr.no_size(opts)
  Lz4Written{Lz4Writer{o, Nil{}, Nil{}, Nil{}}, B.Octets.of_list(wr.header(o, None{}))}

type Lz4Flushed is Data:
  Lz4Flushed{pending: List<&2, U32>, hist: List<&2, U32>, bytes: List<&2, U32>}

# the full blocks go out; fewer than a block's bytes stay. c: the next
# block, if full, and the rest
def wr.flush(fuel: Nat, c: Lz4Cut, +opts: Lz4FrameOptions, +bsz: U32, +hist: List<&2, U32>, acc: List<&2, U32>) -> Lz4Flushed:
  match fuel:
    case 0n:
      match c:
        case Lz4Cut{raw, rest, full}:
          Lz4Flushed{B.append(raw, rest), hist, acc}
    case 1n+f:
      match c:
        case Lz4Cut{+raw, rest, full}:
          match full:
            case True{}:
              wr.flush(f, wr.split(rest, bsz), opts, bsz, wr.keep(B.append(hist, raw)), B.append(acc, wr.block(opts, hist, raw)))
            case False{}:
              Lz4Flushed{B.append(raw, rest), hist, acc}

def wr.fed(r: Lz4Flushed, opts: Lz4FrameOptions, content: List<&2, U32>) -> Lz4Written:
  match r:
    case Lz4Flushed{pending, hist, bytes}:
      Lz4Written{Lz4Writer{opts, pending, hist, content}, B.Octets.of_list(bytes)}

# feed the next piece of the content
def frame_feed(w: Lz4Writer, o: B.Octets) -> Lz4Written:
  match w:
    case Lz4Writer{+opts, pending, hist, content}:
      +xs = B.Octets.to_list(o)
      +p = B.append(pending, xs)
      +bsz = wr.opts.bmax(opts)
      wr.fed(wr.flush(Nat.add(B.len(p), 1n), wr.split(p, bsz), opts, bsz, hist, Nil{}), opts, K.blk.push(xs, content))

def wr.tail(empty: Bool, +opts: Lz4FrameOptions, +hist: List<&2, U32>, +pending: List<&2, U32>) -> List<&2, U32>:
  match empty:
    case True{}:
      Nil{}
    case False{}:
      wr.block(opts, hist, pending)

# the rest of the frame: the last block, the end mark, the content checksum
def frame_finish(w: Lz4Writer) -> B.Octets:
  match w:
    case Lz4Writer{+opts, +pending, hist, content}:
      B.Octets.of_list(B.append(wr.tail(List.is_empty(&2, U32, pending), opts, hist, pending), wr.end(opts, K.blk.rev(content))))

def wr.feed_all(ps: List<&2, B.Octets>, r: Lz4Written, acc: B.Octets) -> B.Octets:
  match ps:
    case Nil{}:
      match r:
        case Lz4Written{w, bytes}:
          B.Octets.append(B.Octets.append(acc, bytes), frame_finish(w))
    case Con{p, t}:
      match r:
        case Lz4Written{w, bytes}:
          wr.feed_all(t, frame_feed(w, p), B.Octets.append(acc, bytes))

# the frame a writer gives for content fed in these pieces
def frame_stream(opts: Lz4FrameOptions, pieces: List<&2, B.Octets>) -> B.Octets:
  wr.feed_all(pieces, frame_start(opts), B.Octets.empty())
