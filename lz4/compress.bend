# bend-osdev-lz4, compression: a block compressor and a frame writer, from the
# LZ4 project's specifications (lz4_Block_format.md, lz4_Frame_format.md).
#
# The block compressor is a greedy LZ77 matcher with a single-entry hash
# table: at each position it looks up the last position whose next four bytes
# hashed the same, extends the match as far as the end-of-block rules allow
# (a match starts 12 bytes or more before the end and ends 5 bytes or more
# before it), and emits literals and matches as LZ4 sequences.
#
# The matcher is a choice (Lz4Matcher): this greedy one, or LZ4HC's
# hash-chain search (hc.bend) at a level. Both write ordinary LZ4 blocks.
#
# block_compress checks its own output: it decodes it and, should that not
# give the input back, answers the literal-only block instead. So a law can
# say, for every input, that what it writes decodes to the input.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./block.bend as K
import ./frame.bend as F
import ./seq.bend as S
import ./hc.bend as H

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

def cmp.done(lits: List<&2, U32>, cur: List<&2, U32>, out: List<&2, U32>) -> Lz4Enc:
  Lz4EncDone{S.seq.last(B.rev_onto(lits, cur), out)}

# a match of ml bytes, or (shorter than 4) one more literal
def cmp.emit(ok: Bool, tab: Array<Lz4Cand>, +cur: List<&2, U32>, +i: U32, +ml: Nat, +off: U32, lim: U32, end: U32, +lits: List<&2, U32>, out: List<&2, U32>) -> Lz4Enc:
  match ok:
    case True{}:
      Lz4EncGo{tab, B.drop(ml, cur), U32.add(i, U32.from_nat(ml)), lim, end, Nil{}, S.seq.push(K.blk.rev(lits), off, ml, out)}
    case False{}:
      match cur:
        case Nil{}:
          cmp.done(lits, Nil{}, out)
        case Con{b, t}:
          Lz4EncGo{tab, t, U32.add(i, 1), lim, end, Con{b, lits}, out}

def cmp.found(valid: Bool, +suf: List<&2, U32>, +cur: List<&2, U32>, +k: U32) -> Nat:
  match valid:
    case True{}:
      S.seq.common(suf, True{}, cur, k, 0n)
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
          K.blk.rev(S.seq.last(B.rev_onto(lits, cur), out))
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
      +all = B.append.fast(dict, xs)
      +base = B.len.fast(dict)
      tab = cmp.seed(base, Array.new(Lz4Cand, 12n, Lz4Cand{0, Nil{}}), all, 0)
      cmp.loop(Nat.add(B.len.fast(xs), 1n), Lz4EncGo{tab, B.drop(base, all), U32.from_nat(base), U32.sub(total, 12), U32.sub(total, 5), Nil{}, Nil{}})
    case False{}:
      K.blk.rev(S.seq.last(xs, Nil{}))

# the block for xs, after the history dict (at most its last 65535 bytes)
def cmp.block(+dict: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  +d = B.drop(Nat.sub(B.len.fast(dict), 65535n), dict)
  +total = U32.from_nat(Nat.add(B.len.fast(d), B.len.fast(xs)))
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

# the same bytes, in the same order; live: the bytes so far agree (a tail
# call, so it runs on lists of any length)
def cmp.same.go(xs: List<&2, U32>, ys: List<&2, U32>, live: Bool) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      live
    case Con{a, s} Con{b, t}:
      cmp.same.go(s, t, Bool.and(live, cmp.u32_eq(a, b)))
    case _ _:
      False{}

def cmp.same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  cmp.same.go(xs, ys, True{})

def cmp.keep(ok: Bool, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match ok:
    case True{}:
      c
    case False{}:
      K.block_literals(o)

# the block c if it decodes to o, else the literal-only block. r is the
# decoder's own answer (its output list), compared with o as it comes out,
# without building the decoded bytes as Octets
def cmp.check(r: Result<&2, &2, K.Lz4Error, K.Lz4Out>, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match r:
    case Fail{e}:
      K.block_literals(o)
    case Done{K.Lz4Out{acc, room}}:
      cmp.keep(cmp.same(K.blk.rev(acc), B.Octets.to_list(o)), c, o)

# the same after a dictionary of k bytes, which the decoder's output starts
# with
def cmp.check_dict(r: Result<&2, &2, K.Lz4Error, K.Lz4Out>, +k: Nat, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match r:
    case Fail{e}:
      K.block_literals(o)
    case Done{K.Lz4Out{acc, room}}:
      cmp.keep(cmp.same(B.drop(k, K.blk.rev(acc)), B.Octets.to_list(o)), c, o)

# The public interface: blocks

# the matcher's block for o, unchecked
def block_compress_unchecked(o: B.Octets) -> B.Octets:
  B.Octets.of_list(cmp.block(Nil{}, B.Octets.to_list(o)))

# a block for o: the matcher's, checked by decoding it
def block_compress(+o: B.Octets) -> B.Octets:
  +c = block_compress_unchecked(o)
  cmp.check(K.blk.run(B.Octets.to_list(c), Nil{}, B.Octets.len(o)), c, o)

# a block for o that may refer back into dict (the bytes before it), checked
def block_compress_dict(+dict: B.Octets, +o: B.Octets) -> B.Octets:
  +c = B.Octets.of_list(cmp.block(B.Octets.to_list(dict), B.Octets.to_list(o)))
  cmp.check_dict(K.blk.run(B.Octets.to_list(c), K.blk.rev(B.Octets.to_list(dict)), B.Octets.len(o)), B.Octets.len(dict), c, o)

# The matchers

# which matcher writes the blocks: the greedy one above (fast), or LZ4HC's
# hash-chain search with these parameters
type Lz4Matcher is Data:
  Lz4MatchFast{}
  Lz4MatchHC{params: H.Lz4HcParams}

# the greedy matcher, which block_compress uses
def Lz4Matcher.default() -> Lz4Matcher:
  Lz4MatchFast{}

# LZ4HC at a level (3 to 12; below 3 is 3, above 12 is 12)
def Lz4Matcher.hc(+level: U32) -> Lz4Matcher:
  Lz4MatchHC{H.Lz4HcParams.level(level)}

# the matcher's block for xs after the history dict, as a byte list
def cmp.block_with(m: Lz4Matcher, +dict: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Lz4MatchFast{}:
      cmp.block(dict, xs)
    case Lz4MatchHC{p}:
      H.hc.block(p, dict, xs)

# this matcher's block for o, unchecked
def block_compress_unchecked_with(m: Lz4Matcher, o: B.Octets) -> B.Octets:
  B.Octets.of_list(cmp.block_with(m, Nil{}, B.Octets.to_list(o)))

# a block for o: this matcher's, checked by decoding it
def block_compress_with(m: Lz4Matcher, +o: B.Octets) -> B.Octets:
  +c = block_compress_unchecked_with(m, o)
  cmp.check(K.blk.run(B.Octets.to_list(c), Nil{}, B.Octets.len(o)), c, o)

# a block for o that may refer back into dict, by this matcher, checked
def block_compress_dict_with(m: Lz4Matcher, +dict: B.Octets, +o: B.Octets) -> B.Octets:
  +c = B.Octets.of_list(cmp.block_with(m, B.Octets.to_list(dict), B.Octets.to_list(o)))
  cmp.check_dict(K.blk.run(B.Octets.to_list(c), K.blk.rev(B.Octets.to_list(dict)), B.Octets.len(o)), B.Octets.len(dict), c, o)

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
# only); matcher: what finds the matches
type Lz4FrameOptions is Data:
  Lz4FrameOptions{block_max: Lz4BlockMax, block_size: U32, indep: Bool, block_sum: Bool, content_sum: Bool, content_size: Bool, matcher: Lz4Matcher}

# what the lz4 tool writes by default: 64 KB independent blocks and a
# content checksum (FLG 0x64, BD 0x40), the greedy matcher
def Lz4FrameOptions.default() -> Lz4FrameOptions:
  Lz4FrameOptions{Lz4Max64KB{}, 65536, True{}, False{}, True{}, False{}, Lz4MatchFast{}}

# the same options with another matcher
def Lz4FrameOptions.with_matcher(opts: Lz4FrameOptions, m: Lz4Matcher) -> Lz4FrameOptions:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize, old}:
      Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize, m}

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
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize, matcher}:
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
      B.append(B.le32(U32.from_nat(B.len.fast(comp))), B.append.fast(comp, wr.sum(bsum, comp)))
    case False{}:
      B.append(B.le32(U32.or(U32.from_nat(B.len.fast(raw)), 2147483648)), B.append.fast(raw, wr.sum(bsum, raw)))

# block_compress_dict on lists: the same bytes, without the conversions to
# and from Octets (which cost memory on large blocks)
def wr.literals(+xs: List<&2, U32>) -> List<&2, U32>:
  B.append.fast(K.lit.h0(B.len.fast(xs)), xs)

def wr.pick(ok: Bool, +c: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      c
    case False{}:
      wr.literals(xs)

def wr.checked.at(r: Result<&2, &2, K.Lz4Error, K.Lz4Out>, +k: Nat, +c: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Fail{e}:
      wr.literals(xs)
    case Done{K.Lz4Out{acc, room}}:
      wr.pick(cmp.same(B.drop(k, K.blk.rev(acc)), xs), c, xs)

def wr.checked(m: Lz4Matcher, +hist: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  +c = cmp.block_with(m, hist, xs)
  wr.checked.at(K.blk.run(c, K.blk.rev(hist), B.len.fast(xs)), B.len.fast(hist), c, xs)

def wr.comp(indep: Bool, m: Lz4Matcher, +hist: List<&2, U32>, +raw: List<&2, U32>) -> List<&2, U32>:
  match indep:
    case True{}:
      wr.checked(m, Nil{}, raw)
    case False{}:
      wr.checked(m, hist, raw)

# the bytes of one block of raw, after the history hist
def wr.block(+opts: Lz4FrameOptions, +hist: List<&2, U32>, +raw: List<&2, U32>) -> List<&2, U32>:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize, matcher}:
      +comp = wr.comp(indep, matcher, hist, raw)
      wr.stored(Nat.is_lt(B.len.fast(comp), B.len.fast(raw)), bsum, comp, raw)

def wr.keep(+xs: List<&2, U32>) -> List<&2, U32>:
  B.drop(Nat.sub(B.len.fast(xs), 65535n), xs)

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
# the rest; acc: the frame's bytes so far, reversed
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
              wr.blocks(f, wr.split(rest, bsz), opts, bsz, wr.keep(B.append.fast(hist, raw)), B.rev_onto(wr.block(opts, hist, raw), acc))

def wr.end(opts: Lz4FrameOptions, content: List<&2, U32>) -> List<&2, U32>:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize, matcher}:
      B.append(B.le32(0), wr.sum(csum, content))

def wr.size_of(on: Bool, +xs: List<&2, U32>) -> Maybe<&2, Nat>:
  match on:
    case True{}:
      Some{B.len.fast(xs)}
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
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize, matcher}:
      wr.cut(wr.bmax(bmax), bsize)

def wr.opts.csize(opts: Lz4FrameOptions) -> Bool:
  match opts:
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize, matcher}:
      csize

# The public interface: frames

# a frame holding o
def frame_compress(+opts: Lz4FrameOptions, o: B.Octets) -> B.Octets:
  +xs = B.Octets.to_list(o)
  +hd = wr.header(opts, wr.size_of(wr.opts.csize(opts), xs))
  +bsz = wr.opts.bmax(opts)
  B.Octets.of_list(B.append(hd, B.rev_onto(wr.blocks(Nat.add(B.len.fast(xs), 1n), wr.split(xs, bsz), opts, bsz, Nil{}, Nil{}), wr.end(opts, xs))))

# a frame holding o, with the default options
def compress(o: B.Octets) -> B.Octets:
  frame_compress(Lz4FrameOptions.default(), o)

# a frame holding o, with the default options but LZ4HC at this level
def compress_hc(+level: U32, o: B.Octets) -> B.Octets:
  frame_compress(Lz4FrameOptions.with_matcher(Lz4FrameOptions.default(), Lz4Matcher.hc(level)), o)

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
    case Lz4FrameOptions{bmax, bsize, indep, bsum, csum, csize, matcher}:
      Lz4FrameOptions{bmax, bsize, indep, bsum, csum, False{}, matcher}

def frame_start(opts: Lz4FrameOptions) -> Lz4Written:
  +o = wr.no_size(opts)
  Lz4Written{Lz4Writer{o, Nil{}, Nil{}, Nil{}}, B.Octets.of_list(wr.header(o, None{}))}

type Lz4Flushed is Data:
  Lz4Flushed{pending: List<&2, U32>, hist: List<&2, U32>, bytes: List<&2, U32>}

# the full blocks go out; fewer than a block's bytes stay. c: the next
# block, if full, and the rest; acc: the bytes out so far, reversed
def wr.flush(fuel: Nat, c: Lz4Cut, +opts: Lz4FrameOptions, +bsz: U32, +hist: List<&2, U32>, acc: List<&2, U32>) -> Lz4Flushed:
  match fuel:
    case 0n:
      match c:
        case Lz4Cut{raw, rest, full}:
          Lz4Flushed{B.append.fast(raw, rest), hist, acc}
    case 1n+f:
      match c:
        case Lz4Cut{+raw, rest, full}:
          match full:
            case True{}:
              wr.flush(f, wr.split(rest, bsz), opts, bsz, wr.keep(B.append.fast(hist, raw)), B.rev_onto(wr.block(opts, hist, raw), acc))
            case False{}:
              Lz4Flushed{B.append.fast(raw, rest), hist, acc}

def wr.fed(r: Lz4Flushed, opts: Lz4FrameOptions, content: List<&2, U32>) -> Lz4Written:
  match r:
    case Lz4Flushed{pending, hist, bytes}:
      Lz4Written{Lz4Writer{opts, pending, hist, content}, B.Octets.of_list(B.rev(bytes))}

# feed the next piece of the content
def frame_feed(w: Lz4Writer, o: B.Octets) -> Lz4Written:
  match w:
    case Lz4Writer{+opts, pending, hist, content}:
      +xs = B.Octets.to_list(o)
      +p = B.append.fast(pending, xs)
      +bsz = wr.opts.bmax(opts)
      wr.fed(wr.flush(Nat.add(B.len.fast(p), 1n), wr.split(p, bsz), opts, bsz, hist, Nil{}), opts, K.blk.push(xs, content))

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
      B.Octets.of_list(B.append.fast(wr.tail(List.is_empty(&2, U32, pending), opts, hist, pending), wr.end(opts, K.blk.rev(content))))

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
