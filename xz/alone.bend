# bend-osdev-xz: the legacy .lzma format ("LZMA alone"): its 13-byte header,
# both ways, and decoding, one-shot and streaming.
#
# Written from the description of the .lzma format in the LZMA SDK
# ("lzma-specification" and lzma.txt, Igor Pavlov) and in XZ Utils'
# documentation (lzma-file-format.txt; xz(1) for the limits on lc and lp),
# all public domain. A .lzma file is
#
#   1 byte    the properties, (pb * 5 + lp) * 9 + lc
#   4 bytes   the dictionary size, little-endian
#   8 bytes   the uncompressed size, little-endian; all ones means unknown
#   then one LZMA stream, ending with the end marker if the size is unknown,
#   and with or without it if the size is known
#
# lc + lp must not exceed 4 and pb must not exceed 4 (xz(1) documents these
# limits; the literal probabilities fit the decoder's array only within
# them). A dictionary size below 4096 is taken as 4096, as the LZMA SDK
# specifies. Nothing may follow the stream.
#
# The LZMA decoding itself is lzma.bend's, through its interface: a step
# decodes one byte (or the end marker), and this file checks after each step
# whether the stream went wrong or ended. The dictionary array grows as the
# output does (lzma.bend's XzLzma.dict_grow), as in LZMA2.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./rangecoder.bend as R
import ./lzma.bend as L

# The header

# lc, lp and pb; the dictionary size; the uncompressed size, None if unknown
type XzAloneHeader is Data:
  XzAloneHeader{lc: Nat, lp: Nat, pb: Nat, dict_size: U32, size: Maybe<&2, W.W64>}

def XzAloneHeader.size(h: XzAloneHeader) -> Maybe<&2, W.W64>:
  match h:
    case XzAloneHeader{lc, lp, pb, d, s}:
      s

# the properties byte of lc, lp and pb
def XzAlone.props(+lc: Nat, +lp: Nat, +pb: Nat) -> U32:
  U32.from_nat(Nat.add(Nat.mul(Nat.add(Nat.mul(pb, 5n), lp), 9n), lc))

# whether a properties byte is valid: below 225 (so pb at most 4), with lc +
# lp at most 4
def XzAlone.props_valid(+b: U32) -> Bool:
  Bool.and(U32.is_lt(b, 225), U32.is_le(U32.add(U32.mod(b, 9), U32.mod(U32.div(b, 9), 5)), 4))

def XzAl.size_ok(s: Maybe<&2, W.W64>) -> Bool:
  match s:
    case None{}:
      True{}
    case Some{w}:
      Bool.not(W.W64.is_eq(w, W.W64.max()))

# whether a header can be written and read back: lc + lp at most 4, pb at
# most 4, and a known size other than all ones (which means unknown)
def XzAloneHeader.valid(h: XzAloneHeader) -> Bool:
  match h:
    case XzAloneHeader{+lc, +lp, +pb, d, s}:
      Bool.and(Nat.is_le(Nat.add(lc, lp), 4n), Bool.and(Nat.is_le(pb, 4n), XzAl.size_ok(s)))

def XzAl.size_field(s: Maybe<&2, W.W64>) -> W.W64:
  match s:
    case None{}:
      W.W64.max()
    case Some{w}:
      w

# the header's 13 bytes
def XzAlone.header_bytes(h: XzAloneHeader) -> B.Octets:
  match h:
    case XzAloneHeader{lc, lp, pb, d, s}:
      B.Octets.of_list(Con{XzAlone.props(lc, lp, pb), B.append(B.le32(d), B.le64(XzAl.size_field(s)))})

def XzAl.size_of.pick(all: Bool, +w: W.W64) -> Maybe<&2, W.W64>:
  match all:
    case True{}:
      None{}
    case False{}:
      Some{w}

def XzAl.size_of(+w: W.W64) -> Maybe<&2, W.W64>:
  XzAl.size_of.pick(W.W64.is_eq(w, W.W64.max()), w)

def XzAl.parse.got(+lc: Nat, +lp: Nat, +pb: Nat, d: Maybe<&2, U32>, s: Maybe<&2, W.W64>) -> Result<&2, &2, E.XzError, XzAloneHeader>:
  match d s:
    case Some{dv} Some{+sv}:
      Done{XzAloneHeader{lc, lp, pb, dv, XzAl.size_of(sv)}}
    case _ _:
      Fail{E.XzTruncated{}}

# the dictionary size and the uncompressed size, after the properties byte
def XzAl.parse.fields(+lc: Nat, +lp: Nat, +pb: Nat, +xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzAloneHeader>:
  XzAl.parse.got(lc, lp, pb, B.le32_at(xs, 0n), B.le64_at(xs, 4n))

def XzAl.parse.props(ok: Bool, +b: U32, +xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzAloneHeader>:
  match ok:
    case True{}:
      XzAl.parse.fields(U32.to_nat(U32.mod(b, 9)), U32.to_nat(U32.mod(U32.div(b, 9), 5)), U32.to_nat(U32.div(b, 45)), xs)
    case False{}:
      Fail{E.XzBadFilterProps{}}

# the header at the front of a byte list (each element a byte)
def XzAl.parse(xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzAloneHeader>:
  match xs:
    case Nil{}:
      Fail{E.XzTruncated{}}
    case Con{+b, t}:
      XzAl.parse.props(XzAlone.props_valid(b), b, t)

# the header at the front of o: XzBadFilterProps for a bad properties byte,
# XzTruncated if o is shorter than 13 bytes
def XzAlone.header(o: B.Octets) -> Result<&2, &2, E.XzError, XzAloneHeader>:
  XzAl.parse(B.Octets.to_list(o))

# whether o's length is the declared size (any length, if it is unknown)
def XzAlone.has_size(+o: B.Octets, s: Maybe<&2, W.W64>) -> Bool:
  match s:
    case None{}:
      True{}
    case Some{w}:
      W.W64.is_eq(W.W64.from_nat(B.Octets.len(o)), w)

# The parameters: the most output allowed

type XzAloneParams is Data:
  XzAloneParams{max_out: U32}

# 16 MiB, as XzParams.default()
def XzAloneParams.default() -> XzAloneParams:
  XzAloneParams{16777216}

def XzAloneParams.max_out(p: XzAloneParams) -> U32:
  match p:
    case XzAloneParams{m}:
      m

# The decoder

# how far the stream may go: exactly n bytes (the size is known), or up to
# max (it is not)
type XzAlLimit is Data:
  XzAlKnown{n: U32}
  XzAlUpTo{max: U32}

def XzAl.limit.pick(fits: Bool, +n: U32) -> Result<&2, &2, E.XzError, XzAlLimit>:
  match fits:
    case True{}:
      Done{XzAlKnown{n}}
    case False{}:
      Fail{E.XzOutputTooLarge{}}

def XzAl.limit(s: Maybe<&2, W.W64>, +max: U32) -> Result<&2, &2, E.XzError, XzAlLimit>:
  match s:
    case None{}:
      Done{XzAlUpTo{max}}
    case Some{+w}:
      XzAl.limit.pick(Bool.and(U32.is_eq(W.W64.hi(w), 0), U32.is_le(W.W64.lo(w), max)), W.W64.lo(w))

def XzAl.limit.top(l: XzAlLimit) -> U32:
  match l:
    case XzAlKnown{n}:
      n
    case XzAlUpTo{m}:
      m

# where decoding stands: going on, the end marker read, or gone wrong (an
# impossible distance, or the range decoder saw corruption or ran out)
type XzAlState is Data:
  XzAlGo{}
  XzAlEnd{}
  XzAlBad{}

type XzAlRun is Type:
  XzAlRun{lz: L.XzLzma, st: XzAlState}

# the dictionary array's depth now and at most, and the limit
type XzAlCtl is Data:
  XzAlCtl{depth: Nat, maxdepth: Nat, limit: XzAlLimit}

# the run, its control, and whether it may go on
type XzAlBatch is Type:
  XzAlBatch{run: XzAlRun, ctl: XzAlCtl, more: Bool}

def XzAl.check.pick(ok: Bool, rd: R.XzRd, dict: Array<U32>, regs: L.XzLzRegs, out: List<&2, U32>) -> XzAlRun:
  match ok:
    case True{}:
      XzAlRun{L.XzLzma{rd, dict, regs, out}, XzAlGo{}}
    case False{}:
      XzAlRun{L.XzLzma{rd, dict, regs, out}, XzAlBad{}}

def XzAl.check.rd(r: R.XzRdOk, dict: Array<U32>, regs: L.XzLzRegs, out: List<&2, U32>) -> XzAlRun:
  R.XzRdOk{rd, ok} = r
  XzAl.check.pick(ok, rd, dict, regs, out)

def XzAl.check.end(end: Bool, rd: R.XzRd, dict: Array<U32>, regs: L.XzLzRegs, out: List<&2, U32>) -> XzAlRun:
  match end:
    case True{}:
      XzAlRun{L.XzLzma{rd, dict, regs, out}, XzAlEnd{}}
    case False{}:
      XzAlRun{L.XzLzma{rd, dict, regs, out}, XzAlBad{}}

def XzAl.check.regs(ok: Bool, +end: Bool, rd: R.XzRd, dict: Array<U32>, regs: L.XzLzRegs, out: List<&2, U32>) -> XzAlRun:
  match ok:
    case True{}:
      XzAl.check.rd(R.XzRd.ok(rd), dict, regs, out)
    case False{}:
      XzAl.check.end(end, rd, dict, regs, out)

# where the decoder stands after a step
def XzAl.check(s: L.XzLzma) -> XzAlRun:
  L.XzLzma{rd, dict, +regs, out} = s
  XzAl.check.regs(L.XzLzRegs.ok(regs), L.XzLzRegs.at_end(regs), rd, dict, regs, out)

# at most n steps, stopping at the end marker or at corruption
def XzAl.steps(n: Nat, r: XzAlRun) -> XzAlRun:
  match n:
    case 0n:
      r
    case 1n+m:
      match r:
        case XzAlRun{lz, st}:
          match st:
            case XzAlGo{}:
              XzAl.steps(m, XzAl.check(L.XzLzma.step(lz)))
            case XzAlEnd{}:
              XzAlRun{lz, XzAlEnd{}}
            case XzAlBad{}:
              XzAlRun{lz, XzAlBad{}}

def XzAl.is_go(+st: XzAlState) -> Bool:
  match st:
    case XzAlGo{}:
      True{}
    case _:
      False{}

def XzAl.batch.fin(r: XzAlRun, +ctl: XzAlCtl) -> XzAlBatch:
  XzAlRun{lz, +st} = r
  XzAlBatch{XzAlRun{lz, st}, ctl, XzAl.is_go(st)}

# b steps (b at most 65536), the dictionary grown for them first
def XzAl.batch(r: XzAlRun, +ctl: XzAlCtl, +b: U32) -> XzAlBatch:
  XzAlRun{lz, +st} = r
  L.XzLzma{rd, dict, +regs, out} = lz
  match ctl:
    case XzAlCtl{+depth, +maxd, limit}:
      +nd = L.XzLzma.dict_want(depth, maxd, L.XzLzRegs.pos(regs), b)
      XzAl.batch.fin(XzAl.steps(U32.to_nat(b), XzAlRun{L.XzLzma{rd, L.XzLzma.dict_grow(dict, depth, nd), regs, out}, st}), XzAlCtl{nd, maxd, limit})

def XzAl.run.pick(go: Bool, r: XzAlRun, +ctl: XzAlCtl, more: Bool, +todo: U32) -> XzAlBatch:
  match go:
    case True{}:
      XzAl.batch(r, ctl, U32.min(todo, 65536))
    case False{}:
      XzAlBatch{r, ctl, more}

def XzAl.run.step(bt: XzAlBatch, +todo: U32) -> XzAlBatch:
  XzAlBatch{r, ctl, +more} = bt
  XzAl.run.pick(Bool.and(more, U32.is_lt(0, todo)), r, ctl, more, todo)

# todo more steps at most, in batches of 65536
def XzAl.run(fuel: Nat, bt: XzAlBatch, +todo: U32) -> XzAlBatch:
  match fuel:
    case 0n:
      bt
    case 1n+f:
      XzAl.run(f, XzAl.run.step(bt, todo), U32.sub(todo, U32.min(todo, 65536)))

def XzAl.run.all(bt: XzAlBatch, +todo: U32) -> XzAlBatch:
  XzAl.run(1n+U32.to_nat(U32.shrn(todo, 16n)), bt, todo)

# The end: what the decoder answers once it has all its input

# the output, if the range decoder read all its input and ended cleanly
def XzAl.fin.rd(r: Array<U32> & Bool, out: List<&2, U32>) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  (probs, ok) = r
  match ok:
    case True{}:
      Done{out}
    case False{}:
      Fail{E.XzCorruptLzma{}}

def XzAl.fin.left(r: R.XzRdLeft, out: List<&2, U32>) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  R.XzRdLeft{rd, left} = r
  match left:
    case 0n:
      XzAl.fin.rd(R.XzRd.finish(rd), out)
    case 1n+k:
      Fail{E.XzTrailingData{}}

# the stream ended (after the end marker, or at its known size): nothing may
# follow, and the range decoder must end at 0
def XzAl.fin(lz: L.XzLzma) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  L.XzLzma{rd, dict, regs, out} = lz
  XzAl.fin.left(R.XzRd.left(rd), out)

def XzAl.bad.left(r: R.XzRdLeft) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  R.XzRdLeft{rd, left} = r
  match left:
    case 0n:
      Fail{E.XzTruncated{}}
    case 1n+k:
      Fail{E.XzCorruptLzma{}}

# corruption: XzTruncated if the input ran out, else XzCorruptLzma
def XzAl.bad(lz: L.XzLzma) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  L.XzLzma{rd, dict, regs, out} = lz
  XzAl.bad.left(R.XzRd.left(rd))

# one more symbol, which must be the end marker; tl: what to answer if it is
# an ordinary symbol
def XzAl.last.st(st: XzAlState, +tl: E.XzError, lz: L.XzLzma) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  match st:
    case XzAlEnd{}:
      XzAl.fin(lz)
    case XzAlGo{}:
      Fail{tl}
    case XzAlBad{}:
      XzAl.bad(lz)

def XzAl.last.pick(r: XzAlRun, +tl: E.XzError) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  XzAlRun{lz, st} = r
  XzAl.last.st(st, tl, lz)

def XzAl.last(lz: L.XzLzma, +tl: E.XzError) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  XzAl.last.pick(XzAl.check(L.XzLzma.step(lz)), tl)

# at the known size: the end, or the end marker next
def XzAl.known.left(r: R.XzRdLeft, dict: Array<U32>, regs: L.XzLzRegs, out: List<&2, U32>) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  R.XzRdLeft{rd, left} = r
  match left:
    case 0n:
      XzAl.fin(L.XzLzma{rd, dict, regs, out})
    case 1n+k:
      XzAl.last(L.XzLzma{rd, dict, regs, out}, E.XzCorruptLzma{})

def XzAl.known.at(clean: Bool, lz: L.XzLzma) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  match clean:
    case True{}:
      L.XzLzma{rd, dict, regs, out} = lz
      XzAl.known.left(R.XzRd.left(rd), dict, regs, out)
    case False{}:
      Fail{E.XzCorruptLzma{}}

# the stream reached its limit still going: at a known size no match may run
# past it; past the maximum only the end marker may come
def XzAl.full(+limit: XzAlLimit, lz: L.XzLzma) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  match limit:
    case XzAlKnown{n}:
      L.XzLzma{rd, dict, +regs, out} = lz
      XzAl.known.at(U32.is_eq(L.XzLzRegs.pending(regs), 0), L.XzLzma{rd, dict, regs, out})
    case XzAlUpTo{m}:
      XzAl.last(lz, E.XzOutputTooLarge{})

# the end marker before the known size is corruption
def XzAl.ended(+limit: XzAlLimit, lz: L.XzLzma) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  match limit:
    case XzAlKnown{n}:
      Fail{E.XzCorruptLzma{}}
    case XzAlUpTo{m}:
      XzAl.fin(lz)

def XzAl.close.st(st: XzAlState, +limit: XzAlLimit, lz: L.XzLzma) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  match st:
    case XzAlGo{}:
      XzAl.full(limit, lz)
    case XzAlEnd{}:
      XzAl.ended(limit, lz)
    case XzAlBad{}:
      XzAl.bad(lz)

def XzAl.close.go(r: XzAlRun, +ctl: XzAlCtl) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  XzAlRun{lz, st} = r
  match ctl:
    case XzAlCtl{depth, maxd, +limit}:
      XzAl.close.st(st, limit, lz)

def XzAl.close.at(bt: XzAlBatch) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  XzAlBatch{r, ctl, more} = bt
  XzAl.close.go(r, ctl)

def XzAl.pos(r: XzAlRun) -> XzAlRun & U32:
  XzAlRun{lz, st} = r
  L.XzLzma{rd, dict, +regs, out} = lz
  (XzAlRun{L.XzLzma{rd, dict, regs, out}, st}, L.XzLzRegs.pos(regs))

def XzAl.close.todo(rp: XzAlRun & U32, +ctl: XzAlCtl, more: Bool) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  (r, +pos) = rp
  match ctl:
    case XzAlCtl{depth, maxd, +limit}:
      XzAl.close.at(XzAl.run.all(XzAlBatch{r, ctl, more}, U32.sub(XzAl.limit.top(limit), pos)))

# all the input is in: decode to the end, and answer the output not yet
# answered (reversed)
def XzAl.close(bt: XzAlBatch) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  XzAlBatch{r, ctl, more} = bt
  XzAl.close.todo(XzAl.pos(r), ctl, more)

# Starting: the header read, the data from its first byte on (5 bytes at
# least: the range decoder's start)

def XzAl.ds(+d: U32) -> U32:
  L.XzLz.sel(U32.is_lt(d, 4096), 4096, d)

def XzAl.begin.go(+lc: Nat, +lp: Nat, +pb: Nat, +ds: U32, +limit: XzAlLimit, data: List<&2, U32>) -> XzAlBatch:
  +k = L.XzLzma.dict_depth(U32.min(U32.min(ds, XzAl.limit.top(limit)), 2147483648))
  +regs = L.XzLzRegs.set_props(L.XzLzRegs.start(U32.min(ds, U32.shln(1, k))), lc, lp, pb)
  +d0 = Nat.min(k, 12n)
  XzAl.batch.fin(XzAl.check.rd(R.XzRd.ok(R.XzRd.start(R.XzRd.fresh(), data)), Array.new(U32, d0, 0), regs, Nil{}), XzAlCtl{d0, k, limit})

def XzAl.begin.lim(r: Result<&2, &2, E.XzError, XzAlLimit>, +h: XzAloneHeader, data: List<&2, U32>) -> Result<&2, &1, E.XzError, XzAlBatch>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+limit}:
      match h:
        case XzAloneHeader{+lc, +lp, +pb, +d, s}:
          Done{XzAl.begin.go(lc, lp, pb, XzAl.ds(d), limit, data)}

def XzAl.begin(+h: XzAloneHeader, +p: XzAloneParams, data: List<&2, U32>) -> Result<&2, &1, E.XzError, XzAlBatch>:
  XzAl.begin.lim(XzAl.limit(XzAloneHeader.size(h), XzAloneParams.max_out(p)), h, data)

# Whether xs has at least n bytes
def XzAl.has(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match xs:
        case Nil{}:
          False{}
        case Con{h, t}:
          XzAl.has(p, t)

def XzAl.body.out(r: Result<&2, &2, E.XzError, List<&2, U32>>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{out}:
      Done{B.Octets.of_list(List.reverse(&2, U32, out))}

def XzAl.body.ran(r: Result<&2, &1, E.XzError, XzAlBatch>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bt}:
      XzAl.body.out(XzAl.close(bt))

def XzAl.body.go(ok: Bool, +h: XzAloneHeader, +p: XzAloneParams, +data: List<&2, U32>) -> Result<&2, &2, E.XzError, B.Octets>:
  match ok:
    case True{}:
      XzAl.body.ran(XzAl.begin(h, p, data))
    case False{}:
      Fail{E.XzTruncated{}}

# the stream after the header, decoded whole
def XzAl.body(+h: XzAloneHeader, +p: XzAloneParams, +data: List<&2, U32>) -> Result<&2, &2, E.XzError, B.Octets>:
  XzAl.body.go(XzAl.has(5n, data), h, p, data)

# the output, if its length is the declared size (a last guard: the decoder
# stops at the size already)
def XzAl.guard.pick(ok: Bool, +o: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match ok:
    case True{}:
      Done{o}
    case False{}:
      Fail{E.XzCorruptLzma{}}

def XzAl.guard(h: XzAloneHeader, r: Result<&2, &2, E.XzError, B.Octets>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+o}:
      XzAl.guard.pick(XzAlone.has_size(o, XzAloneHeader.size(h)), o)

def XzAl.decode.hdr(r: Result<&2, &2, E.XzError, XzAloneHeader>, +p: XzAloneParams, +xs: List<&2, U32>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+h}:
      XzAl.guard(h, XzAl.body(h, p, B.drop(13n, xs)))

# a whole .lzma file: its data, or the first failure
def XzAlone.decode(+p: XzAloneParams, +input: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  XzAl.decode.hdr(XzAlone.header(input), p, B.Octets.to_list(input))

# Streaming: the header is buffered until it and the range decoder's first
# 5 bytes are in; then each feed decodes as far as the input surely reaches
# (a symbol reads 48 bytes at most), and finish decodes the rest

type XzAloneDecoder is Type:
  XzAlHead{p: XzAloneParams, buf: List<&2, U32>}
  XzAlBody{bt: XzAlBatch}

type XzAloneFed is Type:
  XzAloneFed{dec: XzAloneDecoder, out: B.Octets}

def XzAlone.start(p: XzAloneParams) -> XzAloneDecoder:
  XzAlHead{p, Nil{}}

def XzAl.round.at(go: Bool, r: XzAlRun, +ctl: XzAlCtl, +s: U32) -> XzAlBatch:
  match go:
    case True{}:
      XzAl.run.all(XzAlBatch{r, ctl, True{}}, s)
    case False{}:
      XzAlBatch{r, ctl, False{}}

# one round: the steps the unread input surely covers, up to the limit
def XzAl.round.go(r: R.XzRdLeft, dict: Array<U32>, +regs: L.XzLzRegs, out: List<&2, U32>, +st: XzAlState, +ctl: XzAlCtl) -> XzAlBatch:
  R.XzRdLeft{rd, +left} = r
  match ctl:
    case XzAlCtl{depth, maxd, +limit}:
      +s = U32.min(U32.div(U32.from_nat(Nat.min(left, 4294967295n)), 48), U32.sub(XzAl.limit.top(limit), L.XzLzRegs.pos(regs)))
      XzAl.round.at(U32.is_lt(0, s), XzAlRun{L.XzLzma{rd, dict, regs, out}, st}, ctl, s)

def XzAl.round(bt: XzAlBatch) -> XzAlBatch:
  XzAlBatch{r, ctl, more} = bt
  XzAlRun{lz, +st} = r
  L.XzLzma{rd, dict, regs, out} = lz
  XzAl.round.go(R.XzRd.left(rd), dict, regs, out, st, ctl)

def XzAl.rounds(fuel: Nat, bt: XzAlBatch) -> XzAlBatch:
  match fuel:
    case 0n:
      bt
    case 1n+f:
      match bt:
        case XzAlBatch{r, ctl, more}:
          match more:
            case True{}:
              XzAl.rounds(f, XzAl.round(XzAlBatch{r, ctl, True{}}))
            case False{}:
              XzAlBatch{r, ctl, False{}}

# the output so far, handed out: the decoder keeps going with none
def XzAl.hand(bt: XzAlBatch) -> XzAloneFed:
  XzAlBatch{r, ctl, more} = bt
  XzAlRun{lz, +st} = r
  L.XzLzma{rd, dict, regs, out} = lz
  XzAloneFed{XzAlBody{XzAlBatch{XzAlRun{L.XzLzma{rd, dict, regs, Nil{}}, st}, ctl, XzAl.is_go(st)}}, B.Octets.of_list(List.reverse(&2, U32, out))}

# rounds until the input surely covers no more steps (each round makes a
# byte at least, so the limit + 1 rounds are enough)
def XzAl.decode_some(bt: XzAlBatch) -> XzAloneFed:
  XzAlBatch{r, +ctl, more} = bt
  match ctl:
    case XzAlCtl{depth, maxd, +limit}:
      XzAl.hand(XzAl.rounds(1n+U32.to_nat(XzAl.limit.top(limit)), XzAlBatch{r, ctl, more}))

def XzAl.feed.begun(r: Result<&2, &1, E.XzError, XzAlBatch>) -> Result<&2, &1, E.XzError, XzAloneFed>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bt}:
      Done{XzAl.decode_some(bt)}

def XzAl.feed.hdr(r: Result<&2, &2, E.XzError, XzAloneHeader>, +p: XzAloneParams, +buf: List<&2, U32>) -> Result<&2, &1, E.XzError, XzAloneFed>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+h}:
      XzAl.feed.begun(XzAl.begin(h, p, B.drop(13n, buf)))

def XzAl.feed.head(ready: Bool, +p: XzAloneParams, +buf: List<&2, U32>) -> Result<&2, &1, E.XzError, XzAloneFed>:
  match ready:
    case True{}:
      XzAl.feed.hdr(XzAl.parse(buf), p, buf)
    case False{}:
      Done{XzAloneFed{XzAlHead{p, buf}, B.Octets.empty()}}

def XzAl.feed.more(bt: XzAlBatch, xs: List<&2, U32>) -> XzAlBatch:
  XzAlBatch{r, ctl, more} = bt
  XzAlRun{lz, st} = r
  L.XzLzma{rd, dict, regs, out} = lz
  XzAlBatch{XzAlRun{L.XzLzma{R.XzRd.feed(rd, xs), dict, regs, out}, st}, ctl, more}

# more input; the answer holds the output decoded so far
def XzAlone.feed(d: XzAloneDecoder, input: B.Octets) -> Result<&2, &1, E.XzError, XzAloneFed>:
  match d:
    case XzAlHead{+p, buf}:
      +buf2 = B.append.fast(buf, B.Octets.to_list(input))
      XzAl.feed.head(XzAl.has(18n, buf2), p, buf2)
    case XzAlBody{bt}:
      Done{XzAl.decode_some(XzAl.feed.more(bt, B.Octets.to_list(input)))}

def XzAl.finish.hdr(r: Result<&2, &2, E.XzError, XzAloneHeader>, +p: XzAloneParams, +buf: List<&2, U32>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+h}:
      XzAl.body(h, p, B.drop(13n, buf))

# the end of the input: the rest of the output, or the failure
def XzAlone.finish(d: XzAloneDecoder) -> Result<&2, &2, E.XzError, B.Octets>:
  match d:
    case XzAlHead{+p, +buf}:
      XzAl.finish.hdr(XzAl.parse(buf), p, buf)
    case XzAlBody{bt}:
      XzAl.body.out(XzAl.close(bt))
