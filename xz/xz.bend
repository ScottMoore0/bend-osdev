# bend-osdev-xz: decompression of .xz files ("The .xz File Format", version
# 1.2.x, Lasse Collin and Igor Pavlov; public domain).
#
# An .xz file is one or more streams, each followed by stream padding (null
# bytes, a multiple of four). A stream is a header, blocks, an index and a
# footer; a block is a header, compressed data (LZMA2, possibly after delta
# filters), null padding to a multiple of four, and a check of the
# uncompressed data. The decoder checks every CRC32, every block check, the
# index against the blocks, the footer against the header and the index, and
# every padding byte, and stops at the first failure with an XzError naming
# it. It never answers more output than the caller's maximum.
#
# xz_decode is one-shot. XzDecoder.start / feed / finish is the same decoder
# in pieces: feed answers the output decoded so far, finish says whether the
# input ended where an .xz file may end. Output is released a chunk at a time,
# before the block's check is verified, so a caller that must not act on
# unverified data should use xz_decode, which answers nothing on failure.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./container.bend as C
import ./integrity.bend as I
import ./lzma2.bend as L2
import ./delta.bend as D

# The decoder's parameters: the most output it may produce (so at most
# 2^32 - 1 bytes)
type XzParams is Data:
  XzParams{max_out: U32}

# 16 MiB of output at most
def XzParams.default() -> XzParams:
  XzParams{16777216}

def XzParams.max_out(+p: XzParams) -> U32:
  match p:
    case XzParams{m}:
      m

# The stream being decoded: its check ID, the records of its blocks so far
# (most recent first), and how much more output the maximum allows
type XzRun is Data:
  XzRun{check: U32, records: List<&2, C.XzRecord>, room: U32}

# What comes next
type XzPhase is Type:
  # a stream header
  XzPhHeader{}
  # a block header, or the index
  XzPhBlock{}
  # a block's compressed data: its header, the LZMA2 decoder, the delta
  # decoders (in the order they are undone), the check, and the output so far
  XzPhData{hdr: C.XzBlockHeader, l2: L2.XzLzma2, deltas: List<&1, D.XzDelta>, chk: I.XzCheck, usize: Nat}
  # a block's padding and check
  XzPhTail{hdr: C.XzBlockHeader, chk: I.XzCheck, csize: Nat, usize: Nat}
  XzPhIndex{}
  # the stream footer, after an index of isize bytes
  XzPhFooter{isize: Nat}
  # stream padding: n null bytes so far
  XzPhPad{n: Nat}

# The streaming decoder: the phase, the stream, and the input buffered but
# not yet decoded
type XzDecoder is Type:
  XzDecoder{ph: XzPhase, run: XzRun, buf: List<&2, U32>}

# What feed answers: the decoder, and the output decoded by this feed
type XzFed is Type:
  XzFed{dec: XzDecoder, out: B.Octets}

type XzStep is Type:
  XzWait{dec: XzDecoder, acc: List<&2, B.Octets>}
  XzGo{dec: XzDecoder, acc: List<&2, B.Octets>}
  XzStop{error: E.XzError}

def XzRun.check(+r: XzRun) -> U32:
  match r:
    case XzRun{check, records, room}:
      check

def XzRun.room(+r: XzRun) -> U32:
  match r:
    case XzRun{check, records, room}:
      room

def XzRun.records(+r: XzRun) -> List<&2, C.XzRecord>:
  match r:
    case XzRun{check, records, room}:
      records

def XzRun.set_room(r: XzRun, +n: U32) -> XzRun:
  match r:
    case XzRun{check, records, room}:
      XzRun{check, records, n}

def XzRun.record(r: XzRun, x: C.XzRecord) -> XzRun:
  match r:
    case XzRun{check, records, room}:
      XzRun{check, Con{x, records}, room}

# A new stream with check ID check (the output count carries on)
def XzRun.stream(r: XzRun, check: U32) -> XzRun:
  match r:
    case XzRun{old, records, room}:
      XzRun{check, Nil{}, room}

# The stream header

def Xz.header.check(m: Maybe<&2, I.XzCheck>, +check: U32, run: XzRun, rest: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match m:
    case None{}:
      XzStop{E.XzUnsupportedCheck{check}}
    case Some{c}:
      XzGo{XzDecoder{XzPhBlock{}, XzRun.stream(run, check), rest}, acc}

def Xz.header(r: Result<&2, &2, E.XzError, C.XzGot<U32>>, run: XzRun, +buf: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match r:
    case Fail{E.XzTruncated{}}:
      XzWait{XzDecoder{XzPhHeader{}, run, buf}, acc}
    case Fail{e}:
      XzStop{e}
    case Done{C.XzGot{+check, rest}}:
      Xz.header.check(I.XzCheck.start(check), check, run, rest, acc)

# The filter chain: deltas, then LZMA2 last

def Xz.filter.lzma2.dict(m: Maybe<&2, U32>) -> Maybe<&2, E.XzError>:
  match m:
    case Some{n}:
      None{}
    case None{}:
      Some{E.XzBadFilterProps{}}

def Xz.filter.lzma2(xs: List<&2, U32>) -> Maybe<&2, E.XzError>:
  match xs:
    case Con{b, Nil{}}:
      Xz.filter.lzma2.dict(L2.XzLzma2.dict_size(b))
    case _:
      Some{E.XzBadFilterProps{}}

def Xz.filter.delta(+n: Nat) -> Maybe<&2, E.XzError>:
  match n:
    case 1n:
      None{}
    case _:
      Some{E.XzBadFilterProps{}}

# the first problem with filter f, if any (last: f ends the chain)
def Xz.filter.err.last(lz: Bool, known: Bool, +id: Nat, props: B.Octets) -> Maybe<&2, E.XzError>:
  match lz known:
    case True{} _:
      Xz.filter.lzma2(B.Octets.to_list(props))
    case False{} True{}:
      Some{E.XzBadBlockHeader{}}
    case False{} False{}:
      Some{E.XzUnsupportedFilter{id}}

def Xz.filter.err.mid(delta: Bool, lz: Bool, +id: Nat, props: B.Octets) -> Maybe<&2, E.XzError>:
  match delta lz:
    case True{} _:
      Xz.filter.delta(B.Octets.len(props))
    case False{} True{}:
      Some{E.XzBadBlockHeader{}}
    case False{} False{}:
      Some{E.XzUnsupportedFilter{id}}

def Xz.filter.err(last: Bool, f: C.XzFilter) -> Maybe<&2, E.XzError>:
  match last:
    case True{}:
      match f:
        case C.XzFilter{+id, props}:
          Xz.filter.err.last(Nat.is_eq(id, 33n), Bool.and(Nat.is_ge(id, 3n), Nat.is_le(id, 11n)), id, props)
    case False{}:
      match f:
        case C.XzFilter{+id, props}:
          Xz.filter.err.mid(Nat.is_eq(id, 3n), Nat.is_eq(id, 33n), id, props)

def Xz.is_nil(+xs: List<&2, C.XzFilter>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def Xz.chain.check(fs: List<&2, C.XzFilter>) -> Maybe<&2, E.XzError>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, +t}:
      Maybe.or(&2, E.XzError, Xz.filter.err(Xz.is_nil(t), f), Xz.chain.check(t))

# the first (only) properties byte of a filter
def Xz.props_byte(o: B.Octets) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, 0n), 0)

def Xz.filter.props(f: C.XzFilter) -> B.Octets:
  match f:
    case C.XzFilter{id, props}:
      props

# The decoders of a checked chain: the deltas, last one first, and the LZMA2
# dictionary size
type XzChain is Type:
  XzChain{deltas: List<&1, D.XzDelta>, dict: U32}

# f is the filter in hand, rest the ones after it
def Xz.chain.build.go(rest: List<&2, C.XzFilter>, f: C.XzFilter, acc: List<&1, D.XzDelta>) -> XzChain:
  match rest:
    case Nil{}:
      XzChain{acc, Maybe.default(&2, U32, L2.XzLzma2.dict_size(Xz.props_byte(Xz.filter.props(f))), 0)}
    case Con{g, u}:
      Xz.chain.build.go(u, g, Con{D.XzDelta.start(U32.add(Xz.props_byte(Xz.filter.props(f)), 1)), acc})

def Xz.chain.build(fs: List<&2, C.XzFilter>) -> XzChain:
  match fs:
    case Nil{}:
      XzChain{Nil{}, 0}
    case Con{f, t}:
      Xz.chain.build.go(t, f, Nil{})

def Xz.block.filters(+h: C.XzBlockHeader) -> List<&2, C.XzFilter>:
  match h:
    case C.XzBlockHeader{size, csize, usize, filters}:
      filters

def Xz.block.size(+h: C.XzBlockHeader) -> Nat:
  match h:
    case C.XzBlockHeader{size, csize, usize, filters}:
      size

def Xz.block.go(c: XzChain, +hdr: C.XzBlockHeader, +run: XzRun, rest: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  XzChain{ds, +dict} = c
  +chk = Maybe.default(&2, I.XzCheck, I.XzCheck.start(XzRun.check(run)), I.XzCheckNone{})
  XzGo{XzDecoder{XzPhData{hdr, L2.XzLzma2.start(dict, XzRun.room(run)), ds, chk, 0n}, run, rest}, acc}

def Xz.block.chain(e: Maybe<&2, E.XzError>, +hdr: C.XzBlockHeader, +run: XzRun, rest: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match e:
    case Some{x}:
      XzStop{x}
    case None{}:
      Xz.block.go(Xz.chain.build(Xz.block.filters(hdr)), hdr, run, rest, acc)

def Xz.block.hdr(r: Result<&2, &2, E.XzError, C.XzGot<C.XzBlockHeader>>, +buf: List<&2, U32>, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match r:
    case Fail{E.XzTruncated{}}:
      XzWait{XzDecoder{XzPhBlock{}, run, buf}, acc}
    case Fail{e}:
      XzStop{e}
    case Done{C.XzGot{+hdr, rest}}:
      Xz.block.chain(Xz.chain.check(Xz.block.filters(hdr)), hdr, run, rest, acc)

def Xz.block.pick(index: Bool, +b0: U32, +buf: List<&2, U32>, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match index:
    case True{}:
      XzGo{XzDecoder{XzPhIndex{}, run, buf}, acc}
    case False{}:
      Xz.block.hdr(C.XzC.block(b0, buf), buf, run, acc)

def Xz.block(buf: List<&2, U32>, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match buf:
    case Nil{}:
      XzWait{XzDecoder{XzPhBlock{}, run, Nil{}}, acc}
    case Con{+b0, t}:
      Xz.block.pick(U32.is_eq(b0, 0), b0, Con{b0, t}, run, acc)

# A block's compressed data

# the delta decoders over a piece of output
type XzDeltas is Type:
  XzDeltas{deltas: List<&1, D.XzDelta>, out: B.Octets}

def Xz.deltas.go(ds: List<&1, D.XzDelta>, r: D.XzDeltaOut, done: List<&1, D.XzDelta>) -> XzDeltas:
  match ds:
    case Nil{}:
      D.XzDeltaOut{d, o} = r
      XzDeltas{List.reverse(&1, D.XzDelta, Con{d, done}), o}
    case Con{d2, rest}:
      D.XzDeltaOut{d, o} = r
      Xz.deltas.go(rest, D.XzDelta.update(d2, o), Con{d, done})

def Xz.deltas(ds: List<&1, D.XzDelta>, o: B.Octets) -> XzDeltas:
  match ds:
    case Nil{}:
      XzDeltas{Nil{}, o}
    case Con{d, rest}:
      Xz.deltas.go(rest, D.XzDelta.update(d, o), Nil{})

def Xz.size_ok(m: Maybe<&2, Nat>, +v: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Nat.is_eq(x, v)

def Xz.sizes_ok(+h: C.XzBlockHeader, +cs: Nat, +us: Nat) -> Bool:
  match h:
    case C.XzBlockHeader{size, csize, usize, filters}:
      Bool.and(Xz.size_ok(csize, cs), Xz.size_ok(usize, us))

def Xz.data.sized(ok: Bool, +hdr: C.XzBlockHeader, chk: I.XzCheck, +csize: Nat, +usize: Nat, run: XzRun, rest: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match ok:
    case False{}:
      XzStop{E.XzBadBlockSize{}}
    case True{}:
      XzGo{XzDecoder{XzPhTail{hdr, chk, csize, usize}, run, rest}, acc}

def Xz.data.end(r: Result<&2, &2, E.XzError, L2.XzL2Rest>, +hdr: C.XzBlockHeader, chk: I.XzCheck, +usize: Nat, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match r:
    case Fail{e}:
      XzStop{e}
    case Done{L2.XzL2Rest{rest, +consumed, +room}}:
      Xz.data.sized(Xz.sizes_ok(hdr, consumed, usize), hdr, chk, consumed, usize, XzRun.set_room(run, room), rest, acc)

def Xz.data.more(ended: Bool, +hdr: C.XzBlockHeader, l2: L2.XzLzma2, ds: List<&1, D.XzDelta>, chk: I.XzCheck, +usize: Nat, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match ended:
    case False{}:
      XzWait{XzDecoder{XzPhData{hdr, l2, ds, chk, usize}, run, Nil{}}, acc}
    case True{}:
      Xz.data.end(L2.XzLzma2.finish.list(l2), hdr, chk, usize, run, acc)

def Xz.data.out(r: XzDeltas, +hdr: C.XzBlockHeader, l2: L2.XzLzma2, ended: Bool, chk: I.XzCheck, +usize: Nat, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  XzDeltas{ds, +o} = r
  +n = B.Octets.len(o)
  Xz.data.more(ended, hdr, l2, ds, I.XzCheck.update(chk, o), Nat.add(usize, n), run, Con{o, acc})

def Xz.data.fed(r: Result<&2, &1, E.XzError, L2.XzLzma2Fed>, +hdr: C.XzBlockHeader, ds: List<&1, D.XzDelta>, chk: I.XzCheck, +usize: Nat, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match r:
    case Fail{e}:
      XzStop{e}
    case Done{L2.XzLzma2Fed{l2, out, ended}}:
      Xz.data.out(Xz.deltas(ds, out), hdr, l2, ended, chk, usize, run, acc)

def Xz.data(buf: List<&2, U32>, +hdr: C.XzBlockHeader, l2: L2.XzLzma2, ds: List<&1, D.XzDelta>, chk: I.XzCheck, +usize: Nat, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match buf:
    case Nil{}:
      XzWait{XzDecoder{XzPhData{hdr, l2, ds, chk, usize}, run, Nil{}}, acc}
    case Con{h, t}:
      Xz.data.fed(L2.XzLzma2.feed.list(l2, Con{h, t}), hdr, ds, chk, usize, run, acc)

# A block's padding and check; then its record

def Xz.tail.verify(pad_ok: Bool, check_ok: Bool, +hdr: C.XzBlockHeader, +csize: Nat, +cs: Nat, +usize: Nat, run: XzRun, rest: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match pad_ok check_ok:
    case False{} _:
      XzStop{E.XzBadPadding{}}
    case True{} False{}:
      XzStop{E.XzBadCheck{}}
    case True{} True{}:
      +unpadded = Nat.add(Nat.add(Xz.block.size(hdr), csize), cs)
      XzGo{XzDecoder{XzPhBlock{}, XzRun.record(run, C.XzRecord{unpadded, usize}), rest}, acc}

def Xz.tail.have(ok: Bool, +pad: Nat, +cs: Nat, +buf: List<&2, U32>, +hdr: C.XzBlockHeader, chk: I.XzCheck, +csize: Nat, +usize: Nat, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match ok:
    case False{}:
      XzWait{XzDecoder{XzPhTail{hdr, chk, csize, usize}, run, buf}, acc}
    case True{}:
      +after = B.drop(pad, buf)
      Xz.tail.verify(C.XzC.all_zero(B.take(pad, buf)), B.Octets.is_eq(B.Octets.of_list(B.take(cs, after)), I.XzCheck.finish(chk)), hdr, csize, cs, usize, run, B.drop(cs, after), acc)

def Xz.tail(+buf: List<&2, U32>, +hdr: C.XzBlockHeader, chk: I.XzCheck, +csize: Nat, +usize: Nat, +run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  +cs = I.XzCheck.size(XzRun.check(run))
  +pad = Nat.mod(Nat.sub(4n, Nat.mod(csize, 4n)), 4n)
  Xz.tail.have(C.XzC.has(Nat.add(pad, cs), buf), pad, cs, buf, hdr, chk, csize, usize, run, acc)

# The index: its records must be the blocks', in order

# (a tail call per record, so an index of any length is compared)
def Xz.records_eq.go(xs: List<&2, C.XzRecord>, ys: List<&2, C.XzRecord>, ok: Bool) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      ok
    case Con{C.XzRecord{a, b}, s} Con{C.XzRecord{c, d}, t}:
      Xz.records_eq.go(s, t, Bool.and(ok, Bool.and(Nat.is_eq(a, c), Nat.is_eq(b, d))))
    case _ _:
      False{}

def Xz.records_eq(xs: List<&2, C.XzRecord>, ys: List<&2, C.XzRecord>) -> Bool:
  Xz.records_eq.go(xs, ys, True{})

def Xz.index.ok(ok: Bool, +isize: Nat, run: XzRun, rest: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match ok:
    case False{}:
      XzStop{E.XzBadIndex{}}
    case True{}:
      XzGo{XzDecoder{XzPhFooter{isize}, run, rest}, acc}

def Xz.index(r: Result<&2, &2, E.XzError, C.XzGot<C.XzIndex>>, +run: XzRun, +buf: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match r:
    case Fail{E.XzTruncated{}}:
      XzWait{XzDecoder{XzPhIndex{}, run, buf}, acc}
    case Fail{e}:
      XzStop{e}
    case Done{C.XzGot{C.XzIndex{recs, +isize}, rest}}:
      Xz.index.ok(Xz.records_eq(recs, List.reverse(&2, C.XzRecord, XzRun.records(run))), isize, run, rest, acc)

# The stream footer: its backward size is the index's size, and its flags
# are the header's

def Xz.footer.ok(back_ok: Bool, flags_ok: Bool, run: XzRun, rest: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match back_ok flags_ok:
    case False{} _:
      XzStop{E.XzBadBackwardSize{}}
    case True{} False{}:
      XzStop{E.XzFlagsMismatch{}}
    case True{} True{}:
      XzGo{XzDecoder{XzPhPad{0n}, run, rest}, acc}

def Xz.footer(r: Result<&2, &2, E.XzError, C.XzGot<C.XzFooter>>, +isize: Nat, +run: XzRun, +buf: List<&2, U32>, acc: List<&2, B.Octets>) -> XzStep:
  match r:
    case Fail{E.XzTruncated{}}:
      XzWait{XzDecoder{XzPhFooter{isize}, run, buf}, acc}
    case Fail{e}:
      XzStop{e}
    case Done{C.XzGot{C.XzFooter{+back, +check}, rest}}:
      Xz.footer.ok(Nat.is_eq(back, isize), U32.is_eq(check, XzRun.check(run)), run, rest, acc)

# Stream padding: null bytes, then (at a multiple of four) another stream

def Xz.pad.pick(zero: Bool, aligned: Bool, +n: Nat, +buf: List<&2, U32>, +t: List<&2, U32>, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match zero aligned:
    case True{} _:
      XzGo{XzDecoder{XzPhPad{1n+n}, run, t}, acc}
    case False{} True{}:
      XzGo{XzDecoder{XzPhHeader{}, run, buf}, acc}
    case False{} False{}:
      XzStop{E.XzBadPadding{}}

def Xz.pad(buf: List<&2, U32>, +n: Nat, run: XzRun, acc: List<&2, B.Octets>) -> XzStep:
  match buf:
    case Nil{}:
      XzWait{XzDecoder{XzPhPad{n}, run, Nil{}}, acc}
    case Con{+h, +t}:
      Xz.pad.pick(U32.is_eq(h, 0), Nat.is_eq(Nat.mod(n, 4n), 0n), n, Con{h, t}, t, run, acc)

# The decoder

def XzDecoder.step(d: XzDecoder, acc: List<&2, B.Octets>) -> XzStep:
  XzDecoder{ph, +run, +buf} = d
  match ph:
    case XzPhHeader{}:
      Xz.header(C.XzC.header(buf), run, buf, acc)
    case XzPhBlock{}:
      Xz.block(buf, run, acc)
    case XzPhData{hdr, l2, ds, chk, usize}:
      Xz.data(buf, hdr, l2, ds, chk, usize, run, acc)
    case XzPhTail{hdr, chk, csize, usize}:
      Xz.tail(buf, hdr, chk, csize, usize, run, acc)
    case XzPhIndex{}:
      Xz.index(C.XzC.index(buf), run, buf, acc)
    case XzPhFooter{isize}:
      Xz.footer(C.XzC.footer(buf), isize, run, buf, acc)
    case XzPhPad{n}:
      Xz.pad(buf, n, run, acc)

def XzDecoder.loop(n: Nat, r: XzStep) -> XzStep:
  match n:
    case 0n:
      r
    case 1n+p:
      match r:
        case XzGo{d, acc}:
          XzDecoder.loop(p, XzDecoder.step(d, acc))
        case XzWait{d, acc}:
          XzWait{d, acc}
        case XzStop{e}:
          XzStop{e}

# the pieces of output (most recent first) joined; a single piece (a whole
# block decoded in one feed) is answered as it is, not copied
def XzDecoder.out(acc: List<&2, B.Octets>) -> B.Octets:
  match acc:
    case Nil{}:
      B.Octets.empty()
    case Con{o, Nil{}}:
      o
    case Con{o, t}:
      B.Octets.concat(List.reverse(&2, B.Octets, Con{o, t}))

def XzDecoder.feed.fin(r: XzStep) -> Result<&2, &1, E.XzError, XzFed>:
  match r:
    case XzGo{d, acc}:
      Done{XzFed{d, XzDecoder.out(acc)}}
    case XzWait{d, acc}:
      Done{XzFed{d, XzDecoder.out(acc)}}
    case XzStop{e}:
      Fail{e}

# A decoder at the start of an .xz file
def XzDecoder.start(+p: XzParams) -> XzDecoder:
  XzDecoder{XzPhHeader{}, XzRun{0, Nil{}, XzParams.max_out(p)}, Nil{}}

# More input: the answer holds the output decoded so far. Every step of the
# loop either reads input or (at most twice in a row) moves to a phase that
# will, so 2 * (bytes buffered) + 4 steps is enough.
def XzDecoder.feed(d: XzDecoder, input: B.Octets) -> Result<&2, &1, E.XzError, XzFed>:
  XzDecoder{ph, run, buf} = d
  +buf2 = B.append.fast(buf, B.Octets.to_list(input))
  XzDecoder.feed.fin(XzDecoder.loop(1n+Nat.add(Nat.mul(2n, B.len.fast(buf2)), 3n), XzGo{XzDecoder{ph, run, buf2}, Nil{}}))

def XzDecoder.finish.pad(n: Nat, out: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match n:
    case 0n:
      Done{out}
    case 1n+k:
      Fail{E.XzBadPadding{}}

def XzDecoder.finish.ph(ph: XzPhase, out: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match ph:
    case XzPhPad{n}:
      XzDecoder.finish.pad(Nat.mod(n, 4n), out)
    case _:
      Fail{E.XzTruncated{}}

def XzDecoder.finish.fed(r: Result<&2, &1, E.XzError, XzFed>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{XzFed{d, out}}:
      XzDecoder{ph, run, buf} = d
      XzDecoder.finish.ph(ph, out)

# The end of the input: the file must end after a stream (and its padding);
# the answer is any output not yet answered by feed (normally none)
def XzDecoder.finish(d: XzDecoder) -> Result<&2, &2, E.XzError, B.Octets>:
  XzDecoder.finish.fed(XzDecoder.feed(d, B.Octets.empty()))

# One-shot

# the output, if it is no longer than max (it never is: the LZMA2 decoders
# refuse to go past it; this guard makes the bound plain)
def Xz.bound.pick(ok: Bool, o: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match ok:
    case True{}:
      Done{o}
    case False{}:
      Fail{E.XzOutputTooLarge{}}

def Xz.bound(+max: U32, r: Result<&2, &2, E.XzError, B.Octets>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+o}:
      Xz.bound.pick(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o)

# (finish's output is normally empty: then out is answered as it is, not
# copied)
def xz_decode.join.pick(n: Nat, out: B.Octets, o: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match n:
    case 0n:
      Done{out}
    case 1n+k:
      Done{B.Octets.append(out, o)}

def xz_decode.join(r: Result<&2, &2, E.XzError, B.Octets>, out: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+o}:
      xz_decode.join.pick(B.Octets.len(o), out, o)

def xz_decode.fin(r: Result<&2, &1, E.XzError, XzFed>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{XzFed{d, out}}:
      xz_decode.join(XzDecoder.finish(d), out)

# A whole .xz file: its decompressed data, or the first failure
def xz_decode(+p: XzParams, input: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  Xz.bound(XzParams.max_out(p), xz_decode.fin(XzDecoder.feed(XzDecoder.start(p), input)))
