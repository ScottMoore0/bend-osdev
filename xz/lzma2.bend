# bend-osdev-xz: the LZMA2 decoder, one-shot and streaming.
#
# Written from the description of LZMA2 in "The .xz File Format" (5.3.1) and
# the LZMA specification in the LZMA SDK (both public domain). An LZMA2 stream
# is a sequence of chunks, each opened by a control byte:
#
#   0x00          the end of the stream
#   0x01          an uncompressed chunk, after a dictionary reset
#   0x02          an uncompressed chunk
#   0x03 - 0x7F   invalid
#   0x80 - 0xFF   an LZMA chunk; bits 5 and 6 say what it resets: 0 nothing,
#                 1 the state, 2 the state and the properties (a props byte
#                 follows the sizes), 3 all that and the dictionary; bits 0
#                 to 4 are bits 16 to 20 of the uncompressed size less one
#
# An uncompressed chunk has a two-byte (big-endian) size less one; an LZMA
# chunk has its uncompressed size less one (16 more bits) and its compressed
# size less one (16 bits). The first chunk must reset the dictionary, and the
# first LZMA chunk after a dictionary reset must set the properties. Each LZMA
# chunk starts a new range decoder, which must end exactly at the chunk's end.
#
# The streaming decoder decodes whole chunks: feed buffers input until the
# next chunk is complete (at most 64 KiB of compressed data and 2 MiB of
# output), decodes it, and answers the output of every chunk it completed.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./rangecoder.bend as R
import ./lzma.bend as L

# The control flags: the next chunk must reset the dictionary; the next LZMA
# chunk must set the properties; the end marker was read; how many more bytes
# may be output; and how many input bytes were consumed
type XzL2Ctl is Data:
  XzL2Ctl{need_reset: Bool, need_props: Bool, ended: Bool, room: U32, consumed: Nat, depth: Nat, maxdepth: Nat}

# The decoder: probabilities, dictionary, LZMA registers, control flags, and
# the input buffered but not yet decoded
type XzLzma2 is Type:
  XzLzma2{probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, ctl: XzL2Ctl, buf: List<&2, U32>}

# What feed answers: the decoder, the output of the chunks it completed, and
# whether the end marker has been read
type XzLzma2Fed is Type:
  XzLzma2Fed{dec: XzLzma2, out: B.Octets, ended: Bool}

# What finish answers: the bytes after the end marker, the size of the LZMA2
# stream itself, and how much more output the maximum allows
type XzLzma2End is Data:
  XzLzma2End{rest: B.Octets, consumed: Nat, room: U32}

# One step of the chunk loop
type XzL2Step is Type:
  # stopped: the next chunk is not complete yet, or the stream has ended
  XzL2Wait{dec: XzLzma2, acc: List<&2, U32>}
  # a chunk was decoded: go on
  XzL2Go{dec: XzLzma2, acc: List<&2, U32>}
  XzL2Fail{error: E.XzError}

# The dictionary size of an LZMA2 properties byte ("The .xz File Format",
# 5.3.1): 2^32 - 1 for 40, otherwise (2 | (b & 1)) << (b / 2 + 11); a byte
# above 40 is invalid
def XzLzma2.dict_size.pick(ok: Bool, top: Bool, +b: U32) -> Maybe<&2, U32>:
  match ok top:
    case True{} True{}:
      Some{4294967295}
    case True{} False{}:
      Some{U32.shln(U32.or(2, U32.and(b, 1)), U32.to_nat(U32.add(U32.shr(b), 11)))}
    case False{} _:
      None{}

def XzLzma2.dict_size(+b: U32) -> Maybe<&2, U32>:
  XzLzma2.dict_size.pick(U32.is_le(b, 40), U32.is_eq(b, 40), b)

# The dictionary array holds 2^k bytes for the least k with 2^k at least
# need (k at most 31)
def XzLzma2.depth.pick(small: Bool, +need: U32) -> Nat:
  match small:
    case True{}:
      0n
    case False{}:
      1n+U32.log2(U32.sub(need, 1))

def XzLzma2.depth(+need: U32) -> Nat:
  XzLzma2.depth.pick(U32.is_le(need, 1), need)

# A decoder for an LZMA2 stream with dictionary size dict_size, which may
# output at most max_out bytes. The dictionary array is the smaller of the
# two (and at most 2^31 bytes), so memory follows max_out as well.
def XzLzma2.start.depth(+dict_size: U32, +max_out: U32) -> Nat:
  XzLzma2.depth(U32.min(U32.min(dict_size, max_out), 2147483648))

def XzLzma2.start.regs(+dict_size: U32, +k: Nat) -> L.XzLzRegs:
  L.XzLzRegs.start(U32.min(dict_size, U32.shln(1, k)))

def XzLzma2.start.go(+dict_size: U32, +max_out: U32, +k: Nat) -> XzLzma2:
  XzLzma2{Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), XzLzma2.start.regs(dict_size, k), XzL2Ctl{True{}, True{}, False{}, max_out, 0n, Nat.min(k, 12n), k}, Nil{}}

def XzLzma2.start(+dict_size: U32, +max_out: U32) -> XzLzma2:
  XzLzma2.start.go(dict_size, max_out, XzLzma2.start.depth(dict_size, max_out))

# The control flags
def XzL2Ctl.need_reset(+c: XzL2Ctl) -> Bool:
  match c:
    case XzL2Ctl{need_reset, need_props, ended, room, consumed, depth, maxdepth}:
      need_reset

def XzL2Ctl.need_props(+c: XzL2Ctl) -> Bool:
  match c:
    case XzL2Ctl{need_reset, need_props, ended, room, consumed, depth, maxdepth}:
      need_props

def XzL2Ctl.ended(+c: XzL2Ctl) -> Bool:
  match c:
    case XzL2Ctl{need_reset, need_props, ended, room, consumed, depth, maxdepth}:
      ended

def XzL2Ctl.room(+c: XzL2Ctl) -> U32:
  match c:
    case XzL2Ctl{need_reset, need_props, ended, room, consumed, depth, maxdepth}:
      room

# after the end marker
def XzL2Ctl.end(c: XzL2Ctl) -> XzL2Ctl:
  match c:
    case XzL2Ctl{need_reset, need_props, ended, room, consumed, depth, maxdepth}:
      XzL2Ctl{need_reset, need_props, True{}, room, 1n+consumed, depth, maxdepth}

# after a chunk of n input bytes and u output bytes
def XzL2Ctl.chunk(c: XzL2Ctl, need_props: Bool, +n: Nat, +u: U32, nd: Nat) -> XzL2Ctl:
  match c:
    case XzL2Ctl{need_reset, old_props, ended, room, consumed, depth, maxdepth}:
      XzL2Ctl{False{}, need_props, ended, U32.sub(room, u), Nat.add(consumed, n), nd, maxdepth}

def XzL2Ctl.depth(+c: XzL2Ctl) -> Nat:
  match c:
    case XzL2Ctl{need_reset, need_props, ended, room, consumed, depth, maxdepth}:
      depth

def XzL2Ctl.maxdepth(+c: XzL2Ctl) -> Nat:
  match c:
    case XzL2Ctl{need_reset, need_props, ended, room, consumed, depth, maxdepth}:
      maxdepth

# The dictionary array grows (doubling at least) as the output does, up to
# 2^maxdepth bytes. It grows only before positions wrap, so slot i keeps
# position i.
def XzLzma2.grow.copy(n: Nat, r: Array<U32> & U32, new: Array<U32>, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      (old, +v) = r
      Array.set(U32, new, i, v)
    case 1n+p:
      (old, +v) = r
      +j = U32.add(i, 1)
      XzLzma2.grow.copy(p, Array.get(U32, old, j), Array.set(U32, new, i, v), j)

def XzLzma2.grow.pick(more: Bool, dict: Array<U32>, +cur: Nat, +want: Nat) -> Array<U32>:
  match more:
    case True{}:
      XzLzma2.grow.copy(U32.to_nat(U32.sub(U32.shln(1, cur), 1)), Array.get(U32, dict, 0), Array.new(U32, want, 0), 0)
    case False{}:
      dict

# the depth for writing u more bytes at position pos
def XzLzma2.want(+cur: Nat, +max: Nat, +pos: U32, +u: U32) -> Nat:
  Nat.max(cur, Nat.min(max, XzLzma2.depth(U32.min(U32.add(pos, u), 2147483648))))

def XzLzma2.grow(dict: Array<U32>, +cur: Nat, +want: Nat) -> Array<U32>:
  XzLzma2.grow.pick(Nat.is_lt(cur, want), dict, cur, want)

# Whether xs has at least n bytes
def XzLzma2.has(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match xs:
        case Nil{}:
          False{}
        case Con{h, t}:
          XzLzma2.has(p, t)

def XzLzma2.dict_reset_if(reset: Bool, regs: L.XzLzRegs) -> L.XzLzRegs:
  match reset:
    case True{}:
      L.XzLzRegs.dict_reset(regs)
    case False{}:
      regs

def XzLzma2.state_reset_if(reset: Bool, regs: L.XzLzRegs) -> L.XzLzRegs:
  match reset:
    case True{}:
      L.XzLzRegs.state_reset(regs)
    case False{}:
      regs

def XzLzma2.probs_if(reset: Bool, probs: Array<U32>) -> Array<U32>:
  match reset:
    case True{}:
      R.XzRd.fresh()
    case False{}:
      probs

# Uncompressed chunks
def XzLzma2.raw.done(r: L.XzLzDict, probs: Array<U32>, ctl: XzL2Ctl, rest: List<&2, U32>) -> XzL2Step:
  L.XzLzDict{dict, regs, out} = r
  XzL2Go{XzLzma2{probs, dict, regs, ctl, rest}, out}

def XzLzma2.raw.have(ok: Bool, +size: U32, +reset: Bool, +data: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match ok:
    case False{}:
      XzL2Wait{XzLzma2{probs, dict, regs, ctl, buf}, acc}
    case True{}:
      +regs2 = XzLzma2.dict_reset_if(reset, regs)
      +nd = XzLzma2.want(XzL2Ctl.depth(ctl), XzL2Ctl.maxdepth(ctl), L.XzLzRegs.pos(regs2), size)
      +ctl2 = XzL2Ctl.chunk(ctl, Bool.or(XzL2Ctl.need_props(ctl), reset), Nat.add(3n, U32.to_nat(size)), size, nd)
      XzLzma2.raw.done(L.XzLzma.copy_in(B.take.fast(U32.to_nat(size), data), XzLzma2.grow(dict, XzL2Ctl.depth(ctl), nd), regs2, acc), probs, ctl2, B.drop(U32.to_nat(size), data))

def XzLzma2.raw.room(over: Bool, +size: U32, +reset: Bool, +data: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match over:
    case True{}:
      XzL2Fail{E.XzOutputTooLarge{}}
    case False{}:
      XzLzma2.raw.have(XzLzma2.has(U32.to_nat(size), data), size, reset, data, buf, probs, dict, regs, ctl, acc)

def XzLzma2.raw.check(bad: Bool, +reset: Bool, +rest: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match bad:
    case True{}:
      XzL2Fail{E.XzCorruptLzma{}}
    case False{}:
      match rest:
        case Con{+hi, Con{+lo, data}}:
          +size = U32.add(U32.add(U32.shln(U32.and(hi, 255), 8n), U32.and(lo, 255)), 1)
          XzLzma2.raw.room(U32.is_lt(XzL2Ctl.room(ctl), size), size, reset, data, buf, probs, dict, regs, ctl, acc)
        case _:
          XzL2Wait{XzLzma2{probs, dict, regs, ctl, buf}, acc}

def XzLzma2.raw(+c: U32, +rest: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  +reset = U32.is_eq(c, 1)
  XzLzma2.raw.check(Bool.and(Bool.not(reset), XzL2Ctl.need_reset(ctl)), reset, rest, buf, probs, dict, regs, ctl, acc)

# LZMA chunks
def XzLzma2.lz.done(r: L.XzLzChunk, ctl: XzL2Ctl, rest: List<&2, U32>) -> XzL2Step:
  L.XzLzChunk{probs, dict, regs, out, ok} = r
  match ok:
    case True{}:
      XzL2Go{XzLzma2{probs, dict, regs, ctl, rest}, out}
    case False{}:
      XzL2Fail{E.XzCorruptLzma{}}

def XzLzma2.lz.have(ok: Bool, +mode: U32, +u: U32, +p: Nat, +hl: Nat, +data: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match ok:
    case False{}:
      XzL2Wait{XzLzma2{probs, dict, regs, ctl, buf}, acc}
    case True{}:
      +sreset = U32.is_ge(mode, 1)
      +regs2 = XzLzma2.state_reset_if(sreset, XzLzma2.dict_reset_if(U32.is_eq(mode, 3), regs))
      +nd = XzLzma2.want(XzL2Ctl.depth(ctl), XzL2Ctl.maxdepth(ctl), L.XzLzRegs.pos(regs2), u)
      +ctl2 = XzL2Ctl.chunk(ctl, False{}, Nat.add(hl, p), u, nd)
      XzLzma2.lz.done(L.XzLzma.chunk(U32.to_nat(u), XzLzma2.probs_if(sreset, probs), XzLzma2.grow(dict, XzL2Ctl.depth(ctl), nd), regs2, acc, B.take.fast(p, data)), ctl2, B.drop(p, data))

def XzLzma2.lz.room(over: Bool, +mode: U32, +u: U32, +p: Nat, +hl: Nat, +data: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match over:
    case True{}:
      XzL2Fail{E.XzOutputTooLarge{}}
    case False{}:
      XzLzma2.lz.have(XzLzma2.has(p, data), mode, u, p, hl, data, buf, probs, dict, regs, ctl, acc)

# lc = props mod 9, lp = (props / 9) mod 5, pb = props / 45; LZMA2 allows
# lc + lp at most 4
def XzLzma2.lz.setp(ok: Bool, +pr: U32, +mode: U32, +u: U32, +p: Nat, +data: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match ok:
    case False{}:
      XzL2Fail{E.XzCorruptLzma{}}
    case True{}:
      +regs2 = L.XzLzRegs.set_props(regs, U32.to_nat(U32.mod(pr, 9)), U32.to_nat(U32.mod(U32.div(pr, 9), 5)), U32.to_nat(U32.div(pr, 45)))
      XzLzma2.lz.room(U32.is_lt(XzL2Ctl.room(ctl), u), mode, u, p, 6n, data, buf, probs, dict, regs2, ctl, acc)

def XzLzma2.lz.props(has_props: Bool, +mode: U32, +u: U32, +p: Nat, +data: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match has_props:
    case False{}:
      XzLzma2.lz.room(U32.is_lt(XzL2Ctl.room(ctl), u), mode, u, p, 5n, data, buf, probs, dict, regs, ctl, acc)
    case True{}:
      match data:
        case Con{+pr, d2}:
          +b = U32.and(pr, 255)
          XzLzma2.lz.setp(Bool.and(U32.is_lt(b, 225), U32.is_le(U32.add(U32.mod(b, 9), U32.mod(U32.div(b, 9), 5)), 4)), b, mode, u, p, d2, buf, probs, dict, regs, ctl, acc)
        case Nil{}:
          XzL2Wait{XzLzma2{probs, dict, regs, ctl, buf}, acc}

def XzLzma2.lz.check(bad: Bool, +mode: U32, +c: U32, +rest: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match bad:
    case True{}:
      XzL2Fail{E.XzCorruptLzma{}}
    case False{}:
      match rest:
        case Con{+b1, Con{+b2, Con{+b3, Con{+b4, data}}}}:
          +u = U32.add(U32.add(U32.shln(U32.and(c, 31), 16n), U32.add(U32.shln(U32.and(b1, 255), 8n), U32.and(b2, 255))), 1)
          +p = U32.to_nat(U32.add(U32.add(U32.shln(U32.and(b3, 255), 8n), U32.and(b4, 255)), 1))
          XzLzma2.lz.props(U32.is_ge(mode, 2), mode, u, p, data, buf, probs, dict, regs, ctl, acc)
        case _:
          XzL2Wait{XzLzma2{probs, dict, regs, ctl, buf}, acc}

def XzLzma2.lz(+c: U32, +rest: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  +mode = U32.and(U32.shrn(c, 5n), 3)
  +bad = Bool.or(Bool.and(Bool.not(U32.is_eq(mode, 3)), XzL2Ctl.need_reset(ctl)), Bool.and(U32.is_lt(mode, 2), XzL2Ctl.need_props(ctl)))
  XzLzma2.lz.check(bad, mode, c, rest, buf, probs, dict, regs, ctl, acc)

# One chunk, from its control byte c: 0 ends the stream, 1 and 2 open
# uncompressed chunks, 3 to 127 are invalid, and the rest open LZMA chunks
def XzLzma2.control.low(eos: Bool, +c: U32, +rest: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match eos:
    case True{}:
      XzL2Wait{XzLzma2{probs, dict, regs, XzL2Ctl.end(ctl), rest}, acc}
    case False{}:
      XzLzma2.raw(c, rest, buf, probs, dict, regs, ctl, acc)

def XzLzma2.control.high(bad: Bool, +c: U32, +rest: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match bad:
    case True{}:
      XzL2Fail{E.XzCorruptLzma{}}
    case False{}:
      XzLzma2.lz(c, rest, buf, probs, dict, regs, ctl, acc)

def XzLzma2.control(low: Bool, +c: U32, +rest: List<&2, U32>, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match low:
    case True{}:
      XzLzma2.control.low(U32.is_eq(c, 0), c, rest, buf, probs, dict, regs, ctl, acc)
    case False{}:
      XzLzma2.control.high(U32.is_lt(c, 128), c, rest, buf, probs, dict, regs, ctl, acc)

def XzLzma2.step.go(ended: Bool, +buf: List<&2, U32>, probs: Array<U32>, dict: Array<U32>, regs: L.XzLzRegs, +ctl: XzL2Ctl, acc: List<&2, U32>) -> XzL2Step:
  match ended:
    case True{}:
      XzL2Wait{XzLzma2{probs, dict, regs, ctl, buf}, acc}
    case False{}:
      match buf:
        case Nil{}:
          XzL2Wait{XzLzma2{probs, dict, regs, ctl, Nil{}}, acc}
        case Con{+c, +rest}:
          XzLzma2.control(U32.is_lt(c, 3), c, rest, Con{c, rest}, probs, dict, regs, ctl, acc)

def XzLzma2.step(d: XzLzma2, acc: List<&2, U32>) -> XzL2Step:
  XzLzma2{probs, dict, regs, +ctl, buf} = d
  XzLzma2.step.go(XzL2Ctl.ended(ctl), buf, probs, dict, regs, ctl, acc)

# Chunks until one is incomplete or the stream ends; each chunk read takes at
# least one byte, so n = 1 + the bytes buffered is enough
def XzLzma2.loop(n: Nat, r: XzL2Step) -> XzL2Step:
  match n:
    case 0n:
      r
    case 1n+p:
      match r:
        case XzL2Go{d, acc}:
          XzLzma2.loop(p, XzLzma2.step(d, acc))
        case XzL2Wait{d, acc}:
          XzL2Wait{d, acc}
        case XzL2Fail{e}:
          XzL2Fail{e}

def XzLzma2.fed(d: XzLzma2, acc: List<&2, U32>) -> XzLzma2Fed:
  XzLzma2{probs, dict, regs, +ctl, buf} = d
  XzLzma2Fed{XzLzma2{probs, dict, regs, ctl, buf}, B.Octets.of_list(List.reverse(&2, U32, acc)), XzL2Ctl.ended(ctl)}

def XzLzma2.feed.fin(r: XzL2Step) -> Result<&2, &1, E.XzError, XzLzma2Fed>:
  match r:
    case XzL2Go{d, acc}:
      Done{XzLzma2.fed(d, acc)}
    case XzL2Wait{d, acc}:
      Done{XzLzma2.fed(d, acc)}
    case XzL2Fail{e}:
      Fail{e}

# Streaming, on a byte list (internal: the .xz decoder feeds its own buffer
# without making it Octets). Every element of xs is a byte (0 to 255).
def XzLzma2.feed.list(d: XzLzma2, xs: List<&2, U32>) -> Result<&2, &1, E.XzError, XzLzma2Fed>:
  XzLzma2{probs, dict, regs, ctl, buf} = d
  +buf2 = B.append.fast(buf, xs)
  XzLzma2.feed.fin(XzLzma2.loop(1n+B.len.fast(buf2), XzL2Go{XzLzma2{probs, dict, regs, ctl, buf2}, Nil{}}))

# Streaming: more input; the answer holds the output of every chunk completed
def XzLzma2.feed(d: XzLzma2, input: B.Octets) -> Result<&2, &1, E.XzError, XzLzma2Fed>:
  XzLzma2.feed.list(d, B.Octets.to_list(input))

# What finish.list answers (internal): finish's answer, with the bytes after
# the end marker as a list
type XzL2Rest is Data:
  XzL2Rest{rest: List<&2, U32>, consumed: Nat, room: U32}

def XzLzma2.finish.go(ended: Bool, +consumed: Nat, +room: U32, buf: List<&2, U32>) -> Result<&2, &2, E.XzError, XzL2Rest>:
  match ended:
    case True{}:
      Done{XzL2Rest{buf, consumed, room}}
    case False{}:
      Fail{E.XzTruncated{}}

def XzLzma2.finish.list(d: XzLzma2) -> Result<&2, &2, E.XzError, XzL2Rest>:
  XzLzma2{probs, dict, regs, ctl, buf} = d
  match ctl:
    case XzL2Ctl{need_reset, need_props, ended, +room, +consumed, depth, maxdepth}:
      XzLzma2.finish.go(ended, consumed, room, buf)

def XzLzma2.finish.oct(r: Result<&2, &2, E.XzError, XzL2Rest>) -> Result<&2, &2, E.XzError, XzLzma2End>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{XzL2Rest{rest, consumed, room}}:
      Done{XzLzma2End{B.Octets.of_list(rest), consumed, room}}

# The end of the input: the bytes after the end marker and the stream's size,
# or XzTruncated if the end marker has not been read
def XzLzma2.finish(d: XzLzma2) -> Result<&2, &2, E.XzError, XzLzma2End>:
  XzLzma2.finish.oct(XzLzma2.finish.list(d))

# One-shot: a whole LZMA2 stream, and nothing after it
def XzLzma2.decode.empty(n: Nat, out: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match n:
    case 0n:
      Done{out}
    case 1n+k:
      Fail{E.XzTrailingData{}}

def XzLzma2.decode.end(r: Result<&2, &2, E.XzError, XzLzma2End>, out: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{XzLzma2End{rest, consumed, room}}:
      XzLzma2.decode.empty(B.Octets.len(rest), out)

def XzLzma2.decode.fin(r: Result<&2, &1, E.XzError, XzLzma2Fed>) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{XzLzma2Fed{dec, out, ended}}:
      XzLzma2.decode.end(XzLzma2.finish(dec), out)

def XzLzma2.decode(+dict_size: U32, +max_out: U32, input: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  XzLzma2.decode.fin(XzLzma2.feed(XzLzma2.start(dict_size, max_out), input))
