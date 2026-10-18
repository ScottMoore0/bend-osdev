# bend-osdev-xz: the LZMA decoder, a chunk at a time.
#
# Written from the LZMA specification in the LZMA SDK ("lzma-specification",
# Igor Pavlov, public domain): literals coded with lc, lp and pb; matches and
# the repeated distances rep0 to rep3; the twelve-state machine; lengths and
# distances.
#
# The decoder emits exactly one byte per step: a step either copies the next
# byte of a match still pending, or decodes the next symbol (a literal, a
# short rep, or a match whose first byte it copies). So a chunk of n bytes is
# n steps, and a match running past the chunk's end leaves a length pending,
# which XzLzma.finish reports as corruption.
#
# The dictionary is an array whose size is a power of two at least the
# dictionary size (or the most output allowed, if that is smaller); positions
# wrap. Every distance is checked against the bytes written since the last
# dictionary reset and against the dictionary size, so a read never reaches a
# byte that was not written.
import Base
import ./rangecoder.bend as R

# The registers: the state (0 to 11), the four repeated distances (each one
# less than the distance), the length of the match still to copy, the bytes
# written since the dictionary reset, the last byte written, the literal and
# position parameters (lc as a count; lp and pb as masks), the dictionary
# size, and ok, which turns False on an impossible distance.
type XzLzRegs is Data:
  XzLzRegs{state: U32, rep0: U32, rep1: U32, rep2: U32, rep3: U32, len: U32, pos: U32, prev: U32, lc: Nat, lpmask: U32, pbmask: U32, dsize: U32, ok: Bool}

# The decoder: range decoder (with the probabilities), dictionary, registers,
# and the output so far (most recent byte first)
type XzLzma is Type:
  XzLzma{rd: R.XzRd, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>}

# Where each probability lives (the spec's arrays, laid end to end):
#   IsMatch 0 (12 x 16), IsRep 192, IsRepG0 204, IsRepG1 216, IsRepG2 228,
#   IsRep0Long 240 (12 x 16), PosSlot 432 (4 x 64), SpecPos 688 (115),
#   Align 803 (16), the match length decoder 819 (514), the rep length
#   decoder 1333 (514), and the literals from 1847 (0x300 per context)

def XzLz.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# The state machine
def XzLz.after_lit(+s: U32) -> U32:
  XzLz.sel(U32.is_lt(s, 4), 0, XzLz.sel(U32.is_lt(s, 10), U32.sub(s, 3), U32.sub(s, 6)))

def XzLz.after_match(+s: U32) -> U32:
  XzLz.sel(U32.is_lt(s, 7), 7, 10)

def XzLz.after_rep(+s: U32) -> U32:
  XzLz.sel(U32.is_lt(s, 7), 8, 11)

def XzLz.after_short(+s: U32) -> U32:
  XzLz.sel(U32.is_lt(s, 7), 9, 11)

# The registers after a dictionary reset (lc, lp, pb and the size kept)
def XzLzRegs.dict_reset(r: XzLzRegs) -> XzLzRegs:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLzRegs{state, rep0, rep1, rep2, rep3, len, 0, 0, lc, lpmask, pbmask, dsize, ok}

# The registers after a state reset
def XzLzRegs.state_reset(r: XzLzRegs) -> XzLzRegs:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLzRegs{0, 0, 0, 0, 0, 0, pos, prev, lc, lpmask, pbmask, dsize, True{}}

# New lc, lp and pb
def XzLzRegs.set_props(r: XzLzRegs, lc: Nat, +lp: Nat, +pb: Nat) -> XzLzRegs:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, olc, olp, opb, dsize, ok}:
      XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, U32.sub(U32.shln(1, lp), 1), U32.sub(U32.shln(1, pb), 1), dsize, ok}

# The registers at the start: dictionary size dsize, lc = lp = pb = 0 until a
# chunk sets them
def XzLzRegs.start(dsize: U32) -> XzLzRegs:
  XzLzRegs{0, 0, 0, 0, 0, 0, 0, 0, 0n, 0, 0, dsize, True{}}

def XzLzRegs.pos(r: XzLzRegs) -> U32:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      pos

# Whether the last chunk ended cleanly: no impossible distance, no match left
def XzLzRegs.clean(r: XzLzRegs) -> Bool:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      Bool.and(ok, U32.is_eq(len, 0))

# Whether every distance so far was possible (False after the end marker too)
def XzLzRegs.ok(r: XzLzRegs) -> Bool:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      ok

# Whether the last match was the end marker (rep0 holds its distance)
def XzLzRegs.at_end(r: XzLzRegs) -> Bool:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      U32.is_eq(rep0, 4294967295)

# The length of the match still to copy
def XzLzRegs.pending(r: XzLzRegs) -> U32:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      len

# Emitting a byte: into the dictionary and the output
def XzLz.put(rd: R.XzRd, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>, +b: U32) -> XzLzma:
  match regs:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, +pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLzma{rd, Array.set(U32, dict, pos, b), XzLzRegs{state, rep0, rep1, rep2, rep3, len, U32.add(pos, 1), b, lc, lpmask, pbmask, dsize, ok}, Con{b, out}}

# Copying the next byte of the pending match
def XzLz.copy.go(r: Array<U32> & U32, rd: R.XzRd, regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  (dict, +b) = r
  XzLz.put(rd, dict, regs, out, b)

def XzLz.copy(rd: R.XzRd, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  match regs:
    case XzLzRegs{state, +rep0, rep1, rep2, rep3, +len, +pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLz.copy.go(Array.get(U32, dict, U32.sub(U32.sub(pos, rep0), 1)), rd, XzLzRegs{state, rep0, rep1, rep2, rep3, U32.sub(len, 1), pos, prev, lc, lpmask, pbmask, dsize, ok}, out)

# Literals. r holds the bit decoded at base + offset + m, where offset selects
# the match-byte probabilities while mm is 1; mb is the match byte, shifted so
# that its bit 7 is the next one to compare
def XzLz.lit.go(n: Nat, r: R.XzBit, +base: U32, +m: U32, +mb: U32, +mbit: U32, +mm: U32) -> R.XzSym:
  match n:
    case 0n:
      R.XzBit{rd, b} = r
      R.XzSym{rd, U32.and(U32.add(U32.shl(m), R.XzRd.bitval(b)), 255)}
    case 1n+p:
      R.XzBit{rd, b} = r
      +v = R.XzRd.bitval(b)
      +m2 = U32.add(U32.shl(m), v)
      +mm2 = U32.and(mm, U32.xor(1, U32.xor(v, mbit)))
      +mbit2 = U32.and(U32.shrn(mb, 7n), 1)
      XzLz.lit.go(p, R.XzRd.bit(rd, U32.add(base, U32.add(U32.mul(mm2, U32.shln(U32.add(1, mbit2), 8n)), m2))), base, m2, U32.shl(mb), mbit2, mm2)

def XzLz.lit.fin(r: R.XzSym, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzSym{rd, +b} = r
  match regs:
    case XzLzRegs{+state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLz.put(rd, dict, XzLzRegs{XzLz.after_lit(state), rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}, out, b)

def XzLz.lit.start(r: Array<U32> & U32, rd: R.XzRd, regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  (dict, +mb) = r
  match regs:
    case XzLzRegs{+state, rep0, rep1, rep2, rep3, len, +pos, +prev, +lc, +lpmask, pbmask, dsize, ok}:
      +ctx = U32.add(U32.shln(U32.and(pos, lpmask), lc), U32.shrn(prev, Nat.sub(8n, lc)))
      +base = U32.add(1847, U32.mul(768, ctx))
      +mm = R.XzRd.bitval(U32.is_ge(state, 7))
      +mbit = U32.and(U32.shrn(mb, 7n), 1)
      XzLz.lit.fin(XzLz.lit.go(7n, R.XzRd.bit(rd, U32.add(base, U32.add(U32.mul(mm, U32.shln(U32.add(1, mbit), 8n)), 1))), base, 1, U32.shl(mb), mbit, mm), dict, XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}, out)

def XzLz.literal(rd: R.XzRd, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  match regs:
    case XzLzRegs{state, +rep0, rep1, rep2, rep3, len, +pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLz.lit.start(Array.get(U32, dict, U32.sub(U32.sub(pos, rep0), 1)), rd, XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}, out)

# Lengths (0 to 271, two less than the match length) from the decoder at base
def XzLz.len.mid(r: R.XzBit, +base: U32, +ps: U32) -> R.XzSym:
  R.XzBit{rd, b} = r
  match b:
    case False{}:
      R.XzRd.plus(R.XzRd.tree(rd, U32.add(base, U32.add(130, U32.mul(ps, 8))), 3n), 8)
    case True{}:
      R.XzRd.plus(R.XzRd.tree(rd, U32.add(base, 258), 8n), 16)

def XzLz.len.low(r: R.XzBit, +base: U32, +ps: U32) -> R.XzSym:
  R.XzBit{rd, b} = r
  match b:
    case False{}:
      R.XzRd.tree(rd, U32.add(base, U32.add(2, U32.mul(ps, 8))), 3n)
    case True{}:
      XzLz.len.mid(R.XzRd.bit(rd, U32.add(base, 1)), base, ps)

def XzLz.length(rd: R.XzRd, +base: U32, +ps: U32) -> R.XzSym:
  XzLz.len.low(R.XzRd.bit(rd, base), base, ps)

# Distances (one less than the distance) for a match of length class ls
def XzLz.dist.align(r: R.XzSym, +base: U32) -> R.XzSym:
  R.XzSym{rd, +hi} = r
  R.XzRd.plus(R.XzRd.rev(rd, 803, 4n), U32.add(base, U32.shln(hi, 4n)))

def XzLz.dist.far(model: Bool, rd: R.XzRd, +slot: U32, +nd: U32, +base: U32) -> R.XzSym:
  match model:
    case True{}:
      R.XzRd.plus(R.XzRd.rev(rd, U32.sub(U32.add(688, base), slot), U32.to_nat(nd)), base)
    case False{}:
      XzLz.dist.align(R.XzRd.direct(rd, U32.to_nat(U32.sub(nd, 4))), base)

def XzLz.dist.pick(small: Bool, rd: R.XzRd, +slot: U32) -> R.XzSym:
  match small:
    case True{}:
      R.XzSym{rd, slot}
    case False{}:
      +nd = U32.sub(U32.shr(slot), 1)
      +base = U32.shln(U32.or(2, U32.and(slot, 1)), U32.to_nat(nd))
      XzLz.dist.far(U32.is_lt(slot, 14), rd, slot, nd, base)

def XzLz.dist.slot(r: R.XzSym) -> R.XzSym:
  R.XzSym{rd, +slot} = r
  XzLz.dist.pick(U32.is_lt(slot, 4), rd, slot)

def XzLz.distance(rd: R.XzRd, +ls: U32) -> R.XzSym:
  XzLz.dist.slot(R.XzRd.tree(rd, U32.add(432, U32.shln(ls, 6n)), 6n))

# The end marker: a match whose distance is 2^32 (stored as one less,
# 4294967295). It copies nothing: the registers keep that distance as rep0,
# no length pending, and ok False (the distance fits nowhere), so a decoder
# that does not expect it (LZMA2) sees corruption, and one that does (the
# .lzma format) sees XzLzRegs.at_end
def XzLzRegs.end_mark(r: XzLzRegs) -> XzLzRegs:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLzRegs{state, rep0, rep1, rep2, rep3, 0, pos, prev, lc, lpmask, pbmask, dsize, False{}}

def XzLz.match.go(eom: Bool, rd: R.XzRd, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  match eom:
    case True{}:
      XzLzma{rd, dict, XzLzRegs.end_mark(regs), out}
    case False{}:
      XzLz.copy(rd, dict, regs, out)

# A match: its length, then its distance, which must lie within the bytes
# written and the dictionary
def XzLz.match.dist(r: R.XzSym, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>, +l: U32) -> XzLzma:
  R.XzSym{rd, +d} = r
  match regs:
    case XzLzRegs{+state, +rep0, +rep1, +rep2, rep3, len, +pos, prev, lc, lpmask, pbmask, +dsize, ok}:
      +fits = Bool.and(U32.is_lt(d, pos), U32.is_lt(d, dsize))
      XzLz.match.go(U32.is_eq(d, 4294967295), rd, dict, XzLzRegs{XzLz.after_match(state), d, rep0, rep1, rep2, U32.add(l, 2), pos, prev, lc, lpmask, pbmask, dsize, Bool.and(ok, fits)}, out)

def XzLz.match.len(r: R.XzSym, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzSym{rd, +l} = r
  XzLz.match.dist(XzLz.distance(rd, U32.min(l, 3)), dict, regs, out, l)

# A rep match: its length; the distances were already rotated
def XzLz.rep.len(r: R.XzSym, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzSym{rd, +l} = r
  match regs:
    case XzLzRegs{+state, rep0, rep1, rep2, rep3, len, +pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLz.copy(rd, dict, XzLzRegs{XzLz.after_rep(state), rep0, rep1, rep2, rep3, U32.add(l, 2), pos, prev, lc, lpmask, pbmask, dsize, Bool.and(ok, U32.is_gt(pos, 0))}, out)

def XzLz.posstate(+regs: XzLzRegs) -> U32:
  match regs:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      U32.and(pos, pbmask)

def XzLz.state(+regs: XzLzRegs) -> U32:
  match regs:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      state

# rep0 kept, or rep1, rep2 or rep3 moved to the front
def XzLzRegs.use1(r: XzLzRegs) -> XzLzRegs:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLzRegs{state, rep1, rep0, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}

def XzLzRegs.use2(r: XzLzRegs) -> XzLzRegs:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLzRegs{state, rep2, rep0, rep1, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}

def XzLzRegs.use3(r: XzLzRegs) -> XzLzRegs:
  match r:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLzRegs{state, rep3, rep0, rep1, rep2, len, pos, prev, lc, lpmask, pbmask, dsize, ok}

# A short rep: one byte from rep0
def XzLzRegs.short(r: XzLzRegs) -> XzLzRegs:
  match r:
    case XzLzRegs{+state, rep0, rep1, rep2, rep3, len, +pos, prev, lc, lpmask, pbmask, dsize, ok}:
      XzLzRegs{XzLz.after_short(state), rep0, rep1, rep2, rep3, 1, pos, prev, lc, lpmask, pbmask, dsize, Bool.and(ok, U32.is_gt(pos, 0))}

def XzLz.is_g2(r: R.XzBit, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzBit{rd, b} = r
  match b:
    case False{}:
      XzLz.rep.len(XzLz.length(rd, 1333, XzLz.posstate(regs)), dict, XzLzRegs.use2(regs), out)
    case True{}:
      XzLz.rep.len(XzLz.length(rd, 1333, XzLz.posstate(regs)), dict, XzLzRegs.use3(regs), out)

def XzLz.is_g1(r: R.XzBit, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzBit{rd, b} = r
  match b:
    case False{}:
      XzLz.rep.len(XzLz.length(rd, 1333, XzLz.posstate(regs)), dict, XzLzRegs.use1(regs), out)
    case True{}:
      XzLz.is_g2(R.XzRd.bit(rd, U32.add(228, XzLz.state(regs))), dict, regs, out)

def XzLz.is_long(r: R.XzBit, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzBit{rd, b} = r
  match b:
    case False{}:
      XzLz.copy(rd, dict, XzLzRegs.short(regs), out)
    case True{}:
      XzLz.rep.len(XzLz.length(rd, 1333, XzLz.posstate(regs)), dict, regs, out)

def XzLz.is_g0(r: R.XzBit, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzBit{rd, b} = r
  match b:
    case False{}:
      XzLz.is_long(R.XzRd.bit(rd, U32.add(240, U32.add(U32.shln(XzLz.state(regs), 4n), XzLz.posstate(regs)))), dict, regs, out)
    case True{}:
      XzLz.is_g1(R.XzRd.bit(rd, U32.add(216, XzLz.state(regs))), dict, regs, out)

def XzLz.is_rep(r: R.XzBit, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzBit{rd, b} = r
  match b:
    case False{}:
      XzLz.match.len(XzLz.length(rd, 819, XzLz.posstate(regs)), dict, regs, out)
    case True{}:
      XzLz.is_g0(R.XzRd.bit(rd, U32.add(204, XzLz.state(regs))), dict, regs, out)

def XzLz.is_match(r: R.XzBit, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  R.XzBit{rd, b} = r
  match b:
    case False{}:
      XzLz.literal(rd, dict, regs, out)
    case True{}:
      XzLz.is_rep(R.XzRd.bit(rd, U32.add(192, XzLz.state(regs))), dict, regs, out)

def XzLz.symbol(rd: R.XzRd, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  XzLz.is_match(R.XzRd.bit(rd, U32.add(U32.shln(XzLz.state(regs), 4n), XzLz.posstate(regs))), dict, regs, out)

def XzLz.step.pick(pending: Bool, rd: R.XzRd, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzma:
  match pending:
    case True{}:
      XzLz.copy(rd, dict, regs, out)
    case False{}:
      XzLz.symbol(rd, dict, regs, out)

def XzLz.pending(+regs: XzLzRegs) -> Bool:
  match regs:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, pos, prev, lc, lpmask, pbmask, dsize, ok}:
      Bool.not(U32.is_eq(len, 0))

# One step: exactly one byte out
def XzLzma.step(s: XzLzma) -> XzLzma:
  XzLzma{rd, dict, +regs, out} = s
  XzLz.step.pick(XzLz.pending(regs), rd, dict, regs, out)

# n steps: n bytes out
def XzLzma.run(n: Nat, s: XzLzma) -> XzLzma:
  match n:
    case 0n:
      s
    case 1n+p:
      XzLzma.run(p, XzLzma.step(s))

# The dictionary side of the decoder, between chunks
type XzLzDict is Type:
  XzLzDict{dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>}

# Bytes copied in as they are (an uncompressed chunk)
def XzLz.put.raw(dict: Array<U32>, regs: XzLzRegs, +b: U32) -> Array<U32> & XzLzRegs:
  match regs:
    case XzLzRegs{state, rep0, rep1, rep2, rep3, len, +pos, prev, lc, lpmask, pbmask, dsize, ok}:
      (Array.set(U32, dict, pos, b), XzLzRegs{state, rep0, rep1, rep2, rep3, len, U32.add(pos, 1), b, lc, lpmask, pbmask, dsize, ok})

def XzLzma.copy_in.go(xs: List<&2, U32>, st: Array<U32> & XzLzRegs, out: List<&2, U32>) -> XzLzDict:
  match xs:
    case Nil{}:
      (dict, regs) = st
      XzLzDict{dict, regs, out}
    case Con{h, t}:
      (dict, regs) = st
      +b = U32.and(h, 255)
      XzLzma.copy_in.go(t, XzLz.put.raw(dict, regs, b), Con{b, out})

def XzLzma.copy_in(xs: List<&2, U32>, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>) -> XzLzDict:
  XzLzma.copy_in.go(xs, (dict, regs), out)

# The result of decoding one LZMA chunk: the probabilities, dictionary and
# registers to carry on with, the output so far, and whether the chunk ended
# cleanly (the range decoder read exactly its input and ended at 0, every
# distance was possible, and no match runs past the chunk)
type XzLzChunk is Type:
  XzLzChunk{probs: Array<U32>, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>, ok: Bool}

def XzLzma.chunk.fin2(r: Array<U32> & Bool, dict: Array<U32>, +regs: XzLzRegs, out: List<&2, U32>) -> XzLzChunk:
  (probs, ok) = r
  XzLzChunk{probs, dict, regs, out, Bool.and(ok, XzLzRegs.clean(regs))}

def XzLzma.chunk.fin(s: XzLzma) -> XzLzChunk:
  XzLzma{rd, dict, regs, out} = s
  XzLzma.chunk.fin2(R.XzRd.finish(rd), dict, regs, out)

# One LZMA chunk: n bytes out from the compressed bytes input
def XzLzma.chunk(n: Nat, probs: Array<U32>, dict: Array<U32>, regs: XzLzRegs, out: List<&2, U32>, input: List<&2, U32>) -> XzLzChunk:
  XzLzma.chunk.fin(XzLzma.run(n, XzLzma{R.XzRd.start(probs, input), dict, regs, out}))

# The dictionary array: 2^k slots for the least k with 2^k at least need (k
# at most 31). It grows (doubling at least) as the output does, up to 2^max
# slots, and only before positions wrap, so slot i keeps position i.
def XzLzma.dict_depth.pick(small: Bool, +need: U32) -> Nat:
  match small:
    case True{}:
      0n
    case False{}:
      1n+U32.log2(U32.sub(need, 1))

def XzLzma.dict_depth(+need: U32) -> Nat:
  XzLzma.dict_depth.pick(U32.is_le(need, 1), need)

def XzLzma.dict_grow.copy(n: Nat, r: Array<U32> & U32, new: Array<U32>, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      (old, +v) = r
      Array.set(U32, new, i, v)
    case 1n+p:
      (old, +v) = r
      +j = U32.add(i, 1)
      XzLzma.dict_grow.copy(p, Array.get(U32, old, j), Array.set(U32, new, i, v), j)

def XzLzma.dict_grow.pick(more: Bool, dict: Array<U32>, +cur: Nat, +want: Nat) -> Array<U32>:
  match more:
    case True{}:
      XzLzma.dict_grow.copy(U32.to_nat(U32.sub(U32.shln(1, cur), 1)), Array.get(U32, dict, 0), Array.new(U32, want, 0), 0)
    case False{}:
      dict

# the depth for writing u more bytes at position pos (cur now, max at most)
def XzLzma.dict_want(+cur: Nat, +max: Nat, +pos: U32, +u: U32) -> Nat:
  Nat.max(cur, Nat.min(max, XzLzma.dict_depth(U32.min(U32.add(pos, u), 2147483648))))

# the array of 2^cur slots, grown to 2^want if that is more
def XzLzma.dict_grow(dict: Array<U32>, +cur: Nat, +want: Nat) -> Array<U32>:
  XzLzma.dict_grow.pick(Nat.is_lt(cur, want), dict, cur, want)
