# bend-osdev-deflate: blocks (RFC 1951, 3.2.3 to 3.2.7): the choice of a
# block's type, stored, fixed or dynamic, and the writing of each.
#
# The deflater cuts its tokens into blocks of at most a given number of
# tokens (section 4: "The compressor terminates a block when it determines
# that starting a new block with fresh trees would be useful, or when the
# block size fills up the compressor's block buffer"; here the buffer's size
# is the parameter). For each block it counts the symbols, builds the dynamic
# codes (dynamic.bend), works out exactly how many bits each type would take
# from where the writer stands, and writes the smallest (DflBlockAuto), or
# the type the strategy names. A stored block holds at most 65535 bytes
# (3.2.4: LEN is 16 bits), so a longer one is written as several.
import Base
import ../bytes/bytes.bend as B
import ./bits.bend as K
import ./huffman.bend as H
import ./table.bend as T
import ./codes.bend as C
import ./match.bend as M
import ./dynamic.bend as D

type DflBlockStrategy is Data:
  # the smallest of stored, fixed and dynamic, block by block
  DflBlockAuto{}
  DflBlockFixed{}
  DflBlockDynamic{}
  DflBlockStored{}

# Symbol counts

def blk.bump(+s: U32, +t: T.DflTab) -> T.DflTab:
  T.tab.set9(s, t, U32.add(T.tab.get9(s, t), 1))

type DflFreq is Data:
  DflFreq{lt: T.DflTab, dt: T.DflTab}

def blk.freq.tok(t: M.DflTok, f: DflFreq) -> DflFreq:
  match t:
    case M.DflLit{b}:
      match f:
        case DflFreq{lt, dt}:
          DflFreq{blk.bump(b, lt), dt}
    case M.DflMatch{l, d}:
      match f:
        case DflFreq{lt, dt}:
          DflFreq{blk.bump(U32.add(C.code_of_len(l), 257), lt), blk.bump(C.code_of_dist(d), dt)}

def blk.freq.go(toks: List<&2, M.DflTok>, f: DflFreq) -> DflFreq:
  match toks:
    case Nil{}:
      f
    case Con{t, rest}:
      blk.freq.go(rest, blk.freq.tok(t, f))

# the counts of a block's literal/length symbols (the end of block, 256,
# once) and distance symbols
def blk.freq(toks: List<&2, M.DflTok>) -> DflFreq:
  blk.freq.go(toks, DflFreq{blk.bump(256, T.DflTNil{}), T.DflTNil{}})

# Sizes in bits

def blk.extra.lit(big: Bool, +i: U32) -> Nat:
  match big:
    case True{}:
      C.code_lext(U32.sub(i, 257))
    case False{}:
      0n

# the extra bits of literal/length symbol i (lit) or distance symbol i
def blk.extra(lit: Bool, +i: U32) -> Nat:
  match lit:
    case True{}:
      blk.extra.lit(U32.is_le(257, i), i)
    case False{}:
      C.code_dext(i)

# sum of count * (length + extra bits) over the symbols from i on
def blk.cost.go(fs: List<&2, U32>, ls: List<&2, U32>, +lit: Bool, +i: U32, n: Nat) -> Nat:
  match fs:
    case Nil{}:
      n
    case Con{f, ft}:
      match ls:
        case Nil{}:
          n
        case Con{l, lt}:
          blk.cost.go(ft, lt, lit, U32.add(i, 1), Nat.add(n, Nat.mul(U32.to_nat(f), Nat.add(U32.to_nat(l), blk.extra(lit, i)))))

# a block's bits after its header, with these code lengths
def blk.cost(+lf: List<&2, U32>, +df: List<&2, U32>, ll: List<&2, U32>, dl: List<&2, U32>) -> Nat:
  Nat.add(blk.cost.go(lf, ll, True{}, 0, 0n), blk.cost.go(df, dl, False{}, 0, 0n))

# a stored block of n bytes from a writer with k bits pending (several
# blocks past 65535 bytes, each after the first starting at a byte boundary)
def blk.stored.bits(+n: Nat, +k: Nat) -> Nat:
  +pad = Nat.mod(Nat.sub(8n, Nat.mod(Nat.add(k, 3n), 8n)), 8n)
  +chunks = Nat.max(1n, Nat.div(Nat.add(n, 65534n), 65535n))
  Nat.add(Nat.add(3n, pad), Nat.add(Nat.mul(Nat.sub(chunks, 1n), 8n), Nat.add(Nat.mul(chunks, 32n), Nat.mul(n, 8n))))

# Writing

def blk.put.sym(w: K.DflOut, +t: T.DflTab, +s: U32) -> K.DflOut:
  K.out.put(w, H.huff_bits(t, s), H.huff_len(t, s))

def blk.put.tok(w: K.DflOut, tk: M.DflTok, +lt: T.DflTab, +dt: T.DflTab) -> K.DflOut:
  match tk:
    case M.DflLit{b}:
      blk.put.sym(w, lt, b)
    case M.DflMatch{+l, +d}:
      +c = C.code_of_len(l)
      +e = C.code_of_dist(d)
      +w1 = K.out.put(blk.put.sym(w, lt, U32.add(c, 257)), U32.sub(l, C.code_lbase(c)), C.code_lext(c))
      K.out.put(blk.put.sym(w1, dt, e), U32.sub(d, C.code_dbase(e)), C.code_dext(e))

def blk.put.toks(toks: List<&2, M.DflTok>, w: K.DflOut, +lt: T.DflTab, +dt: T.DflTab) -> K.DflOut:
  match toks:
    case Nil{}:
      blk.put.sym(w, lt, 256)
    case Con{tk, rest}:
      blk.put.toks(rest, blk.put.tok(w, tk, lt, dt), lt, dt)

# a block's header bits: BFINAL, then BTYPE (two bits, low bit first)
def blk.head(w: K.DflOut, final: Bool, +btype: U32) -> K.DflOut:
  K.out.put(K.out.bit(w, final), btype, 2n)

def blk.fixed(w: K.DflOut, +final: Bool, toks: List<&2, M.DflTok>) -> K.DflOut:
  blk.put.toks(toks, blk.head(w, final, 1), H.huff_table(H.huff_fixed_lit()), H.huff_table(H.huff_fixed_dist()))

def blk.dynamic(w: K.DflOut, +final: Bool, toks: List<&2, M.DflTok>, +h: D.DflDynHdr, +ll: List<&2, U32>, +dl: List<&2, U32>) -> K.DflOut:
  blk.put.toks(toks, D.dyn_write_header(w, final, h), H.huff_table(ll), H.huff_table(dl))

# one stored block of at most 65535 bytes (3.2.4: the header bits, the rest
# of the byte skipped, LEN and NLEN, the bytes)
def blk.stored.one(w: K.DflOut, final: Bool, +xs: List<&2, U32>) -> K.DflOut:
  +n = U32.from_nat(B.len.fast(xs))
  K.out.bytes(K.out.bytes(K.out.align(blk.head(w, final, 0)), B.append.fast(B.le16(n), B.le16(U32.xor(n, 65535)))), xs)

# bytes as stored blocks: fuel blocks of 65535, then the rest (final if
# final)
def blk.stored.go(fuel: Nat, +final: Bool, w: K.DflOut, +xs: List<&2, U32>) -> K.DflOut:
  match fuel:
    case 0n:
      blk.stored.one(w, final, xs)
    case 1n+f:
      blk.stored.go(f, final, blk.stored.one(w, False{}, B.take.fast(65535n, xs)), B.drop(65535n, xs))

# bytes as stored blocks, 65535 at most each; the last final if final
def blk.stored(w: K.DflOut, +final: Bool, +xs: List<&2, U32>) -> K.DflOut:
  +n = B.len.fast(xs)
  blk.stored.go(Nat.sub(Nat.max(1n, Nat.div(Nat.add(n, 65534n), 65535n)), 1n), final, w, xs)

# Choosing

def blk.read(+n: Nat, +t: T.DflTab) -> List<&2, U32>:
  D.dyn.read(n, 0, t, Nil{})

# a block's counts, its dynamic codes' lengths and header
type DflDyn is Data:
  DflDyn{lf: List<&2, U32>, df: List<&2, U32>, ll: List<&2, U32>, dl: List<&2, U32>, h: D.DflDynHdr}

def blk.dyn.of(+lf: List<&2, U32>, +df: List<&2, U32>) -> DflDyn:
  +ll = D.dyn_lengths(lf, 15n)
  +dl = D.dyn_lengths(df, 15n)
  DflDyn{lf, df, ll, dl, D.dyn_header(ll, dl)}

def blk.dyn.freq(f: DflFreq) -> DflDyn:
  match f:
    case DflFreq{lt, dt}:
      blk.dyn.of(blk.read(286n, lt), blk.read(30n, dt))

def blk.dyn(toks: List<&2, M.DflTok>) -> DflDyn:
  blk.dyn.freq(blk.freq(toks))

def blk.dynamic.d(w: K.DflOut, +final: Bool, toks: List<&2, M.DflTok>, d: DflDyn) -> K.DflOut:
  match d:
    case DflDyn{lf, df, ll, dl, h}:
      blk.dynamic(w, final, toks, h, ll, dl)

def blk.min3.pick(a_le_b: Bool, a_le_c: Bool, b_le_c: Bool) -> U32:
  match a_le_b:
    case True{}:
      match a_le_c:
        case True{}:
          0
        case False{}:
          2
    case False{}:
      match b_le_c:
        case True{}:
          1
        case False{}:
          2

# 0: stored, 1: fixed, 2: dynamic, whichever is smallest (the first of
# equals)
def blk.min3(+a: Nat, +b: Nat, +c: Nat) -> U32:
  blk.min3.pick(Nat.is_le(a, b), Nat.is_le(a, c), Nat.is_le(b, c))

def blk.auto.coded(fixed: Bool, w: K.DflOut, +final: Bool, toks: List<&2, M.DflTok>, d: DflDyn) -> K.DflOut:
  match fixed:
    case True{}:
      blk.fixed(w, final, toks)
    case False{}:
      blk.dynamic.d(w, final, toks, d)

def blk.auto.at(stored: Bool, fixed: Bool, w: K.DflOut, +final: Bool, toks: List<&2, M.DflTok>, +raw: List<&2, U32>, d: DflDyn) -> K.DflOut:
  match stored:
    case True{}:
      blk.stored(w, final, raw)
    case False{}:
      blk.auto.coded(fixed, w, final, toks, d)

# the bits a fixed block takes after its header
def blk.fixed.cost(+lf: List<&2, U32>, +df: List<&2, U32>) -> Nat:
  blk.cost(lf, df, H.huff_fixed_lit(), H.huff_fixed_dist())

def blk.choose.of(+which: U32, w: K.DflOut, +final: Bool, toks: List<&2, M.DflTok>, +raw: List<&2, U32>, d: DflDyn) -> K.DflOut:
  blk.auto.at(U32.is_eq(which, 0), U32.is_eq(which, 1), w, final, toks, raw, d)

def blk.choose(+w: K.DflOut, +final: Bool, toks: List<&2, M.DflTok>, +raw: List<&2, U32>, +d: DflDyn) -> K.DflOut:
  match d:
    case DflDyn{+lf, +df, +ll, +dl, +h}:
      +stored = blk.stored.bits(B.len.fast(raw), Nat.mod(K.out.bits(w), 8n))
      +fixed = Nat.add(3n, blk.fixed.cost(lf, df))
      +dynamic = Nat.add(D.dyn_header_bits(h), blk.cost(lf, df, ll, dl))
      blk.choose.of(blk.min3(stored, fixed, dynamic), w, final, toks, raw, DflDyn{lf, df, ll, dl, h})

# The public interface

# one block holding the tokens toks, whose bytes are raw (final: it is the
# stream's last), of the type the strategy says
def block_write(w: K.DflOut, +final: Bool, s: DflBlockStrategy, +toks: List<&2, M.DflTok>, +raw: List<&2, U32>) -> K.DflOut:
  match s:
    case DflBlockStored{}:
      blk.stored(w, final, raw)
    case DflBlockFixed{}:
      blk.fixed(w, final, toks)
    case DflBlockDynamic{}:
      blk.dynamic.d(w, final, toks, blk.dyn(toks))
    case DflBlockAuto{}:
      blk.choose(w, final, toks, raw, blk.dyn(toks))

# how many bytes tokens stand for
def blk.span(toks: List<&2, M.DflTok>, n: Nat) -> Nat:
  match toks:
    case Nil{}:
      n
    case Con{t, rest}:
      match t:
        case M.DflLit{b}:
          blk.span(rest, 1n+n)
        case M.DflMatch{l, d}:
          blk.span(rest, Nat.add(U32.to_nat(l), n))

# the writer, the tokens still to write, their bytes
type DflCut is Data:
  DflCut{w: K.DflOut, toks: List<&2, M.DflTok>, raw: List<&2, U32>}

def blk.cut.last(more: List<&2, M.DflTok>) -> Bool:
  match more:
    case Nil{}:
      True{}
    case Con{t, r}:
      False{}

# the next block: its first bt tokens
def blk.cut.step(+final: Bool, +s: DflBlockStrategy, +bt: Nat, w: K.DflOut, +toks: List<&2, M.DflTok>, +raw: List<&2, U32>) -> DflCut:
  +these = List.take(&2, M.DflTok, toks, bt)
  +more = List.drop(&2, M.DflTok, toks, bt)
  +n = blk.span(these, 0n)
  DflCut{block_write(w, Bool.and(final, blk.cut.last(more)), s, these, B.take.fast(n, raw)), more, B.drop(n, raw)}

def blk.cut.go(fuel: Nat, +final: Bool, +s: DflBlockStrategy, +bt: Nat, st: DflCut) -> K.DflOut:
  match fuel:
    case 0n:
      match st:
        case DflCut{w, toks, raw}:
          w
    case 1n+f:
      match st:
        case DflCut{w, toks, raw}:
          match toks:
            case Nil{}:
              w
            case Con{t, ts}:
              blk.cut.go(f, final, s, bt, blk.cut.step(final, s, bt, w, Con{t, ts}, raw))

# tokens (standing for the bytes raw) as blocks of at most bt tokens (at
# least 1); the last block is final if final; no tokens at all make one
# empty block
def blocks_write(w: K.DflOut, +final: Bool, +s: DflBlockStrategy, +bt: Nat, +toks: List<&2, M.DflTok>, +raw: List<&2, U32>) -> K.DflOut:
  match toks:
    case Nil{}:
      block_write(w, final, s, Nil{}, raw)
    case Con{t, ts}:
      +b = Nat.max(bt, 1n)
      blk.cut.go(1n+Nat.div(List.length(&2, M.DflTok, Con{t, ts}), b), final, s, b, DflCut{w, Con{t, ts}, raw})
