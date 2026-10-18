# bend-osdev-bzip2: compression (the encoder side of Tsai, "BZip2 Format
# Specification", sections 2 to 4).
#
# The input is cut into blocks as it is RLE1-encoded: a block takes runs
# until its RLE1 bytes would pass the block size (level x 100,000, less 19,
# as the bzip2 tool leaves). Each block is transformed (bwt.bend), move-to-
# front and RLE2 coded (mtf.bend), and Huffman coded with one table built
# from its symbol frequencies, no code longer than 17 bits. The format asks
# for at least two tables, so the block carries the same table twice and
# every selector names the first. That is a valid stream, though larger than
# the bzip2 tool's, which fits up to six tables to the data.
#
# Streaming: Bzip2Writer.start, feed and finish. The writer holds the input
# not yet in a block and the bits not yet a whole byte; each feed answers the
# whole bytes ready. A feed that does not complete a block scans the held
# input again on the next feed, so feeding many tiny pieces costs time
# quadratic in the block size.
import Base
import ../bytes/bytes.bend as B
import ./list.bend as L
import ./bits.bend as K
import ./rle.bend as R
import ./mtf.bend as M
import ./bwt.bend as W
import ./huffman.bend as H
import ./stream.bend as S

# The options: the block size digit, 1 to 9 (values outside are taken as 9),
# and the longest Huffman code allowed, 9 to 20 (values outside are taken as
# the nearest; every decoder takes 20, the bzip2 tool writes at most 17)
type Bzip2CompressOptions is Data:
  Bzip2CompressOptions{level: U32, max_code: U32}

# level 9, codes of at most 17 bits, as the bzip2 tool
def Bzip2CompressOptions.default() -> Bzip2CompressOptions:
  Bzip2CompressOptions{9, 17}

def cmp.level.pick(ok: Bool, +l: U32) -> U32:
  match ok:
    case True{}:
      l
    case False{}:
      9

# Cutting the input into blocks

def cmp.level(+l: U32) -> U32:
  cmp.level.pick(Bool.and(U32.is_le(1, l), U32.is_le(l, 9)), l)

# a block: its RLE1 bytes and its input bytes, both reversed; the input after
# it; whether it was closed by the block size (False: the input ran out)
type Bzip2Cut is Data:
  Bzip2Cut{rle: List<&2, U32>, raw: List<&2, U32>, rest: List<&2, U32>, full: Bool}

type Bzip2Scan is Data:
  Bzip2ScanGo{xs: List<&2, U32>, run: R.Bzip2Rle1Run, rle: List<&2, U32>, raw: List<&2, U32>, n: Nat}
  Bzip2ScanStop{c: Bzip2Cut}

def cut.close(fits: Bool, e: R.Bzip2Rle1Emit, +y: U32, t: List<&2, U32>, rle: List<&2, U32>, raw: List<&2, U32>, +n: Nat, +k: Nat) -> Bzip2Scan:
  match fits:
    case True{}:
      match e:
        case R.Bzip2Rle1Emit{out, run}:
          Bzip2ScanGo{t, run, L.bz.push(out, rle), Con{y, raw}, Nat.add(n, k)}
    case False{}:
      match e:
        case R.Bzip2Rle1Emit{out, run}:
          Bzip2ScanStop{Bzip2Cut{L.bz.push(out, rle), raw, Con{y, t}, True{}}}

def cut.step(+y: U32, t: List<&2, U32>, run: R.Bzip2Rle1Run, rle: List<&2, U32>, raw: List<&2, U32>, +n: Nat, +cap: Nat) -> Bzip2Scan:
  +e = R.rle1.enc.step(y, run)
  +k = L.bz.len(R.rle1.emit.out(e))
  cut.close(Nat.is_le(Nat.add(Nat.add(n, k), 5n), cap), e, B.byte(y), t, rle, raw, n, k)

def cut.go(fuel: Nat, st: Bzip2Scan, +cap: Nat) -> Bzip2Cut:
  match fuel:
    case 0n:
      match st:
        case Bzip2ScanStop{c}:
          c
        case Bzip2ScanGo{xs, run, rle, raw, n}:
          Bzip2Cut{L.bz.push(R.rle1.emit.run(run), rle), raw, xs, False{}}
    case 1n+f:
      match st:
        case Bzip2ScanStop{c}:
          c
        case Bzip2ScanGo{xs, run, rle, raw, n}:
          match xs:
            case Nil{}:
              Bzip2Cut{L.bz.push(R.rle1.emit.run(run), rle), raw, Nil{}, False{}}
            case Con{y, t}:
              cut.go(f, cut.step(y, t, run, rle, raw, n, cap), cap)

# the next block of xs, at most cap RLE1 bytes
def cut(+xs: List<&2, U32>, +cap: Nat) -> Bzip2Cut:
  cut.go(1n+L.bz.len(xs), Bzip2ScanGo{xs, R.rle1.enc.start(), Nil{}, Nil{}, 0n}, cap)

# Writing a block

def wr.bits(w: K.Bzip2Out, +n: Nat, v: U32) -> K.Bzip2Out:
  K.out.bits(w, n, v)

# the symbol map: 16 group bits, then 16 bits for each group used
def wr.flags(xs: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{h, t}:
      wr.flags(t, Array.set(U32, a, h, 1))

# the 16 bits of group g (flags of bytes 16g to 16g + 15, the first highest)
def wr.group.go(n: Nat, r: Array<U32> & U32, +i: U32, +v: U32) -> Array<U32> & U32:
  match n:
    case 0n:
      (a, f) = r
      (a, v)
    case 1n+p:
      (a, f) = r
      +j = U32.add(i, 1)
      wr.group.go(p, Array.get(U32, a, j), j, U32.or(U32.shl(v), f))

def wr.group(a: Array<U32>, +g: U32) -> Array<U32> & U32:
  +i = U32.mul(g, 16)
  wr.group.go(16n, Array.get(U32, a, i), i, 0)

def wr.map.used(ws: List<&2, U32>, +v: U32) -> U32:
  match ws:
    case Nil{}:
      v
    case Con{w, t}:
      wr.map.used(t, U32.or(U32.shl(v), K.bits.b(U32.is_ne(w, 0))))

def wr.map.word(on: Bool, x: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  match on:
    case True{}:
      K.out.bits(w, 16n, x)
    case False{}:
      w

def wr.map.words(ws: List<&2, U32>, w: K.Bzip2Out) -> K.Bzip2Out:
  match ws:
    case Nil{}:
      w
    case Con{+x, t}:
      wr.map.words(t, wr.map.word(U32.is_ne(x, 0), x, w))

# the 16 group words, in order (reversed into acc); r: the array and the
# word of group g
def wr.groups(n: Nat, r: Array<U32> & U32, +g: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, v) = r
      +h = U32.add(g, 1)
      wr.groups(p, wr.group(a, h), h, Con{v, acc})

def wr.map(+alpha: List<&2, U32>, w: K.Bzip2Out) -> K.Bzip2Out:
  +ws = L.bz.rev(wr.groups(16n, wr.group(wr.flags(alpha, [0 : U32*256n]), 0), 0, Nil{}))
  wr.map.words(ws, K.out.bits(w, 16n, wr.map.used(ws, 0)))

# n selectors, all naming table 0 (each a single 0 bit)
def wr.sels(n: Nat, w: K.Bzip2Out) -> K.Bzip2Out:
  match n:
    case 0n:
      w
    case 1n+p:
      wr.sels(p, K.out.bit(w, 0))

def wr.steps.up(n: Nat, more: Bool, +cur: U32, +l: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  match n:
    case 0n:
      K.out.bit(w, 0)
    case 1n+p:
      match more:
        case True{}:
          wr.steps.up(p, U32.is_lt(U32.add(cur, 1), l), U32.add(cur, 1), l, K.out.bits(w, 2n, 2))
        case False{}:
          K.out.bit(w, 0)

def wr.steps.down(n: Nat, more: Bool, +cur: U32, +l: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  match n:
    case 0n:
      K.out.bit(w, 0)
    case 1n+p:
      match more:
        case True{}:
          wr.steps.down(p, U32.is_gt(U32.sub(cur, 1), l), U32.sub(cur, 1), l, K.out.bits(w, 2n, 3))
        case False{}:
          K.out.bit(w, 0)

def wr.steps.pick(c: Cmp, +cur: U32, +l: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  match c:
    case EQ{}:
      K.out.bit(w, 0)
    case LT{}:
      wr.steps.up(20n, True{}, cur, l, w)
    case GT{}:
      wr.steps.down(20n, True{}, cur, l, w)

def wr.steps(n: Nat, +cur: U32, +l: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  wr.steps.pick(U32.cmp(cur, l), cur, l, w)

# the lengths of a table: a 5-bit start (the first length), then each length
# as steps from the one before
def wr.lens.go(ls: List<&2, U32>, +cur: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  match ls:
    case Nil{}:
      w
    case Con{+l, t}:
      wr.lens.go(t, l, wr.steps(20n, cur, l, w))

def wr.head(ls: List<&2, U32>) -> U32:
  match ls:
    case Nil{}:
      1
    case Con{h, t}:
      h

def wr.lens(+ls: List<&2, U32>, w: K.Bzip2Out) -> K.Bzip2Out:
  +first = wr.head(ls)
  wr.lens.go(ls, first, K.out.bits(w, 5n, first))

# the symbols, each by its code
def wr.code(r: Array<U32> & U32, w: K.Bzip2Out) -> Array<U32> & K.Bzip2Out:
  (a, +v) = r
  (a, K.out.bits(w, U32.to_nat(U32.shrn(v, 24n)), U32.and(v, 16777215)))

def wr.syms(xs: List<&2, U32>, aw: Array<U32> & K.Bzip2Out) -> K.Bzip2Out:
  match xs:
    case Nil{}:
      (a, w) = aw
      w
    case Con{h, t}:
      (a, w) = aw
      wr.syms(t, wr.code(Array.get(U32, a, h), w))

# symbol frequencies, for na symbols
def wr.freq(xs: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{+h, t}:
      wr.freq(t, W.bwt.bump(Array.get(U32, a, h), h))

def wr.freqs.go(n: Nat, r: Array<U32> & U32, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, v) = r
      +j = U32.sub(i, 1)
      wr.freqs.go(p, Array.get(U32, a, j), j, Con{v, acc})

def wr.freqs(+syms: List<&2, U32>, +na: Nat) -> List<&2, U32>:
  +top = U32.sub(U32.from_nat(na), 1)
  wr.freqs.go(na, Array.get(U32, wr.freq(syms, [0 : U32*512n]), top), top, Nil{})

# the symbols of a block: MTF and RLE2 of its last column, then the end of
# block
def wr.symbols(+last: List<&2, U32>, +alpha: List<&2, U32>) -> List<&2, U32>:
  L.bz.rev(Con{U32.from_nat(1n+L.bz.len(alpha)), L.bz.rev(M.mtf.enc.fast(last, alpha, Nil{}, Nil{}))})

def wr.selectors(+n: Nat) -> Nat:
  Nat.div(Nat.add(n, 49n), 50n)

def wr.block.syms(+syms: List<&2, U32>, +na: Nat, +lim: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  +ls = H.huff_lengths(wr.freqs(syms, na), lim)
  +nsym = L.bz.len(syms)
  +w2 = wr.lens(ls, wr.lens(ls, wr.sels(wr.selectors(nsym), wr.bits(wr.bits(w, 3n, 2), 15n, U32.from_nat(wr.selectors(nsym))))))
  wr.syms(syms, (H.huff_codes(ls), w2))

# the block header: the magic, the CRC, the randomised bit (0), origPtr
def wr.block.head(w: K.Bzip2Out, +crc: U32, +ptr: U32) -> K.Bzip2Out:
  K.out.bits(K.out.bit(K.out.bits(K.out.bits(K.out.bits(w, 24n, 3227993), 24n, 2511705), 32n, crc), 0), 24n, ptr)

def wr.block.bwt(b: W.Bzip2BwtList, +alpha: List<&2, U32>, +crc: U32, +lim: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  match b:
    case W.Bzip2BwtList{last, +ptr}:
      wr.block.syms(wr.symbols(last, alpha), 1n+1n+L.bz.len(alpha), lim, wr.map(alpha, wr.block.head(w, crc, ptr)))

# one block: the header, the symbol map, two tables, the selectors and the
# symbols
def wr.block(+rle: List<&2, U32>, +crc: U32, +lim: U32, w: K.Bzip2Out) -> K.Bzip2Out:
  wr.block.bwt(W.bwt_forward_list(rle), M.mtf.used(rle), crc, lim, w)

# The writer: the options (normalized), the bits written and not yet handed
# out, the combined CRC, and the input not yet in a block

type Bzip2Writer is Data:
  Bzip2Writer{opts: Bzip2CompressOptions, out: K.Bzip2Out, comb: U32, buf: List<&2, U32>}

# what a feed answers: the writer, and the bytes ready
type Bzip2Written is Data:
  Bzip2Written{writer: Bzip2Writer, bytes: B.Octets}

# the most RLE1 bytes a block takes
def wr.cap(o: Bzip2CompressOptions) -> Nat:
  match o:
    case Bzip2CompressOptions{level, lim}:
      Nat.sub(Nat.mul(U32.to_nat(level), 100000n), 19n)

def wr.lim(o: Bzip2CompressOptions) -> U32:
  match o:
    case Bzip2CompressOptions{level, lim}:
      lim

def wr.norm(+level: U32, lim: U32) -> Bzip2CompressOptions:
  Bzip2CompressOptions{level, U32.clamp(lim, 9, 20)}

# the stream header
def Bzip2Writer.start(opts: Bzip2CompressOptions) -> Bzip2Writer:
  match opts:
    case Bzip2CompressOptions{l, lim}:
      +level = cmp.level(l)
      Bzip2Writer{wr.norm(level, lim), K.out.bits(K.out.bits(K.out.bits(K.out.bits(K.out.new(), 8n, 66), 8n, 90), 8n, 104), 8n, U32.add(48, level)), 0, Nil{}}

# one block written (crc: its input's CRC)
def wr.put(+rle: List<&2, U32>, +crc: U32, +set: Bzip2CompressOptions, w: K.Bzip2Out, +comb: U32, buf: List<&2, U32>) -> Bzip2Writer:
  Bzip2Writer{set, wr.block(L.bz.rev(rle), crc, wr.lim(set), w), S.bzip2_combine(comb, crc), buf}

type Bzip2WrStep is Data:
  Bzip2WrMore{w: Bzip2Writer}
  Bzip2WrWait{w: Bzip2Writer}

def wr.cut(c: Bzip2Cut, +set: Bzip2CompressOptions, w: K.Bzip2Out, +comb: U32) -> Bzip2WrStep:
  match c:
    case Bzip2Cut{rle, +raw, rest, full}:
      match full:
        case True{}:
          Bzip2WrMore{wr.put(rle, S.bzip2_crc(B.Octets.of_list(L.bz.rev(raw))), set, w, comb, rest)}
        case False{}:
          Bzip2WrWait{Bzip2Writer{set, w, comb, L.bz.rev(raw)}}

# every block the buffer fills, written
def wr.blocks(fuel: Nat, st: Bzip2WrStep) -> Bzip2Writer:
  match fuel:
    case 0n:
      match st:
        case Bzip2WrMore{w}:
          w
        case Bzip2WrWait{w}:
          w
    case 1n+f:
      match st:
        case Bzip2WrWait{w}:
          w
        case Bzip2WrMore{w}:
          match w:
            case Bzip2Writer{+set, out, comb, +buf}:
              wr.blocks(f, wr.cut(cut(buf, wr.cap(set)), set, out, comb))

def wr.hand.go(r: List<&2, U32> & K.Bzip2Out, set: Bzip2CompressOptions, comb: U32, buf: List<&2, U32>) -> Bzip2Written:
  (acc, out) = r
  Bzip2Written{Bzip2Writer{set, out, comb, buf}, B.Octets.of_list(L.bz.rev(acc))}

def wr.hand(w: Bzip2Writer) -> Bzip2Written:
  match w:
    case Bzip2Writer{set, out, comb, buf}:
      wr.hand.go(K.out.take(out), set, comb, buf)

# more input: the bytes of every block it completes
def Bzip2Writer.feed(w: Bzip2Writer, o: B.Octets) -> Bzip2Written:
  match w:
    case Bzip2Writer{set, out, comb, buf}:
      +xs = L.bz.push(L.bz.rev(buf), B.Octets.to_list(o))
      wr.hand(wr.blocks(1n+L.bz.len(xs), Bzip2WrMore{Bzip2Writer{set, out, comb, xs}}))

def wr.last(c: Bzip2Cut, +set: Bzip2CompressOptions, w: K.Bzip2Out, +comb: U32) -> Bzip2Writer:
  match c:
    case Bzip2Cut{rle, +raw, rest, full}:
      match raw:
        case Nil{}:
          Bzip2Writer{set, w, comb, Nil{}}
        case Con{h, t}:
          wr.put(rle, S.bzip2_crc(B.Octets.of_list(L.bz.rev(Con{h, t}))), set, w, comb, Nil{})

def wr.end(w: Bzip2Writer) -> List<&2, U32>:
  match w:
    case Bzip2Writer{set, out, +comb, buf}:
      K.out.finish(K.out.bits(K.out.bits(K.out.bits(out, 24n, 1536581), 24n, 3690640), 32n, comb))

# the end: the last block (whatever input is held), the end of the stream and
# the combined CRC, padded to a whole byte
def Bzip2Writer.finish(w: Bzip2Writer) -> B.Octets:
  match w:
    case Bzip2Writer{+set, out, comb, +buf}:
      B.Octets.of_list(wr.end(wr.last(cut(buf, wr.cap(set)), set, out, comb)))

def wr.written.bytes(r: Bzip2Written) -> B.Octets:
  match r:
    case Bzip2Written{w, bytes}:
      bytes

def wr.written.writer(r: Bzip2Written) -> Bzip2Writer:
  match r:
    case Bzip2Written{w, bytes}:
      w

# o compressed, with these options
def compress_with(opts: Bzip2CompressOptions, o: B.Octets) -> B.Octets:
  +r = Bzip2Writer.feed(Bzip2Writer.start(opts), o)
  B.Octets.append(wr.written.bytes(r), Bzip2Writer.finish(wr.written.writer(r)))

# o compressed with the default options (level 9, codes of at most 17 bits)
def compress(o: B.Octets) -> B.Octets:
  compress_with(Bzip2CompressOptions.default(), o)
