# bend-osdev-zstd, compression: a frame writer with raw, RLE and compressed
# blocks (RFC 8878), the compressed ones from a greedy LZ77 matcher, raw
# literals and the predefined sequence tables.
#
# compress checks its own output: it decodes the frame and, should that not
# give the input back, answers a frame of raw blocks (raw_frame) instead,
# whose decoding is proved. So LAWS.bend can say, for every input, that what
# it writes decodes back to the input.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bits.bend as Bi
import ./fse.bend as F
import ./sequences.bend as S
import ./xxh64.bend as X
import ./frame.bend as Fr
import ./zstd.bend as Z

# block_size: where the content is cut into blocks (1 to 131072; 0 or more
# means 131072); checksum: a content checksum; matcher: compressed blocks
# (else raw and RLE blocks only)
type ZstdCompressOptions is Data:
  ZstdCompressOptions{block_size: U32, checksum: Bool, matcher: Bool}

def ZstdCompressOptions.default() -> ZstdCompressOptions:
  ZstdCompressOptions{131072, True{}, True{}}

# Small helpers

def cmp.le(n: Nat, +v: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      B.rev(acc)
    case 1n+k:
      cmp.le(k, Nat.div(v, 256n), Con{U32.from_nat(Nat.mod(v, 256n)), acc})

# the n-byte little-endian field of v
def cmp.field(n: Nat, +v: Nat) -> List<&2, U32>:
  cmp.le(n, v, Nil{})

def cmp.pick(-A: Data, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

# The frame header: single-segment, with the content size (1, 2, 4 or 8
# bytes), and the checksum flag

# the content size field: 1 byte below 256, 2 (less 256) below 65792, 4 up
# to 2^32 - 1, else 8 (each test made only if the one before fails)
def cmp.fcs_flag.wide(small: Bool) -> Nat:
  match small:
    case True{}:
      2n
    case False{}:
      3n

def cmp.fcs_flag.mid(small: Bool, +n: Nat) -> Nat:
  match small:
    case True{}:
      1n
    case False{}:
      cmp.fcs_flag.wide(Nat.is_le(n, 4294967295n))

def cmp.fcs_flag.go(small: Bool, +n: Nat) -> Nat:
  match small:
    case True{}:
      0n
    case False{}:
      cmp.fcs_flag.mid(Nat.is_lt(n, 65792n), n)

def cmp.fcs_flag(+n: Nat) -> Nat:
  cmp.fcs_flag.go(Nat.is_lt(n, 256n), n)

def cmp.fcs_field(flag: Nat, +n: Nat) -> List<&2, U32>:
  match flag:
    case 0n:
      cmp.field(1n, n)
    case 1n+p:
      match p:
        case 0n:
          cmp.field(2n, Nat.sub(n, 256n))
        case 1n+q:
          match q:
            case 0n:
              cmp.field(4n, n)
            case 1n+r:
              cmp.field(8n, n)

def cmp.header(+n: Nat, check: Bool) -> List<&2, U32>:
  +flag = cmp.fcs_flag(n)
  +fhd = Nat.add(Nat.add(Nat.mul(flag, 64n), 32n), cmp.pick(Nat, check, 4n, 0n))
  Con{40, Con{181, Con{47, Con{253, Con{U32.from_nat(fhd), cmp.fcs_field(flag, n)}}}}}

# a block header: last, type, size
def cmp.bh(last: Bool, +t: Nat, +size: Nat) -> List<&2, U32>:
  cmp.field(3n, Nat.add(Nat.add(cmp.pick(Nat, last, 1n, 0n), Nat.mul(t, 2n)), Nat.mul(size, 8n)))

# The matcher: a greedy LZ77 matcher with a single-entry hash table (16384
# slots, keyed by the next four bytes). Every match it takes has 4 bytes or
# more and stays inside its block; offsets reach back anywhere in the frame
# (the frame is single-segment: its window is its whole content).

# a table slot: a position + 1 (0: empty), and the content from there on
type ZsCand is Data:
  ZsCand{pos: Nat, suf: List<&2, U32>}

# a sequence found: literals length, offset, match length
type ZsCSeq is Data:
  ZsCSeq{ll: Nat, off: Nat, ml: Nat}

# 14 bits of a hash of the next four bytes
def cmp.hash(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      U32.shrn(U32.mul(U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n))), 2654435761), 18n)
    case _:
      0

# the first bytes of a and b are the same
def cmp.heads(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a:
    case Con{x, s}:
      match b:
        case Con{y, t}:
          U32.is_eq(x, y)
        case Nil{}:
          False{}
    case Nil{}:
      False{}

# how many bytes a and b share from their starts, k at most; ok: their
# first bytes are the same
def cmp.common(k: Nat, ok: Bool, a: List<&2, U32>, b: List<&2, U32>, n: Nat) -> Nat:
  match k:
    case 0n:
      n
    case 1n+j:
      match ok:
        case False{}:
          n
        case True{}:
          match a:
            case Nil{}:
              n
            case Con{x, +s}:
              match b:
                case Nil{}:
                  n
                case Con{y, +t}:
                  cmp.common(j, cmp.heads(s, t), s, t, 1n+n)

# the matcher's state: the table; the content from position i on; the end
# of the block; the literals since the last match (ll of them); the block's
# literals and sequences so far (reversed)
type ZsM is Type:
  ZsM{tab: Array<ZsCand>, cur: List<&2, U32>, i: Nat, end: Nat, ll: Nat, lits: List<&2, U32>, seqs: List<&2, ZsCSeq>}

# a literal (the next byte)
def cmp.m.lit(tab: Array<ZsCand>, cur: List<&2, U32>, +i: Nat, end: Nat, +ll: Nat, lits: List<&2, U32>, seqs: List<&2, ZsCSeq>) -> ZsM:
  match cur:
    case Nil{}:
      ZsM{tab, Nil{}, i, end, ll, lits, seqs}
    case Con{+b, t}:
      ZsM{tab, t, 1n+i, end, 1n+ll, Con{b, lits}, seqs}

# a match of ml bytes at offset off, or (shorter than 4) a literal
def cmp.m.emit(ok: Bool, tab: Array<ZsCand>, +cur: List<&2, U32>, +i: Nat, end: Nat, +ml: Nat, +off: Nat, +ll: Nat, lits: List<&2, U32>, seqs: List<&2, ZsCSeq>) -> ZsM:
  match ok:
    case True{}:
      ZsM{tab, B.drop(ml, cur), Nat.add(i, ml), end, 0n, lits, Con{ZsCSeq{ll, off, ml}, seqs}}
    case False{}:
      cmp.m.lit(tab, cur, i, end, ll, lits, seqs)

def cmp.m.len(valid: Bool, +k: Nat, +suf: List<&2, U32>, +cur: List<&2, U32>) -> Nat:
  match valid:
    case True{}:
      cmp.common(k, cmp.heads(suf, cur), suf, cur, 0n)
    case False{}:
      0n

# the slot for this position: its old entry is the candidate
def cmp.m.cand(r: Array<ZsCand> & ZsCand, +h: U32, +cur: List<&2, U32>, +i: Nat, +end: Nat, ll: Nat, lits: List<&2, U32>, seqs: List<&2, ZsCSeq>) -> ZsM:
  (tab, c) = r
  match c:
    case ZsCand{+pos, suf}:
      +ml = cmp.m.len(Nat.is_lt(0n, pos), Nat.sub(end, i), suf, cur)
      cmp.m.emit(Nat.is_le(4n, ml), Array.set(ZsCand, tab, h, ZsCand{1n+i, cur}), cur, i, end, ml, Nat.sub(1n+i, pos), ll, lits, seqs)

def cmp.m.step(room: Bool, tab: Array<ZsCand>, +cur: List<&2, U32>, +i: Nat, +end: Nat, ll: Nat, lits: List<&2, U32>, seqs: List<&2, ZsCSeq>) -> ZsM:
  match room:
    case True{}:
      +h = cmp.hash(cur)
      cmp.m.cand(Array.get(ZsCand, tab, h), h, cur, i, end, ll, lits, seqs)
    case False{}:
      cmp.m.lit(tab, cur, i, end, ll, lits, seqs)

def cmp.m.next(more: Bool, tab: Array<ZsCand>, +cur: List<&2, U32>, +i: Nat, +end: Nat, ll: Nat, lits: List<&2, U32>, seqs: List<&2, ZsCSeq>) -> ZsM:
  match more:
    case True{}:
      cmp.m.step(Nat.is_le(Nat.add(i, 4n), end), tab, cur, i, end, ll, lits, seqs)
    case False{}:
      ZsM{tab, cur, i, end, ll, lits, seqs}

# every step moves on a byte or more, so fuel of the block's length + 1
# reaches its end
def cmp.m.loop(fuel: Nat, st: ZsM) -> ZsM:
  match fuel:
    case 0n:
      st
    case 1n+f:
      match st:
        case ZsM{tab, cur, +i, +end, ll, lits, seqs}:
          cmp.m.loop(f, cmp.m.next(Nat.is_lt(i, end), tab, cur, i, end, ll, lits, seqs))

# Sequences, with the predefined tables

def cmp.nth(xs: List<&2, Nat>, i: Nat) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, xs, i), 0n)

# the last index whose baseline is at most v
def cmp.code(bs: List<&2, Nat>, +v: Nat, +i: Nat, best: Nat) -> Nat:
  match bs:
    case Nil{}:
      best
    case Con{+b, rest}:
      cmp.code(rest, v, 1n+i, cmp.pick(Nat, Nat.is_le(b, v), i, best))

# a sequence's codes, extra values and extra bits
type ZsCodes is Data:
  ZsCodes{llc: Nat, llx: Nat, llb: Nat, ofc: Nat, ofx: Nat, mlc: Nat, mlx: Nat, mlb: Nat}

def cmp.codes(s: ZsCSeq) -> ZsCodes:
  match s:
    case ZsCSeq{+ll, off, +ml}:
      +llc = cmp.code(S.ZstdSeq.ll_base(), ll, 0n, 0n)
      +mlc = cmp.code(S.ZstdSeq.ml_base(), ml, 0n, 0n)
      +ofv = Nat.add(off, 3n)
      +ofc = F.ZstdFse.highbit(ofv)
      ZsCodes{llc, Nat.sub(ll, cmp.nth(S.ZstdSeq.ll_base(), llc)), cmp.nth(S.ZstdSeq.ll_bits(), llc), ofc, Nat.sub(ofv, Bi.ZstdBits.pow2(ofc)), mlc, Nat.sub(ml, cmp.nth(S.ZstdSeq.ml_base(), mlc)), cmp.nth(S.ZstdSeq.ml_bits(), mlc)}

def cmp.c.ll(c: ZsCodes) -> Nat:
  match c:
    case ZsCodes{llc, llx, llb, ofc, ofx, mlc, mlx, mlb}:
      llc

def cmp.c.of(c: ZsCodes) -> Nat:
  match c:
    case ZsCodes{llc, llx, llb, ofc, ofx, mlc, mlx, mlb}:
      ofc

def cmp.c.ml(c: ZsCodes) -> Nat:
  match c:
    case ZsCodes{llc, llx, llb, ofc, ofx, mlc, mlx, mlb}:
      mlc

# the extra bits of a sequence: offset, match length, literals length
def cmp.c.extra(c: ZsCodes) -> List<&2, Bool>:
  match c:
    case ZsCodes{llc, llx, llb, ofc, ofx, mlc, mlx, mlb}:
      List.append(&2, Bool, Bi.ZstdBits.of_nat(ofc, ofx), List.append(&2, Bool, Bi.ZstdBits.of_nat(mlb, mlx), Bi.ZstdBits.of_nat(llb, llx)))

# a field's states, from the last sequence back: the state of the first
# sequence, and the update bits after each one but the last (in order)
type ZsChain is Data:
  ZsChain{s: Nat, ups: List<&2, List<&2, Bool>>}

def cmp.chain.ok(ok: Bool, e: F.ZstdFseEntry, +s: Nat, +tn: Nat, ups: List<&2, List<&2, Bool>>) -> Maybe<&2, ZsChain>:
  match ok:
    case True{}:
      match e:
        case F.ZstdFseEntry{sym, nb, base}:
          Some{ZsChain{s, Con{Bi.ZstdBits.of_nat(nb, Nat.sub(tn, base)), ups}}}
    case False{}:
      None{}

def cmp.chain.found(m: Maybe<&2, Nat>, +t: F.ZstdFseTable, +x: Nat, +tn: Nat, ups: List<&2, List<&2, Bool>>) -> Maybe<&2, ZsChain>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      +e = F.ZstdFse.entry(t, s)
      cmp.chain.ok(F.ZstdFse.fits(e, x, tn), e, s, tn, ups)

# xs: the codes before the ones done, nearest first
def cmp.chain(xs: List<&2, Nat>, +t: F.ZstdFseTable, cur: Maybe<&2, ZsChain>) -> Maybe<&2, ZsChain>:
  match xs:
    case Nil{}:
      cur
    case Con{+x, rest}:
      match cur:
        case None{}:
          None{}
        case Some{ZsChain{+tn, ups}}:
          cmp.chain(rest, t, cmp.chain.found(F.ZstdFse.find(t, x, tn), t, x, tn, ups))

def cmp.chain.start(m: Maybe<&2, Nat>) -> Maybe<&2, ZsChain>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{ZsChain{s, Nil{}}}

def cmp.states(rs: List<&2, Nat>, +t: F.ZstdFseTable) -> Maybe<&2, ZsChain>:
  match rs:
    case Nil{}:
      None{}
    case Con{+last, earlier}:
      cmp.chain(earlier, t, cmp.chain.start(F.ZstdFse.first(t, last)))

def cmp.head(xs: List<&2, List<&2, Bool>>) -> List<&2, Bool>:
  match xs:
    case Con{h, t}:
      h
    case Nil{}:
      Nil{}

def cmp.tail(xs: List<&2, List<&2, Bool>>) -> List<&2, List<&2, Bool>>:
  match xs:
    case Con{h, t}:
      t
    case Nil{}:
      Nil{}

# the bit fields after the initial states, in reading order, pushed
# (reversed) onto acc
def cmp.seqbits(cs: List<&2, ZsCodes>, +ul: List<&2, List<&2, Bool>>, +um: List<&2, List<&2, Bool>>, +uo: List<&2, List<&2, Bool>>, acc: List<&2, List<&2, Bool>>) -> List<&2, List<&2, Bool>>:
  match cs:
    case Nil{}:
      acc
    case Con{c, rest}:
      match rest:
        case Nil{}:
          Con{cmp.c.extra(c), acc}
        case Con{r1, r2}:
          cmp.seqbits(Con{r1, r2}, cmp.tail(ul), cmp.tail(um), cmp.tail(uo), Con{cmp.head(uo), Con{cmp.head(um), Con{cmp.head(ul), Con{cmp.c.extra(c), acc}}}})

# the fields (reversed) joined, in order
def cmp.flatten(rs: List<&2, List<&2, Bool>>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match rs:
    case Nil{}:
      acc
    case Con{h, t}:
      cmp.flatten(t, List.append(&2, Bool, h, acc))

def cmp.map_ll(cs: List<&2, ZsCodes>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      cmp.map_ll(t, Con{cmp.c.ll(c), acc})

def cmp.map_of(cs: List<&2, ZsCodes>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      cmp.map_of(t, Con{cmp.c.of(c), acc})

def cmp.map_ml(cs: List<&2, ZsCodes>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      cmp.map_ml(t, Con{cmp.c.ml(c), acc})

def cmp.map_codes(ss: List<&2, ZsCSeq>, acc: List<&2, ZsCodes>) -> List<&2, ZsCodes>:
  match ss:
    case Nil{}:
      List.reverse(&2, ZsCodes, acc)
    case Con{s, t}:
      cmp.map_codes(t, Con{cmp.codes(s), acc})

def cmp.bits3(l: Maybe<&2, ZsChain>, o: Maybe<&2, ZsChain>, m: Maybe<&2, ZsChain>, +cs: List<&2, ZsCodes>) -> Maybe<&2, List<&2, Bool>>:
  match l:
    case None{}:
      None{}
    case Some{ZsChain{sl, ul}}:
      match o:
        case None{}:
          None{}
        case Some{ZsChain{so, uo}}:
          match m:
            case None{}:
              None{}
            case Some{ZsChain{sm, um}}:
              Some{cmp.flatten(cmp.seqbits(cs, ul, um, uo, [Bi.ZstdBits.of_nat(6n, sm), Bi.ZstdBits.of_nat(5n, so), Bi.ZstdBits.of_nat(6n, sl)]), Nil{})}


# the number of sequences, in 1, 2 or 3 bytes
def cmp.nseq(+n: Nat) -> List<&2, U32>:
  cmp.pick(List<&2, U32>, Nat.is_lt(n, 128n), [U32.from_nat(n)], cmp.pick(List<&2, U32>, Nat.is_lt(n, 32512n), [U32.from_nat(Nat.add(128n, Nat.div(n, 256n))), U32.from_nat(Nat.mod(n, 256n))], [255, U32.from_nat(Nat.mod(Nat.sub(n, 32512n), 256n)), U32.from_nat(Nat.div(Nat.sub(n, 32512n), 256n))]))

def cmp.seq.of(m: Maybe<&2, List<&2, Bool>>, +n: Nat) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{bits}:
      Some{B.append.fast(cmp.nseq(n), Con{0, Bi.ZstdBits.pack_backward(bits)})}

# the sequences section: the count, the modes byte (the predefined tables
# for all three fields), the bitstream
def cmp.seq_section(ss: List<&2, ZsCSeq>) -> Maybe<&2, List<&2, U32>>:
  match ss:
    case Nil{}:
      Some{[0]}
    case Con{h, t}:
      +cs = cmp.map_codes(Con{h, t}, Nil{})
      cmp.seq.of(cmp.bits3(cmp.states(cmp.map_ll(cs, Nil{}), F.ZstdFse.table_ll()), cmp.states(cmp.map_of(cs, Nil{}), F.ZstdFse.table_of()), cmp.states(cmp.map_ml(cs, Nil{}), F.ZstdFse.table_ml()), cs), List.length(&2, ZsCodes, cs))

# raw literals: a header of 1, 2 or 3 bytes, then the bytes
def cmp.lit_header(+n: Nat) -> List<&2, U32>:
  cmp.pick(List<&2, U32>, Nat.is_lt(n, 32n), [U32.from_nat(Nat.mul(n, 8n))], cmp.pick(List<&2, U32>, Nat.is_lt(n, 4096n), [U32.from_nat(Nat.add(4n, Nat.mul(Nat.mod(n, 16n), 16n))), U32.from_nat(Nat.div(n, 16n))], [U32.from_nat(Nat.add(12n, Nat.mul(Nat.mod(n, 16n), 16n))), U32.from_nat(Nat.mod(Nat.div(n, 16n), 256n)), U32.from_nat(Nat.div(n, 4096n))]))

def cmp.body(m: Maybe<&2, List<&2, U32>>, +lits: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{seq}:
      Some{B.append.fast(cmp.lit_header(B.len.fast(lits)), B.append.fast(lits, seq))}

# Blocks: RLE when every byte is the same (and there are two or more),
# compressed when that is smaller, else raw

def cmp.all(xs: List<&2, U32>, +b: U32, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      ok
    case Con{h, t}:
      cmp.all(t, b, Bool.and(ok, U32.is_eq(h, b)))

def cmp.rle(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{+h, t}:
      match t:
        case Nil{}:
          False{}
        case Con{h2, t2}:
          cmp.all(Con{h2, t2}, h, True{})
    case Nil{}:
      False{}

def cmp.first(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{h, t}:
      h
    case Nil{}:
      0

def cmp.choose(small: Bool, +last: Bool, +raw: List<&2, U32>, +n: Nat, +c: List<&2, U32>) -> List<&2, U32>:
  match small:
    case True{}:
      B.append.fast(cmp.bh(last, 2n, B.len.fast(c)), c)
    case False{}:
      B.append.fast(cmp.bh(last, 0n, n), raw)

def cmp.comp_or_raw(body: Maybe<&2, List<&2, U32>>, +last: Bool, +raw: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  match body:
    case None{}:
      B.append.fast(cmp.bh(last, 0n, n), raw)
    case Some{+c}:
      cmp.choose(Nat.is_lt(B.len.fast(c), n), last, raw, n, c)

def cmp.block_bytes(rle: Bool, +last: Bool, +raw: List<&2, U32>, +n: Nat, body: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match rle:
    case True{}:
      B.append.fast(cmp.bh(last, 1n, n), [cmp.first(raw)])
    case False{}:
      cmp.comp_or_raw(body, last, raw, n)

# The frame: the content cut into blocks; the matcher's table carries over

type ZsW is Type:
  ZsW{tab: Array<ZsCand>, cur: List<&2, U32>, i: Nat, n: Nat, bsize: U32, acc: List<&2, U32>}

def cmp.w.matched(m: ZsM, +raw: List<&2, U32>, +len: Nat, +last: Bool, +n: Nat, +bsize: U32, acc: List<&2, U32>) -> ZsW:
  match m:
    case ZsM{tab, cur, i, end, ll, lits, seqs}:
      +bytes = cmp.block_bytes(cmp.rle(raw), last, raw, len, cmp.body(cmp.seq_section(List.reverse(&2, ZsCSeq, seqs)), B.rev(lits)))
      ZsW{tab, cur, end, n, bsize, B.rev_onto(bytes, acc)}

# the next block's length: the block size, or what is left (counted in U32,
# so that no large Nat is compared; see AGENTS.md on --verdict)
def cmp.w.len(+bsize: U32, +left: Nat) -> Nat:
  U32.to_nat(U32.min(bsize, U32.from_nat(left)))

def cmp.w.block(matcher: Bool, tab: Array<ZsCand>, +cur: List<&2, U32>, +i: Nat, +n: Nat, +bsize: U32, acc: List<&2, U32>) -> ZsW:
  match matcher:
    case True{}:
      +len = cmp.w.len(bsize, Nat.sub(n, i))
      +raw = B.take.fast(len, cur)
      +last = Nat.is_le(n, Nat.add(i, len))
      cmp.w.matched(cmp.m.loop(1n+len, ZsM{tab, cur, i, Nat.add(i, len), 0n, Nil{}, Nil{}}), raw, len, last, n, bsize, acc)
    case False{}:
      +len = cmp.w.len(bsize, Nat.sub(n, i))
      +raw = B.take.fast(len, cur)
      +last = Nat.is_le(n, Nat.add(i, len))
      ZsW{tab, B.drop(len, cur), Nat.add(i, len), n, bsize, B.rev_onto(cmp.block_bytes(cmp.rle(raw), last, raw, len, None{}), acc)}

# blocks until the content is used up (at least one, for empty content);
# every block takes a byte or more, so fuel of the length + 1 suffices
def cmp.w.loop(k: Nat, more: Bool, +matcher: Bool, st: ZsW) -> ZsW:
  match k:
    case 0n:
      st
    case 1n+j:
      match more:
        case False{}:
          st
        case True{}:
          match st:
            case ZsW{tab, cur, +i, +n, +bsize, acc}:
              +len = cmp.w.len(bsize, Nat.sub(n, i))
              cmp.w.loop(j, Nat.is_lt(Nat.add(i, len), n), matcher, cmp.w.block(matcher, tab, cur, i, n, bsize, acc))

def cmp.w.out(st: ZsW) -> List<&2, U32>:
  match st:
    case ZsW{tab, cur, i, n, bsize, acc}:
      B.rev(acc)

def cmp.sum(check: Bool, +o: B.Octets) -> List<&2, U32>:
  match check:
    case True{}:
      B.le32(W.W64.lo(X.ZstdXxh64.hash(W.W64.zero(), o)))
    case False{}:
      Nil{}

def cmp.bsize(+b: U32) -> U32:
  cmp.pick(U32, Bool.or(U32.is_eq(b, 0), U32.is_lt(131072, b)), 131072, b)

# The fallback: a frame whose decoding is proved (LAWS.bend) for every
# input. Not single-segment (FHD 0: no content size, no checksum, no
# dictionary), a 1 KB window, each byte in a raw block of its own, and an
# empty last block: 4 bytes per byte. compress answers it only if its own
# frame fails to decode back to its input.

def cmp.raw_blocks(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [1, 0, 0]
    case Con{b, t}:
      Con{8, Con{0, Con{0, Con{b, cmp.raw_blocks(t)}}}}

def Zstd.raw_frame(o: B.Octets) -> B.Octets:
  B.Octets.of_list(Con{40, Con{181, Con{47, Con{253, Con{0, Con{0, cmp.raw_blocks(B.Octets.to_list(o))}}}}}})

# Checking a frame: decode it and compare

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

# the same bytes in the same order (live: so far)
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
      Zstd.raw_frame(o)

def cmp.check(r: Result<&2, &2, E.ZstdError, B.Octets>, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match r:
    case Fail{e}:
      Zstd.raw_frame(o)
    case Done{d}:
      cmp.keep(cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)), c, o)

# The public interface

# a frame holding o, unchecked: single-segment, with the content size, cut
# into blocks of the block size (RLE, compressed or raw, whichever is
# smallest), and the checksum if the options ask for it
def compress_unchecked(opts: ZstdCompressOptions, +o: B.Octets) -> B.Octets:
  match opts:
    case ZstdCompressOptions{block_size, +checksum, +matcher}:
      +xs = B.Octets.to_list(o)
      +n = B.len.fast(xs)
      +blocks = cmp.w.out(cmp.w.loop(1n+n, True{}, matcher, ZsW{Array.new(ZsCand, 14n, ZsCand{0n, Nil{}}), xs, 0n, n, cmp.bsize(block_size), Nil{}}))
      B.Octets.of_list(B.append.fast(cmp.header(n, checksum), B.append.fast(blocks, cmp.sum(checksum, o))))

# a frame holding o, with these options, checked: decoded and compared with
# o; should they differ, the frame of raw blocks
def compress_with(opts: ZstdCompressOptions, +o: B.Octets) -> B.Octets:
  +c = compress_unchecked(opts, o)
  cmp.check(Z.decompress_with(Z.ZstdOptions.unlimited(), c), c, o)

# the same with ZstdCompressOptions.default()
def compress(+o: B.Octets) -> B.Octets:
  compress_with(ZstdCompressOptions.default(), o)
