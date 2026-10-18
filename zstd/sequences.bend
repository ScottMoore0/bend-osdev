# bend-osdev-zstd, the sequences section of a compressed block (RFC 8878,
# section 3.1.1.3.2): its header, the literals length, offset and match
# length tables (predefined, RLE, FSE-compressed or repeated), and the
# sequences the interleaved FSE states decode from its bitstream.
#
# A sequence is a literals length, an offset value (above 3 an offset plus
# 3; 1 to 3 a repeat offset, block.bend resolves it) and a match length.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bits.bend as Bi
import ./fse.bend as F

type ZstdSeq is Data:
  ZstdSeq{ll: Nat, ofv: Nat, ml: Nat}

# the tables of the last block, which repeat mode reuses
type ZstdSeqTables is Data:
  ZstdSeqTables{ll: Maybe<&2, F.ZstdFseTable>, of: Maybe<&2, F.ZstdFseTable>, ml: Maybe<&2, F.ZstdFseTable>}

# the sequences, and the tables for the next block
type ZstdSequences is Data:
  ZstdSequences{seqs: List<&2, ZstdSeq>, tables: ZstdSeqTables}

def ZstdSeqTables.none() -> ZstdSeqTables:
  ZstdSeqTables{None{}, None{}, None{}}

# The codes (RFC 8878, section 3.1.1.3.2.1.1): a literals length code is the
# length below 16, then a baseline and extra bits; a match length code is
# the length minus 3 below 32, then the same; an offset code n is
# 2^n plus n extra bits.

def seq.nth(xs: List<&2, Nat>, i: Nat) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, xs, i), 0n)

def ZstdSeq.ll_base() -> List<&2, Nat>:
  [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 16n, 18n, 20n, 22n, 24n, 28n, 32n, 40n, 48n, 64n, 128n, 256n, 512n, 1024n, 2048n, 4096n, 8192n, 16384n, 32768n, 65536n]

def ZstdSeq.ll_bits() -> List<&2, Nat>:
  [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n, 1n, 1n, 1n, 2n, 2n, 3n, 3n, 4n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 16n]

def ZstdSeq.ml_base() -> List<&2, Nat>:
  [3n, 4n, 5n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 16n, 17n, 18n, 19n, 20n, 21n, 22n, 23n, 24n, 25n, 26n, 27n, 28n, 29n, 30n, 31n, 32n, 33n, 34n, 35n, 37n, 39n, 41n, 43n, 47n, 51n, 59n, 67n, 83n, 99n, 131n, 259n, 515n, 1027n, 2051n, 4099n, 8195n, 16387n, 32771n, 65539n]

def ZstdSeq.ml_bits() -> List<&2, Nat>:
  [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n, 1n, 1n, 1n, 2n, 2n, 3n, 3n, 4n, 4n, 5n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 16n]

# The tables (RFC 8878, section 3.1.1.3.2.1): a mode per field; RLE gives
# the symbol in a byte, FSE-compressed a table description

# a table read, and the position after it
type ZsSeqTab is Data:
  ZsSeqTab{t: F.ZstdFseTable, pos: Nat}

def seq.pos(r: ZsSeqTab) -> Nat:
  match r:
    case ZsSeqTab{t, pos}:
      pos

def seq.tab(r: ZsSeqTab) -> F.ZstdFseTable:
  match r:
    case ZsSeqTab{t, pos}:
      t

def seq.desc(m: Maybe<&2, F.ZstdFseDesc>, +pos: Nat) -> Result<&2, &2, E.ZstdError, ZsSeqTab>:
  match m:
    case None{}:
      Fail{E.ZstdBadFseTable{}}
    case Some{F.ZstdFseDesc{+al, probs, used}}:
      do Result<&2, &2, E.ZstdError, ZsSeqTab>:
        t : F.ZstdFseTable <- E.ZstdError.need(F.ZstdFseTable, F.ZstdFse.table(al, probs), E.ZstdBadFseTable{})
        return ZsSeqTab{t, Nat.add(pos, used)}

def seq.nat(xs: List<&2, U32>, i: Nat) -> Nat:
  U32.to_nat(B.byte(Maybe.default(&2, U32, B.at(xs, i), 0)))

# the table of a field in this mode, at xs[pos]: predefined (default), RLE,
# FSE-compressed (accuracy log at most max_al, symbols at most max_sym) or
# repeated (prev)
def seq.mode(mode: Nat, +xs: List<&2, U32>, +pos: Nat, +n: Nat, default: F.ZstdFseTable, +max_al: Nat, +max_sym: Nat, prev: Maybe<&2, F.ZstdFseTable>) -> Result<&2, &2, E.ZstdError, ZsSeqTab>:
  match mode:
    case 0n:
      Done{ZsSeqTab{default, pos}}
    case 1n+p:
      match p:
        case 0n:
          +sym = seq.nat(xs, pos)
          do Result<&2, &2, E.ZstdError, ZsSeqTab>:
            u1 : Unit <- E.ZstdError.require(Nat.is_lt(pos, n), E.ZstdBadSequencesHeader{})
            u2 : Unit <- E.ZstdError.require(Nat.is_le(sym, max_sym), E.ZstdBadFseTable{})
            return ZsSeqTab{F.ZstdFse.rle(sym), 1n+pos}
        case 1n+q:
          match q:
            case 0n:
              seq.desc(F.ZstdFse.read_description(B.drop(pos, xs), max_al, max_sym), pos)
            case 1n+r:
              do Result<&2, &2, E.ZstdError, ZsSeqTab>:
                t : F.ZstdFseTable <- E.ZstdError.need(F.ZstdFseTable, prev, E.ZstdNoFseTable{})
                return ZsSeqTab{t, pos}

# Decoding (RFC 8878, section 3.1.1.3.2.2): the states start in the
# literals length, offset and match length order, each read in its
# accuracy log's bits; a sequence's codes come from the three states, its
# extra bits are read offset first, then match length, then literals
# length; then, but for the last sequence, the states are updated in the
# literals length, match length, offset order. The bitstream must be used up.

type ZsSq is Data:
  ZsSq{sll: Nat, sof: Nat, sml: Nat, bits: List<&2, Bool>, acc: List<&2, ZstdSeq>}

def seq.update(last: Bool, ell: F.ZstdFseEntry, eml: F.ZstdFseEntry, eof: F.ZstdFseEntry, bits: List<&2, Bool>, acc: List<&2, ZstdSeq>) -> Maybe<&2, ZsSq>:
  match last:
    case True{}:
      Some{ZsSq{0n, 0n, 0n, bits, acc}}
    case False{}:
      do Maybe<&2, ZsSq>:
        +l : Bi.ZstdBits <- F.ZstdFse.next(ell, bits)
        +m : Bi.ZstdBits <- F.ZstdFse.next(eml, Bi.ZstdBits.rest(l))
        +o : Bi.ZstdBits <- F.ZstdFse.next(eof, Bi.ZstdBits.rest(m))
        return ZsSq{Bi.ZstdBits.value(l), Bi.ZstdBits.value(o), Bi.ZstdBits.value(m), Bi.ZstdBits.rest(o), acc}

# one sequence from the states in st (last: no update after it)
def seq.one(+tll: F.ZstdFseTable, +tof: F.ZstdFseTable, +tml: F.ZstdFseTable, st: ZsSq, last: Bool) -> Maybe<&2, ZsSq>:
  match st:
    case ZsSq{+sll, +sof, +sml, bits, acc}:
      +ell = F.ZstdFse.entry(tll, sll)
      +eof = F.ZstdFse.entry(tof, sof)
      +eml = F.ZstdFse.entry(tml, sml)
      +ofc = F.ZstdFse.sym(eof)
      +mlc = F.ZstdFse.sym(eml)
      +llc = F.ZstdFse.sym(ell)
      do Maybe<&2, ZsSq>:
        +o : Bi.ZstdBits <- Bi.ZstdBits.read(ofc, bits)
        +m : Bi.ZstdBits <- Bi.ZstdBits.read(seq.nth(ZstdSeq.ml_bits(), mlc), Bi.ZstdBits.rest(o))
        +l : Bi.ZstdBits <- Bi.ZstdBits.read(seq.nth(ZstdSeq.ll_bits(), llc), Bi.ZstdBits.rest(m))
        s : ZstdSeq = ZstdSeq{Nat.add(seq.nth(ZstdSeq.ll_base(), llc), Bi.ZstdBits.value(l)), Nat.add(Bi.ZstdBits.pow2(ofc), Bi.ZstdBits.value(o)), Nat.add(seq.nth(ZstdSeq.ml_base(), mlc), Bi.ZstdBits.value(m))}
        r : ZsSq <- seq.update(last, ell, eml, eof, Bi.ZstdBits.rest(l), Con{s, acc})
        return r

def seq.loop(n: Nat, +tll: F.ZstdFseTable, +tof: F.ZstdFseTable, +tml: F.ZstdFseTable, cur: Maybe<&2, ZsSq>) -> Maybe<&2, ZsSq>:
  match n:
    case 0n:
      cur
    case 1n+(+k):
      match cur:
        case None{}:
          None{}
        case Some{st}:
          seq.loop(k, tll, tof, tml, seq.one(tll, tof, tml, st, Nat.is_eq(k, 0n)))

def seq.init(bits: List<&2, Bool>, +tll: F.ZstdFseTable, +tof: F.ZstdFseTable, +tml: F.ZstdFseTable) -> Maybe<&2, ZsSq>:
  do Maybe<&2, ZsSq>:
    +l : Bi.ZstdBits <- Bi.ZstdBits.read(F.ZstdFse.al(tll), bits)
    +o : Bi.ZstdBits <- Bi.ZstdBits.read(F.ZstdFse.al(tof), Bi.ZstdBits.rest(l))
    +m : Bi.ZstdBits <- Bi.ZstdBits.read(F.ZstdFse.al(tml), Bi.ZstdBits.rest(o))
    return ZsSq{Bi.ZstdBits.value(l), Bi.ZstdBits.value(o), Bi.ZstdBits.value(m), Bi.ZstdBits.rest(m), Nil{}}

def seq.finish(m: Maybe<&2, ZsSq>) -> Result<&2, &2, E.ZstdError, List<&2, ZstdSeq>>:
  match m:
    case None{}:
      Fail{E.ZstdBadSequenceStream{}}
    case Some{ZsSq{a, b, c, bits, acc}}:
      match bits:
        case Nil{}:
          Done{List.reverse(&2, ZstdSeq, acc)}
        case Con{h, t}:
          Fail{E.ZstdBadSequenceStream{}}

def seq.stream(bm: Maybe<&2, List<&2, Bool>>, +n: Nat, +tll: F.ZstdFseTable, +tof: F.ZstdFseTable, +tml: F.ZstdFseTable) -> Result<&2, &2, E.ZstdError, List<&2, ZstdSeq>>:
  match bm:
    case None{}:
      Fail{E.ZstdBadSequenceStream{}}
    case Some{bits}:
      seq.finish(seq.loop(n, tll, tof, tml, seq.init(bits, tll, tof, tml)))

def seq.body(+count: Nat, +pos: Nat, +xs: List<&2, U32>, +n: Nat, prev: ZstdSeqTables) -> Result<&2, &2, E.ZstdError, ZstdSequences>:
  match prev:
    case ZstdSeqTables{pll, pof, pml}:
      +modes = seq.nat(xs, pos)
      do Result<&2, &2, E.ZstdError, ZstdSequences>:
        u1 : Unit <- E.ZstdError.require(Nat.is_lt(pos, n), E.ZstdBadSequencesHeader{})
        u2 : Unit <- E.ZstdError.require(Nat.is_eq(Nat.mod(modes, 4n), 0n), E.ZstdBadSequencesHeader{})
        +a : ZsSeqTab <- seq.mode(Nat.div(modes, 64n), xs, 1n+pos, n, F.ZstdFse.table_ll(), 9n, 35n, pll)
        +b : ZsSeqTab <- seq.mode(Nat.mod(Nat.div(modes, 16n), 4n), xs, seq.pos(a), n, F.ZstdFse.table_of(), 8n, 31n, pof)
        +c : ZsSeqTab <- seq.mode(Nat.mod(Nat.div(modes, 4n), 4n), xs, seq.pos(b), n, F.ZstdFse.table_ml(), 9n, 52n, pml)
        seqs : List<&2, ZstdSeq> <- seq.stream(Bi.ZstdBits.backward(B.drop(seq.pos(c), xs)), count, seq.tab(a), seq.tab(b), seq.tab(c))
        return ZstdSequences{seqs, ZstdSeqTables{Some{seq.tab(a)}, Some{seq.tab(b)}, Some{seq.tab(c)}}}

# the number of sequences: one byte below 128, two below 255, else three
def seq.count(zero: Bool, small: Bool, mid: Bool, +b0: Nat, +xs: List<&2, U32>, +n: Nat, prev: ZstdSeqTables) -> Result<&2, &2, E.ZstdError, ZstdSequences>:
  match zero:
    case True{}:
      do Result<&2, &2, E.ZstdError, ZstdSequences>:
        u : Unit <- E.ZstdError.require(Nat.is_eq(n, 1n), E.ZstdBadSequencesHeader{})
        return ZstdSequences{Nil{}, prev}
    case False{}:
      match small:
        case True{}:
          seq.body(b0, 1n, xs, n, prev)
        case False{}:
          match mid:
            case True{}:
              do Result<&2, &2, E.ZstdError, ZstdSequences>:
                u : Unit <- E.ZstdError.require(Nat.is_le(2n, n), E.ZstdBadSequencesHeader{})
                r : ZstdSequences <- seq.body(Nat.add(Nat.mul(Nat.sub(b0, 128n), 256n), seq.nat(xs, 1n)), 2n, xs, n, prev)
                return r
            case False{}:
              do Result<&2, &2, E.ZstdError, ZstdSequences>:
                u : Unit <- E.ZstdError.require(Nat.is_le(3n, n), E.ZstdBadSequencesHeader{})
                r : ZstdSequences <- seq.body(Nat.add(Nat.add(seq.nat(xs, 1n), Nat.mul(seq.nat(xs, 2n), 256n)), 32512n), 3n, xs, n, prev)
                return r

# The public interface

# the sequences section xs (the rest of a compressed block after its
# literals): the sequences, and the tables for the next block (prev: the
# last block's, for repeat mode)
def ZstdSeq.decode(xs: List<&2, U32>, prev: ZstdSeqTables) -> Result<&2, &2, E.ZstdError, ZstdSequences>:
  match xs:
    case Nil{}:
      Fail{E.ZstdBadSequencesHeader{}}
    case Con{+h, t}:
      +all = {Con{h, t} : List<&2, U32>}
      +b0 = seq.nat(all, 0n)
      seq.count(Nat.is_eq(b0, 0n), Nat.is_lt(b0, 128n), Nat.is_lt(b0, 255n), b0, all, B.len.fast(all), prev)
