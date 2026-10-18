# bend-osdev-zstd, blocks (RFC 8878, sections 3.1.1.2 and 3.1.1.3): the
# window, the repeat offsets, and the decoding of a compressed block, its
# literals and sequences run against the window.
#
# The window holds the bytes a match may copy: the dictionary's content,
# then the frame's bytes. Each sequence copies its literals, then a match:
# offset values above 3 give an offset (value - 3); 1 to 3 pick a repeat
# offset (shifted by one when the literals length is 0, the third then
# meaning repeat offset 1 minus 1), and the repeat offsets move as RFC 8878
# section 3.1.2.5 says. A match may reach into the dictionary while the
# frame's output is within the window size, and only within the window
# after that (RFC 8878, section 5).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./huffman.bend as H
import ./literals.bend as L
import ./sequences.bend as S

# The window: an array of 2^depth bytes (a power of two at least the window
# and the dictionary together), indexed by position modulo its size, and
# the next byte's position. An Array is updated in place, so the window is
# a Type: it has one owner, the decoder.

type ZstdWindow is Type:
  ZstdWindow{arr: Array<U32>, pos: Nat}

# an empty window of 2^d bytes
def ZstdWin.new(d: Nat) -> ZstdWindow:
  ZstdWindow{Array.new(U32, d, 0), 0n}

# the window after one more byte
def ZstdWin.put(w: ZstdWindow, b: U32) -> ZstdWindow:
  match w:
    case ZstdWindow{arr, +pos}:
      ZstdWindow{Array.set(U32, arr, U32.from_nat(pos), b), 1n+pos}

def ZstdWin.puts(xs: List<&2, U32>, w: ZstdWindow) -> ZstdWindow:
  match xs:
    case Nil{}:
      w
    case Con{h, t}:
      ZstdWin.puts(t, ZstdWin.put(w, h))

# the window and the output after some bytes
type ZsWOut is Type:
  ZsWOut{w: ZstdWindow, out: List<&2, U32>}

def win.copy.got(r: Array<U32> & U32, +pos: Nat, out: List<&2, U32>) -> ZsWOut:
  (a, b) = r
  +v = b
  ZsWOut{ZstdWindow{Array.set(U32, a, U32.from_nat(pos), v), 1n+pos}, Con{v, out}}

# one byte of a match: the byte off back, put again (and onto out)
def ZstdWin.copy1(w: ZstdWindow, +off: Nat, out: List<&2, U32>) -> ZsWOut:
  match w:
    case ZstdWindow{arr, +pos}:
      win.copy.got(Array.get(U32, arr, U32.from_nat(Nat.sub(pos, off))), pos, out)

# one literal: into the window and onto out
def ZstdWin.lit1(o: ZsWOut, +b: U32) -> ZsWOut:
  match o:
    case ZsWOut{w, out}:
      ZsWOut{ZstdWin.put(w, b), Con{b, out}}

# the least d with 2^d >= n (at least 1): p = 2^d, done: n <= p
def win.log2sup(fuel: Nat, done: Bool, +n: Nat, +d: Nat, +p: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      match done:
        case True{}:
          d
        case False{}:
          +q = Nat.add(p, p)
          win.log2sup(f, Nat.is_le(n, q), n, 1n+d, q)

# the depth a window of size w after a dictionary of size dl needs (the
# array is at most 2^32 bytes: its positions are U32 modulo its size)
def ZstdWin.depth(+w: Nat, +dl: Nat) -> Nat:
  +n = Nat.add(w, dl)
  Nat.min(32n, win.log2sup(64n, Nat.is_le(n, 2n), n, 1n, 2n))

# The repeat offsets

type ZstdReps is Data:
  ZstdReps{r1: Nat, r2: Nat, r3: Nat}

def ZstdReps.initial() -> ZstdReps:
  ZstdReps{1n, 4n, 8n}

# the offset of a sequence, and the repeat offsets after it
type ZsOff is Data:
  ZsOff{off: Nat, reps: ZstdReps}

def blk.rep(k: Nat, reps: ZstdReps) -> ZsOff:
  match k:
    case 0n:
      match reps:
        case ZstdReps{+r1, r2, r3}:
          ZsOff{r1, ZstdReps{r1, r2, r3}}
    case 1n+p:
      match p:
        case 0n:
          match reps:
            case ZstdReps{+r1, +r2, r3}:
              ZsOff{r2, ZstdReps{r2, r1, r3}}
        case 1n+q:
          match q:
            case 0n:
              match reps:
                case ZstdReps{r1, r2, +r3}:
                  ZsOff{r3, ZstdReps{r3, r1, r2}}
            case 1n+r:
              match reps:
                case ZstdReps{+r1, r2, r3}:
                  +o = Nat.sub(r1, 1n)
                  ZsOff{o, ZstdReps{o, r1, r2}}

# the repeat offset an offset value of 1 to 3 picks: 0 to 2, or 3 for
# repeat offset 1 minus 1 (with a literals length of 0, the values shift)
def blk.k(ll: Nat, +ofv: Nat) -> Nat:
  match ll:
    case 0n:
      ofv
    case 1n+p:
      Nat.sub(ofv, 1n)

def blk.offset.pick(fresh: Bool, +ll: Nat, +ofv: Nat, reps: ZstdReps) -> ZsOff:
  match fresh:
    case True{}:
      match reps:
        case ZstdReps{r1, r2, r3}:
          +o = Nat.sub(ofv, 3n)
          ZsOff{o, ZstdReps{o, r1, r2}}
    case False{}:
      blk.rep(blk.k(ll, ofv), reps)

# the offset of a sequence with literals length ll and offset value ofv,
# and the repeat offsets after it (RFC 8878, section 3.1.2.5)
def ZstdBlk.offset(+ll: Nat, +ofv: Nat, reps: ZstdReps) -> ZsOff:
  blk.offset.pick(Nat.is_lt(3n, ofv), ll, ofv, reps)

def blk.off(r: ZsOff) -> Nat:
  match r:
    case ZsOff{off, reps}:
      off

def blk.reps(r: ZsOff) -> ZstdReps:
  match r:
    case ZsOff{off, reps}:
      reps

# Running the sequences
#
# lits: the literals left (nlits of them); o: the window and the block's
# bytes so far (reversed: blk of them); produced: the frame's bytes so far

type ZsEx is Type:
  ZsEx{lits: List<&2, U32>, nlits: Nat, o: ZsWOut, blk: Nat, produced: Nat, reps: ZstdReps}

# n literals (there are that many)
def blk.lits(n: Nat, lits: List<&2, U32>, o: ZsWOut) -> ZsWOut:
  match n:
    case 0n:
      o
    case 1n+k:
      match lits:
        case Nil{}:
          o
        case Con{h, t}:
          blk.lits(k, t, ZstdWin.lit1(o, h))

# n bytes, each the one off back (the copy may overlap what it writes)
def blk.copy(n: Nat, +off: Nat, o: ZsWOut) -> ZsWOut:
  match n:
    case 0n:
      o
    case 1n+k:
      match o:
        case ZsWOut{w, out}:
          blk.copy(k, off, ZstdWin.copy1(w, off, out))

# how far back a match may reach: the frame's bytes and the dictionary
# while the frame is within the window, else the window
def blk.limit(within: Bool, +produced: Nat, +w: Nat, +dl: Nat) -> Nat:
  match within:
    case True{}:
      Nat.add(produced, dl)
    case False{}:
      w

def blk.match.ok(fits: Bool, reach: Bool, room: Bool, ex: ZsEx, +off: Nat, +ml: Nat) -> Result<&2, &1, E.ZstdError, ZsEx>:
  match fits:
    case False{}:
      Fail{E.ZstdBlockTooLarge{}}
    case True{}:
      match reach:
        case False{}:
          Fail{E.ZstdBadOffset{}}
        case True{}:
          match room:
            case False{}:
              Fail{E.ZstdBlockTooLarge{}}
            case True{}:
              match ex:
                case ZsEx{lits, nlits, o, blk, produced, reps}:
                  Done{ZsEx{lits, nlits, blk.copy(ml, off, o), Nat.add(blk, ml), Nat.add(produced, ml), reps}}

def blk.match(ex: ZsEx, +ll: Nat, +ofv: Nat, +ml: Nat, +w: Nat, +dl: Nat, +block_max: Nat) -> Result<&2, &1, E.ZstdError, ZsEx>:
  match ex:
    case ZsEx{lits, nlits, o, +blk, +produced, reps}:
      +r = ZstdBlk.offset(ll, ofv, reps)
      +off = blk.off(r)
      blk.match.ok(Nat.is_le(blk, block_max), Bool.and(Nat.is_lt(0n, off), Nat.is_le(off, blk.limit(Nat.is_le(produced, w), produced, w, dl))), Nat.is_le(Nat.add(blk, ml), block_max), ZsEx{lits, nlits, o, blk, produced, blk.reps(r)}, off, ml)

def blk.seq.lits(ok: Bool, +ll: Nat, +ofv: Nat, +ml: Nat, +lits: List<&2, U32>, +nlits: Nat, o: ZsWOut, +blk: Nat, +produced: Nat, reps: ZstdReps, +w: Nat, +dl: Nat, +block_max: Nat) -> Result<&2, &1, E.ZstdError, ZsEx>:
  match ok:
    case False{}:
      Fail{E.ZstdLiteralsExhausted{}}
    case True{}:
      blk.match(ZsEx{B.drop(ll, lits), Nat.sub(nlits, ll), blk.lits(ll, lits, o), Nat.add(blk, ll), Nat.add(produced, ll), reps}, ll, ofv, ml, w, dl, block_max)

def blk.seq(s: S.ZstdSeq, ex: ZsEx, +w: Nat, +dl: Nat, +block_max: Nat) -> Result<&2, &1, E.ZstdError, ZsEx>:
  match s:
    case S.ZstdSeq{+ll, ofv, ml}:
      match ex:
        case ZsEx{lits, +nlits, o, blk, produced, reps}:
          blk.seq.lits(Nat.is_le(ll, nlits), ll, ofv, ml, lits, nlits, o, blk, produced, reps, w, dl, block_max)

def blk.last.ok(ok: Bool, ex: ZsEx) -> Result<&2, &1, E.ZstdError, ZsEx>:
  match ok:
    case True{}:
      Done{ex}
    case False{}:
      Fail{E.ZstdBlockTooLarge{}}

# the literals after the last sequence
def blk.last(ex: ZsEx, +block_max: Nat) -> Result<&2, &1, E.ZstdError, ZsEx>:
  match ex:
    case ZsEx{lits, +nlits, o, blk, produced, reps}:
      +blk2 = Nat.add(blk, nlits)
      blk.last.ok(Nat.is_le(blk2, block_max), ZsEx{Nil{}, 0n, blk.lits(nlits, lits, o), blk2, Nat.add(produced, nlits), reps})

def blk.run(seqs: List<&2, S.ZstdSeq>, r: Result<&2, &1, E.ZstdError, ZsEx>, +w: Nat, +dl: Nat, +block_max: Nat) -> Result<&2, &1, E.ZstdError, ZsEx>:
  match seqs:
    case Nil{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{ex}:
          blk.last(ex, block_max)
    case Con{s, rest}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{ex}:
          blk.run(rest, blk.seq(s, ex, w, dl, block_max), w, dl, block_max)

# What a frame keeps from block to block (besides the window): the last
# Huffman tree and sequence tables, the repeat offsets, and how many bytes
# the frame has produced
type ZstdBlockState is Data:
  ZstdBlockState{huf: Maybe<&2, H.ZstdHufTable>, tables: S.ZstdSeqTables, reps: ZstdReps, produced: Nat}

# a block's bytes, the state after it, and the window
type ZstdBlockOut is Type:
  ZstdBlockOut{bytes: List<&2, U32>, st: ZstdBlockState, win: ZstdWindow}

# a block's literals and sequences, and its tree and tables
type ZsParsed is Data:
  ZsParsed{lits: List<&2, U32>, seqs: List<&2, S.ZstdSeq>, huf: Maybe<&2, H.ZstdHufTable>, tables: S.ZstdSeqTables}

def blk.l.rest(l: L.ZstdLiterals) -> List<&2, U32>:
  match l:
    case L.ZstdLiterals{lits, rest, tree}:
      rest

def blk.parsed(l: L.ZstdLiterals, q: S.ZstdSequences) -> ZsParsed:
  match l:
    case L.ZstdLiterals{lits, rest, tree}:
      match q:
        case S.ZstdSequences{seqs, tables}:
          ZsParsed{lits, seqs, tree, tables}

def blk.parse(xs: List<&2, U32>, huf: Maybe<&2, H.ZstdHufTable>, tables: S.ZstdSeqTables, +block_max: Nat) -> Result<&2, &2, E.ZstdError, ZsParsed>:
  do Result<&2, &2, E.ZstdError, ZsParsed>:
    +l : L.ZstdLiterals <- L.ZstdLit.decode(xs, block_max, huf)
    q : S.ZstdSequences <- S.ZstdSeq.decode(blk.l.rest(l), tables)
    return blk.parsed(l, q)

def blk.out(r: Result<&2, &1, E.ZstdError, ZsEx>, huf: Maybe<&2, H.ZstdHufTable>, tables: S.ZstdSeqTables) -> Result<&2, &1, E.ZstdError, ZstdBlockOut>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ZsEx{lits, nlits, o, blk, produced, reps}}:
      match o:
        case ZsWOut{w, out}:
          Done{ZstdBlockOut{B.rev(out), ZstdBlockState{huf, tables, reps, produced}, w}}

def blk.exec(p: Result<&2, &2, E.ZstdError, ZsParsed>, win: ZstdWindow, reps: ZstdReps, produced: Nat, +w: Nat, +dl: Nat, +block_max: Nat) -> Result<&2, &1, E.ZstdError, ZstdBlockOut>:
  match p:
    case Fail{e}:
      Fail{e}
    case Done{ZsParsed{+lits, seqs, huf, tables}}:
      blk.out(blk.run(seqs, Done{ZsEx{lits, B.len.fast(lits), ZsWOut{win, Nil{}}, 0n, produced, reps}}, w, dl, block_max), huf, tables)

# The public interface

# the compressed block xs (its content, Block_Size bytes) after the state
# st and the window win: its bytes, the state after it, and the window. w:
# the window size; dl: the dictionary content's size; block_max:
# Block_Maximum_Size
def ZstdBlk.decode(xs: List<&2, U32>, st: ZstdBlockState, win: ZstdWindow, +w: Nat, +dl: Nat, +block_max: Nat) -> Result<&2, &1, E.ZstdError, ZstdBlockOut>:
  match st:
    case ZstdBlockState{huf, tables, reps, produced}:
      blk.exec(blk.parse(xs, huf, tables, block_max), win, reps, produced, w, dl, block_max)

# the state after a byte of a raw or RLE block (counted)
def ZstdBlk.put(st: ZstdBlockState) -> ZstdBlockState:
  match st:
    case ZstdBlockState{huf, tables, reps, produced}:
      ZstdBlockState{huf, tables, reps, 1n+produced}

def ZstdBlk.produced(st: ZstdBlockState) -> Nat:
  match st:
    case ZstdBlockState{huf, tables, reps, produced}:
      produced
