# bend-osdev-zstd, Finite State Entropy (RFC 8878, section 4.1): table
# descriptions, decoding tables, decoding and encoding.
#
# Usable on its own. A distribution is an accuracy log and a probability per
# symbol (ZstdFseCount{n}, or ZstdFseLess{}: "less than 1", which takes one
# state); ZstdFse.table builds its decoding table, one entry (symbol, number of
# bits, baseline) per state. A decoder in state s emits the entry's symbol,
# then reads the entry's number of bits as a value v and goes to state
# baseline + v. Bit strings are bits.bend's (List<&2, Bool>, in reading
# order). ZstdFse.decode and ZstdFse.encode run one state over a bit string; the
# zstd streams interleave several states, and the sequences and Huffman
# files do that with ZstdFse.entry.
import Base
import ../bytes/bytes.bend as B
import ./bits.bend as Bi

type ZstdFseProb is Data:
  ZstdFseLess{}
  ZstdFseCount{n: Nat}

type ZstdFseEntry is Data:
  ZstdFseEntry{sym: Nat, nb: Nat, base: Nat}

# a complete binary tree over the states, most significant bit first
type ZsFseTree is Data:
  ZsFseLeaf{e: ZstdFseEntry}
  ZsFseNode{lo: ZsFseTree, hi: ZsFseTree}

# a decoding table: its accuracy log, the tree, and the entries in state
# order (which the encoder searches)
type ZstdFseTable is Data:
  ZstdFseTable{al: Nat, tree: ZsFseTree, entries: List<&2, ZstdFseEntry>}

# a table description read: the accuracy log, the probabilities, and how
# many bytes it took
type ZstdFseDesc is Data:
  ZstdFseDesc{al: Nat, probs: List<&2, ZstdFseProb>, used: Nat}

# symbols decoded, and the bits after them
type ZstdFseSyms is Data:
  ZstdFseSyms{syms: List<&2, Nat>, rest: List<&2, Bool>}

# Small helpers

# the position of the highest set bit of n (n at least 1); p = 2^k <= n,
# more: 2p <= n
def fse.highbit.go(fuel: Nat, more: Bool, +n: Nat, +p: Nat, +k: Nat) -> Nat:
  match fuel:
    case 0n:
      k
    case 1n+f:
      match more:
        case True{}:
          +q = Nat.add(p, p)
          fse.highbit.go(f, Nat.is_le(Nat.add(q, q), n), n, q, 1n+k)
        case False{}:
          k

def ZstdFse.highbit(+n: Nat) -> Nat:
  fse.highbit.go(64n, Nat.is_le(2n, n), n, 1n, 0n)

def fse.abs(p: ZstdFseProb) -> Nat:
  match p:
    case ZstdFseLess{}:
      1n
    case ZstdFseCount{n}:
      n

def fse.total(ps: List<&2, ZstdFseProb>, acc: Nat) -> Nat:
  match ps:
    case Nil{}:
      acc
    case Con{h, t}:
      fse.total(t, Nat.add(acc, fse.abs(h)))

def fse.pick(-A: Data, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

# The tree

def fse.dummy() -> ZstdFseEntry:
  ZstdFseEntry{0n, 0n, 0n}

# the entry of state s; half = 2^(k-1); low: s < half
def fse.get(k: Nat, t: ZsFseTree, low: Bool, +half: Nat, +s: Nat) -> ZstdFseEntry:
  match k:
    case 0n:
      match t:
        case ZsFseLeaf{e}:
          e
        case ZsFseNode{lo, hi}:
          fse.dummy()
    case 1n+p:
      match t:
        case ZsFseLeaf{e}:
          e
        case ZsFseNode{lo, hi}:
          match low:
            case True{}:
              +h = Nat.div(half, 2n)
              fse.get(p, lo, Nat.is_lt(s, h), h, s)
            case False{}:
              +h = Nat.div(half, 2n)
              +s2 = Nat.sub(s, half)
              fse.get(p, hi, Nat.is_lt(s2, h), h, s2)

# the trees of the next level up: neighbours paired
def fse.pairs(ts: List<&2, ZsFseTree>, acc: List<&2, ZsFseTree>) -> List<&2, ZsFseTree>:
  match ts:
    case Con{a, Con{b, rest}}:
      fse.pairs(rest, Con{ZsFseNode{a, b}, acc})
    case Con{a, Nil{}}:
      List.reverse(&2, ZsFseTree, Con{a, acc})
    case Nil{}:
      List.reverse(&2, ZsFseTree, acc)

def fse.leaves(es: List<&2, ZstdFseEntry>, acc: List<&2, ZsFseTree>) -> List<&2, ZsFseTree>:
  match es:
    case Nil{}:
      List.reverse(&2, ZsFseTree, acc)
    case Con{e, rest}:
      fse.leaves(rest, Con{ZsFseLeaf{e}, acc})

# the tree of depth k over 2^k trees of depth 0
def fse.build(k: Nat, ts: List<&2, ZsFseTree>) -> ZsFseTree:
  match k:
    case 0n:
      match ts:
        case Nil{}:
          ZsFseLeaf{fse.dummy()}
        case Con{h, rest}:
          h
    case 1n+p:
      fse.build(p, fse.pairs(ts, Nil{}))

# The decoding table (RFC 8878, section 4.1.1: "FSE Table Description")
#
# Symbols of probability "less than 1" take the last states, one each, from
# the end down. The others are spread: each symbol in order takes as many
# states as its probability, starting at 0 and stepping by
# size/2 + size/8 + 3 (modulo the size), skipping the states the first ones
# took. Then, state by state in order, a symbol's states get the numbers
# from its probability up (x); a state's number of bits is al - highbit(x)
# and its baseline (x << bits) - size.

# the symbol at each position, a trie like the tree
type ZsSlots is Data:
  ZsSlotNone{}
  ZsSlotSym{sym: Nat}
  ZsSlotNode{lo: ZsSlots, hi: ZsSlots}

def fse.slot.lo(t: ZsSlots) -> ZsSlots:
  match t:
    case ZsSlotNode{lo, hi}:
      lo
    case _:
      ZsSlotNone{}

def fse.slot.hi(t: ZsSlots) -> ZsSlots:
  match t:
    case ZsSlotNode{lo, hi}:
      hi
    case _:
      ZsSlotNone{}

# t with v at position s (depth k, half = 2^(k-1), low: s < half)
def fse.slot.set(k: Nat, low: Bool, +half: Nat, +s: Nat, +t: ZsSlots, +v: Nat) -> ZsSlots:
  match k:
    case 0n:
      ZsSlotSym{v}
    case 1n+p:
      match low:
        case True{}:
          +h = Nat.div(half, 2n)
          ZsSlotNode{fse.slot.set(p, Nat.is_lt(s, h), h, s, fse.slot.lo(t), v), fse.slot.hi(t)}
        case False{}:
          +h = Nat.div(half, 2n)
          +s2 = Nat.sub(s, half)
          ZsSlotNode{fse.slot.lo(t), fse.slot.set(p, Nat.is_lt(s2, h), h, s2, fse.slot.hi(t), v)}

def fse.slot.get(k: Nat, t: ZsSlots, low: Bool, +half: Nat, +s: Nat) -> Nat:
  match k:
    case 0n:
      match t:
        case ZsSlotSym{v}:
          v
        case _:
          0n
    case 1n+p:
      match t:
        case ZsSlotNode{lo, hi}:
          match low:
            case True{}:
              +h = Nat.div(half, 2n)
              fse.slot.get(p, lo, Nat.is_lt(s, h), h, s)
            case False{}:
              +h = Nat.div(half, 2n)
              +s2 = Nat.sub(s, half)
              fse.slot.get(p, hi, Nat.is_lt(s2, h), h, s2)
        case _:
          0n

def fse.put(+al: Nat, +size: Nat, +pos: Nat, +t: ZsSlots, +v: Nat) -> ZsSlots:
  +half = Nat.div(size, 2n)
  fse.slot.set(al, Nat.is_lt(pos, half), half, pos, t, v)

def fse.at(+al: Nat, +size: Nat, +pos: Nat, +t: ZsSlots) -> Nat:
  +half = Nat.div(size, 2n)
  fse.slot.get(al, t, Nat.is_lt(pos, half), half, pos)

# the "less than 1" symbols, from the last state down; high: the next one
type ZsSpread is Data:
  ZsSpread{pos: Nat, slots: ZsSlots}

def fse.less(ps: List<&2, ZstdFseProb>, +al: Nat, +size: Nat, +sym: Nat, +high: Nat, t: ZsSlots) -> ZsSpread:
  match ps:
    case Nil{}:
      ZsSpread{high, t}
    case Con{p, rest}:
      match p:
        case ZstdFseLess{}:
          fse.less(rest, al, size, 1n+sym, Nat.sub(high, 1n), fse.put(al, size, high, t, sym))
        case ZstdFseCount{n}:
          fse.less(rest, al, size, 1n+sym, high, t)

# the next free position: q stepped on while it is past high (fuel: the
# table size)
def fse.advance(fuel: Nat, over: Bool, +q: Nat, +step: Nat, +size: Nat, +high: Nat) -> Nat:
  match fuel:
    case 0n:
      q
    case 1n+f:
      match over:
        case True{}:
          +q2 = Nat.mod(Nat.add(q, step), size)
          fse.advance(f, Nat.is_lt(high, q2), q2, step, size, high)
        case False{}:
          q

# n states for sym, from pos on
def fse.place(n: Nat, +al: Nat, +size: Nat, +step: Nat, +high: Nat, +sym: Nat, +pos: Nat, t: ZsSlots) -> ZsSpread:
  match n:
    case 0n:
      ZsSpread{pos, t}
    case 1n+k:
      +q = Nat.mod(Nat.add(pos, step), size)
      fse.place(k, al, size, step, high, sym, fse.advance(size, Nat.is_lt(high, q), q, step, size, high), fse.put(al, size, pos, t, sym))

def fse.spread(ps: List<&2, ZstdFseProb>, +al: Nat, +size: Nat, +step: Nat, +high: Nat, +sym: Nat, sp: ZsSpread) -> ZsSlots:
  match ps:
    case Nil{}:
      ZsSpread{pos, t} = sp
      t
    case Con{p, rest}:
      match p:
        case ZstdFseLess{}:
          fse.spread(rest, al, size, step, high, 1n+sym, sp)
        case ZstdFseCount{n}:
          ZsSpread{pos, t} = sp
          fse.spread(rest, al, size, step, high, 1n+sym, fse.place(n, al, size, step, high, sym, pos, t))

# each symbol's first state number: its probability (1 for "less than 1")
def fse.firsts(ps: List<&2, ZstdFseProb>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{p, rest}:
      fse.firsts(rest, Con{fse.abs(p), acc})

def fse.nth(xs: List<&2, Nat>, i: Nat) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, xs, i), 0n)

# the entries, state by state; nexts: each symbol's next state number
def fse.entries(fuel: Nat, +al: Nat, +size: Nat, +st: Nat, +slots: ZsSlots, +nexts: List<&2, Nat>, acc: List<&2, ZstdFseEntry>) -> List<&2, ZstdFseEntry>:
  match fuel:
    case 0n:
      List.reverse(&2, ZstdFseEntry, acc)
    case 1n+f:
      +sym = fse.at(al, size, st, slots)
      +x = fse.nth(nexts, sym)
      +nb = Nat.sub(al, ZstdFse.highbit(x))
      +base = Nat.sub(Nat.mul(x, Bi.ZstdBits.pow2(nb)), size)
      fse.entries(f, al, size, 1n+st, slots, List.set(&2, Nat, nexts, sym, 1n+x), Con{ZstdFseEntry{sym, nb, base}, acc})

def fse.table.of(sp: ZsSpread, +al: Nat, +size: Nat, +step: Nat, +ps: List<&2, ZstdFseProb>) -> ZstdFseTable:
  match sp:
    case ZsSpread{high, t}:
      +slots = fse.spread(ps, al, size, step, high, 0n, ZsSpread{0n, t})
      +es = fse.entries(size, al, size, 0n, slots, fse.firsts(ps, Nil{}), Nil{})
      ZstdFseTable{al, fse.build(al, fse.leaves(es, Nil{})), es}

def fse.table.ok(ok: Bool, +al: Nat, +ps: List<&2, ZstdFseProb>) -> Maybe<&2, ZstdFseTable>:
  match ok:
    case True{}:
      +size = Bi.ZstdBits.pow2(al)
      +step = Nat.add(Nat.add(Nat.div(size, 2n), Nat.div(size, 8n)), 3n)
      Some{fse.table.of(fse.less(ps, al, size, 0n, Nat.sub(size, 1n), ZsSlotNone{}), al, size, step, ps)}
    case False{}:
      None{}

# The public interface: tables

# the decoding table of a distribution: None unless the probabilities sum to
# 2^al (al at most 15)
def ZstdFse.table(+al: Nat, +ps: List<&2, ZstdFseProb>) -> Maybe<&2, ZstdFseTable>:
  fse.table.ok(Bool.and(Nat.is_le(al, 15n), Nat.is_eq(fse.total(ps, 0n), Bi.ZstdBits.pow2(al))), al, ps)

# the table of RLE mode: one state, the symbol, no bits
def ZstdFse.rle(+sym: Nat) -> ZstdFseTable:
  +e = {ZstdFseEntry{sym, 0n, 0n} : ZstdFseEntry}
  ZstdFseTable{0n, ZsFseLeaf{e}, [e]}

def ZstdFse.al(t: ZstdFseTable) -> Nat:
  match t:
    case ZstdFseTable{al, tree, es}:
      al

# the entry of state s
def ZstdFse.entry(t: ZstdFseTable, +s: Nat) -> ZstdFseEntry:
  match t:
    case ZstdFseTable{+al, tree, es}:
      +half = Nat.div(Bi.ZstdBits.pow2(al), 2n)
      fse.get(al, tree, Nat.is_lt(s, half), half, s)

# The predefined distributions (RFC 8878, section 3.1.1.3.2.2)

def fse.probs(xs: List<&2, U32>, acc: List<&2, ZstdFseProb>) -> List<&2, ZstdFseProb>:
  match xs:
    case Nil{}:
      List.reverse(&2, ZstdFseProb, acc)
    case Con{+h, t}:
      fse.probs(t, Con{fse.pick(ZstdFseProb, U32.is_eq(h, 0), ZstdFseLess{}, ZstdFseCount{U32.to_nat(h)}), acc})

# literals lengths, accuracy log 6 (0 here stands for -1, "less than 1")
def ZstdFse.predefined_ll() -> List<&2, ZstdFseProb>:
  fse.probs([4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1, 0, 0, 0, 0], Nil{})

# match lengths, accuracy log 6
def ZstdFse.predefined_ml() -> List<&2, ZstdFseProb>:
  fse.probs([1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0], Nil{})

# offset codes, accuracy log 5
def ZstdFse.predefined_of() -> List<&2, ZstdFseProb>:
  fse.probs([1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], Nil{})

def fse.table_or_rle(m: Maybe<&2, ZstdFseTable>) -> ZstdFseTable:
  match m:
    case Some{t}:
      t
    case None{}:
      ZstdFse.rle(0n)

def ZstdFse.table_ll() -> ZstdFseTable:
  fse.table_or_rle(ZstdFse.table(6n, ZstdFse.predefined_ll()))

def ZstdFse.table_ml() -> ZstdFseTable:
  fse.table_or_rle(ZstdFse.table(6n, ZstdFse.predefined_ml()))

def ZstdFse.table_of() -> ZstdFseTable:
  fse.table_or_rle(ZstdFse.table(5n, ZstdFse.predefined_of()))

# Table descriptions (RFC 8878, section 4.1.1), read from a forward bitstream
#
# The accuracy log is 5 plus the first 4 bits. Then a value per symbol, in
# order, until the probabilities reach 2^al: with r points remaining, a
# value is 0 to r + 1, in nb - 1 or nb bits (nb the least with 2^nb > r + 1:
# the low values, below low = 2^nb - 1 - (r + 1), take nb - 1 bits); the
# probability is the value minus 1 (-1: "less than 1"). A probability of 0
# is followed by 2-bit repeat flags: that many more zeros, and another flag
# after a 3. The description ends on a byte boundary.

type ZsFseRd is Data:
  ZsFseGo{bits: List<&2, Bool>, used: Nat, remaining: Nat, nsym: Nat, acc: List<&2, ZstdFseProb>}
  ZsFseZeros{bits: List<&2, Bool>, used: Nat, remaining: Nat, nsym: Nat, acc: List<&2, ZstdFseProb>}
  ZsFseStop{used: Nat, acc: List<&2, ZstdFseProb>}
  ZsFseFail{}

# the symbol read: it fits in the remaining points, or the description is
# malformed; a zero is followed by repeat flags
def fse.rd.fit(ok: Bool, p: ZstdFseProb, zero: Bool, bits: List<&2, Bool>, used: Nat, remaining: Nat, +nsym: Nat, acc: List<&2, ZstdFseProb>) -> ZsFseRd:
  match ok:
    case True{}:
      match zero:
        case True{}:
          ZsFseZeros{bits, used, remaining, 1n+nsym, Con{p, acc}}
        case False{}:
          ZsFseGo{bits, used, remaining, 1n+nsym, Con{p, acc}}
    case False{}:
      ZsFseFail{}

# the probability of value v
def fse.rd.prob(v: Nat, bits: List<&2, Bool>, used: Nat, +remaining: Nat, nsym: Nat, acc: List<&2, ZstdFseProb>) -> ZsFseRd:
  match v:
    case 0n:
      fse.rd.fit(Nat.is_le(1n, remaining), ZstdFseLess{}, False{}, bits, used, Nat.sub(remaining, 1n), nsym, acc)
    case 1n+p:
      +q = p
      fse.rd.fit(Nat.is_le(q, remaining), ZstdFseCount{q}, Nat.is_eq(q, 0n), bits, used, Nat.sub(remaining, q), nsym, acc)

# a value read in nb bits: from 2^(nb-1) up it stands for v - low
def fse.rd.big(big: Bool, +v: Nat, +low: Nat, bits: List<&2, Bool>, used: Nat, remaining: Nat, nsym: Nat, acc: List<&2, ZstdFseProb>) -> ZsFseRd:
  match big:
    case True{}:
      fse.rd.prob(Nat.sub(v, low), bits, used, remaining, nsym, acc)
    case False{}:
      fse.rd.prob(v, bits, used, remaining, nsym, acc)

def fse.rd.extra(r: Maybe<&2, Bi.ZstdBits>, +v: Nat, +nb: Nat, +low: Nat, +used: Nat, remaining: Nat, nsym: Nat, acc: List<&2, ZstdFseProb>) -> ZsFseRd:
  match r:
    case None{}:
      ZsFseFail{}
    case Some{Bi.ZstdBits{e, bits}}:
      +hv = Bi.ZstdBits.pow2(Nat.sub(nb, 1n))
      +v2 = Nat.add(v, Nat.mul(e, hv))
      fse.rd.big(Nat.is_le(hv, v2), v2, low, bits, Nat.add(used, nb), remaining, nsym, acc)

# v, read in nb - 1 bits: below low it is the value
def fse.rd.small(small: Bool, +v: Nat, +nb: Nat, +low: Nat, +bits: List<&2, Bool>, +used: Nat, remaining: Nat, nsym: Nat, acc: List<&2, ZstdFseProb>) -> ZsFseRd:
  match small:
    case True{}:
      fse.rd.prob(v, bits, Nat.add(used, Nat.sub(nb, 1n)), remaining, nsym, acc)
    case False{}:
      fse.rd.extra(Bi.ZstdBits.read_le(1n, bits), v, nb, low, used, remaining, nsym, acc)

def fse.rd.value(r: Maybe<&2, Bi.ZstdBits>, +nb: Nat, +low: Nat, +used: Nat, remaining: Nat, nsym: Nat, acc: List<&2, ZstdFseProb>) -> ZsFseRd:
  match r:
    case None{}:
      ZsFseFail{}
    case Some{Bi.ZstdBits{+v, bits}}:
      fse.rd.small(Nat.is_lt(v, low), v, nb, low, bits, used, remaining, nsym, acc)

# the next symbol: none when the points are used up; too many symbols is a
# failure
def fse.rd.go(stop: Bool, over: Bool, +bits: List<&2, Bool>, +used: Nat, +remaining: Nat, nsym: Nat, acc: List<&2, ZstdFseProb>) -> ZsFseRd:
  match stop:
    case True{}:
      ZsFseStop{used, acc}
    case False{}:
      match over:
        case True{}:
          ZsFseFail{}
        case False{}:
          +top = Nat.add(remaining, 1n)
          +nb = Nat.add(ZstdFse.highbit(top), 1n)
          +low = Nat.sub(Nat.sub(Bi.ZstdBits.pow2(nb), 1n), top)
          fse.rd.value(Bi.ZstdBits.read_le(Nat.sub(nb, 1n), bits), nb, low, used, remaining, nsym, acc)

type ZsFseZ is Data:
  ZsFseZ{nsym: Nat, acc: List<&2, ZstdFseProb>}

# n more zeros, each within the symbol limit (over: nsym past max_sym)
def fse.rd.zeros.add(n: Nat, over: Bool, +max_sym: Nat, +nsym: Nat, acc: List<&2, ZstdFseProb>) -> Maybe<&2, ZsFseZ>:
  match n:
    case 0n:
      Some{ZsFseZ{nsym, acc}}
    case 1n+k:
      match over:
        case True{}:
          None{}
        case False{}:
          fse.rd.zeros.add(k, Nat.is_lt(max_sym, 1n+nsym), max_sym, 1n+nsym, Con{ZstdFseCount{0n}, acc})

def fse.rd.zeros.after(m: Maybe<&2, ZsFseZ>, more: Bool, bits: List<&2, Bool>, used: Nat, remaining: Nat) -> ZsFseRd:
  match m:
    case None{}:
      ZsFseFail{}
    case Some{ZsFseZ{nsym, acc}}:
      match more:
        case True{}:
          ZsFseZeros{bits, used, remaining, nsym, acc}
        case False{}:
          ZsFseGo{bits, used, remaining, nsym, acc}

def fse.rd.zeros(r: Maybe<&2, Bi.ZstdBits>, +max_sym: Nat, +used: Nat, remaining: Nat, +nsym: Nat, acc: List<&2, ZstdFseProb>) -> ZsFseRd:
  match r:
    case None{}:
      ZsFseFail{}
    case Some{Bi.ZstdBits{+rep, bits}}:
      fse.rd.zeros.after(fse.rd.zeros.add(rep, Nat.is_lt(max_sym, nsym), max_sym, nsym, acc), Nat.is_eq(rep, 3n), bits, Nat.add(used, 2n), remaining)

# every step reads a bit or more, or stops
def fse.rd.loop(fuel: Nat, st: ZsFseRd, +max_sym: Nat) -> ZsFseRd:
  match fuel:
    case 0n:
      ZsFseFail{}
    case 1n+f:
      match st:
        case ZsFseGo{bits, used, +remaining, +nsym, acc}:
          fse.rd.loop(f, fse.rd.go(Nat.is_eq(remaining, 0n), Nat.is_lt(max_sym, nsym), bits, used, remaining, nsym, acc), max_sym)
        case ZsFseZeros{bits, used, remaining, nsym, acc}:
          fse.rd.loop(f, fse.rd.zeros(Bi.ZstdBits.read_le(2n, bits), max_sym, used, remaining, nsym, acc), max_sym)
        case ZsFseStop{used, acc}:
          ZsFseStop{used, acc}
        case ZsFseFail{}:
          ZsFseFail{}

def fse.rd.result(st: ZsFseRd, +al: Nat) -> Maybe<&2, ZstdFseDesc>:
  match st:
    case ZsFseStop{used, acc}:
      Some{ZstdFseDesc{al, List.reverse(&2, ZstdFseProb, acc), Nat.div(Nat.add(used, 7n), 8n)}}
    case _:
      None{}

def fse.rd.begin(ok: Bool, +al: Nat, +bits: List<&2, Bool>, +max_sym: Nat) -> Maybe<&2, ZstdFseDesc>:
  match ok:
    case True{}:
      fse.rd.result(fse.rd.loop(Nat.add(Bi.ZstdBits.len(bits), 2n), ZsFseGo{bits, 4n, Bi.ZstdBits.pow2(al), 0n, Nil{}}, max_sym), al)
    case False{}:
      None{}

def fse.rd.start(r: Maybe<&2, Bi.ZstdBits>, +max_al: Nat, +max_sym: Nat) -> Maybe<&2, ZstdFseDesc>:
  match r:
    case None{}:
      None{}
    case Some{Bi.ZstdBits{a, bits}}:
      +al = Nat.add(a, 5n)
      fse.rd.begin(Nat.is_le(al, max_al), al, bits, max_sym)

# The public interface: descriptions, decoding, encoding

# the table description at the start of xs (bytes): its distribution and
# size in bytes; None if it is malformed, its accuracy log passes max_al, or
# it gives probabilities to symbols past max_sym
def ZstdFse.read_description(xs: List<&2, U32>, +max_al: Nat, +max_sym: Nat) -> Maybe<&2, ZstdFseDesc>:
  fse.rd.start(Bi.ZstdBits.read_le(4n, Bi.ZstdBits.forward(B.take.fast(512n, xs))), max_al, max_sym)

def ZstdFse.sym(e: ZstdFseEntry) -> Nat:
  match e:
    case ZstdFseEntry{sym, nb, base}:
      sym

def ZstdFse.nb(e: ZstdFseEntry) -> Nat:
  match e:
    case ZstdFseEntry{sym, nb, base}:
      nb

# the state after e: its baseline plus its bits read as a value
def fse.next.add(r: Maybe<&2, Bi.ZstdBits>, +base: Nat) -> Maybe<&2, Bi.ZstdBits>:
  match r:
    case None{}:
      None{}
    case Some{Bi.ZstdBits{v, rest}}:
      Some{Bi.ZstdBits{Nat.add(base, v), rest}}

def ZstdFse.next(e: ZstdFseEntry, bits: List<&2, Bool>) -> Maybe<&2, Bi.ZstdBits>:
  match e:
    case ZstdFseEntry{sym, nb, base}:
      fse.next.add(Bi.ZstdBits.read(nb, bits), base)

# n symbols, the first from the state in cur (with the bits after it)
def fse.dec(n: Nat, +t: ZstdFseTable, cur: Maybe<&2, Bi.ZstdBits>, acc: List<&2, Nat>) -> Maybe<&2, ZstdFseSyms>:
  match n:
    case 0n:
      match cur:
        case None{}:
          None{}
        case Some{Bi.ZstdBits{s, bits}}:
          Some{ZstdFseSyms{List.reverse(&2, Nat, acc), bits}}
    case 1n+k:
      match k:
        case 0n:
          match cur:
            case None{}:
              None{}
            case Some{Bi.ZstdBits{s, bits}}:
              Some{ZstdFseSyms{List.reverse(&2, Nat, Con{ZstdFse.sym(ZstdFse.entry(t, s)), acc}), bits}}
        case 1n+j:
          match cur:
            case None{}:
              None{}
            case Some{Bi.ZstdBits{s, bits}}:
              +e = ZstdFse.entry(t, s)
              fse.dec(1n+j, t, ZstdFse.next(e, bits), Con{ZstdFse.sym(e), acc})

# n symbols of one state over bits: the first state is read in al bits, and
# each later one follows from the one before; with the bits after them
def ZstdFse.decode(+t: ZstdFseTable, bits: List<&2, Bool>, n: Nat) -> Maybe<&2, ZstdFseSyms>:
  match n:
    case 0n:
      Some{ZstdFseSyms{Nil{}, bits}}
    case 1n+k:
      fse.dec(1n+k, t, Bi.ZstdBits.read(ZstdFse.al(t), bits), Nil{})

# Encoding: the states are chosen from the last symbol back. For a symbol x
# whose successor state is t, a state s of x whose range (its baseline, and
# the 2^nb values after it) holds t; the bits are t - baseline. The encoder
# checks each choice against ZstdFse.entry, the decoder's own lookup, so what
# it writes decodes back whatever the search found (LAWS.bend).

# e is a state of x whose range holds t
def ZstdFse.fits(e: ZstdFseEntry, +x: Nat, +t: Nat) -> Bool:
  match e:
    case ZstdFseEntry{sym, nb, +base}:
      Bool.and(Nat.is_eq(sym, x), Bool.and(Nat.is_le(base, t), Nat.is_lt(Nat.sub(t, base), Bi.ZstdBits.pow2(nb))))

def fse.keep(found: Maybe<&2, Nat>, hit: Bool, +i: Nat) -> Maybe<&2, Nat>:
  match found:
    case None{}:
      match hit:
        case True{}:
          Some{i}
        case False{}:
          None{}
    case Some{j}:
      Some{j}

# the first state of x whose range holds t
def fse.find(es: List<&2, ZstdFseEntry>, +i: Nat, +x: Nat, +t: Nat, found: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      found
    case Con{e, rest}:
      fse.find(rest, 1n+i, x, t, fse.keep(found, ZstdFse.fits(e, x, t), i))

# the first state of x
def fse.first(es: List<&2, ZstdFseEntry>, +i: Nat, +x: Nat, found: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      found
    case Con{e, rest}:
      fse.first(rest, 1n+i, x, fse.keep(found, Nat.is_eq(ZstdFse.sym(e), x), i))

def ZstdFse.entries(t: ZstdFseTable) -> List<&2, ZstdFseEntry>:
  match t:
    case ZstdFseTable{al, tree, es}:
      es

# a state, and the bits that follow its symbol
type ZsFseEnc is Data:
  ZsFseEnc{s: Nat, bits: List<&2, Bool>}

def fse.enc.ok(ok: Bool, e: ZstdFseEntry, +s: Nat, +tn: Nat, acc: List<&2, Bool>) -> Maybe<&2, ZsFseEnc>:
  match ok:
    case True{}:
      match e:
        case ZstdFseEntry{sym, nb, base}:
          Some{ZsFseEnc{s, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, Nat.sub(tn, base)), acc)}}
    case False{}:
      None{}

def fse.enc.found(m: Maybe<&2, Nat>, +t: ZstdFseTable, +x: Nat, +tn: Nat, acc: List<&2, Bool>) -> Maybe<&2, ZsFseEnc>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      +e = ZstdFse.entry(t, s)
      fse.enc.ok(ZstdFse.fits(e, x, tn), e, s, tn, acc)

# xs: the symbols before the one encoded so far, nearest first
def fse.enc(xs: List<&2, Nat>, +t: ZstdFseTable, cur: Maybe<&2, ZsFseEnc>) -> Maybe<&2, ZsFseEnc>:
  match xs:
    case Nil{}:
      cur
    case Con{+x, rest}:
      match cur:
        case None{}:
          None{}
        case Some{ZsFseEnc{+tn, acc}}:
          fse.enc(rest, t, fse.enc.found(fse.find(ZstdFse.entries(t), 0n, x, tn, None{}), t, x, tn, acc))

def fse.enc.start.ok(ok: Bool, +s: Nat) -> Maybe<&2, ZsFseEnc>:
  match ok:
    case True{}:
      Some{ZsFseEnc{s, Nil{}}}
    case False{}:
      None{}

def fse.enc.start(m: Maybe<&2, Nat>, +t: ZstdFseTable, +x: Nat) -> Maybe<&2, ZsFseEnc>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      fse.enc.start.ok(Nat.is_eq(ZstdFse.sym(ZstdFse.entry(t, s)), x), s)

def fse.enc.finish.ok(ok: Bool, +al: Nat, +s: Nat, acc: List<&2, Bool>) -> Maybe<&2, List<&2, Bool>>:
  match ok:
    case True{}:
      Some{List.append(&2, Bool, Bi.ZstdBits.of_nat(al, s), acc)}
    case False{}:
      None{}

def fse.enc.finish(m: Maybe<&2, ZsFseEnc>, +al: Nat) -> Maybe<&2, List<&2, Bool>>:
  match m:
    case None{}:
      None{}
    case Some{ZsFseEnc{+s, acc}}:
      fse.enc.finish.ok(Nat.is_lt(s, Bi.ZstdBits.pow2(al)), al, s, acc)

def fse.encode.go(rs: List<&2, Nat>, +t: ZstdFseTable) -> Maybe<&2, List<&2, Bool>>:
  match rs:
    case Nil{}:
      Some{Nil{}}
    case Con{+last, earlier}:
      fse.enc.finish(fse.enc(earlier, t, fse.enc.start(fse.first(ZstdFse.entries(t), 0n, last, None{}), t, last)), ZstdFse.al(t))

# the bits ZstdFse.decode reads the symbols syms from; None if a symbol has no
# state in the table (probability 0) or a range holds no successor
def ZstdFse.encode(+t: ZstdFseTable, syms: List<&2, Nat>) -> Maybe<&2, List<&2, Bool>>:
  fse.encode.go(List.reverse(&2, Nat, syms), t)

# the first state of x whose range holds t (the search the encoder makes;
# ZstdFse.fits checks what it finds)
def ZstdFse.find(t: ZstdFseTable, +x: Nat, +tn: Nat) -> Maybe<&2, Nat>:
  fse.find(ZstdFse.entries(t), 0n, x, tn, None{})

# the first state of x
def ZstdFse.first(t: ZstdFseTable, +x: Nat) -> Maybe<&2, Nat>:
  fse.first(ZstdFse.entries(t), 0n, x, None{})
