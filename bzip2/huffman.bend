# bend-osdev-bzip2: the Huffman codes (Tsai, "BZip2 Format Specification",
# section 3.4, and the canonical code assignment it describes).
#
# A table is a code length (1 to 20) for each symbol of the alphabet. The
# codes are canonical: in order of length, and within a length in order of
# symbol, each code is the one after the last, shifted left when the length
# grows. A table whose lengths ask for more codes of some length than fit
# (an over-full table) gets the codes that fit; the symbols past them can
# never be read, as with the bzip2 tool. A code no symbol has is refused
# when it is read.
#
# Decoding walks a binary tree, one bit per step. Encoding builds lengths
# from symbol frequencies (Huffman's algorithm, with the frequencies halved
# until no code is longer than the limit) and gives each symbol its code.
import Base
import ./bits.bend as K

type Bzip2Huff is Data:
  Bzip2HufLeaf{sym: U32}
  Bzip2HufNode{zero: Bzip2Huff, one: Bzip2Huff}
  Bzip2HufNone{}

# the value a read answers when the bits match no code
def huf.bad() -> U32:
  4294967295

def huf.leaf(t: Bzip2Huff, +sym: U32) -> Bzip2Huff:
  match t:
    case Bzip2HufNone{}:
      Bzip2HufLeaf{sym}
    case Bzip2HufLeaf{s}:
      Bzip2HufLeaf{s}
    case Bzip2HufNode{z, o}:
      Bzip2HufNode{z, o}

def huf.bit(+code: U32, +mask: U32) -> Bool:
  U32.is_ne(U32.and(code, mask), 0)

# sym at the l-bit code `code`, whose next bit is `one` (mask: that bit)
def huf.ins(l: Nat, t: Bzip2Huff, one: Bool, +code: U32, +mask: U32, +sym: U32) -> Bzip2Huff:
  match l:
    case 0n:
      huf.leaf(t, sym)
    case 1n+p:
      match t:
        case Bzip2HufNode{z, o}:
          match one:
            case True{}:
              Bzip2HufNode{z, huf.ins(p, o, huf.bit(code, U32.shr(mask)), code, U32.shr(mask), sym)}
            case False{}:
              Bzip2HufNode{huf.ins(p, z, huf.bit(code, U32.shr(mask)), code, U32.shr(mask), sym), o}
        case Bzip2HufNone{}:
          match one:
            case True{}:
              Bzip2HufNode{Bzip2HufNone{}, huf.ins(p, Bzip2HufNone{}, huf.bit(code, U32.shr(mask)), code, U32.shr(mask), sym)}
            case False{}:
              Bzip2HufNode{huf.ins(p, Bzip2HufNone{}, huf.bit(code, U32.shr(mask)), code, U32.shr(mask), sym), Bzip2HufNone{}}
        case Bzip2HufLeaf{s}:
          Bzip2HufLeaf{s}

# The canonical assignment: the next code, and the tree so far
type Bzip2HufAcc is Data:
  Bzip2HufAcc{code: U32, tree: Bzip2Huff}

def huf.put.fit(fits: Bool, +lnat: Nat, +code: U32, +mask: U32, t: Bzip2Huff, +sym: U32) -> Bzip2Huff:
  match fits:
    case True{}:
      huf.ins(lnat, t, huf.bit(code, mask), code, mask, sym)
    case False{}:
      t

def huf.put(eq: Bool, a: Bzip2HufAcc, +lnat: Nat, +lim: U32, +sym: U32) -> Bzip2HufAcc:
  match eq:
    case True{}:
      match a:
        case Bzip2HufAcc{+code, t}:
          Bzip2HufAcc{U32.add(code, 1), huf.put.fit(U32.is_lt(code, lim), lnat, code, U32.shr(lim), t, sym)}
    case False{}:
      a

# the symbols of length len (lnat as a Nat; lim = 2^len), in order
def huf.scan(ls: List<&2, U32>, +len: U32, +lnat: Nat, +lim: U32, +sym: U32, a: Bzip2HufAcc) -> Bzip2HufAcc:
  match ls:
    case Nil{}:
      a
    case Con{h, t}:
      huf.scan(t, len, lnat, lim, U32.add(sym, 1), huf.put(U32.is_eq(h, len), a, lnat, lim, sym))

def huf.shift(a: Bzip2HufAcc) -> Bzip2HufAcc:
  match a:
    case Bzip2HufAcc{code, t}:
      Bzip2HufAcc{U32.shl(code), t}

def huf.build.go(n: Nat, +ls: List<&2, U32>, +len: U32, +lnat: Nat, a: Bzip2HufAcc) -> Bzip2HufAcc:
  match n:
    case 0n:
      a
    case 1n+p:
      huf.build.go(p, ls, U32.add(len, 1), 1n+lnat, huf.shift(huf.scan(ls, len, lnat, U32.shln(1, lnat), 0, a)))

def huf.acc.tree(a: Bzip2HufAcc) -> Bzip2Huff:
  match a:
    case Bzip2HufAcc{code, t}:
      t

# the decoding tree of a table: ls[i] is symbol i's code length (1 to 20)
def huff_tree(+ls: List<&2, U32>) -> Bzip2Huff:
  huf.acc.tree(huf.build.go(20n, ls, 1, 1n, Bzip2HufAcc{0, Bzip2HufNone{}}))

# Decoding: g is the reader and the bit just read, at the node whose
# children are z and o
def huf.dec.go(fuel: Nat, g: K.Bzip2Flag, z: Bzip2Huff, o: Bzip2Huff) -> K.Bzip2Got:
  match fuel:
    case 0n:
      match g:
        case K.Bzip2Flag{r, b}:
          K.Bzip2Got{r, huf.bad()}
    case 1n+f:
      match g:
        case K.Bzip2Flag{r, b}:
          match b:
            case True{}:
              match o:
                case Bzip2HufLeaf{s}:
                  K.Bzip2Got{r, s}
                case Bzip2HufNone{}:
                  K.Bzip2Got{r, huf.bad()}
                case Bzip2HufNode{z2, o2}:
                  huf.dec.go(f, K.bits.flag(r), z2, o2)
            case False{}:
              match z:
                case Bzip2HufLeaf{s}:
                  K.Bzip2Got{r, s}
                case Bzip2HufNone{}:
                  K.Bzip2Got{r, huf.bad()}
                case Bzip2HufNode{z2, o2}:
                  huf.dec.go(f, K.bits.flag(r), z2, o2)

# the next symbol from r (huf.bad() if the bits match no code)
def huff_decode(t: Bzip2Huff, r: K.Bzip2Bits) -> K.Bzip2Got:
  match t:
    case Bzip2HufNode{z, o}:
      huf.dec.go(20n, K.bits.flag(r), z, o)
    case Bzip2HufLeaf{s}:
      K.Bzip2Got{r, s}
    case Bzip2HufNone{}:
      K.Bzip2Got{r, huf.bad()}

# Encoding: code lengths from frequencies

# a tree with its weight
type Bzip2HufW is Data:
  Bzip2HufW{w: U32, t: Bzip2Huff}

def huf.w.le(+a: Bzip2HufW, +b: Bzip2HufW) -> Bool:
  match a:
    case Bzip2HufW{wa, ta}:
      match b:
        case Bzip2HufW{wb, tb}:
          U32.is_le(wa, wb)

def huf.before(xs: List<&2, Bzip2HufW>, +x: Bzip2HufW) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      huf.w.le(x, h)

# x into the list xs, sorted by weight (first: whether x goes before xs's head)
def huf.insert(xs: List<&2, Bzip2HufW>, first: Bool, +x: Bzip2HufW) -> List<&2, Bzip2HufW>:
  match xs:
    case Nil{}:
      [x]
    case Con{h, +t}:
      match first:
        case True{}:
          Con{x, Con{h, t}}
        case False{}:
          Con{h, huf.insert(t, huf.before(t, x), x)}

def huf.add(+xs: List<&2, Bzip2HufW>, +x: Bzip2HufW) -> List<&2, Bzip2HufW>:
  huf.insert(xs, huf.before(xs, x), x)

# the leaves, weight max(f, 1) each, sorted
def huf.leaves(fs: List<&2, U32>, +sym: U32, acc: List<&2, Bzip2HufW>) -> List<&2, Bzip2HufW>:
  match fs:
    case Nil{}:
      acc
    case Con{f, t}:
      huf.leaves(t, U32.add(sym, 1), huf.add(acc, Bzip2HufW{U32.max(f, 1), Bzip2HufLeaf{sym}}))

def huf.join(a: Bzip2HufW, b: Bzip2HufW) -> Bzip2HufW:
  match a:
    case Bzip2HufW{wa, ta}:
      match b:
        case Bzip2HufW{wb, tb}:
          Bzip2HufW{U32.add(wa, wb), Bzip2HufNode{ta, tb}}

def huf.w.tree(a: Bzip2HufW) -> Bzip2Huff:
  match a:
    case Bzip2HufW{w, t}:
      t

# Huffman's algorithm: join the two lightest until one tree is left
def huf.merge(fuel: Nat, xs: List<&2, Bzip2HufW>) -> Bzip2Huff:
  match fuel:
    case 0n:
      Bzip2HufNone{}
    case 1n+f:
      match xs:
        case Nil{}:
          Bzip2HufNone{}
        case Con{a, rest}:
          match rest:
            case Nil{}:
              huf.w.tree(a)
            case Con{b, more}:
              huf.merge(f, huf.add(more, huf.join(a, b)))

# each leaf's depth into the array of lengths
def huf.depths(t: Bzip2Huff, +d: U32, a: Array<U32>) -> Array<U32>:
  match t:
    case Bzip2HufLeaf{s}:
      Array.set(U32, a, s, d)
    case Bzip2HufNode{z, o}:
      huf.depths(o, U32.add(d, 1), huf.depths(z, U32.add(d, 1), a))
    case Bzip2HufNone{}:
      a

type Bzip2HufLens is Type:
  Bzip2HufLens{a: Array<U32>, ls: List<&2, U32>, max: U32}

def huf.lens.go(n: Nat, r: Array<U32> & U32, +i: U32, acc: List<&2, U32>, +mx: U32) -> Bzip2HufLens:
  match n:
    case 0n:
      (a, v) = r
      Bzip2HufLens{a, acc, mx}
    case 1n+p:
      (a, +v) = r
      +j = U32.sub(i, 1)
      huf.lens.go(p, Array.get(U32, a, j), j, Con{v, acc}, U32.max(mx, v))

def huf.halve(fs: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      Con{U32.add(1, U32.shr(f)), huf.halve(t)}

def huf.lengths.pick(ok: Bool, ls: List<&2, U32>, fs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{ls}
    case False{}:
      None{}

def huf.lengths.done(r: Bzip2HufLens, fs: List<&2, U32>, +limit: U32) -> Maybe<&2, List<&2, U32>>:
  match r:
    case Bzip2HufLens{a, ls, mx}:
      huf.lengths.pick(U32.is_le(mx, limit), ls, fs)

def huf.lengths.try(+n: U32, +fs: List<&2, U32>, +limit: U32) -> Maybe<&2, List<&2, U32>>:
  +t = huf.merge(512n, huf.leaves(fs, 0, Nil{}))
  a = huf.depths(t, 0, [0 : U32*512n])
  huf.lengths.done(huf.lens.go(U32.to_nat(n), Array.get(U32, a, U32.sub(n, 1)), U32.sub(n, 1), Nil{}, 0), fs, limit)

def huf.lengths.go(fuel: Nat, m: Maybe<&2, List<&2, U32>>, +n: U32, +fs: List<&2, U32>, +limit: U32) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match m:
        case Some{ls}:
          ls
        case None{}:
          +h = huf.halve(fs)
          huf.lengths.go(f, huf.lengths.try(n, h, limit), n, h, limit)

# code lengths for symbols with frequencies fs (at least two symbols), none
# longer than limit (at least 9, so that 258 symbols fit)
def huff_lengths(+fs: List<&2, U32>, +limit: U32) -> List<&2, U32>:
  +n = U32.from_nat(List.length(&2, U32, fs))
  huf.lengths.go(32n, huf.lengths.try(n, fs, limit), n, fs, limit)

# The canonical codes of a table, for writing: entry i holds symbol i's code
# in its low 24 bits and its length above them

def huf.code.put(eq: Bool, r: Array<U32> & U32, +len: U32, +sym: U32) -> Array<U32> & U32:
  match eq:
    case True{}:
      (a, +code) = r
      (Array.set(U32, a, sym, U32.or(code, U32.shln(len, 24n))), U32.add(code, 1))
    case False{}:
      r

def huf.code.scan(ls: List<&2, U32>, +len: U32, +sym: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match ls:
    case Nil{}:
      r
    case Con{h, t}:
      huf.code.scan(t, len, U32.add(sym, 1), huf.code.put(U32.is_eq(h, len), r, len, sym))

def huf.code.shift(r: Array<U32> & U32) -> Array<U32> & U32:
  (a, code) = r
  (a, U32.shl(code))

def huf.code.go(n: Nat, +ls: List<&2, U32>, +len: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match n:
    case 0n:
      r
    case 1n+p:
      huf.code.go(p, ls, U32.add(len, 1), huf.code.shift(huf.code.scan(ls, len, 0, r)))

def huf.code.arr(r: Array<U32> & U32) -> Array<U32>:
  (a, code) = r
  a

# the codes of a table of lengths (an array of 512 entries)
def huff_codes(+ls: List<&2, U32>) -> Array<U32>:
  huf.code.arr(huf.code.go(20n, ls, 1, ([0 : U32*512n], 0)))
