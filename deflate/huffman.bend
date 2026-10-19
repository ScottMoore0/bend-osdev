# bend-osdev-deflate: Huffman codes from code lengths, shared by the inflater
# and the deflater (RFC 1951, 3.2.2).
#
# A code is given by one code length per symbol (0: the symbol has no code).
# The codes are canonical, as 3.2.2 defines them: "All codes of a given bit
# length have lexicographically consecutive values, in the same order as the
# symbols they represent; Shorter codes lexicographically precede longer
# codes." huff_tree builds them by 3.2.2's three steps (count the codes of
# each length, find the first code of each length, give each symbol the
# next code of its length) and puts each code, most significant bit first,
# into a binary tree whose leaves are the symbols: the inflater walks it one
# bit at a time (its first bit is the code's most significant, 3.1.1).
#
# huff_kraft tells whether the lengths ask for more codes than fit
# (over-subscribed), exactly fill the code space (complete), or leave codes
# unused (incomplete); the inflater refuses what zlib refuses (see
# inflate.bend). huff_code is a symbol's code as the tree holds it (the path
# to its leaf); huff_table is every symbol's code, for the deflater.
import Base
import ./table.bend as T
import ./eq.bend as Q

type DflTree is Data:
  DflHNil{}
  DflHLeaf{sym: U32}
  DflHNode{zero: DflTree, one: DflTree}

# Counting the codes of each length

def hf.inc(xs: List<&2, U32>, i: Nat) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match i:
        case 0n:
          Con{U32.add(h, 1), t}
        case 1n+p:
          Con{h, hf.inc(t, p)}

def hf.get(xs: List<&2, U32>, i: Nat) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          hf.get(t, p)

def hf.zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{0, hf.zeros(p)}

def hf.counts.go(ls: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      acc
    case Con{h, t}:
      hf.counts.go(t, hf.inc(acc, U32.to_nat(h)))

# bl_count: how many codes have each length 0 to 15 (3.2.2, step 1)
def hf.counts(ls: List<&2, U32>) -> List<&2, U32>:
  hf.counts.go(ls, hf.zeros(16n))

# next_code: the first code of each length (3.2.2, step 2: "code = (code +
# bl_count[bits-1]) << 1", with bl_count[0] taken as 0)
def hf.next.go(cs: List<&2, U32>, +code: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case Con{c, t}:
      +nc = U32.shl(U32.add(code, c))
      hf.next.go(t, nc, Con{nc, acc})

def hf.next(cs: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c0, +t}:
      # next_code[1] = (0 + 0) << 1; then each from the count one shorter
      Con{0, hf.next.go(List.take(&2, U32, Con{0, t}, 15n), 0, Nil{})}

# The tree

def hf.bit(+code: U32, p: Nat) -> Bool:
  U32.is_eq(U32.and(U32.shrn(code, p), 1), 1)

# sym at the l-bit code `code`, whose next bit (most significant first) is b
def hf.ins(l: Nat, b: Bool, +code: U32, t: DflTree, +sym: U32) -> DflTree:
  match l:
    case 0n:
      match t:
        case DflHNil{}:
          DflHLeaf{sym}
        case DflHLeaf{s}:
          DflHLeaf{s}
        case DflHNode{z, o}:
          DflHNode{z, o}
    case 1n+ +p:
      match b:
        case True{}:
          match t:
            case DflHNode{z, o}:
              DflHNode{z, hf.ins(p, hf.bit(code, Nat.sub(p, 1n)), code, o, sym)}
            case DflHNil{}:
              DflHNode{DflHNil{}, hf.ins(p, hf.bit(code, Nat.sub(p, 1n)), code, DflHNil{}, sym)}
            case DflHLeaf{s}:
              DflHLeaf{s}
        case False{}:
          match t:
            case DflHNode{z, o}:
              DflHNode{hf.ins(p, hf.bit(code, Nat.sub(p, 1n)), code, z, sym), o}
            case DflHNil{}:
              DflHNode{hf.ins(p, hf.bit(code, Nat.sub(p, 1n)), code, DflHNil{}, sym), DflHNil{}}
            case DflHLeaf{s}:
              DflHLeaf{s}

type DflHufAcc is Data:
  DflHufAcc{next: List<&2, U32>, tree: DflTree}

def hf.put.len(+l: Nat, a: DflHufAcc, +sym: U32) -> DflHufAcc:
  match l:
    case 0n:
      a
    case 1n+p:
      match a:
        case DflHufAcc{+next, tree}:
          +code = hf.get(next, l)
          DflHufAcc{hf.inc(next, l), hf.ins(l, hf.bit(code, p), code, tree, sym)}

# each symbol in turn gets the next code of its length (3.2.2, step 3)
def hf.assign(ls: List<&2, U32>, +sym: U32, a: DflHufAcc) -> DflHufAcc:
  match ls:
    case Nil{}:
      a
    case Con{h, t}:
      hf.assign(t, U32.add(sym, 1), hf.put.len(U32.to_nat(h), a, sym))

def hf.acc.tree(a: DflHufAcc) -> DflTree:
  match a:
    case DflHufAcc{next, tree}:
      tree

# the decoding tree of the code with lengths ls (ls[i]: symbol i's length)
def huff_tree(+ls: List<&2, U32>) -> DflTree:
  hf.acc.tree(hf.assign(ls, 0, DflHufAcc{hf.next(hf.counts(ls)), DflHNil{}}))

# Over-subscribed, complete, incomplete (Kraft's inequality, code by code)

type DflKraft is Data:
  # no symbol has a code
  DflKraftEmpty{}
  # one symbol has a code, of one bit (incomplete, the other bit unused)
  DflKraftSingle{}
  # the codes fill the code space exactly
  DflKraftComplete{}
  # some codes are left unused
  DflKraftIncomplete{}
  # the lengths ask for more codes than fit
  DflKraftOver{}

# left: how many codes of the current length are still free (capped: once
# above 288 no count of symbols can use them up, nor ask for too many)
def hf.kraft.go(cs: List<&2, U32>, over: Bool, +left: Nat) -> Nat:
  match cs:
    case Nil{}:
      match over:
        case True{}:
          0n
        case False{}:
          1n+left
    case Con{c, t}:
      match over:
        case True{}:
          0n
        case False{}:
          +l2 = Nat.add(left, left)
          +cn = U32.to_nat(c)
          hf.kraft.go(t, Nat.is_lt(l2, cn), Nat.min(Nat.sub(l2, cn), 300n))

def hf.sum(cs: List<&2, U32>, +n: U32) -> U32:
  match cs:
    case Nil{}:
      n
    case Con{c, t}:
      hf.sum(t, U32.add(n, c))

def hf.kraft.small(none: Bool, single: Bool) -> DflKraft:
  match none:
    case True{}:
      DflKraftEmpty{}
    case False{}:
      match single:
        case True{}:
          DflKraftSingle{}
        case False{}:
          DflKraftIncomplete{}

def hf.kraft.of(r: Nat, +used: U32, +c1: U32) -> DflKraft:
  match r:
    case 0n:
      DflKraftOver{}
    case 1n+left:
      match left:
        case 0n:
          DflKraftComplete{}
        case 1n+q:
          hf.kraft.small(U32.is_eq(used, 0), Bool.and(U32.is_eq(used, 1), U32.is_eq(c1, 1)))

def hf.kraft.cs(cs: List<&2, U32>) -> DflKraft:
  match cs:
    case Nil{}:
      DflKraftEmpty{}
    case Con{c0, +t}:
      hf.kraft.of(hf.kraft.go(t, False{}, 1n), hf.sum(t, 0), hf.get(t, 0n))

def huff_kraft(ls: List<&2, U32>) -> DflKraft:
  hf.kraft.cs(hf.counts(ls))

# A symbol's code, as the tree holds it

def hf.path.pick(a: Maybe<&2, List<&2, Bool>>, b: Maybe<&2, List<&2, Bool>>) -> Maybe<&2, List<&2, Bool>>:
  match a:
    case Some{p}:
      Some{Con{False{}, p}}
    case None{}:
      match b:
        case Some{q}:
          Some{Con{True{}, q}}
        case None{}:
          None{}

def hf.path.leaf(eq: Bool) -> Maybe<&2, List<&2, Bool>>:
  match eq:
    case True{}:
      Some{Nil{}}
    case False{}:
      None{}

# the bits from t down to sym's leaf, the first bit sent first
def huff_path(t: DflTree, +sym: U32) -> Maybe<&2, List<&2, Bool>>:
  match t:
    case DflHNil{}:
      None{}
    case DflHLeaf{s}:
      hf.path.leaf(Q.eq.u32(s, sym))
    case DflHNode{z, o}:
      hf.path.pick(huff_path(z, sym), huff_path(o, sym))

def hf.code.of(t: DflTree, +sym: U32) -> Maybe<&2, List<&2, Bool>>:
  match t:
    case DflHNode{z, o}:
      huff_path(DflHNode{z, o}, sym)
    case _:
      None{}

# the code of sym in the code with lengths ls (None if it has none)
def huff_code(+ls: List<&2, U32>, +sym: U32) -> Maybe<&2, List<&2, Bool>>:
  hf.code.of(huff_tree(ls), sym)

# a symbol and the bits after its code
type DflDecoded is Data:
  DflDecoded{sym: U32, rest: List<&2, Bool>}

# the symbol whose code starts bits, and the bits after it (None if the bits
# match no code, or end first): t is the tree below the bits read so far
def hf.decode(bits: List<&2, Bool>, t: DflTree) -> Maybe<&2, DflDecoded>:
  match bits:
    case Nil{}:
      None{}
    case Con{b, rest}:
      match b:
        case True{}:
          match t:
            case DflHNode{z, o}:
              match o:
                case DflHLeaf{s}:
                  Some{DflDecoded{s, rest}}
                case DflHNil{}:
                  None{}
                case DflHNode{z2, o2}:
                  hf.decode(rest, DflHNode{z2, o2})
            case _:
              None{}
        case False{}:
          match t:
            case DflHNode{z, o}:
              match z:
                case DflHLeaf{s}:
                  Some{DflDecoded{s, rest}}
                case DflHNil{}:
                  None{}
                case DflHNode{z2, o2}:
                  hf.decode(rest, DflHNode{z2, o2})
            case _:
              None{}

def huff_decode(t: DflTree, bits: List<&2, Bool>) -> Maybe<&2, DflDecoded>:
  hf.decode(bits, t)

# The encoder's table: every symbol's code, in a table keyed by symbol (the
# code's bits in the order they are sent, the first at bit 0, and its length
# above bit 16)

def hf.walk(t: DflTree, +bits: U32, +depth: Nat, tab: T.DflTab) -> T.DflTab:
  match t:
    case DflHNil{}:
      tab
    case DflHLeaf{s}:
      T.tab.set9(s, tab, U32.or(bits, U32.shln(U32.from_nat(depth), 16n)))
    case DflHNode{z, o}:
      hf.walk(o, U32.or(bits, U32.shln(1, depth)), 1n+depth, hf.walk(z, bits, 1n+depth, tab))

def huff_table(+ls: List<&2, U32>) -> T.DflTab:
  hf.walk(huff_tree(ls), 0, 0n, T.DflTNil{})

# a symbol's code from the table: its bits (as sent, the first at bit 0)
def huff_bits(+tab: T.DflTab, +sym: U32) -> U32:
  U32.and(T.tab.get9(sym, tab), 65535)

# and its length
def huff_len(+tab: T.DflTab, +sym: U32) -> Nat:
  U32.to_nat(U32.shrn(T.tab.get9(sym, tab), 16n))

# The fixed codes (3.2.6)

def hf.rep(n: Nat, +v: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      hf.rep(p, v, Con{v, acc})

# literal/length lengths: 0-143 8 bits, 144-255 9, 256-279 7, 280-287 8
def huff_fixed_lit() -> List<&2, U32>:
  hf.rep(144n, 8, hf.rep(112n, 9, hf.rep(24n, 7, hf.rep(8n, 8, Nil{}))))

# "Distance codes 0-31 are represented by (fixed-length) 5-bit codes"
def huff_fixed_dist() -> List<&2, U32>:
  hf.rep(32n, 5, Nil{})
