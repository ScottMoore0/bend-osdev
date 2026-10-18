# bend-osdev-fdt, strindex.bend: indexes of the strings block, so that the
# reader and the deduplicating writer need not search it from its start.
# Internal: nothing here is public interface, and any of it may change.
#
# By offset (the reader): FdtIx holds, for every offset of the strings
# block, the bytes from that offset on. It is a binary trie over the
# offset's 32 bits, least significant first: the offsets whose low bit is 0
# go left, the others right, and so on, so each level halves the list of
# suffixes. Built once, in one pass per level; a lookup reads at most 32
# levels. PROOF.bend: ix_at proves a lookup equal to dropping that many
# bytes, for every block and every offset (the reader's reference,
# tb.name_at in tree.bend).
#
# By name (the deduplicating writer): FdtDict maps a name (its bytes) to
# the first offset at which the name and a NUL occur in the block. It is a
# trie with one level per byte, each level a list of siblings (property
# names use few distinct bytes, so the lists are short). When a name is added at the end of the block, every
# tail of it (from each of its offsets up to its NUL) is entered, unless the
# trie holds it already, so a later name that is the tail of an earlier one
# finds its offset, as dtc shares them. PROOF.bend: dk_find proves a lookup
# equal to searching the block (the writer's reference, dedup.find in
# tree.bend), for every block built this way and every name without NULs.
import Base

# By offset

# the suffixes of a byte list: from the whole list down to its last byte
def ix.tails(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Con{Con{h, t}, ix.tails(t)}

# every other element: the first, third, ... (keep True) or the second,
# fourth, ... (keep False)
def ix.alt(xs: List<&2, List<&2, U32>>, keep: Bool) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match keep:
        case True{}:
          Con{h, ix.alt(t, False{})}
        case False{}:
          ix.alt(t, True{})

# The same two, tail-recursive (PROOF.bend: tails_fast, alt_fast); ix.tails
# and ix.alt above are the reference forms the proofs compute through

def ix.tails.go(xs: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case Con{+h, +t}:
      ix.tails.go(t, Con{Con{h, t}, acc})

def ix.tails.fast(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  List.reverse(&2, List<&2, U32>, ix.tails.go(xs, Nil{}))

def ix.alt.go(xs: List<&2, List<&2, U32>>, keep: Bool, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      match keep:
        case True{}:
          ix.alt.go(t, False{}, Con{h, acc})
        case False{}:
          ix.alt.go(t, True{}, acc)

def ix.alt.fast(xs: List<&2, List<&2, U32>>, keep: Bool) -> List<&2, List<&2, U32>>:
  List.reverse(&2, List<&2, U32>, ix.alt.go(xs, keep, Nil{}))

# the trie: no suffix; one suffix, at offset 0 of what is left; or the
# even and the odd offsets, each halved
type FdtIx is Data:
  FdtIxNone{}
  FdtIxOne{v: List<&2, U32>}
  FdtIxBin{even: FdtIx, odd: FdtIx}

# the trie of k levels over a list of suffixes (the i-th at offset i)
def ix.build(k: Nat, xs: List<&2, List<&2, U32>>) -> FdtIx:
  match k:
    case 0n:
      match xs:
        case Nil{}:
          FdtIxNone{}
        case Con{h, t}:
          FdtIxOne{h}
    case 1n+(+p):
      match xs:
        case Nil{}:
          FdtIxNone{}
        case Con{+h, t}:
          match t:
            case Nil{}:
              FdtIxOne{h}
            case Con{+h2, +t2}:
              FdtIxBin{ix.build(p, ix.alt.fast(Con{h, Con{h2, t2}}, True{})), ix.build(p, ix.alt.fast(Con{h, Con{h2, t2}}, False{}))}

# every bit of w is 0
def ix.zero(k: Nat, w: Word(k)) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          ix.zero(p, t)
        case WCon{True{}, t}:
          False{}

def ix.one(z: Bool, v: List<&2, U32>) -> List<&2, U32>:
  match z:
    case True{}:
      v
    case False{}:
      Nil{}

# the suffix at the offset whose k bits are w (empty past the end)
def ix.get(t: FdtIx, k: Nat, w: Word(k)) -> List<&2, U32>:
  match t:
    case FdtIxNone{}:
      Nil{}
    case FdtIxOne{v}:
      ix.one(ix.zero(k, w), v)
    case FdtIxBin{e, o}:
      match k:
        case 0n:
          Nil{}
        case 1n+p:
          match w:
            case WCon{False{}, r}:
              ix.get(e, p, r)
            case WCon{True{}, r}:
              ix.get(o, p, r)

# the index of a strings block, and the bytes from offset off on
def ix.of(strs: List<&2, U32>) -> FdtIx:
  ix.build(32n, ix.tails.fast(strs))

def ix.at(t: FdtIx, off: U32) -> List<&2, U32>:
  match off:
    case U32{w}:
      ix.get(t, 32n, w)

# By name

# a list of sibling nodes, one per next byte: the byte, the offset of the
# name that ends there (if the block holds that name), the nodes below it,
# and the next sibling
type FdtNt is Data:
  NtEnd{}
  NtKid{byte: U32, val: Maybe<&2, Nat>, down: FdtNt, next: FdtNt}

# the whole index: the offset of the empty name, and the nodes below it
type FdtDict is Data:
  FdtDict{root: Maybe<&2, Nat>, kids: FdtNt}

def nt.empty() -> FdtDict:
  FdtDict{None{}, NtEnd{}}

# the first offset a name has is kept
def nt.keep(v: Maybe<&2, Nat>, o: Nat) -> Maybe<&2, Nat>:
  match v:
    case None{}:
      Some{o}
    case Some{x}:
      Some{x}

# the first of the siblings t is byte c
def nt.hit(t: FdtNt, c: U32) -> Bool:
  match t:
    case NtEnd{}:
      False{}
    case NtKid{x, v, d, n}:
      U32.is_eq(c, x)

# the offset of the name c, r among siblings t (h: nt.hit(t, c))
def nt.find(t: FdtNt, h: Bool, +c: U32, r: List<&2, U32>) -> Maybe<&2, Nat>:
  match t:
    case NtEnd{}:
      None{}
    case NtKid{x, v, +d, +n}:
      match h:
        case True{}:
          match r:
            case Nil{}:
              v
            case Con{+c2, r2}:
              nt.find(d, nt.hit(d, c2), c2, r2)
        case False{}:
          nt.find(n, nt.hit(n, c), c, r)

# a new branch for the name c, r at offset o
def nt.chain(r: List<&2, U32>, c: U32, o: Nat) -> FdtNt:
  match r:
    case Nil{}:
      NtKid{c, Some{o}, NtEnd{}, NtEnd{}}
    case Con{c2, r2}:
      NtKid{c, None{}, nt.chain(r2, c2, o), NtEnd{}}

# siblings t with the name c, r at offset o, unless it has an offset already
# (h: nt.hit(t, c)); a new byte goes last
def nt.add(t: FdtNt, h: Bool, +c: U32, r: List<&2, U32>, +o: Nat) -> FdtNt:
  match t:
    case NtEnd{}:
      nt.chain(r, c, o)
    case NtKid{x, v, +d, +n}:
      match h:
        case True{}:
          match r:
            case Nil{}:
              NtKid{x, nt.keep(v, o), d, n}
            case Con{+c2, r2}:
              NtKid{x, v, nt.add(d, nt.hit(d, c2), c2, r2, o), n}
        case False{}:
          NtKid{x, v, d, nt.add(n, nt.hit(n, c), c, r, o)}

# the offset of name u
def nt.get(u: List<&2, U32>, t: FdtDict) -> Maybe<&2, Nat>:
  match u:
    case Nil{}:
      match t:
        case FdtDict{v, ks}:
          v
    case Con{+c, r}:
      match t:
        case FdtDict{v, +ks}:
          nt.find(ks, nt.hit(ks, c), c, r)

# the index with name u at offset o, unless it has an offset already
def nt.put(u: List<&2, U32>, t: FdtDict, +o: Nat) -> FdtDict:
  match u:
    case Nil{}:
      match t:
        case FdtDict{v, ks}:
          FdtDict{nt.keep(v, o), ks}
    case Con{+c, r}:
      match t:
        case FdtDict{v, +ks}:
          FdtDict{v, nt.add(ks, nt.hit(ks, c), c, r, o)}

# the bytes of xs before its first NUL, if it has one (nul: its first byte
# is a NUL)
def dk.isnul(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      U32.is_eq(0, h)

def dk.mcon(h: U32, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Some{Con{h, k}}

def dk.key(xs: List<&2, U32>, nul: Bool) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, +t}:
      match nul:
        case True{}:
          Some{Nil{}}
        case False{}:
          dk.mcon(h, dk.key(t, dk.isnul(t)))

def dk.key_of(+xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  dk.key(xs, dk.isnul(xs))

def dk.put(m: Maybe<&2, List<&2, U32>>, t: FdtDict, +o: Nat) -> FdtDict:
  match m:
    case None{}:
      t
    case Some{k}:
      nt.put(k, t, o)

# t with the name at each offset of xs (the bytes from there to the next
# NUL), xs's first byte being at offset o
def dk.ins(xs: List<&2, U32>, t: FdtDict, +o: Nat) -> FdtDict:
  match xs:
    case Nil{}:
      t
    case Con{+h, +r}:
      dk.ins(r, dk.put(dk.key_of(Con{h, r}), t, o), 1n+o)
