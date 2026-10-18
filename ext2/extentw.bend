# bend-osdev-ext2: writing ext4 extent trees (extent.bend reads them), for
# trees of depth 0 (up to four extents in i_block) and depth 1 (an index in
# i_block over up to four leaf blocks of (block_size - 12) / 12 extents
# each). A tree is loaded as its extents in order, changed as a list
# (a block added, merged into its neighbours where it continues them; a cut
# at a logical block), and stored back in the shallowest shape that holds
# it, reusing its leaf blocks. A deeper tree, or one that would need more
# than four leaves, is refused (Ext2ExtentFull), as is writing into an
# unwritten extent (Ext2Unwritten): splitting those is not done here.
#
# Layout: the ext4 disk-layout documentation, "Extent Tree": the header
# (magic 0xF30A, entries, max, depth, generation), ext4_extent (ee_block,
# ee_len, ee_start_hi, ee_start_lo; a length above 32768 is unwritten),
# ext4_extent_idx (ei_block, ei_leaf_lo, ei_leaf_hi), and the 4-byte
# checksum after a leaf block's max entries.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./csum.bend as K
import ./super.bend as S
import ./extent.bend as X
import ./patch.bend as P
import ./meta.bend as T
import ./bitmap.bend as M
import ./alloc.bend as A
import ./wopts.bend as WO

# A loaded tree: its extents in order, and its leaf blocks (depth 1)
type Ext2ExtTree is Data:
  Ext2ExtTree{extents: List<&2, X.Ext2Extent>, leaves: List<&2, Nat>}

def Ext2ExtW.magic() -> U32:
  62218

# the longest written extent (an unwritten one is one shorter)
def Ext2ExtW.max_len() -> Nat:
  32768n

# extents per leaf block
def Ext2ExtW.leaf_max(+fs: S.Ext2Fs) -> Nat:
  Nat.div(Nat.sub(S.Ext2Fs.block_size(fs), 12n), 12n)

# n extents of a node from byte off on, onto acc (reversed)
def Ext2ExtW.parse(n: Nat, +o: B.Octets, +off: Nat, acc: List<&2, X.Ext2Extent>) -> List<&2, X.Ext2Extent>:
  match n:
    case 0n:
      acc
    case 1n+k:
      Ext2ExtW.parse(k, o, Nat.add(off, 12n), Con{X.Ext2Extent.parse(o, off), acc})

def Ext2ExtW.parse_index(n: Nat, +o: B.Octets, +off: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      List.reverse(&2, Nat, acc)
    case 1n+k:
      Ext2ExtW.parse_index(k, o, Nat.add(off, 12n), Con{X.Ext2ExtentIndex.leaf(X.Ext2ExtentIndex.parse(o, off)), acc})

def Ext2ExtW.check_node(+o: B.Octets, +cap: Nat, +depth: Nat, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  X.Ext2Extent.check_header(X.Ext2ExtentHeader.parse(o), cap, depth, ino)

def Ext2ExtW.entries(+o: B.Octets) -> Nat:
  X.Ext2Extent.entries(X.Ext2ExtentHeader.parse(o))

# the leaves' extents, read in order onto acc (reversed)
def Ext2ExtW.load.leaves(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ls: List<&2, Nat>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +iseed: U32, acc: List<&2, X.Ext2Extent>) -> Result<&2, &2, E.Ext2Error, List<&2, X.Ext2Extent>>:
  match ls:
    case Nil{}:
      Done{List.reverse(&2, X.Ext2Extent, acc)}
    case Con{+b, t}:
      do Result<&2, &2, E.Ext2Error, List<&2, X.Ext2Extent>>:
        S.Ext2.require(Bool.and(Nat.is_lt(0n, b), Nat.is_lt(b, S.Ext2Fs.blocks(fs))), E.Ext2BadBlockRef{ino, b})
        +o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, b)
        X.Ext2Extent.check_csum(S.Ext2Fs.verify_meta(fs), iseed, o, ino, b)
        Ext2ExtW.check_node(o, Ext2ExtW.leaf_max(fs), 0n, ino)
        Ext2ExtW.load.leaves(~Dv, ~block_size, ~read_block, t, d, fs, ino, iseed, Ext2ExtW.parse(Ext2ExtW.entries(o), o, 12n, acc))

def Ext2ExtW.load.depth(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, depth: Nat, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +iseed: U32, +iblock: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2ExtTree>:
  match depth:
    case 0n:
      do Result<&2, &2, E.Ext2Error, Ext2ExtTree>:
        Ext2ExtW.check_node(iblock, 4n, 0n, ino)
        return Ext2ExtTree{List.reverse(&2, X.Ext2Extent, Ext2ExtW.parse(Ext2ExtW.entries(iblock), iblock, 12n, Nil{})), Nil{}}
    case 1n:
      +ls = Ext2ExtW.parse_index(Ext2ExtW.entries(iblock), iblock, 12n, Nil{})
      do Result<&2, &2, E.Ext2Error, Ext2ExtTree>:
        Ext2ExtW.check_node(iblock, 4n, 1n, ino)
        es : List<&2, X.Ext2Extent> <- Ext2ExtW.load.leaves(~Dv, ~block_size, ~read_block, ls, d, fs, ino, iseed, Nil{})
        return Ext2ExtTree{es, ls}
    case _:
      Fail{E.Ext2ExtentFull{ino}}

# the extent tree of inode ino (generation gen) whose root is iblock
def Ext2ExtW.load(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +gen: U32, +iblock: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2ExtTree>:
  Ext2ExtW.load.depth(~Dv, ~block_size, ~read_block, X.Ext2Extent.root_depth(iblock), d, fs, ino, K.Ext2Csum.inode_seed(S.Ext2Fs.seed(fs), U32.from_nat(ino), gen), iblock)

# Changing the extent list

type Ext2ExtHit is Data:
  Ext2ExtHole{}
  Ext2ExtAt{block: Nat}
  Ext2ExtUnwritten{}

def Ext2ExtW.at(written: Bool, +s: Nat, k: Nat) -> Ext2ExtHit:
  match written:
    case True{}:
      Ext2ExtAt{Nat.add(s, k)}
    case False{}:
      Ext2ExtUnwritten{}

def Ext2ExtW.classify.pick(before: Bool, inside: Bool, w: Bool, +s: Nat, k: Nat) -> Maybe<&2, Ext2ExtHit>:
  match before inside:
    case True{} _:
      Some{Ext2ExtHole{}}
    case False{} True{}:
      Some{Ext2ExtW.at(w, s, k)}
    case False{} False{}:
      None{}

# what extent e says of logical block l: there, a hole (it starts past l,
# and later ones start later still), or look further
def Ext2ExtW.classify(e: X.Ext2Extent, +l: Nat) -> Maybe<&2, Ext2ExtHit>:
  match e:
    case X.Ext2Extent{+b, +n, +s, w}:
      Ext2ExtW.classify.pick(Nat.is_lt(l, b), Nat.is_lt(l, Nat.add(b, n)), w, s, Nat.sub(l, b))

def Ext2ExtW.lookup.go(es: List<&2, X.Ext2Extent>, +l: Nat, found: Maybe<&2, Ext2ExtHit>) -> Ext2ExtHit:
  match es found:
    case _ Some{h}:
      h
    case Nil{} None{}:
      Ext2ExtHole{}
    case Con{e, t} None{}:
      Ext2ExtW.lookup.go(t, l, Ext2ExtW.classify(e, l))

# where logical block l is in a list of extents
def Ext2ExtW.lookup(es: List<&2, X.Ext2Extent>, +l: Nat) -> Ext2ExtHit:
  Ext2ExtW.lookup.go(es, l, None{})

# whether extent e (written, shorter than the longest) ends just before
# logical block l at physical block p
def Ext2ExtW.ends_at(+e: X.Ext2Extent, +l: Nat, +p: Nat) -> Bool:
  match e:
    case X.Ext2Extent{+b, +n, +s, w}:
      Bool.and(w, Bool.and(Nat.is_lt(n, Ext2ExtW.max_len()), Bool.and(Nat.is_eq(Nat.add(b, n), l), Nat.is_eq(Nat.add(s, n), p))))

# whether extent e (written, shorter than the longest) starts just after
# logical block l at physical block p
def Ext2ExtW.starts_after(+e: X.Ext2Extent, +l: Nat, +p: Nat) -> Bool:
  match e:
    case X.Ext2Extent{+b, +n, +s, w}:
      Bool.and(w, Bool.and(Nat.is_lt(n, Ext2ExtW.max_len()), Bool.and(Nat.is_eq(b, Nat.add(l, 1n)), Nat.is_eq(s, Nat.add(p, 1n)))))

def Ext2ExtW.grow(e: X.Ext2Extent) -> X.Ext2Extent:
  match e:
    case X.Ext2Extent{b, n, s, w}:
      X.Ext2Extent{b, Nat.add(n, 1n), s, w}

def Ext2ExtW.len_of(e: X.Ext2Extent) -> Nat:
  match e:
    case X.Ext2Extent{b, n, s, w}:
      n

def Ext2ExtW.join.pick(both: Bool, +prev: X.Ext2Extent, +x: X.Ext2Extent, t: List<&2, X.Ext2Extent>) -> List<&2, X.Ext2Extent>:
  match both:
    case True{}:
      match prev:
        case X.Ext2Extent{b, n, s, w}:
          Con{X.Ext2Extent{b, Nat.add(Nat.add(n, 1n), Ext2ExtW.len_of(x)), s, w}, t}
    case False{}:
      Con{Ext2ExtW.grow(prev), Con{x, t}}

# prev (grown to take the new block) joined with next when it continues it
def Ext2ExtW.join(+prev: X.Ext2Extent, next: List<&2, X.Ext2Extent>, +l: Nat, +p: Nat) -> List<&2, X.Ext2Extent>:
  match next:
    case Con{+x, t}:
      Ext2ExtW.join.pick(Bool.and(Ext2ExtW.starts_after(x, l, p), Nat.is_le(Nat.add(Nat.add(Ext2ExtW.len_of(prev), 1n), Ext2ExtW.len_of(x)), Ext2ExtW.max_len())), prev, x, t)
    case Nil{}:
      [Ext2ExtW.grow(prev)]

def Ext2ExtW.place.pick(cont: Bool, +x: X.Ext2Extent, t: List<&2, X.Ext2Extent>, +l: Nat, +p: Nat) -> List<&2, X.Ext2Extent>:
  match cont:
    case True{}:
      Con{X.Ext2Extent{l, Nat.add(Ext2ExtW.len_of(x), 1n), p, True{}}, t}
    case False{}:
      Con{X.Ext2Extent{l, 1n, p, True{}}, Con{x, t}}

# the new block placed before rest: joined to next if it starts just after
def Ext2ExtW.place(rest: List<&2, X.Ext2Extent>, +l: Nat, +p: Nat) -> List<&2, X.Ext2Extent>:
  match rest:
    case Con{+x, t}:
      Ext2ExtW.place.pick(Ext2ExtW.starts_after(x, l, p), x, t, l, p)
    case Nil{}:
      [X.Ext2Extent{l, 1n, p, True{}}]

def Ext2ExtW.finish.pick(cont: Bool, acc: List<&2, X.Ext2Extent>, rest: List<&2, X.Ext2Extent>, +l: Nat, +p: Nat) -> List<&2, X.Ext2Extent>:
  match cont acc:
    case True{} Con{+prev, at}:
      List.reverse.go(&2, X.Ext2Extent, at, Ext2ExtW.join(prev, rest, l, p))
    case _ _:
      List.reverse.go(&2, X.Ext2Extent, acc, Ext2ExtW.place(rest, l, p))

def Ext2ExtW.last_ends_at(acc: List<&2, X.Ext2Extent>, +l: Nat, +p: Nat) -> Bool:
  match acc:
    case Con{+e, t}:
      Ext2ExtW.ends_at(e, l, p)
    case Nil{}:
      False{}

def Ext2ExtW.after(es: List<&2, X.Ext2Extent>, +l: Nat) -> Bool:
  match es:
    case Con{X.Ext2Extent{b, n, s, w}, t}:
      Nat.is_lt(l, b)
    case Nil{}:
      True{}

def Ext2ExtW.insert.go(es: List<&2, X.Ext2Extent>, past: Bool, +l: Nat, +p: Nat, +acc: List<&2, X.Ext2Extent>) -> List<&2, X.Ext2Extent>:
  match es past:
    case Con{e, +t} False{}:
      Ext2ExtW.insert.go(t, Ext2ExtW.after(t, l), l, p, Con{e, acc})
    case _ _:
      Ext2ExtW.finish.pick(Ext2ExtW.last_ends_at(acc, l, p), acc, es, l, p)

# logical block l (a hole) mapped to physical block p, in order, merged into
# the extents it continues
def Ext2ExtW.insert(+es: List<&2, X.Ext2Extent>, +l: Nat, +p: Nat) -> List<&2, X.Ext2Extent>:
  Ext2ExtW.insert.go(es, Ext2ExtW.after(es, l), l, p, Nil{})

# Cutting the list at a logical block

type Ext2ExtCut is Data:
  Ext2ExtCut{extents: List<&2, X.Ext2Extent>, freed: List<&2, Nat>}

def Ext2ExtW.cut.one.pick(gone: Bool, part: Bool, +b: Nat, +n: Nat, +s: Nat, w: Bool, +keep: Nat, acc: List<&2, X.Ext2Extent>, freed: List<&2, Nat>) -> Ext2ExtCut:
  match gone part:
    case True{} _:
      Ext2ExtCut{acc, List.reverse.go(&2, Nat, M.Ext2Bitmap.range(s, Nat.add(s, n)), freed)}
    case False{} True{}:
      +k = Nat.sub(keep, b)
      Ext2ExtCut{Con{X.Ext2Extent{b, k, s, w}, acc}, List.reverse.go(&2, Nat, M.Ext2Bitmap.range(Nat.add(s, k), Nat.add(s, n)), freed)}
    case False{} False{}:
      Ext2ExtCut{Con{X.Ext2Extent{b, n, s, w}, acc}, freed}

def Ext2ExtW.cut.one(e: X.Ext2Extent, +keep: Nat, acc: List<&2, X.Ext2Extent>, freed: List<&2, Nat>) -> Ext2ExtCut:
  match e:
    case X.Ext2Extent{+b, +n, +s, w}:
      Ext2ExtW.cut.one.pick(Nat.is_le(keep, b), Nat.is_lt(keep, Nat.add(b, n)), b, n, s, w, keep, acc, freed)

def Ext2ExtW.cut.go(es: List<&2, X.Ext2Extent>, +keep: Nat, c: Ext2ExtCut) -> Ext2ExtCut:
  match es c:
    case Nil{} Ext2ExtCut{acc, freed}:
      Ext2ExtCut{List.reverse(&2, X.Ext2Extent, acc), freed}
    case Con{e, t} Ext2ExtCut{acc, freed}:
      Ext2ExtW.cut.go(t, keep, Ext2ExtW.cut.one(e, keep, acc, freed))

# the extents cut back to logical blocks below keep, and the physical blocks
# that frees
def Ext2ExtW.cut(es: List<&2, X.Ext2Extent>, +keep: Nat) -> Ext2ExtCut:
  Ext2ExtW.cut.go(es, keep, Ext2ExtCut{Nil{}, Nil{}})

# Encoding

def Ext2ExtW.header(n: Nat, max: Nat, depth: Nat) -> B.Octets:
  B.Octets.concat([B.Octets.le16(Ext2ExtW.magic()), B.Octets.le16(U32.from_nat(n)), B.Octets.le16(U32.from_nat(max)), B.Octets.le16(U32.from_nat(depth)), B.Octets.le32(0)])

def Ext2ExtW.raw_len(w: Bool, +n: Nat) -> Nat:
  match w:
    case True{}:
      n
    case False{}:
      Nat.add(n, 32768n)

def Ext2ExtW.enc(e: X.Ext2Extent) -> B.Octets:
  match e:
    case X.Ext2Extent{b, +n, +s, w}:
      B.Octets.concat([B.Octets.le32(U32.from_nat(b)), B.Octets.le16(U32.from_nat(Ext2ExtW.raw_len(w, n))), B.Octets.le16(U32.and(65535, P.Ext2Patch.hi32(s))), B.Octets.le32(P.Ext2Patch.lo32(s))])

def Ext2ExtW.enc_all(es: List<&2, X.Ext2Extent>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match es:
    case Nil{}:
      List.reverse(&2, B.Octets, acc)
    case Con{e, t}:
      Ext2ExtW.enc_all(t, Con{Ext2ExtW.enc(e), acc})

def Ext2ExtW.enc_index(first: Nat, +leaf: Nat) -> B.Octets:
  B.Octets.concat([B.Octets.le32(U32.from_nat(first)), B.Octets.le32(P.Ext2Patch.lo32(leaf)), B.Octets.le16(U32.and(65535, P.Ext2Patch.hi32(leaf))), B.Octets.le16(0)])

# a node of the given max entries holding es (12 + 12 * max bytes)
def Ext2ExtW.node(+es: List<&2, X.Ext2Extent>, +max: Nat, depth: Nat) -> B.Octets:
  +n = List.length(&2, X.Ext2Extent, es)
  B.Octets.append(Ext2ExtW.header(n, max, depth), B.Octets.append(B.Octets.concat(Ext2ExtW.enc_all(es, Nil{})), B.Octets.zeros(Nat.mul(12n, Nat.sub(max, n)))))

# an empty tree's root (a new file's i_block)
def Ext2ExtW.empty_root() -> B.Octets:
  Ext2ExtW.node(Nil{}, 4n, 0n)

# Storing a tree back: depth 0 when four extents or fewer remain, else depth
# 1 over leaves of at most leaf_max extents each

# a stored tree: its root (i_block), the leaf blocks allocated for it, and
# the leaf blocks it no longer uses (for the caller to free)
type Ext2ExtStore is Data:
  Ext2ExtStore{iblock: B.Octets, added: List<&2, Nat>, freed: List<&2, Nat>}

def Ext2ExtW.push(cur: List<&2, X.Ext2Extent>, acc: List<&2, List<&2, X.Ext2Extent>>) -> List<&2, List<&2, X.Ext2Extent>>:
  match cur:
    case Nil{}:
      acc
    case Con{h, t}:
      Con{List.reverse(&2, X.Ext2Extent, Con{h, t}), acc}

def Ext2ExtW.chunks.go(es: List<&2, X.Ext2Extent>, k: Nat, +m: Nat, cur: List<&2, X.Ext2Extent>, acc: List<&2, List<&2, X.Ext2Extent>>) -> List<&2, List<&2, X.Ext2Extent>>:
  match es k:
    case Nil{} _:
      List.reverse(&2, List<&2, X.Ext2Extent>, Ext2ExtW.push(cur, acc))
    case Con{e, t} 0n:
      Ext2ExtW.chunks.go(t, Nat.sub(m, 1n), m, [e], Ext2ExtW.push(cur, acc))
    case Con{e, t} 1n+j:
      Ext2ExtW.chunks.go(t, j, m, Con{e, cur}, acc)

# es cut into runs of m
def Ext2ExtW.chunks(es: List<&2, X.Ext2Extent>, +m: Nat) -> List<&2, List<&2, X.Ext2Extent>>:
  Ext2ExtW.chunks.go(es, m, m, Nil{}, Nil{})

def Ext2ExtW.first_block(es: List<&2, X.Ext2Extent>) -> Nat:
  match es:
    case Con{X.Ext2Extent{b, n, s, w}, t}:
      b
    case Nil{}:
      0n

def Ext2ExtW.csum.pick(on: Bool, +fs: S.Ext2Fs, +ino: Nat, +gen: U32, +node: B.Octets, +m: Nat) -> B.Octets:
  match on:
    case True{}:
      B.Octets.le32(K.Ext2Csum.extent_block(K.Ext2Csum.inode_seed(S.Ext2Fs.seed(fs), U32.from_nat(ino), gen), node, m))
    case False{}:
      B.Octets.zeros(4n)

# a leaf block holding es (its checksum after max entries, metadata_csum)
def Ext2ExtW.leaf_block(+fs: S.Ext2Fs, +ino: Nat, +gen: U32, +es: List<&2, X.Ext2Extent>) -> B.Octets:
  +m = Ext2ExtW.leaf_max(fs)
  +node = Ext2ExtW.node(es, m, 0n)
  B.Octets.append(node, B.Octets.append(Ext2ExtW.csum.pick(T.Ext2Meta.has_meta(fs), fs, ino, gen, node, m), B.Octets.zeros(Nat.sub(S.Ext2Fs.block_size(fs), Nat.add(16n, Nat.mul(12n, m))))))

def Ext2ExtW.index_all(cs: List<&2, List<&2, X.Ext2Extent>>, ls: List<&2, Nat>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match cs ls:
    case Con{c, ct} Con{l, lt}:
      Ext2ExtW.index_all(ct, lt, Con{Ext2ExtW.enc_index(Ext2ExtW.first_block(c), l), acc})
    case _ _:
      List.reverse(&2, B.Octets, acc)

# a depth-1 root over the leaves ls holding the runs cs
def Ext2ExtW.index_root(+cs: List<&2, List<&2, X.Ext2Extent>>, +ls: List<&2, Nat>) -> B.Octets:
  +k = List.length(&2, Nat, ls)
  B.Octets.append(Ext2ExtW.header(k, 4n, 1n), B.Octets.append(B.Octets.concat(Ext2ExtW.index_all(cs, ls, Nil{})), B.Octets.zeros(Nat.mul(12n, Nat.sub(4n, k)))))

def Ext2ExtW.write_leaves(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, cs: List<&2, List<&2, X.Ext2Extent>>, ls: List<&2, Nat>, r: Result<&2, &2, E.Ext2Error, Dv>, +fs: S.Ext2Fs, +ino: Nat, +gen: U32) -> Result<&2, &2, E.Ext2Error, Dv>:
  match cs ls r:
    case _ _ Fail{e}:
      Fail{e}
    case Con{c, ct} Con{+l, lt} Done{+d}:
      Ext2ExtW.write_leaves(~Dv, ~block_size, ~read_block, ~write_block, ct, lt, T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, l, Ext2ExtW.leaf_block(fs, ino, gen, c)), fs, ino, gen)
    case _ _ Done{d}:
      Done{d}

def Ext2ExtW.store.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, List<&2, Nat>>, +fs: S.Ext2Fs, +ino: Nat, +gen: U32, +cs: List<&2, List<&2, X.Ext2Extent>>, +reuse: List<&2, Nat>, spare: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2ExtStore>>:
  match out:
    case T.Ext2Out{d, +fresh}:
      +ls = List.append(&2, Nat, reuse, fresh)
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2ExtStore>>:
        d2 : Dv <- Ext2ExtW.write_leaves(~Dv, ~block_size, ~read_block, ~write_block, cs, ls, Done{d}, fs, ino, gen)
        return T.Ext2Out{d2, Ext2ExtStore{Ext2ExtW.index_root(cs, ls), fresh, spare}}

def Ext2ExtW.store.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, small: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +gen: U32, +old: List<&2, Nat>, +es: List<&2, X.Ext2Extent>, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2ExtStore>>:
  match small:
    case True{}:
      Done{T.Ext2Out{d, Ext2ExtStore{Ext2ExtW.node(es, 4n, 0n), Nil{}, old}}}
    case False{}:
      +cs = Ext2ExtW.chunks(es, Ext2ExtW.leaf_max(fs))
      +k = List.length(&2, List<&2, X.Ext2Extent>, cs)
      +reuse = List.take(&2, Nat, old, k)
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2ExtStore>>:
        S.Ext2.require(Nat.is_le(k, 4n), E.Ext2ExtentFull{ino})
        out : T.Ext2Out<Dv, List<&2, Nat>> <- A.Ext2Alloc.blocks(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, goal, Nat.sub(k, List.length(&2, Nat, reuse)))
        Ext2ExtW.store.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, ino, gen, cs, reuse, List.drop(&2, Nat, old, k))

# the extents es stored as the tree of inode ino (generation gen), whose
# leaf blocks were old (new leaves are placed from goal)
def Ext2ExtW.store(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +gen: U32, +old: List<&2, Nat>, +es: List<&2, X.Ext2Extent>, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2ExtStore>>:
  Ext2ExtW.store.go(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_le(List.length(&2, X.Ext2Extent, es), 4n), d, fs, wo, ino, gen, old, es, goal)
