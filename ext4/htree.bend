# bend-osdev-ext4: hashed (htree) directories: the lookup, its model, and
# the writer (the ext4 disk-layout documentation, "Hash Tree Directories").
#
# A lookup hashes the name, walks the index from the root down, at each
# level taking the last entry whose hash is at most the name's (entry 0
# counts as hash 0), reads the one leaf block that leads to, and searches
# it. Only if the name is not there and the next index entry's hash is the
# name's hash with bit 0 set (a run of equal hashes continued into the next
# leaf) does it read the next leaf too.
#
# The model: a directory's leaves in index order, each with the hash its
# index entry starts at (lo) and its entries with their hashes. The model's
# lookup uses the same choice of entry (Ext4Htree.pick), the same
# continuation test (Ext4Htree.continues) and the same search of a leaf
# (Ext4Htree.find) as the device lookup; LAWS.bend proves that on every
# ordered model the lookup finds what a linear scan of all leaves finds.
#
# The writer builds a directory's blocks from its entries: it hashes the
# names, sorts them by hash, fills leaves in that order (a leaf ends only
# between two different hashes, so the writer never needs a continuation),
# and builds the index above them, as many levels as the leaves need.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/csum.bend as K
import ../ext2/super.bend as XS
import ../ext2/inode.bend as N
import ../ext2/file.bend as FL
import ../ext2/dir.bend as DR
import ./error.bend as E
import ./options.bend as O
import ./super.bend as S
import ./hash.bend as H
import ./dx.bend as X

# The model

type Ext4HtEnt is Data:
  Ext4HtEnt{hash: Nat, entry: DR.Ext2Dirent}

type Ext4HtLeaf is Data:
  Ext4HtLeaf{lo: Nat, ents: List<&2, Ext4HtEnt>}

def Ext4HtEnt.hash(e: Ext4HtEnt) -> Nat:
  match e:
    case Ext4HtEnt{h, d}:
      h

def Ext4HtEnt.entry(e: Ext4HtEnt) -> DR.Ext2Dirent:
  match e:
    case Ext4HtEnt{h, d}:
      d

def Ext4HtEnt.name(e: Ext4HtEnt) -> B.Octets:
  match e:
    case Ext4HtEnt{h, d}:
      DR.Ext2Dirent.name(d)

def Ext4HtLeaf.lo(l: Ext4HtLeaf) -> Nat:
  match l:
    case Ext4HtLeaf{lo, es}:
      lo

def Ext4HtLeaf.ents(l: Ext4HtLeaf) -> List<&2, Ext4HtEnt>:
  match l:
    case Ext4HtLeaf{lo, es}:
      es

def Ext4DxEntry.lo(e: X.Ext4DxEntry) -> Nat:
  U32.to_nat(X.Ext4DxEntry.hash(e))

# Choosing an index entry: the suffix of xs from the last element whose lo
# is at most h, the first element taken whatever its lo. adv says whether
# the walk moves on past x (whether the next element's lo is at most h).

def Ext4Htree.adv(~A: Data, ~lo: A -> Nat, xs: List<&2, A>, +h: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, t}:
      Nat.is_le(lo(y), h)

def Ext4Htree.pick.go(~A: Data, ~lo: A -> Nat, t: List<&2, A>, x: A, adv: Bool, +h: Nat) -> List<&2, A>:
  match t adv:
    case Nil{} _:
      Con{x, Nil{}}
    case Con{y, u} False{}:
      Con{x, Con{y, u}}
    case Con{y, +u} True{}:
      Ext4Htree.pick.go(~A, ~lo, u, y, Ext4Htree.adv(~A, ~lo, u, h), h)

def Ext4Htree.pick(~A: Data, ~lo: A -> Nat, xs: List<&2, A>, +h: Nat) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, +t}:
      Ext4Htree.pick.go(~A, ~lo, t, x, Ext4Htree.adv(~A, ~lo, t, h), h)

# whether the next index entry, starting at lo, continues a run of entries
# whose hash is h: its hash is h with the collision bit set
def Ext4Htree.continues(+lo: Nat, +h: Nat) -> Bool:
  Nat.is_eq(lo, 1n+h)

def Ext4Htree.cont(~A: Data, ~lo: A -> Nat, xs: List<&2, A>, +h: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, t}:
      Ext4Htree.continues(lo(y), h)

# Searching a leaf: the first element named n

def Ext4Htree.hit(~A: Data, ~name_of: A -> B.Octets, xs: List<&2, A>, +n: B.Octets) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      B.Octets.is_eq(name_of(x), n)

def Ext4Htree.find.go(~A: Data, ~name_of: A -> B.Octets, xs: List<&2, A>, hit: Bool, +n: B.Octets) -> Maybe<&2, A>:
  match xs hit:
    case Nil{} _:
      None{}
    case Con{x, t} True{}:
      Some{x}
    case Con{x, +t} False{}:
      Ext4Htree.find.go(~A, ~name_of, t, Ext4Htree.hit(~A, ~name_of, t, n), n)

def Ext4Htree.find(~A: Data, ~name_of: A -> B.Octets, +xs: List<&2, A>, +n: B.Octets) -> Maybe<&2, A>:
  Ext4Htree.find.go(~A, ~name_of, xs, Ext4Htree.hit(~A, ~name_of, xs, n), n)

def Ext4Htree.find_ent(+es: List<&2, Ext4HtEnt>, +n: B.Octets) -> Maybe<&2, Ext4HtEnt>:
  Ext4Htree.find(~Ext4HtEnt, ~Ext4HtEnt.name, es, n)

# The model's lookup: pick a leaf, search it, and continue into the next
# leaves while their index entries continue the name's hash

def Ext4Htree.from(rest: List<&2, Ext4HtLeaf>, found: Maybe<&2, Ext4HtEnt>, go: Bool, +h: Nat, +n: B.Octets) -> Maybe<&2, Ext4HtEnt>:
  match rest found go:
    case _ Some{e} _:
      Some{e}
    case Nil{} None{} _:
      None{}
    case Con{l, t} None{} False{}:
      None{}
    case Con{l, +t} None{} True{}:
      Ext4Htree.from(t, Ext4Htree.find_ent(Ext4HtLeaf.ents(l), n), Ext4Htree.cont(~Ext4HtLeaf, ~Ext4HtLeaf.lo, t, h), h, n)

def Ext4Htree.lookup.at(xs: List<&2, Ext4HtLeaf>, +h: Nat, +n: B.Octets) -> Maybe<&2, Ext4HtEnt>:
  match xs:
    case Nil{}:
      None{}
    case Con{l, +t}:
      Ext4Htree.from(t, Ext4Htree.find_ent(Ext4HtLeaf.ents(l), n), Ext4Htree.cont(~Ext4HtLeaf, ~Ext4HtLeaf.lo, t, h), h, n)

# the entry named n, by the index, when n's hash is h
def Ext4Htree.lookup(leaves: List<&2, Ext4HtLeaf>, +h: Nat, +n: B.Octets) -> Maybe<&2, Ext4HtEnt>:
  Ext4Htree.lookup.at(Ext4Htree.pick(~Ext4HtLeaf, ~Ext4HtLeaf.lo, leaves, h), h, n)

def Ext4Htree.scan.go(ls: List<&2, Ext4HtLeaf>, +n: B.Octets, found: Maybe<&2, Ext4HtEnt>) -> Maybe<&2, Ext4HtEnt>:
  match ls found:
    case _ Some{e}:
      Some{e}
    case Nil{} None{}:
      None{}
    case Con{l, t} None{}:
      Ext4Htree.scan.go(t, n, Ext4Htree.find_ent(Ext4HtLeaf.ents(l), n))

# the entry named n, by a linear scan of every leaf
def Ext4Htree.scan(ls: List<&2, Ext4HtLeaf>, +n: B.Octets) -> Maybe<&2, Ext4HtEnt>:
  Ext4Htree.scan.go(ls, n, None{})

# The class the law is about

def Ext4Htree.all_lt(es: List<&2, Ext4HtEnt>, +x: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Nat.is_lt(Ext4HtEnt.hash(e), x), Ext4Htree.all_lt(t, x))

def Ext4Htree.all_ge(es: List<&2, Ext4HtEnt>, +x: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Nat.is_le(x, Ext4HtEnt.hash(e)), Ext4Htree.all_ge(t, x))

def Ext4Htree.ordered.pair(+l: Ext4HtLeaf, +m: Ext4HtLeaf) -> Bool:
  +lo = Ext4HtLeaf.lo(m)
  Bool.and(Nat.is_le(Ext4HtLeaf.lo(l), lo), Bool.and(Ext4Htree.all_lt(Ext4HtLeaf.ents(l), lo), Ext4Htree.all_ge(Ext4HtLeaf.ents(m), lo)))

def Ext4Htree.ordered.next(+l: Ext4HtLeaf, t: List<&2, Ext4HtLeaf>, rest: Bool) -> Bool:
  match t:
    case Nil{}:
      rest
    case Con{+m, u}:
      Bool.and(Ext4Htree.ordered.pair(l, m), rest)

# leaves in index order: each leaf's lo at most the next's, every entry
# below the next leaf's lo, and every entry of a leaf after the first at
# least its leaf's lo
def Ext4Htree.ordered(ls: List<&2, Ext4HtLeaf>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{+l, +t}:
      Ext4Htree.ordered.next(l, t, Ext4Htree.ordered(t))

def Ext4Htree.named(es: List<&2, Ext4HtEnt>, +n: B.Octets, +h: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, t}:
      Bool.and(Bool.or(Bool.not(B.Octets.is_eq(Ext4HtEnt.name(e), n)), Nat.is_eq(Ext4HtEnt.hash(e), h)), Ext4Htree.named(t, n, h))

# every entry named n has hash h
def Ext4Htree.consistent(ls: List<&2, Ext4HtLeaf>, +n: B.Octets, +h: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, t}:
      Bool.and(Ext4Htree.named(Ext4HtLeaf.ents(l), n, h), Ext4Htree.consistent(t, n, h))

# The lookup on a device

# the inode seed the index checksums start from, when they are checked
def Ext4Htree.check.pick(on: Bool, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Maybe<&2, U32>:
  match on:
    case True{}:
      Some{K.Ext2Csum.inode_seed(S.Ext4Fs.seed(fs), U32.from_nat(N.Ext2Inode.number_of(i)), N.Ext2Inode.generation(i))}
    case False{}:
      None{}

def Ext4Htree.check(+fs: S.Ext4Fs, +i: N.Ext2Inode) -> Maybe<&2, U32>:
  Ext4Htree.check.pick(S.Ext4Fs.verify_meta(fs), fs, i)

# whether index blocks end in a dx_tail: the filesystem has metadata_csum
def Ext4Htree.tail(+fs: S.Ext4Fs) -> Bool:
  XS.Ext2Super.has_ro_compat(XS.Ext2Fs.sb(S.Ext4Fs.ext2(fs)), XS.Ext2Super.ro_compat_metadata_csum())

def Ext4Htree.levels.pick(large: Bool) -> Nat:
  match large:
    case True{}:
      3n
    case False{}:
      2n

# the most index levels, the root included: 2, or 3 with large_dir, and no
# more than the options allow
def Ext4Htree.max_levels(+fs: S.Ext4Fs) -> Nat:
  Nat.min(Ext4Htree.levels.pick(S.Ext4Fs.has_incompat(fs, S.Ext4Super.incompat_large_dir())), O.Ext4Options.max_levels(S.Ext4Fs.opts(fs)))

# logical block k of directory i, a whole block
def Ext4Htree.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +k: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  +bs = S.Ext4Fs.block_size(fs)
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    +blk : B.Octets <- E.Ext4Error.lift(B.Octets, FL.Ext2File.read_block(~Dv, ~block_size, ~read_block, d, S.Ext4Fs.ext2(fs), i, k))
    E.Ext4.require(Nat.is_eq(B.Octets.len(blk), bs), E.Ext4BadDxNode{N.Ext2Inode.number_of(i), k, "the directory's size is not a whole number of blocks"})
    return blk

# a leaf block reached, and the path to it (at each level, the index entries
# after the one taken, innermost first)
type Ext4HtAt is Data:
  Ext4HtAt{leaf: Nat, path: List<&2, List<&2, X.Ext4DxEntry>>}

def Ext4Htree.choose(first: Bool, es: List<&2, X.Ext4DxEntry>, +h: Nat) -> List<&2, X.Ext4DxEntry>:
  match first:
    case True{}:
      es
    case False{}:
      Ext4Htree.pick(~X.Ext4DxEntry, ~Ext4DxEntry.lo, es, h)

# down the index from the chosen entries (picked: the chosen entry and the
# ones after it), n levels above the leaves: the leaf block reached, and the
# path (at each level, the entries after the one taken, innermost first).
# first: take each node's first entry (the leftmost leaf) rather than pick
def Ext4Htree.descend(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, n: Nat, picked: List<&2, X.Ext4DxEntry>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +h: Nat, +first: Bool, path: List<&2, List<&2, X.Ext4DxEntry>>) -> Result<&2, &2, E.Ext4Error, Ext4HtAt>:
  match n picked:
    case _ Nil{}:
      Fail{E.Ext4BadDxNode{N.Ext2Inode.number_of(i), 0n, "an empty index"}}
    case 0n Con{e, rest}:
      Done{Ext4HtAt{U32.to_nat(X.Ext4DxEntry.block(e)), Con{rest, path}}}
    case 1n+p Con{e, rest}:
      +k = U32.to_nat(X.Ext4DxEntry.block(e))
      do Result<&2, &2, E.Ext4Error, Ext4HtAt>:
        blk : B.Octets <- Ext4Htree.read(~Dv, ~block_size, ~read_block, d, fs, i, k)
        node : X.Ext4DxNode <- X.Ext4DxNode.parse(blk, S.Ext4Fs.block_size(fs), Ext4Htree.tail(fs), Ext4Htree.check(fs, i), N.Ext2Inode.number_of(i), k)
        Ext4Htree.descend(~Dv, ~block_size, ~read_block, p, Ext4Htree.choose(first, X.Ext4DxNode.entries(node), h), d, fs, i, h, first, Con{rest, path})

# the next index entry after the path's position: the entry, how many
# levels above the leaves it is, and the path after it
type Ext4HtNext is Data:
  Ext4HtNext{entry: X.Ext4DxEntry, up: Nat, path: List<&2, List<&2, X.Ext4DxEntry>>}

def Ext4Htree.next(path: List<&2, List<&2, X.Ext4DxEntry>>, +up: Nat) -> Maybe<&2, Ext4HtNext>:
  match path:
    case Nil{}:
      None{}
    case Con{Nil{}, outer}:
      Ext4Htree.next(outer, Nat.add(up, 1n))
    case Con{Con{e, rest}, outer}:
      Some{Ext4HtNext{e, up, Con{rest, outer}}}

# what a lookup does next
type Ext4HtStep is Data:
  Ext4HtRead{leaf: Nat, path: List<&2, List<&2, X.Ext4DxEntry>>}
  Ext4HtDone{found: Maybe<&2, DR.Ext2Dirent>}
  Ext4HtErr{e: E.Ext4Error}

def Ext4Htree.step(r: Result<&2, &2, E.Ext4Error, Ext4HtAt>) -> Ext4HtStep:
  match r:
    case Done{Ext4HtAt{k, path}}:
      Ext4HtRead{k, path}
    case Fail{e}:
      Ext4HtErr{e}

def Ext4Htree.after.cont(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, go: Bool, e: X.Ext4DxEntry, up: Nat, path: List<&2, List<&2, X.Ext4DxEntry>>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +h: Nat) -> Ext4HtStep:
  match go:
    case True{}:
      Ext4Htree.step(Ext4Htree.descend(~Dv, ~block_size, ~read_block, up, Con{e, Nil{}}, d, fs, i, h, True{}, path))
    case False{}:
      Ext4HtDone{None{}}

def Ext4Htree.after.next(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, m: Maybe<&2, Ext4HtNext>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +h: Nat) -> Ext4HtStep:
  match m:
    case None{}:
      Ext4HtDone{None{}}
    case Some{Ext4HtNext{+e, up, path}}:
      Ext4Htree.after.cont(~Dv, ~block_size, ~read_block, Ext4Htree.continues(Ext4DxEntry.lo(e), h), e, up, path, d, fs, i, h)

# after a leaf: done if the name was found there, else on to the next leaf
# if its index entry continues the hash
def Ext4Htree.after(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, found: Maybe<&2, DR.Ext2Dirent>, path: List<&2, List<&2, X.Ext4DxEntry>>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +h: Nat) -> Ext4HtStep:
  match found:
    case Some{x}:
      Ext4HtDone{Some{x}}
    case None{}:
      Ext4Htree.after.next(~Dv, ~block_size, ~read_block, Ext4Htree.next(path, 0n), d, fs, i, h)

def Ext4Htree.search(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, fuel: Nat, st: Ext4HtStep, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +h: Nat, +name: B.Octets) -> Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
  match fuel st:
    case _ Ext4HtDone{m}:
      Done{m}
    case _ Ext4HtErr{e}:
      Fail{e}
    case 0n Ext4HtRead{k, path}:
      Done{None{}}
    case 1n+f Ext4HtRead{k, path}:
      do Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
        es : List<&2, DR.Ext2Dirent> <- E.Ext4Error.lift(List<&2, DR.Ext2Dirent>, DR.Ext2Dir.block(~Dv, ~block_size, ~read_block, d, S.Ext4Fs.ext2(fs), i, k))
        Ext4Htree.search(~Dv, ~block_size, ~read_block, f, Ext4Htree.after(~Dv, ~block_size, ~read_block, Ext4Htree.find(~DR.Ext2Dirent, ~DR.Ext2Dirent.name, es, name), path, d, fs, i, h), d, fs, i, h, name)

def Ext4Htree.dot.pick(dot: Bool, dotdot: Bool, +filetype: Bool, +blk: B.Octets) -> Maybe<&2, Maybe<&2, DR.Ext2Dirent>>:
  match dot dotdot:
    case True{} _:
      Some{DR.Ext2Dirent.decode(filetype, blk)}
    case False{} True{}:
      Some{DR.Ext2Dirent.decode(filetype, B.Octets.drop(12n, blk))}
    case False{} False{}:
      None{}

def Ext4Htree.by_hash(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, special: Maybe<&2, Maybe<&2, DR.Ext2Dirent>>, +root: X.Ext4DxRoot, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +name: B.Octets) -> Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
  match special:
    case Some{m}:
      Done{m}
    case None{}:
      do Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
        hh : H.Ext4DxHash <- H.Ext4Hash.name(H.Ext4Hash.version(X.Ext4DxRoot.version(root), S.Ext4Fs.hash_signed(fs)), S.Ext4Super.hash_seed(S.Ext4Fs.super(fs)), name)
        +h : Nat = U32.to_nat(H.Ext4DxHash.major(hh))
        Ext4Htree.search(~Dv, ~block_size, ~read_block, Nat.add(FL.Ext2File.blocks_needed(S.Ext4Fs.ext2(fs), i), 1n), Ext4Htree.step(Ext4Htree.descend(~Dv, ~block_size, ~read_block, U32.to_nat(X.Ext4DxRoot.levels(root)), Ext4Htree.pick(~X.Ext4DxEntry, ~Ext4DxEntry.lo, X.Ext4DxRoot.entries(root), h), d, fs, i, h, False{}, Nil{})), d, fs, i, h, name)

# the entry named name in hashed directory i (the one a linear reading
# finds): reads the root, the index nodes on the path, and the leaf the
# hash leads to ("." and ".." are the root's own entries)
def Ext4Htree.lookup_dev(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +name: B.Octets) -> Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
  +filetype = S.Ext4Fs.has_incompat(fs, XS.Ext2Super.incompat_filetype())
  do Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
    +blk : B.Octets <- Ext4Htree.read(~Dv, ~block_size, ~read_block, d, fs, i, 0n)
    +root : X.Ext4DxRoot <- X.Ext4DxRoot.parse(blk, S.Ext4Fs.block_size(fs), Ext4Htree.tail(fs), Ext4Htree.check(fs, i), Ext4Htree.max_levels(fs), N.Ext2Inode.number_of(i))
    Ext4Htree.by_hash(~Dv, ~block_size, ~read_block, Ext4Htree.dot.pick(B.Octets.is_eq(name, B.Octets.of_string(".")), B.Octets.is_eq(name, B.Octets.of_string("..")), filetype, blk), root, d, fs, i, name)
