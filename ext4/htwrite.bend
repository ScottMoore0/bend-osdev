# bend-osdev-ext4: the htree writer: a hashed directory's blocks from its
# entries (the ext4 disk-layout documentation, "Hash Tree Directories").
#
# The writer hashes every name (the parameters' hash version, signedness
# and seed), sorts the entries by hash (a stable insertion sort), and fills
# leaves in that order: a leaf takes entries while they fit, and ends only
# between two different hashes, so equal hashes always share a leaf and no
# index entry needs the collision bit. Each leaf's index entry is the hash
# of its first entry (the first leaf's is 0). The index is the root's when
# the leaves fit (dx_root limit), else nodes of leaves under the root, and
# so on, up to the parameters' levels. The blocks come out in logical
# order: the root (block 0), the leaves (1 to L), then the nodes.
#
# Ext4Htree.plan is the leaves as the model (htree.bend) sees them, and
# LAWS.bend proves that every plan is ordered, the class on which the
# index lookup finds what a linear scan finds.
import Base
import ../bytes/bytes.bend as B
import ../ext2/dir.bend as DR
import ../ext2/csum.bend as K
import ../ext2/super.bend as XS
import ./error.bend as E
import ./super.bend as S
import ./hash.bend as H
import ./dx.bend as X
import ./htree.bend as T

# what the writer needs to know of the directory and its filesystem:
#   block_size, version (the hash version the root records: 0 to 2),
#   signed (whether names hash as signed chars), seed (s_hash_seed),
#   csum (Some{inode seed} with metadata_csum: leaf tails and dx_tails),
#   filetype (the filetype feature: entries keep their file type),
#   ino and parent (the inode numbers of "." and ".."),
#   levels (the most index levels, the root included),
#   pad_to (the fewest blocks to produce: empty leaves are added)
type Ext4HtreeParams is Data:
  Ext4HtreeParams{block_size: Nat, version: U32, signed: Bool, seed: List<&2, U32>, csum: Maybe<&2, U32>, filetype: Bool, ino: U32, parent: U32, levels: Nat, pad_to: Nat}

# half MD4, signed chars, no seed, no checksums, the filetype layout, two
# index levels
def Ext4HtreeParams.default(bs: Nat, ino: U32, parent: U32) -> Ext4HtreeParams:
  Ext4HtreeParams{bs, 1, True{}, [0, 0, 0, 0], None{}, True{}, ino, parent, 2n, 0n}

def Ext4HtreeParams.csum.pick(meta: Bool, +fs: S.Ext4Fs, +ino: U32, gen: U32) -> Maybe<&2, U32>:
  match meta:
    case True{}:
      Some{K.Ext2Csum.inode_seed(S.Ext4Fs.seed(fs), ino, gen)}
    case False{}:
      None{}

# the parameters a filesystem gives directory ino (generation gen, parent
# directory parent): its default hash version, signedness, seed, checksums,
# file types and index depth
def Ext4HtreeParams.of_fs(+fs: S.Ext4Fs, +ino: U32, gen: U32, parent: U32) -> Ext4HtreeParams:
  +sb = XS.Ext2Fs.sb(S.Ext4Fs.ext2(fs))
  Ext4HtreeParams{S.Ext4Fs.block_size(fs), S.Ext4Super.def_hash_version(S.Ext4Fs.super(fs)), S.Ext4Fs.hash_signed(fs), S.Ext4Super.hash_seed(S.Ext4Fs.super(fs)), Ext4HtreeParams.csum.pick(XS.Ext2Super.has_ro_compat(sb, XS.Ext2Super.ro_compat_metadata_csum()), fs, ino, gen), XS.Ext2Super.has_incompat(sb, XS.Ext2Super.incompat_filetype()), ino, parent, T.Ext4Htree.max_levels(fs), 0n}

def Ext4HtreeParams.with_pad(p: Ext4HtreeParams, n: Nat) -> Ext4HtreeParams:
  match p:
    case Ext4HtreeParams{bs, v, sg, sd, c, ft, i, pa, l, x}:
      Ext4HtreeParams{bs, v, sg, sd, c, ft, i, pa, l, n}

def Ext4HtreeParams.with_version(p: Ext4HtreeParams, v: U32) -> Ext4HtreeParams:
  match p:
    case Ext4HtreeParams{bs, x, sg, sd, c, ft, i, pa, l, n}:
      Ext4HtreeParams{bs, v, sg, sd, c, ft, i, pa, l, n}

# Sorting by hash: a stable insertion sort

def Ext4Htree.lt_head(xs: List<&2, T.Ext4HtEnt>, +h: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Nat.is_lt(h, T.Ext4HtEnt.hash(x))

def Ext4Htree.insert.go(xs: List<&2, T.Ext4HtEnt>, lt: Bool, e: T.Ext4HtEnt, +h: Nat, acc: List<&2, T.Ext4HtEnt>) -> List<&2, T.Ext4HtEnt>:
  match xs lt:
    case Nil{} _:
      List.reverse.go(&2, T.Ext4HtEnt, acc, Con{e, Nil{}})
    case Con{x, t} True{}:
      List.reverse.go(&2, T.Ext4HtEnt, acc, Con{e, Con{x, t}})
    case Con{x, +t} False{}:
      Ext4Htree.insert.go(t, Ext4Htree.lt_head(t, h), e, h, Con{x, acc})

# e placed in the sorted list xs, after every entry of its hash or lower
def Ext4Htree.insert(+e: T.Ext4HtEnt, +xs: List<&2, T.Ext4HtEnt>) -> List<&2, T.Ext4HtEnt>:
  +h = T.Ext4HtEnt.hash(e)
  Ext4Htree.insert.go(xs, Ext4Htree.lt_head(xs, h), e, h, Nil{})

def Ext4Htree.sort.go(xs: List<&2, T.Ext4HtEnt>, acc: List<&2, T.Ext4HtEnt>) -> List<&2, T.Ext4HtEnt>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      Ext4Htree.sort.go(t, Ext4Htree.insert(x, acc))

# the entries sorted by hash, entries of equal hash in their order
def Ext4Htree.sort(xs: List<&2, T.Ext4HtEnt>) -> List<&2, T.Ext4HtEnt>:
  Ext4Htree.sort.go(xs, Nil{})

# Filling leaves

# the bytes an entry takes at least in a leaf
def Ext4Htree.size(+e: T.Ext4HtEnt) -> Nat:
  DR.Ext2Dirent.min_rec_len(B.Octets.len(T.Ext4HtEnt.name(e)))

# whether the next entry starts a new leaf: the open leaf has entries, the
# entry does not fit, and its hash is above the last one's
def Ext4Htree.split(xs: List<&2, T.Ext4HtEnt>, +cap: Nat, +used: Nat, +prev: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+e, t}:
      Bool.and(Nat.is_lt(0n, used), Bool.and(Nat.is_lt(cap, Nat.add(used, Ext4Htree.size(e))), Nat.is_lt(prev, T.Ext4HtEnt.hash(e))))

# the leaves of the sorted entries xs: cur is the open leaf's entries (last
# first), used their bytes, lo its index hash, prev the last hash seen, acc
# the leaves closed (last first)
def Ext4Htree.chunk(xs: List<&2, T.Ext4HtEnt>, sp: Bool, +cap: Nat, cur: List<&2, T.Ext4HtEnt>, +used: Nat, +lo: Nat, +prev: Nat, acc: List<&2, T.Ext4HtLeaf>) -> List<&2, T.Ext4HtLeaf>:
  match xs sp:
    case Nil{} _:
      List.reverse(&2, T.Ext4HtLeaf, Con{T.Ext4HtLeaf{lo, List.reverse(&2, T.Ext4HtEnt, cur)}, acc})
    case Con{+e, +t} True{}:
      +h = T.Ext4HtEnt.hash(e)
      +sz = Ext4Htree.size(e)
      Ext4Htree.chunk(t, Ext4Htree.split(t, cap, sz, h), cap, Con{e, Nil{}}, sz, h, h, Con{T.Ext4HtLeaf{lo, List.reverse(&2, T.Ext4HtEnt, cur)}, acc})
    case Con{+e, +t} False{}:
      +h = T.Ext4HtEnt.hash(e)
      +u = Nat.add(used, Ext4Htree.size(e))
      Ext4Htree.chunk(t, Ext4Htree.split(t, cap, u, h), cap, Con{e, cur}, u, lo, h, acc)

# the leaves of a directory with entries es, each holding cap bytes of
# entries: the model of what the writer writes
def Ext4Htree.plan(es: List<&2, T.Ext4HtEnt>, +cap: Nat) -> List<&2, T.Ext4HtLeaf>:
  +xs = Ext4Htree.sort(es)
  Ext4Htree.chunk(xs, Ext4Htree.split(xs, cap, 0n, 0n), cap, Nil{}, 0n, 0n, 0n, Nil{})

# Hashing the entries

def Ext4Htree.hashed(es: List<&2, DR.Ext2Dirent>, +v: U32, +seed: List<&2, U32>, acc: List<&2, T.Ext4HtEnt>) -> Result<&2, &2, E.Ext4Error, List<&2, T.Ext4HtEnt>>:
  match es:
    case Nil{}:
      Done{List.reverse(&2, T.Ext4HtEnt, acc)}
    case Con{+e, t}:
      do Result<&2, &2, E.Ext4Error, List<&2, T.Ext4HtEnt>>:
        h : H.Ext4DxHash <- H.Ext4Hash.name(v, seed, DR.Ext2Dirent.name(e))
        Ext4Htree.hashed(t, v, seed, Con{T.Ext4HtEnt{U32.to_nat(H.Ext4DxHash.major(h)), e}, acc})

# Leaf blocks

def Ext4Htree.ft(filetype: Bool, +t: U32) -> U32:
  match filetype:
    case True{}:
      t
    case False{}:
      0

def Ext4Htree.rec.pick(last: Bool, +rest: Nat, +sz: Nat) -> Nat:
  match last:
    case True{}:
      rest
    case False{}:
      sz

# a leaf's entries as stored: each at its shortest rec_len, the last one
# reaching the end of the cap bytes; ft: keep file types
def Ext4Htree.dirents(es: List<&2, T.Ext4HtEnt>, +cap: Nat, +ft: Bool, +used: Nat, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match es:
    case Nil{}:
      List.reverse(&2, B.Octets, acc)
    case Con{+x, +t}:
      +e = T.Ext4HtEnt.entry(x)
      +nm = DR.Ext2Dirent.name(e)
      +sz = Ext4Htree.size(x)
      +rec = Ext4Htree.rec.pick(List.is_empty(&2, T.Ext4HtEnt, t), Nat.sub(cap, used), sz)
      Ext4Htree.dirents(t, cap, ft, Nat.add(used, sz), Con{DR.Ext2Dirent.encode(DR.Ext2Dirent{DR.Ext2Dirent.inode(e), U32.from_nat(rec), U32.from_nat(B.Octets.len(nm)), Ext4Htree.ft(ft, DR.Ext2Dirent.file_type(e)), nm}), acc})

# the checksum tail of a leaf (metadata_csum): an entry of inode 0, rec_len
# 12, name_len 0, file type 0xDE, holding crc32c from the inode's seed over
# the block before it
def Ext4Htree.tail(check: Maybe<&2, U32>, +body: B.Octets) -> B.Octets:
  match check:
    case None{}:
      body
    case Some{s}:
      B.Octets.append(body, B.Octets.append(B.Octets.zeros(4n), B.Octets.append(B.Octets.le16(12), B.Octets.append(B.Octets.of_list([0, 222]), B.Octets.le32(K.Ext2Csum.crc32c(s, body))))))

def Ext4Htree.cap.pick(tail: Bool, +bs: Nat) -> Nat:
  match tail:
    case True{}:
      Nat.sub(bs, 12n)
    case False{}:
      bs

# the bytes of a leaf block that hold entries
def Ext4Htree.cap(+bs: Nat, +check: Maybe<&2, U32>) -> Nat:
  Ext4Htree.cap.pick(X.Ext4Dx.is_some(check), bs)

def Ext4Htree.leaf.body(es: List<&2, T.Ext4HtEnt>, +cap: Nat, +ft: Bool) -> B.Octets:
  match es:
    case Nil{}:
      DR.Ext2Dirent.encode(DR.Ext2Dirent{0, U32.from_nat(cap), 0, 0, B.Octets.empty()})
    case Con{x, t}:
      B.Octets.concat(Ext4Htree.dirents(Con{x, t}, cap, ft, 0n, Nil{}))

def Ext4Htree.leaf_block(+bs: Nat, +check: Maybe<&2, U32>, +ft: Bool, l: T.Ext4HtLeaf) -> B.Octets:
  Ext4Htree.tail(check, Ext4Htree.leaf.body(T.Ext4HtLeaf.ents(l), Ext4Htree.cap(bs, check), ft))

def Ext4Htree.leaf_blocks(ls: List<&2, T.Ext4HtLeaf>, +bs: Nat, +check: Maybe<&2, U32>, +ft: Bool, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match ls:
    case Nil{}:
      List.reverse(&2, B.Octets, acc)
    case Con{l, t}:
      Ext4Htree.leaf_blocks(t, bs, check, ft, Con{Ext4Htree.leaf_block(bs, check, ft, l), acc})

def Ext4Htree.bytes(es: List<&2, T.Ext4HtEnt>, acc: Nat) -> Nat:
  match es:
    case Nil{}:
      acc
    case Con{+x, t}:
      Ext4Htree.bytes(t, Nat.add(acc, Ext4Htree.size(x)))

# whether every leaf's entries fit in cap bytes (only a run of equal hashes
# longer than a block does not)
def Ext4Htree.fits(ls: List<&2, T.Ext4HtLeaf>, +cap: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, t}:
      Bool.and(Nat.is_le(Ext4Htree.bytes(T.Ext4HtLeaf.ents(l), 0n), cap), Ext4Htree.fits(t, cap))

# The index

def Ext4Htree.items(ls: List<&2, T.Ext4HtLeaf>, +k: Nat, acc: List<&2, X.Ext4DxEntry>) -> List<&2, X.Ext4DxEntry>:
  match ls:
    case Nil{}:
      List.reverse(&2, X.Ext4DxEntry, acc)
    case Con{l, t}:
      Ext4Htree.items(t, Nat.add(k, 1n), Con{X.Ext4DxEntry{U32.from_nat(T.Ext4HtLeaf.lo(l)), U32.from_nat(k)}, acc})

def Ext4Htree.first_hash(es: List<&2, X.Ext4DxEntry>) -> U32:
  match es:
    case Nil{}:
      0
    case Con{e, t}:
      X.Ext4DxEntry.hash(e)

# the first n entries and the rest
def Ext4Htree.take(n: Nat, xs: List<&2, X.Ext4DxEntry>, acc: List<&2, X.Ext4DxEntry>) -> List<&2, X.Ext4DxEntry> & List<&2, X.Ext4DxEntry>:
  match n xs:
    case 0n _:
      (List.reverse(&2, X.Ext4DxEntry, acc), xs)
    case _ Nil{}:
      (List.reverse(&2, X.Ext4DxEntry, acc), Nil{})
    case 1n+p Con{h, t}:
      Ext4Htree.take(p, t, Con{h, acc})

type Ext4HtLevel is Data:
  Ext4HtLevel{items: List<&2, X.Ext4DxEntry>, nodes: List<&2, B.Octets>}

# the items grouped into nodes of nlimit entries, the nodes at logical
# blocks k on: one item for each node (its first entry's hash), and the
# node blocks
def Ext4Htree.group(fuel: Nat, r: List<&2, X.Ext4DxEntry> & List<&2, X.Ext4DxEntry>, +nlimit: Nat, +k: Nat, +bs: Nat, +check: Maybe<&2, U32>, items: List<&2, X.Ext4DxEntry>, nodes: List<&2, B.Octets>) -> Ext4HtLevel:
  match fuel:
    case 0n:
      Ext4HtLevel{List.reverse(&2, X.Ext4DxEntry, items), List.reverse(&2, B.Octets, nodes)}
    case 1n+f:
      (g, rest) = r
      match g:
        case Nil{}:
          Ext4HtLevel{List.reverse(&2, X.Ext4DxEntry, items), List.reverse(&2, B.Octets, nodes)}
        case Con{+e, +t}:
          Ext4Htree.group(f, Ext4Htree.take(nlimit, rest, Nil{}), nlimit, Nat.add(k, 1n), bs, check, Con{X.Ext4DxEntry{X.Ext4DxEntry.hash(e), U32.from_nat(k)}, items}, Con{X.Ext4DxNode.encode(bs, check, X.Ext4DxNode{U32.from_nat(nlimit), Con{e, t}}), nodes})

def Ext4HtLevel.items(l: Ext4HtLevel) -> List<&2, X.Ext4DxEntry>:
  match l:
    case Ext4HtLevel{i, n}:
      i

def Ext4HtLevel.nodes(l: Ext4HtLevel) -> List<&2, B.Octets>:
  match l:
    case Ext4HtLevel{i, n}:
      n

type Ext4HtIndex is Data:
  Ext4HtIndex{entries: List<&2, X.Ext4DxEntry>, levels: Nat, nodes: List<&2, B.Octets>}

# the root's entries for the items, a level of nodes added below the root
# while the items do not fit in it (fits: whether they do), k the next free
# block, nodes the node blocks so far; fuel bounds the levels
def Ext4Htree.index(fuel: Nat, fits: Bool, +items: List<&2, X.Ext4DxEntry>, +rlimit: Nat, +nlimit: Nat, +k: Nat, nodes: List<&2, B.Octets>, +levels: Nat, +bs: Nat, +check: Maybe<&2, U32>) -> Result<&2, &2, E.Ext4Error, Ext4HtIndex>:
  match fuel fits:
    case _ True{}:
      Done{Ext4HtIndex{items, levels, nodes}}
    case 0n False{}:
      Fail{E.Ext4HtreeTooBig{"the index needs more levels than allowed"}}
    case 1n+f False{}:
      +n = List.length(&2, X.Ext4DxEntry, items)
      +lv = Ext4Htree.group(1n+n, Ext4Htree.take(nlimit, items, Nil{}), nlimit, k, bs, check, Nil{}, Nil{})
      +up = Ext4HtLevel.items(lv)
      +ns = Ext4HtLevel.nodes(lv)
      Ext4Htree.index(f, Nat.is_le(List.length(&2, X.Ext4DxEntry, up), rlimit), up, rlimit, nlimit, Nat.add(k, List.length(&2, B.Octets, ns)), List.append(&2, B.Octets, nodes, ns), 1n+levels, bs, check)

# Padding to a number of blocks

# the node blocks below the root that n leaves need (fit: whether n fit in
# the root)
def Ext4Htree.nodes_for(fuel: Nat, fit: Bool, +n: Nat, +rlimit: Nat, +nlimit: Nat) -> Nat:
  match fuel fit:
    case 0n _:
      0n
    case _ True{}:
      0n
    case 1n+f False{}:
      +g = Nat.div(Nat.add(n, Nat.sub(nlimit, 1n)), nlimit)
      Nat.add(g, Ext4Htree.nodes_for(f, Nat.is_le(g, rlimit), g, rlimit, nlimit))

def Ext4Htree.blocks_for(+n: Nat, +rlimit: Nat, +nlimit: Nat) -> Nat:
  Nat.add(1n+n, Ext4Htree.nodes_for(4n, Nat.is_le(n, rlimit), n, rlimit, nlimit))

# the fewest leaves, at least n, whose directory has at least want blocks
def Ext4Htree.pad_count(fuel: Nat, enough: Bool, +n: Nat, +want: Nat, +rlimit: Nat, +nlimit: Nat) -> Nat:
  match fuel enough:
    case _ True{}:
      n
    case 0n False{}:
      n
    case 1n+f False{}:
      +m = Nat.add(n, 1n)
      Ext4Htree.pad_count(f, Nat.is_le(want, Ext4Htree.blocks_for(m, rlimit, nlimit)), m, want, rlimit, nlimit)

def Ext4Htree.last_hash.ents(es: List<&2, T.Ext4HtEnt>, +h: Nat) -> Nat:
  match es:
    case Nil{}:
      h
    case Con{e, t}:
      Ext4Htree.last_hash.ents(t, T.Ext4HtEnt.hash(e))

# the hash of the last entry, or of the last leaf's index
def Ext4Htree.last_hash(ls: List<&2, T.Ext4HtLeaf>, +h: Nat) -> Nat:
  match ls:
    case Nil{}:
      h
    case Con{T.Ext4HtLeaf{lo, es}, t}:
      Ext4Htree.last_hash(t, Ext4Htree.last_hash.ents(es, lo))

# the leaves with empty leaves added, up to count, their index hash above
# every entry's
def Ext4Htree.pad(+ls: List<&2, T.Ext4HtLeaf>, +count: Nat) -> List<&2, T.Ext4HtLeaf>:
  +lo = Nat.add(Ext4Htree.last_hash(ls, 0n), 2n)
  List.append(&2, T.Ext4HtLeaf, ls, List.replicate(T.Ext4HtLeaf, Nat.sub(count, List.length(&2, T.Ext4HtLeaf, ls)), T.Ext4HtLeaf{lo, Nil{}}))

# Building the directory

def Ext4Htree.ft2(filetype: Bool) -> U32:
  match filetype:
    case True{}:
      2
    case False{}:
      0

def Ext4Htree.build.fin(+p: Ext4HtreeParams, ls: List<&2, T.Ext4HtLeaf>, idx: Ext4HtIndex, +rlimit: Nat) -> List<&2, B.Octets>:
  match p idx:
    case Ext4HtreeParams{+bs, v, sg, sd, +c, +ft, i, pa, l, x} Ext4HtIndex{es, lv, nodes}:
      Con{X.Ext4DxRoot.encode(bs, c, Ext4Htree.ft2(ft), X.Ext4DxRoot{i, pa, v, U32.from_nat(lv), U32.from_nat(rlimit), es}), List.append(&2, B.Octets, Ext4Htree.leaf_blocks(ls, bs, c, ft, Nil{}), nodes)}

def Ext4Htree.build.go(+p: Ext4HtreeParams, +ents: List<&2, T.Ext4HtEnt>) -> Result<&2, &2, E.Ext4Error, List<&2, B.Octets>>:
  match p:
    case Ext4HtreeParams{+bs, v, sg, sd, +c, ft, i, pa, +l, +x}:
      +cap = Ext4Htree.cap(bs, c)
      +ls0 = Ext4Htree.plan(ents, cap)
      +tail = X.Ext4Dx.is_some(c)
      +rlimit = X.Ext4Dx.limit(bs, 32n, tail)
      +nlimit = X.Ext4Dx.limit(bs, 8n, tail)
      +n0 = List.length(&2, T.Ext4HtLeaf, ls0)
      +ls = Ext4Htree.pad(ls0, Ext4Htree.pad_count(x, Nat.is_le(x, Ext4Htree.blocks_for(n0, rlimit, nlimit)), n0, x, rlimit, nlimit))
      +n = List.length(&2, T.Ext4HtLeaf, ls)
      do Result<&2, &2, E.Ext4Error, List<&2, B.Octets>>:
        E.Ext4.require(Ext4Htree.fits(ls0, cap), E.Ext4HtreeTooBig{"a run of equal hashes is longer than a block"})
        idx : Ext4HtIndex <- Ext4Htree.index(Nat.sub(l, 1n), Nat.is_le(n, rlimit), Ext4Htree.items(ls, 1n, Nil{}), rlimit, nlimit, 1n+n, Nil{}, 0n, bs, c)
        return Ext4Htree.build.fin(p, ls, idx, rlimit)

# the blocks of a hashed directory holding the entries es (their names,
# inode numbers and file types; rec_len and name_len are recomputed), in
# logical order: the root, the leaves, the index nodes. Ext4HtreeTooBig
# when equal hashes overflow a leaf or the index needs more levels than
# allowed; Ext4BadHashVersion for a hash version other than 0 to 2.
def Ext4Htree.build(+p: Ext4HtreeParams, +es: List<&2, DR.Ext2Dirent>) -> Result<&2, &2, E.Ext4Error, List<&2, B.Octets>>:
  match p:
    case Ext4HtreeParams{bs, +v, +sg, +sd, c, ft, i, pa, l, x}:
      do Result<&2, &2, E.Ext4Error, List<&2, B.Octets>>:
        E.Ext4.require(U32.is_le(v, 2), E.Ext4BadHashVersion{v})
        ents : List<&2, T.Ext4HtEnt> <- Ext4Htree.hashed(es, H.Ext4Hash.version(v, sg), sd, Nil{})
        Ext4Htree.build.go(p, ents)
