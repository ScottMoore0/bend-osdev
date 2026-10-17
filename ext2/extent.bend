# bend-osdev-ext2: ext4's extent trees (the ext4 disk-layout documentation,
# "Extent Tree").
#
# A node is a 12-byte header (magic 0xF30A, entries, max, depth, generation)
# and up to max 12-byte entries. The root is i_block (at most 4 entries);
# other nodes are blocks (at most (block_size - 12) / 12 entries), followed
# with metadata_csum by a 4-byte checksum at 12 + 12 * max. In a node of
# depth 0 the entries are extents (first logical block, length, first
# physical block; a length above 32768 marks an unwritten extent of length
# - 32768, which reads as zeros); above, they are indexes (first logical
# block, the child node's block). A child's depth is its parent's less one.
#
# The walk recurses on the depth, refuses a root deeper than the options'
# max_depth before reading anything, and so reads at most max_depth blocks
# for one lookup.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./options.bend as O
import ./field.bend as F
import ./csum.bend as K
import ./super.bend as S
import ./blockmap.bend as M

type Ext2ExtentHeader is Data:
  Ext2ExtentHeader{magic: U32, entries: Nat, max: Nat, depth: Nat, generation: U32}

def Ext2ExtentHeader.parse(+o: B.Octets) -> Ext2ExtentHeader:
  Ext2ExtentHeader{F.Ext2Field.u16(o, 0n), U32.to_nat(F.Ext2Field.u16(o, 2n)), U32.to_nat(F.Ext2Field.u16(o, 4n)), U32.to_nat(F.Ext2Field.u16(o, 6n)), F.Ext2Field.u32(o, 8n)}

def Ext2ExtentHeader.depth(h: Ext2ExtentHeader) -> Nat:
  match h:
    case Ext2ExtentHeader{m, n, x, d, g}:
      d

def Ext2ExtentHeader.max(h: Ext2ExtentHeader) -> Nat:
  match h:
    case Ext2ExtentHeader{m, n, x, d, g}:
      x

# the depth of an extent tree whose root is i_block
def Ext2Extent.root_depth(iblock: B.Octets) -> Nat:
  U32.to_nat(F.Ext2Field.u16(iblock, 6n))

# a leaf entry: first logical block, length, first physical block, and
# whether it is written (an unwritten one reads as zeros)
type Ext2Extent is Data:
  Ext2Extent{block: Nat, len: Nat, start: Nat, written: Bool}

def Ext2Extent.len_of(unwritten: Bool, +raw: Nat) -> Nat:
  match unwritten:
    case True{}:
      Nat.sub(raw, 32768n)
    case False{}:
      raw

# the extent at byte offset off of a node
def Ext2Extent.parse(+o: B.Octets, +off: Nat) -> Ext2Extent:
  +raw = U32.to_nat(F.Ext2Field.u16(o, Nat.add(off, 4n)))
  +unwritten = Nat.is_lt(32768n, raw)
  Ext2Extent{F.Ext2Field.nat(o, off), Ext2Extent.len_of(unwritten, raw), F.Ext2Field.join(F.Ext2Field.u16(o, Nat.add(off, 6n)), F.Ext2Field.u32(o, Nat.add(off, 8n))), Bool.not(unwritten)}

# an index entry: the first logical block below it, and the child's block
type Ext2ExtentIndex is Data:
  Ext2ExtentIndex{block: Nat, leaf: Nat}

def Ext2ExtentIndex.parse(+o: B.Octets, +off: Nat) -> Ext2ExtentIndex:
  Ext2ExtentIndex{F.Ext2Field.nat(o, off), F.Ext2Field.join(F.Ext2Field.u16(o, Nat.add(off, 8n)), F.Ext2Field.u32(o, Nat.add(off, 4n)))}

# Searching one node for logical block l

type Ext2ExtentStep is Data:
  Ext2StepFound{block: Maybe<&2, Nat>}
  Ext2StepStop{}
  Ext2StepNext{}

def Ext2Extent.at.add(small: Bool, +s: Nat, k: Nat) -> Nat:
  match small:
    case True{}:
      Nat.add(s, k)
    case False{}:
      s

# block k of an extent starting at block s, if written (a start too close to
# 2^48 to add to is answered as it is, and the map then refuses it)
def Ext2Extent.at(written: Bool, +s: Nat, k: Nat) -> Maybe<&2, Nat>:
  match written:
    case True{}:
      Some{Ext2Extent.at.add(Nat.is_lt(s, Nat.mul(65535n, Nat.mul(65536n, 65536n))), s, k)}
    case False{}:
      None{}

def Ext2Extent.classify.pick(before: Bool, inside: Bool, +e: Ext2Extent, +l: Nat) -> Ext2ExtentStep:
  match before inside:
    case True{} _:
      Ext2StepStop{}
    case False{} True{}:
      match e:
        case Ext2Extent{b, n, s, w}:
          Ext2StepFound{Ext2Extent.at(w, s, Nat.sub(l, b))}
    case False{} False{}:
      Ext2StepNext{}

# what extent e says of logical block l: there (or unwritten), not there and
# no later extent can hold it (they are sorted), or look further
def Ext2Extent.classify(+e: Ext2Extent, +l: Nat) -> Ext2ExtentStep:
  match e:
    case Ext2Extent{+b, +n, s, w}:
      Ext2Extent.classify.pick(Nat.is_lt(l, b), Nat.is_lt(l, Nat.add(b, n)), e, l)

# the leaf entries from byte off on, n of them, the first classified as st
def Ext2Extent.leaf(n: Nat, st: Ext2ExtentStep, +node: B.Octets, +off: Nat, +l: Nat) -> Maybe<&2, Nat>:
  match n st:
    case 0n _:
      None{}
    case 1n+k Ext2StepFound{m}:
      m
    case 1n+k Ext2StepStop{}:
      None{}
    case 1n+k Ext2StepNext{}:
      +next = Nat.add(off, 12n)
      Ext2Extent.leaf(k, Ext2Extent.classify(Ext2Extent.parse(node, next), l), node, next, l)

def Ext2ExtentIndex.take.pick(covers: Bool, leaf: Nat) -> Maybe<&2, Nat>:
  match covers:
    case True{}:
      Some{leaf}
    case False{}:
      None{}

def Ext2ExtentIndex.take(+ix: Ext2ExtentIndex, +l: Nat) -> Maybe<&2, Nat>:
  match ix:
    case Ext2ExtentIndex{b, leaf}:
      Ext2ExtentIndex.take.pick(Nat.is_le(b, l), leaf)

# the child of the last index entry (of n, from byte off on) that starts at
# or before l; best is the one found so far, cur what the entry at off says
def Ext2ExtentIndex.find(n: Nat, cur: Maybe<&2, Nat>, best: Maybe<&2, Nat>, +node: B.Octets, +off: Nat, +l: Nat) -> Maybe<&2, Nat>:
  match n cur:
    case 0n _:
      best
    case 1n+k None{}:
      best
    case 1n+k Some{c}:
      +next = Nat.add(off, 12n)
      Ext2ExtentIndex.find(k, Ext2ExtentIndex.take(Ext2ExtentIndex.parse(node, next), l), Some{c}, node, next, l)

# Checks on a node

def Ext2Extent.check_header(+h: Ext2ExtentHeader, +cap: Nat, +depth: Nat, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  match h:
    case Ext2ExtentHeader{+magic, +n, +max, +d, g}:
      do Result<&2, &2, E.Ext2Error, Unit>:
        S.Ext2.require(U32.is_eq(magic, 62218), E.Ext2BadExtentMagic{ino, magic})
        S.Ext2.require(Nat.is_le(max, cap), E.Ext2BadExtentHeader{ino, "more entries than the node holds"})
        S.Ext2.require(Nat.is_le(n, max), E.Ext2BadExtentHeader{ino, "more entries than its maximum"})
        S.Ext2.require(Nat.is_eq(d, depth), E.Ext2BadExtentDepth{ino, d})

def Ext2Extent.entries(h: Ext2ExtentHeader) -> Nat:
  match h:
    case Ext2ExtentHeader{m, n, x, d, g}:
      n

# a child block's checksum (metadata_csum): the four bytes after max entries
def Ext2Extent.check_csum(on: Bool, +iseed: U32, +blk: B.Octets, +ino: Nat, +p: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  match on:
    case True{}:
      +max = Ext2ExtentHeader.max(Ext2ExtentHeader.parse(blk))
      +stored = F.Ext2Field.u32(blk, Nat.add(12n, Nat.mul(12n, max)))
      +c = K.Ext2Csum.extent_block(iseed, blk, max)
      S.Ext2.require(U32.is_eq(c, stored), E.Ext2BadExtentCsum{ino, p, stored, c})
    case False{}:
      Done{Unit{}}

# the child node a lookup descends to, read and checked: None for a hole
def Ext2Extent.fetch(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +iseed: U32, child: Maybe<&2, Nat>) -> Result<&2, &2, E.Ext2Error, Maybe<&2, B.Octets>>:
  match child:
    case None{}:
      Done{None{}}
    case Some{+c}:
      do Result<&2, &2, E.Ext2Error, Maybe<&2, B.Octets>>:
        +blk : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, c)
        Ext2Extent.check_csum(S.Ext2Fs.verify_meta(fs), iseed, blk, ino, c)
        return Some{blk}

# The walk: from a node of the given depth (holding at most cap entries; None
# when a lookup found no child) down to a leaf. The recursion is on the
# depth itself.
def Ext2Extent.walk(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +depth: Nat, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +iseed: U32, +cap: Nat, node: Maybe<&2, B.Octets>, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match depth node:
    case _ None{}:
      Done{None{}}
    case 0n Some{+o}:
      +h = Ext2ExtentHeader.parse(o)
      do Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
        Ext2Extent.check_header(h, cap, 0n, ino)
        M.Ext2Map.check_some(fs, ino, Ext2Extent.leaf(Ext2Extent.entries(h), Ext2Extent.classify(Ext2Extent.parse(o, 12n), l), o, 12n, l))
    case 1n+p Some{+o}:
      +h = Ext2ExtentHeader.parse(o)
      do Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
        Ext2Extent.check_header(h, cap, 1n+p, ino)
        child : Maybe<&2, Nat> <- M.Ext2Map.check_some(fs, ino, Ext2ExtentIndex.find(Ext2Extent.entries(h), Ext2ExtentIndex.take(Ext2ExtentIndex.parse(o, 12n), l), None{}, o, 12n, l))
        next : Maybe<&2, B.Octets> <- Ext2Extent.fetch(~Dv, ~block_size, ~read_block, d, fs, ino, iseed, child)
        Ext2Extent.walk(~Dv, ~block_size, ~read_block, p, d, fs, ino, iseed, Nat.div(Nat.sub(S.Ext2Fs.block_size(fs), 12n), 12n), next, l)

def Ext2Extent.map.depth(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ok: Bool, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +gen: U32, +iblock: B.Octets, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match ok:
    case False{}:
      Fail{E.Ext2ExtentTooDeep{ino, Ext2Extent.root_depth(iblock)}}
    case True{}:
      Ext2Extent.walk(~Dv, ~block_size, ~read_block, Ext2Extent.root_depth(iblock), d, fs, ino, K.Ext2Csum.inode_seed(S.Ext2Fs.seed(fs), U32.from_nat(ino), gen), 4n, Some{iblock}, l)

# the block holding logical block l of the inode numbered ino (generation
# gen) whose i_block is the extent tree root iblock: Some{block}, or None for
# a hole or an unwritten extent. A root deeper than the options' max_depth is
# refused before anything is read.
def Ext2Extent.map(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +gen: U32, +iblock: B.Octets, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  Ext2Extent.map.depth(~Dv, ~block_size, ~read_block, Nat.is_le(Ext2Extent.root_depth(iblock), O.Ext2Options.max_depth(S.Ext2Fs.opts(fs))), d, fs, ino, gen, iblock, l)
