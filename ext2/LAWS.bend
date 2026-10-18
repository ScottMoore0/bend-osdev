# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input:
#   * inode numbers and (group, index) pairs convert both ways, for every
#     number of inodes per group (from 1), and the index stays below it;
#   * a directory entry encoded and decoded gives the entry back as the disk
#     stores it, for every entry whose name has name_len bytes;
#   * the block map never answers a block outside the filesystem, nor any
#     block past what the file's size needs (on every in-memory device, every
#     filesystem, every inode);
#   * the extent walk refuses a tree deeper than its bound before it reads
#     anything; and a reader at the end of a file answers the end.
# Each law with a hypothesis has a witness that the hypothesis can hold.
#
# Vectors: superblocks accepted and refused (features named), checksums as
# mke2fs wrote them, inode locations, directory entries, block-map paths.
#
# The writer's laws (directory blocks, the checked operations, mkfs) follow
# the reader's, below.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./options.bend as O
import ./csum.bend as K
import ./super.bend as S
import ./inode.bend as N
import ./blockmap.bend as M
import ./extent.bend as X
import ./file.bend as FL
import ./dir.bend as DR
import ./patch.bend as PA
import ./bitmap.bend as BM
import ./meta.bend as T
import ./wopts.bend as WO
import ./extentw.bend as EW
import ./dirw.bend as DW
import ./fsck.bend as FK
import ./ops.bend as P
import ./run.bend as RN
import ./mkfs.bend as MK
import ./ext2.bend as EX

# Inode numbers: inode 1 + k with 1 + p inodes per group

law inode_locate_number:
  for +p: Nat
  for +k: Nat
  {N.Ext2Inode.number(1n+p, N.Ext2Inode.locate(1n+p, 1n+k)) == 1n+k : Nat}

law inode_locate_index:
  for +p: Nat
  for +k: Nat
  {Nat.is_lt(N.Ext2InodeLoc.index(N.Ext2Inode.locate(1n+p, 1n+k)), 1n+p) == True{} : Bool}

law inode_number_locate:
  for +p: Nat
  for +g: Nat
  for +i: Nat
  for h: {Nat.is_lt(i, 1n+p) == True{} : Bool}
  {N.Ext2Inode.locate(1n+p, N.Ext2Inode.number(1n+p, N.Ext2InodeLoc{g, i})) == N.Ext2InodeLoc{g, i} : N.Ext2InodeLoc}

# the hypothesis holds for every group and the last index of a group
law inode_number_locate_witness:
  for +p: Nat
  {Nat.is_lt(p, 1n+p) == True{} : Bool}

# Directory entries (the filetype layout)

law dirent_round_trip:
  for +e: DR.Ext2Dirent
  for h: {B.Octets.len(DR.Ext2Dirent.name(e)) == U32.to_nat(B.byte(DR.Ext2Dirent.name_len(e))) : Nat}
  {DR.Ext2Dirent.decode(True{}, DR.Ext2Dirent.encode(e)) == Some{DR.Ext2Dirent.norm(e)} : Maybe<&2, DR.Ext2Dirent>}

law dirent_round_trip_witness:
  {B.Octets.len(DR.Ext2Dirent.name(DR.Ext2Dirent{12, 16, 5, 1, B.Octets.of_string("hello")})) == U32.to_nat(B.byte(DR.Ext2Dirent.name_len(DR.Ext2Dirent{12, 16, 5, 1, B.Octets.of_string("hello")}))) : Nat}

# The block map: never a block past the file's size, never a block outside
# the filesystem

law map_past_end:
  for d: D.MemDev
  for +fs: S.Ext2Fs
  for +i: N.Ext2Inode
  for +l: Nat
  for h: {Nat.is_lt(l, FL.Ext2File.blocks_needed(fs, i)) == False{} : Bool}
  {FL.Ext2File.map(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, i, l) == Fail{E.Ext2PastEnd{N.Ext2Inode.number_of(i), l}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>}

# every file has a first block past its end: the one its size needs next
law map_past_end_witness:
  for +fs: S.Ext2Fs
  for +i: N.Ext2Inode
  {Nat.is_lt(FL.Ext2File.blocks_needed(fs, i), FL.Ext2File.blocks_needed(fs, i)) == False{} : Bool}

law map_inside:
  for d: D.MemDev
  for +fs: S.Ext2Fs
  for +i: N.Ext2Inode
  for +l: Nat
  for +q: Nat
  for h: {FL.Ext2File.map(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, i, l) == Done{Some{q}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>}
  {Nat.is_lt(q, S.Ext2Fs.blocks(fs)) == True{} : Bool}

# A small ext2 superblock (64 blocks of 1 KiB, 16 inodes of 128 bytes), with
# a given magic number and incompat features
def Ext2Laws.sample_super(magic: U32, incompat: U32) -> B.Octets:
  B.Octets.concat([B.Octets.le32(16), B.Octets.le32(64), B.Octets.zeros(12n), B.Octets.le32(1), B.Octets.zeros(8n), B.Octets.le32(8192), B.Octets.zeros(4n), B.Octets.le32(16), B.Octets.zeros(12n), B.Octets.le16(magic), B.Octets.zeros(18n), B.Octets.le32(1), B.Octets.zeros(4n), B.Octets.le32(11), B.Octets.le16(128), B.Octets.zeros(6n), B.Octets.le32(incompat), B.Octets.zeros(924n)])

# a regular file of 100 bytes whose first block is block 5
def Ext2Laws.sample_inode() -> N.Ext2Inode:
  N.Ext2Inode.parse(12n, 128n, B.Octets.concat([B.Octets.le16(33188), B.Octets.zeros(2n), B.Octets.le32(100), B.Octets.zeros(32n), B.Octets.le32(5), B.Octets.zeros(84n)]))

law map_inside_witness:
  exs fs: S.Ext2Fs
  {FL.Ext2File.map(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, D.MemDev.blank(1024n, 0n), fs, Ext2Laws.sample_inode(), 0n) == Done{Some{5n}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>}

# Extent trees: a root deeper than the bound is refused, whatever the device

law extent_depth_bound:
  for d: D.MemDev
  for +fs: S.Ext2Fs
  for +ino: Nat
  for +gen: U32
  for +iblock: B.Octets
  for +l: Nat
  for h: {Nat.is_le(X.Ext2Extent.root_depth(iblock), O.Ext2Options.max_depth(S.Ext2Fs.opts(fs))) == False{} : Bool}
  {X.Ext2Extent.map(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, ino, gen, iblock, l) == Fail{E.Ext2ExtentTooDeep{ino, X.Ext2Extent.root_depth(iblock)}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>}

# a root of depth 9 (the default bound is 5)
law extent_depth_bound_witness:
  exs fs: S.Ext2Fs
  {Nat.is_le(X.Ext2Extent.root_depth(B.Octets.of_list([10, 243, 0, 0, 4, 0, 9, 0, 0, 0, 0, 0])), O.Ext2Options.max_depth(S.Ext2Fs.opts(fs))) == False{} : Bool}

# Streaming: a reader at or past the blocks a file needs answers the end

law next_at_end:
  for d: D.MemDev
  for +fs: S.Ext2Fs
  for +i: N.Ext2Inode
  for +k: Nat
  for h: {Nat.is_lt(k, FL.Ext2File.blocks_needed(fs, i)) == False{} : Bool}
  {FL.Ext2File.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, FL.Ext2Reader{i, k}) == Done{FL.Ext2Eof{}} : Result<&2, &2, E.Ext2Error, FL.Ext2Chunk>}

# Vectors: superblocks

law mount_sample:
  {Result.map(&2, &2, E.Ext2Error, S.Ext2Fs, Nat, S.Ext2Fs.groups, S.Ext2Fs.mount(O.Ext2Options.default(), Ext2Laws.sample_super(61267, 2))) == Done{1n} : Result<&2, &2, E.Ext2Error, Nat>}

law mount_bad_magic:
  {Result.map(&2, &2, E.Ext2Error, S.Ext2Fs, Nat, S.Ext2Fs.groups, S.Ext2Fs.mount(O.Ext2Options.default(), Ext2Laws.sample_super(0, 2))) == Fail{E.Ext2BadMagic{0}} : Result<&2, &2, E.Ext2Error, Nat>}

law mount_inline_data:
  {Result.map(&2, &2, E.Ext2Error, S.Ext2Fs, Nat, S.Ext2Fs.groups, S.Ext2Fs.mount(O.Ext2Options.default(), Ext2Laws.sample_super(61267, 32770))) == Fail{E.Ext2Unsupported{"inline_data"}} : Result<&2, &2, E.Ext2Error, Nat>}

law mount_needs_recovery:
  {Result.map(&2, &2, E.Ext2Error, S.Ext2Fs, Nat, S.Ext2Fs.groups, S.Ext2Fs.mount(O.Ext2Options.default(), Ext2Laws.sample_super(61267, 6))) == Fail{E.Ext2NeedsRecovery{}} : Result<&2, &2, E.Ext2Error, Nat>}

# a reader limited to plain ext2 refuses extents, naming them
law mount_ext2_only:
  {Result.map(&2, &2, E.Ext2Error, S.Ext2Fs, Nat, S.Ext2Fs.groups, S.Ext2Fs.mount(O.Ext2Options.with_incompat(O.Ext2Options.default(), O.Ext2Options.ext2_incompat()), Ext2Laws.sample_super(61267, 66))) == Fail{E.Ext2Unsupported{"extent"}} : Result<&2, &2, E.Ext2Error, Nat>}

# Vectors: checksums, as mke2fs 1.47.0 wrote them (UUID
# 6f1c2a3b-4d5e-4f60-8a9b-0c1d2e3f4a5b, metadata_csum, metadata_csum_seed)

law csum_seed:
  {K.Ext2Csum.seed(B.Octets.of_list([111, 28, 42, 59, 77, 94, 79, 96, 138, 155, 12, 29, 46, 63, 74, 91])) == 2096354977 : U32}

law csum_group:
  {K.Ext2Csum.group(2096354977, 0, B.Octets.of_list([10, 0, 0, 0, 26, 0, 0, 0, 42, 0, 0, 0, 198, 3, 117, 0, 2, 0, 4, 0, 0, 0, 0, 0, 205, 137, 97, 125, 117, 0, 136, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 149, 167, 202, 0, 0, 0, 0]), 64n) == 54920 : U32}

law csum_inode:
  {K.Ext2Csum.inode(K.Ext2Csum.inode_seed(2096354977, 2, 0), B.Octets.append(B.Octets.of_list([237, 65, 0, 0, 0, 4, 0, 0, 245, 213, 211, 106, 245, 213, 211, 106, 245, 213, 211, 106, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 10, 243, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 39, 0, 0, 32, 0, 26, 211, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 245, 213, 211, 106]), B.Octets.zeros(108n)), 256n, True{}) == 3541706705 : U32}

# Vectors: inodes, directory entries, block-map paths

law locate_vector:
  {N.Ext2Inode.locate(8n, 137n) == N.Ext2InodeLoc{17n, 0n} : N.Ext2InodeLoc}

law dirent_dot:
  {DR.Ext2Dirent.decode(True{}, B.Octets.of_list([2, 0, 0, 0, 12, 0, 1, 2, 46, 0, 0, 0])) == Some{DR.Ext2Dirent{2, 12, 1, 2, B.Octets.of_string(".")}} : Maybe<&2, DR.Ext2Dirent>}

law dirent_no_filetype:
  {DR.Ext2Dirent.decode(False{}, B.Octets.of_list([11, 0, 0, 0, 20, 0, 10, 0, 108, 111, 115, 116, 43, 102, 111, 117, 110, 100, 0, 0])) == Some{DR.Ext2Dirent{11, 20, 10, 0, B.Octets.of_string("lost+found")}} : Maybe<&2, DR.Ext2Dirent>}

law dirent_bad_rec_len:
  {DR.Ext2Dirent.check(DR.Ext2Dirent{2, 13, 1, 2, B.Octets.of_string(".")}, 1024n, 16n) == Some{"rec_len is not a multiple of 4"} : Maybe<&2, String>}

law dirent_past_block:
  {DR.Ext2Dirent.check(DR.Ext2Dirent{2, 1028, 1, 2, B.Octets.of_string(".")}, 1024n, 16n) == Some{"rec_len past the end of the block"} : Maybe<&2, String>}

law dirent_ok:
  {DR.Ext2Dirent.check(DR.Ext2Dirent{2, 12, 1, 2, B.Octets.of_string(".")}, 1024n, 16n) == None{} : Maybe<&2, String>}

# 4 block numbers per indirect block (as with 16-byte blocks; the checker
# counts in unary, so the vectors keep the numbers small): 12 direct blocks,
# then 4 singly, 16 doubly and 64 triply indirect ones
law path_direct:
  {M.Ext2Map.path(11n, 4n) == Some{M.Ext2MapPath{11n, 0n, 0n}} : Maybe<&2, M.Ext2MapPath>}

law path_single:
  {M.Ext2Map.path(15n, 4n) == Some{M.Ext2MapPath{12n, 1n, 3n}} : Maybe<&2, M.Ext2MapPath>}

law path_double:
  {M.Ext2Map.path(16n, 4n) == Some{M.Ext2MapPath{13n, 2n, 0n}} : Maybe<&2, M.Ext2MapPath>}

law path_triple:
  {M.Ext2Map.path(95n, 4n) == Some{M.Ext2MapPath{14n, 3n, 63n}} : Maybe<&2, M.Ext2MapPath>}

law path_beyond:
  {M.Ext2Map.path(96n, 4n) == None{} : Maybe<&2, M.Ext2MapPath>}

# ---------------------------------------------------------------- writing
#
# The writer's laws. For every input:
#   * directory blocks (dirw.bend, a block's entries as slots): inserting an
#     entry or removing one keeps the total of the records (the block stays
#     exactly covered: rec_len is split or merged, never lost); inserting an
#     entry whose name the block does not hold leaves every other entry as
#     it was, in order; removing one leaves exactly the others;
#   * the checked operations (run.bend): every device Ext2Op.run answers,
#     for every operation, device, filesystem and options that check
#     anything, has bitmaps that agree with its free counts, and is what
#     the operation promised (a write reads back as written, an entry
#     created or removed leaves its directory's other entries as they
#     were, ...); with the full check it passes Ext2Fsck.full (no block
#     owned twice, the bitmaps exact, every link count the number of
#     entries naming the inode);
#   * mkfs (mkfs.bend): every filesystem Ext2Mkfs.make answers, for every
#     device and options, opens with the reader's default options and
#     passes Ext2Fsck.full.
# These hold because each operation checks its result before answering it
# (a result that fails is refused, Ext2CheckFailed, and the caller's device
# is as it was): they say what every answer satisfies, not that an
# operation succeeds. That operations do succeed is what the tests show
# (ref/wgen.py: every operation its model expects to succeed does, and
# e2fsck accepts every image); the kernel that checks these laws counts in
# unary, so an operation on an image is beyond what a law can evaluate.
# Every law with a hypothesis has a witness.

def Ext2Laws.total_or(m: Maybe<&2, List<&2, DW.Ext2Slot>>, d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{xs}:
      DW.Ext2Slots.total(xs)

def Ext2Laws.unnamed_or(m: Maybe<&2, List<&2, DW.Ext2Slot>>, +nm: B.Octets, d: List<&2, DW.Ext2Name>) -> List<&2, DW.Ext2Name>:
  match m:
    case None{}:
      d
    case Some{xs}:
      DW.Ext2Names.unname(DW.Ext2Slots.names(xs), nm)

def Ext2Laws.names_or(m: Maybe<&2, List<&2, DW.Ext2Slot>>, d: List<&2, DW.Ext2Name>) -> List<&2, DW.Ext2Name>:
  match m:
    case None{}:
      d
    case Some{xs}:
      DW.Ext2Slots.names(xs)

law slots_insert_total:
  for +ss: List<&2, DW.Ext2Slot>
  for +n: DW.Ext2Slot
  for +ss2: List<&2, DW.Ext2Slot>
  for h: {DW.Ext2Slots.insert(ss, n) == Some{ss2} : Maybe<&2, List<&2, DW.Ext2Slot>>}
  {DW.Ext2Slots.total(ss2) == DW.Ext2Slots.total(ss) : Nat}

law slots_remove_total:
  for +ss: List<&2, DW.Ext2Slot>
  for +name: B.Octets
  for +ss2: List<&2, DW.Ext2Slot>
  for h: {DW.Ext2Slots.remove(ss, name) == Some{ss2} : Maybe<&2, List<&2, DW.Ext2Slot>>}
  {DW.Ext2Slots.total(ss2) == DW.Ext2Slots.total(ss) : Nat}

law slots_insert_names:
  for +ss: List<&2, DW.Ext2Slot>
  for +n: DW.Ext2Slot
  for +ss2: List<&2, DW.Ext2Slot>
  for hl: {DW.Ext2Slots.lookup(ss, DW.Ext2Slot.name(n)) == None{} : Maybe<&2, DW.Ext2Slot>}
  for hu: {DW.Ext2Slot.used(n) == True{} : Bool}
  for h: {DW.Ext2Slots.insert(ss, n) == Some{ss2} : Maybe<&2, List<&2, DW.Ext2Slot>>}
  {DW.Ext2Names.unname(DW.Ext2Slots.names(ss2), DW.Ext2Slot.name(n)) == DW.Ext2Slots.names(ss) : List<&2, DW.Ext2Name>}

law slots_remove_names:
  for +ss: List<&2, DW.Ext2Slot>
  for +name: B.Octets
  for +ss2: List<&2, DW.Ext2Slot>
  for h: {DW.Ext2Slots.remove(ss, name) == Some{ss2} : Maybe<&2, List<&2, DW.Ext2Slot>>}
  {DW.Ext2Slots.names(ss2) == DW.Ext2Names.unname(DW.Ext2Slots.names(ss), name) : List<&2, DW.Ext2Name>}

# A block of 1 KiB holding "." and "..", and a new entry "a"
def Ext2Laws.dots() -> List<&2, DW.Ext2Slot>:
  [DW.Ext2Slot{2, 12n, 2, B.Octets.of_string(".")}, DW.Ext2Slot{2, 1012n, 2, B.Octets.of_string("..")}]

def Ext2Laws.entry_a() -> DW.Ext2Slot:
  DW.Ext2Slot{12, 0n, 1, B.Octets.of_string("a")}

# the hypotheses hold together: "a" goes into the room after ".."
law slots_insert_witness:
  {Bool.and(Maybe.is_none(&2, DW.Ext2Slot, DW.Ext2Slots.lookup(Ext2Laws.dots(), B.Octets.of_string("a"))), Bool.and(DW.Ext2Slot.used(Ext2Laws.entry_a()), Maybe.is_some(&2, List<&2, DW.Ext2Slot>, DW.Ext2Slots.insert(Ext2Laws.dots(), Ext2Laws.entry_a())))) == True{} : Bool}

law slots_remove_witness:
  {Maybe.is_some(&2, List<&2, DW.Ext2Slot>, DW.Ext2Slots.remove([DW.Ext2Slot{2, 12n, 2, B.Octets.of_string(".")}, DW.Ext2Slot{2, 12n, 2, B.Octets.of_string("..")}, DW.Ext2Slot{12, 1000n, 1, B.Octets.of_string("a")}], B.Octets.of_string("a"))) == True{} : Bool}

# vectors: the split and the merge as the layout describes them
law slots_insert_vector:
  {DW.Ext2Slots.insert(Ext2Laws.dots(), Ext2Laws.entry_a()) == Some{[DW.Ext2Slot{2, 12n, 2, B.Octets.of_string(".")}, DW.Ext2Slot{2, 12n, 2, B.Octets.of_string("..")}, DW.Ext2Slot{12, 1000n, 1, B.Octets.of_string("a")}]} : Maybe<&2, List<&2, DW.Ext2Slot>>}

law slots_remove_vector:
  {DW.Ext2Slots.remove([DW.Ext2Slot{2, 12n, 2, B.Octets.of_string(".")}, DW.Ext2Slot{2, 12n, 2, B.Octets.of_string("..")}, DW.Ext2Slot{12, 1000n, 1, B.Octets.of_string("a")}], B.Octets.of_string("a")) == Some{[DW.Ext2Slot{2, 12n, 2, B.Octets.of_string(".")}, DW.Ext2Slot{2, 1012n, 2, B.Octets.of_string("..")}]} : Maybe<&2, List<&2, DW.Ext2Slot>>}

# the first entry of a block removed: marked unused, its record kept
law slots_remove_first_vector:
  {DW.Ext2Slots.remove([DW.Ext2Slot{12, 1024n, 1, B.Octets.of_string("a")}], B.Octets.of_string("a")) == Some{[DW.Ext2Slot{0, 1024n, 1, B.Octets.of_string("a")}]} : Maybe<&2, List<&2, DW.Ext2Slot>>}

# no room: refused
law slots_insert_full_vector:
  {DW.Ext2Slots.insert([DW.Ext2Slot{2, 12n, 2, B.Octets.of_string(".")}, DW.Ext2Slot{2, 12n, 2, B.Octets.of_string("..")}], Ext2Laws.entry_a()) == None{} : Maybe<&2, List<&2, DW.Ext2Slot>>}

# The checked operations, on an in-memory device

# whether every device a result answers satisfies q (a refusal answers none)
def Ext2Laws.after(r: Result<&2, &2, E.Ext2Error, D.MemDev>, q: D.MemDev -> Bool) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{d2}:
      q(d2)

def Ext2Laws.holds(r: Result<&2, &2, E.Ext2Error, Unit>) -> Bool:
  match r:
    case Done{u}:
      True{}
    case Fail{e}:
      False{}

def Ext2Laws.yes(r: Result<&2, &2, E.Ext2Error, Bool>) -> Bool:
  match r:
    case Done{b}:
      b
    case Fail{e}:
      False{}

def Ext2Laws.run(+op: P.Ext2Op, +d: D.MemDev, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, D.MemDev>:
  RN.Ext2Op.run(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, op, d, fs, wo)

# the bitmaps and the free counts agree
law run_counts:
  for +d: D.MemDev
  for +fs: S.Ext2Fs
  for +wo: WO.Ext2WriteOptions
  for +op: P.Ext2Op
  for h: {WO.Ext2CheckLevel.any(WO.Ext2WriteOptions.check(wo)) == True{} : Bool}
  {Ext2Laws.after(Ext2Laws.run(op, d, fs, wo), d2 => Ext2Laws.holds(FK.Ext2Fsck.counts(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs))) == True{} : Bool}

# the operation did what it promised (Ext2Guard.promise: for each kind of
# operation, what its result must show)
law run_promise:
  for +d: D.MemDev
  for +fs: S.Ext2Fs
  for +wo: WO.Ext2WriteOptions
  for +op: P.Ext2Op
  for h: {WO.Ext2CheckLevel.any(WO.Ext2WriteOptions.check(wo)) == True{} : Bool}
  {Ext2Laws.after(Ext2Laws.run(op, d, fs, wo), d2 => Ext2Laws.yes(RN.Ext2Guard.promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs))) == True{} : Bool}

# after writing a file, reading it gives the data back (the file at path
# read from byte off, len(data) bytes, is data)
law write_reads_back:
  for +d: D.MemDev
  for +fs: S.Ext2Fs
  for +wo: WO.Ext2WriteOptions
  for +path: B.Octets
  for +off: Nat
  for +data: B.Octets
  for h: {WO.Ext2CheckLevel.any(WO.Ext2WriteOptions.check(wo)) == True{} : Bool}
  {Ext2Laws.after(Ext2Laws.run(P.Ext2OpWrite{path, off, data}, d, fs, wo), d2 => Ext2Laws.yes(RN.Ext2Guard.reads_back(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs, path, off, data))) == True{} : Bool}

# creating an entry leaves every other entry of its directory unchanged
# (and the entry is there); removing one likewise (and it is gone)
law create_keeps_others:
  for +d: D.MemDev
  for +fs: S.Ext2Fs
  for +wo: WO.Ext2WriteOptions
  for +path: B.Octets
  for +mode: U32
  for h: {WO.Ext2CheckLevel.any(WO.Ext2WriteOptions.check(wo)) == True{} : Bool}
  {Ext2Laws.after(Ext2Laws.run(P.Ext2OpCreate{path, mode}, d, fs, wo), d2 => Ext2Laws.yes(RN.Ext2Guard.at(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, True{}, d, d2, fs, path))) == True{} : Bool}

law unlink_keeps_others:
  for +d: D.MemDev
  for +fs: S.Ext2Fs
  for +wo: WO.Ext2WriteOptions
  for +path: B.Octets
  for h: {WO.Ext2CheckLevel.any(WO.Ext2WriteOptions.check(wo)) == True{} : Bool}
  {Ext2Laws.after(Ext2Laws.run(P.Ext2OpUnlink{path}, d, fs, wo), d2 => Ext2Laws.yes(RN.Ext2Guard.at(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, False{}, d, d2, fs, path))) == True{} : Bool}

# the default options check (local): the hypothesis of the laws above
law run_check_witness:
  {WO.Ext2CheckLevel.any(WO.Ext2WriteOptions.check(WO.Ext2WriteOptions.default())) == True{} : Bool}

# with the full check: no block belongs to two owners, every bitmap is
# exact, every link count is the number of entries naming the inode
law run_full:
  for +d: D.MemDev
  for +fs: S.Ext2Fs
  for +wo: WO.Ext2WriteOptions
  for +op: P.Ext2Op
  for h: {WO.Ext2CheckLevel.full(WO.Ext2WriteOptions.check(wo)) == True{} : Bool}
  {Ext2Laws.after(Ext2Laws.run(op, d, fs, wo), d2 => Ext2Laws.holds(FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs))) == True{} : Bool}

law run_full_witness:
  {WO.Ext2CheckLevel.full(WO.Ext2WriteOptions.check(WO.Ext2WriteOptions.with_check(WO.Ext2WriteOptions.default(), WO.Ext2CheckFull{}))) == True{} : Bool}

# mkfs gives a volume that opens, and that passes the full check: every
# device Ext2Mkfs.make answers, for every device and options, opens with the
# reader's default options and passes Ext2Fsck.full (make checks what
# Ext2Mkfs.build wrote before answering it)
law mkfs_opens:
  for d: D.MemDev
  for o: MK.Ext2MkfsOptions
  {Ext2Laws.after(MK.Ext2Mkfs.make(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, d, o), d2 => Result.is_done(&2, &2, E.Ext2Error, S.Ext2Fs, EX.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, O.Ext2Options.default()))) == True{} : Bool}

law mkfs_consistent:
  for d: D.MemDev
  for o: MK.Ext2MkfsOptions
  {Ext2Laws.after(MK.Ext2Mkfs.make(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, d, o), d2 => Ext2Laws.holds(Result.bind(&2, &2, E.Ext2Error, S.Ext2Fs, Unit, EX.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, O.Ext2Options.default()), fs => FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs)))) == True{} : Bool}

# Vectors: bitmaps, field patches, extent lists

# 4 bytes: bits 0-10 used, 11-28 free, 29-31 padding
law bitmap_make_vector:
  {B.Octets.hex(BM.Ext2Bitmap.make(4n, 11n, 29n)) == "ff0700e0" : String}

law bitmap_find_vector:
  {BM.Ext2Bitmap.find(BM.Ext2Bitmap.make(4n, 11n, 29n), 0n, 29n, 3n) == [11n, 12n, 13n] : List<&2, Nat>}

law bitmap_count_vector:
  {BM.Ext2Bitmap.count_clear(BM.Ext2Bitmap.update(BM.Ext2Bitmap.make(4n, 11n, 29n), [11n, 20n], True{}), 29n) == 16n : Nat}

law patch_vector:
  {B.Octets.hex(PA.Ext2Patch.u32(B.Octets.zeros(8n), 2n, 305419896)) == "0000785634120000" : String}

# a block appended right after an extent's last joins it
law extent_insert_vector:
  {EW.Ext2ExtW.insert([X.Ext2Extent{0n, 2n, 100n, True{}}], 2n, 102n) == [X.Ext2Extent{0n, 3n, 100n, True{}}] : List<&2, X.Ext2Extent>}

# a block that continues neither neighbour is an extent of its own
law extent_insert_gap_vector:
  {EW.Ext2ExtW.insert([X.Ext2Extent{0n, 2n, 100n, True{}}], 5n, 200n) == [X.Ext2Extent{0n, 2n, 100n, True{}}, X.Ext2Extent{5n, 1n, 200n, True{}}] : List<&2, X.Ext2Extent>}

# a cut in the middle of an extent: the rest freed
law extent_cut_vector:
  {EW.Ext2ExtW.cut([X.Ext2Extent{0n, 4n, 100n, True{}}], 1n) == EW.Ext2ExtCut{[X.Ext2Extent{0n, 1n, 100n, True{}}], [103n, 102n, 101n]} : EW.Ext2ExtCut}
