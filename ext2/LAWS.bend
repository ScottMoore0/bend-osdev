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
