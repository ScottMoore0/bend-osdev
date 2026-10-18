# bend-osdev-ext2: what the writer does, as one record with a named default.
#
#   alloc    the allocation policy: where new inodes and blocks go
#   csum     what to do with an image that carries metadata checksums
#            (metadata_csum, or gdt_csum): update them, or refuse to write
#   check    what each operation checks of its result before answering
#            (none; local: the free counts, and what the operation promised
#            of the file or directory it changed; full: also the whole
#            filesystem, as fsck.bend checks it)
#   extents  new files, directories and slow symbolic links get extent
#            trees when the filesystem has the extent feature (otherwise,
#            and when this is off, block maps)
#   time     the time stamped on what is written (seconds since 1970; the
#            writer has no clock of its own)
#   uid, gid the owner of what is created
import Base

# which group a new inode goes to
type Ext2GroupPick is Data:
  # the lowest group with a free inode
  Ext2PickFirst{}
  # the parent directory's group, then the groups after it, wrapping round
  Ext2PickNear{}
  # the group with the most free inodes (lowest first among equals), to
  # spread directories out
  Ext2PickSpread{}

# where new blocks go
type Ext2BlockPick is Data:
  # the lowest free blocks of the filesystem
  Ext2BlockFirst{}
  # from a goal on: after the file's last block, else at the start of its
  # inode's group; then onwards, wrapping round
  Ext2BlockNear{}

type Ext2AllocPolicy is Data:
  Ext2AllocPolicy{files: Ext2GroupPick, dirs: Ext2GroupPick, blocks: Ext2BlockPick}

# files near their directory, directories spread out, blocks near the file
def Ext2AllocPolicy.default() -> Ext2AllocPolicy:
  Ext2AllocPolicy{Ext2PickNear{}, Ext2PickSpread{}, Ext2BlockNear{}}

# everything first-fit (lowest group, lowest block)
def Ext2AllocPolicy.first_fit() -> Ext2AllocPolicy:
  Ext2AllocPolicy{Ext2PickFirst{}, Ext2PickFirst{}, Ext2BlockFirst{}}

type Ext2CsumMode is Data:
  # recompute every checksum a change touches
  Ext2CsumUpdate{}
  # refuse to write an image that has metadata_csum or gdt_csum
  Ext2CsumRefuse{}

type Ext2CheckLevel is Data:
  Ext2CheckNone{}
  Ext2CheckLocal{}
  Ext2CheckFull{}

type Ext2WriteOptions is Data:
  Ext2WriteOptions{alloc: Ext2AllocPolicy, csum: Ext2CsumMode, check: Ext2CheckLevel, extents: Bool, time: U32, uid: U32, gid: U32}

def Ext2WriteOptions.default() -> Ext2WriteOptions:
  Ext2WriteOptions{Ext2AllocPolicy.default(), Ext2CsumUpdate{}, Ext2CheckLocal{}, True{}, 0, 0, 0}

def Ext2WriteOptions.alloc(o: Ext2WriteOptions) -> Ext2AllocPolicy:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      a

def Ext2WriteOptions.csum(o: Ext2WriteOptions) -> Ext2CsumMode:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      c

def Ext2WriteOptions.check(o: Ext2WriteOptions) -> Ext2CheckLevel:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      k

def Ext2WriteOptions.extents(o: Ext2WriteOptions) -> Bool:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      x

def Ext2WriteOptions.time(o: Ext2WriteOptions) -> U32:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      t

def Ext2WriteOptions.with_alloc(o: Ext2WriteOptions, v: Ext2AllocPolicy) -> Ext2WriteOptions:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      Ext2WriteOptions{v, c, k, x, t, u, g}

def Ext2WriteOptions.with_csum(o: Ext2WriteOptions, v: Ext2CsumMode) -> Ext2WriteOptions:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      Ext2WriteOptions{a, v, k, x, t, u, g}

def Ext2WriteOptions.with_check(o: Ext2WriteOptions, v: Ext2CheckLevel) -> Ext2WriteOptions:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      Ext2WriteOptions{a, c, v, x, t, u, g}

def Ext2WriteOptions.with_extents(o: Ext2WriteOptions, v: Bool) -> Ext2WriteOptions:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      Ext2WriteOptions{a, c, k, v, t, u, g}

def Ext2WriteOptions.with_time(o: Ext2WriteOptions, v: U32) -> Ext2WriteOptions:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      Ext2WriteOptions{a, c, k, x, v, u, g}

def Ext2WriteOptions.uid(o: Ext2WriteOptions) -> U32:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      u

def Ext2WriteOptions.gid(o: Ext2WriteOptions) -> U32:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      g

# the owner (user and group) of what is created
def Ext2WriteOptions.with_owner(o: Ext2WriteOptions, v: U32, w: U32) -> Ext2WriteOptions:
  match o:
    case Ext2WriteOptions{a, c, k, x, t, u, g}:
      Ext2WriteOptions{a, c, k, x, t, v, w}

def Ext2AllocPolicy.files(p: Ext2AllocPolicy) -> Ext2GroupPick:
  match p:
    case Ext2AllocPolicy{f, d, b}:
      f

def Ext2AllocPolicy.dirs(p: Ext2AllocPolicy) -> Ext2GroupPick:
  match p:
    case Ext2AllocPolicy{f, d, b}:
      d

def Ext2AllocPolicy.blocks(p: Ext2AllocPolicy) -> Ext2BlockPick:
  match p:
    case Ext2AllocPolicy{f, d, b}:
      b

# whether the options check anything (local or full)
def Ext2CheckLevel.any(k: Ext2CheckLevel) -> Bool:
  match k:
    case Ext2CheckNone{}:
      False{}
    case _:
      True{}

def Ext2CheckLevel.full(k: Ext2CheckLevel) -> Bool:
  match k:
    case Ext2CheckFull{}:
      True{}
    case _:
      False{}
