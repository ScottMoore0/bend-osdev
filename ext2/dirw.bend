# bend-osdev-ext2: writing directories (Poirier, "Directories"; the ext4
# disk-layout documentation, "Linear (Classic) Directories" and "Checksums").
#
# A directory block is edited as the list of its entries, unused ones
# included, each a slot: the inode (0: unused), the record length, the file
# type and the name. The slots of a block always cover its region exactly
# (every rec_len is kept or split, never lost): inserting an entry takes an
# unused slot that is long enough, or splits a used one whose record is
# longer than its own entry needs, giving it the shortest record its name
# allows and the new entry the rest; removing an entry merges its record
# into the slot before it, or (the first slot of a block) marks it unused.
# With metadata_csum each block ends in a 12-byte tail holding its crc32c.
#
# Hash-indexed directories are refused (Ext2HtreeDir): bend-osdev-ext4
# writes those, keeping their index; a linear edit here would not.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./csum.bend as K
import ./super.bend as S
import ./inode.bend as N
import ./file.bend as FL
import ./dir.bend as DR
import ./patch.bend as P
import ./meta.bend as T
import ./inodew.bend as IW
import ./filew.bend as FW
import ./wopts.bend as WO

# A slot: one entry of a block (rec_len as a Nat, the name's length is its
# name_len)
type Ext2Slot is Data:
  Ext2Slot{inode: U32, rec_len: Nat, file_type: U32, name: B.Octets}

def Ext2Slot.inode(s: Ext2Slot) -> U32:
  match s:
    case Ext2Slot{i, r, f, n}:
      i

def Ext2Slot.rec_len(s: Ext2Slot) -> Nat:
  match s:
    case Ext2Slot{i, r, f, n}:
      r

def Ext2Slot.file_type(s: Ext2Slot) -> U32:
  match s:
    case Ext2Slot{i, r, f, n}:
      f

def Ext2Slot.name(s: Ext2Slot) -> B.Octets:
  match s:
    case Ext2Slot{i, r, f, n}:
      n

def Ext2Slot.used(+s: Ext2Slot) -> Bool:
  Bool.not(U32.is_eq(Ext2Slot.inode(s), 0))

# the record a slot's own entry needs: 8 + its name, to a multiple of 4
def Ext2Slot.need(+s: Ext2Slot) -> Nat:
  DR.Ext2Dirent.min_rec_len(B.Octets.len(Ext2Slot.name(s)))

def Ext2Slot.with_rec_len(s: Ext2Slot, r: Nat) -> Ext2Slot:
  match s:
    case Ext2Slot{i, x, f, n}:
      Ext2Slot{i, r, f, n}

def Ext2Slot.unused(s: Ext2Slot) -> Ext2Slot:
  match s:
    case Ext2Slot{i, r, f, n}:
      Ext2Slot{0, r, f, n}

# an entry's (inode, file type, name): what a directory listing shows
type Ext2Name is Data:
  Ext2Name{inode: U32, file_type: U32, name: B.Octets}

# The slots of a block as a list

# the total of the slots' records (the region they cover)
def Ext2Slots.total(ss: List<&2, Ext2Slot>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Con{s, t}:
      Nat.add(Ext2Slot.rec_len(s), Ext2Slots.total(t))

def Ext2Slots.names.keep(used: Bool, s: Ext2Slot, rest: List<&2, Ext2Name>) -> List<&2, Ext2Name>:
  match used:
    case True{}:
      match s:
        case Ext2Slot{i, r, f, n}:
          Con{Ext2Name{i, f, n}, rest}
    case False{}:
      rest

# the used entries, in order
def Ext2Slots.names(ss: List<&2, Ext2Slot>) -> List<&2, Ext2Name>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      Ext2Slots.names.keep(Ext2Slot.used(s), s, Ext2Slots.names(t))

def Ext2Slots.lookup.pick(hit: Bool, s: Ext2Slot, rest: Maybe<&2, Ext2Slot>) -> Maybe<&2, Ext2Slot>:
  match hit:
    case True{}:
      Some{s}
    case False{}:
      rest

# the used slot named name, if any
def Ext2Slots.lookup(ss: List<&2, Ext2Slot>, +name: B.Octets) -> Maybe<&2, Ext2Slot>:
  match ss:
    case Nil{}:
      None{}
    case Con{+s, t}:
      Ext2Slots.lookup.pick(Bool.and(Ext2Slot.used(s), B.Octets.is_eq(Ext2Slot.name(s), name)), s, Ext2Slots.lookup(t, name))

def Ext2Names.unname.pick(hit: Bool, x: Ext2Name, t: List<&2, Ext2Name>, rest: List<&2, Ext2Name>) -> List<&2, Ext2Name>:
  match hit:
    case True{}:
      t
    case False{}:
      Con{x, rest}

def Ext2Name.name(x: Ext2Name) -> B.Octets:
  match x:
    case Ext2Name{i, f, n}:
      n

# a listing without its first entry named name
def Ext2Names.unname(xs: List<&2, Ext2Name>, +name: B.Octets) -> List<&2, Ext2Name>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      Ext2Names.unname.pick(B.Octets.is_eq(Ext2Name.name(x), name), x, t, Ext2Names.unname(t, name))

def Ext2Slot.fits.pick(used: Bool, +s: Ext2Slot, +need: Nat) -> Bool:
  match used:
    case True{}:
      Nat.is_le(Nat.add(Ext2Slot.need(s), need), Ext2Slot.rec_len(s))
    case False{}:
      Nat.is_le(need, Ext2Slot.rec_len(s))

# Inserting: the first slot with room for the new entry

# whether slot s can take an entry needing need bytes
def Ext2Slot.fits(+s: Ext2Slot, +need: Nat) -> Bool:
  Ext2Slot.fits.pick(Ext2Slot.used(s), s, need)

def Ext2Slot.split.pick(used: Bool, +s: Ext2Slot, +new: Ext2Slot) -> List<&2, Ext2Slot>:
  match used:
    case True{}:
      [Ext2Slot.with_rec_len(s, Ext2Slot.need(s)), Ext2Slot.with_rec_len(new, Nat.sub(Ext2Slot.rec_len(s), Ext2Slot.need(s)))]
    case False{}:
      [Ext2Slot.with_rec_len(new, Ext2Slot.rec_len(s))]

# slot s holding the new entry too (it fits): an unused slot is replaced,
# a used one keeps the record its entry needs and the new entry the rest
def Ext2Slot.split(+s: Ext2Slot, +new: Ext2Slot) -> List<&2, Ext2Slot>:
  Ext2Slot.split.pick(Ext2Slot.used(s), s, new)

def Ext2Slots.cons_some(s: Ext2Slot, r: Maybe<&2, List<&2, Ext2Slot>>) -> Maybe<&2, List<&2, Ext2Slot>>:
  match r:
    case None{}:
      None{}
    case Some{xs}:
      Some{Con{s, xs}}

def Ext2Slots.insert.pick(fits: Bool, u: Bool, +s: Ext2Slot, t: List<&2, Ext2Slot>, +new: Ext2Slot, r: Maybe<&2, List<&2, Ext2Slot>>) -> Maybe<&2, List<&2, Ext2Slot>>:
  match fits:
    case True{}:
      Some{List.append(&2, Ext2Slot, Ext2Slot.split.pick(u, s, new), t)}
    case False{}:
      Ext2Slots.cons_some(s, r)

# slot s (used if u) taking the new entry if it fits, else the slots after it
def Ext2Slots.insert.at(+u: Bool, +s: Ext2Slot, t: List<&2, Ext2Slot>, +new: Ext2Slot, r: Maybe<&2, List<&2, Ext2Slot>>) -> Maybe<&2, List<&2, Ext2Slot>>:
  Ext2Slots.insert.pick(Ext2Slot.fits.pick(u, s, Ext2Slot.need(new)), u, s, t, new, r)

# the slots with the new entry in the first slot that fits it (None if none
# does); the new entry's own rec_len is ignored
def Ext2Slots.insert(ss: List<&2, Ext2Slot>, +new: Ext2Slot) -> Maybe<&2, List<&2, Ext2Slot>>:
  match ss:
    case Nil{}:
      None{}
    case Con{+s, +t}:
      Ext2Slots.insert.at(Ext2Slot.used(s), s, t, new, Ext2Slots.insert(t, new))

# Removing: the first used slot named name

def Ext2Slot.hit(+s: Ext2Slot, +name: B.Octets) -> Bool:
  Bool.and(Ext2Slot.used(s), B.Octets.is_eq(Ext2Slot.name(s), name))

def Ext2Slot.absorb(p: Ext2Slot, +s: Ext2Slot) -> Ext2Slot:
  match p:
    case Ext2Slot{i, r, f, n}:
      Ext2Slot{i, Nat.add(r, Ext2Slot.rec_len(s)), f, n}

def Ext2Slots.rm.pick(hit: Bool, +prev: Ext2Slot, +s: Ext2Slot, t: List<&2, Ext2Slot>, r: Maybe<&2, List<&2, Ext2Slot>>) -> Maybe<&2, List<&2, Ext2Slot>>:
  match hit:
    case True{}:
      Some{Con{Ext2Slot.absorb(prev, s), t}}
    case False{}:
      Ext2Slots.cons_some(prev, r)

# the slots after prev, with the first named name merged into the slot
# before it; the list comes back starting with prev
def Ext2Slots.rm(ss: List<&2, Ext2Slot>, +prev: Ext2Slot, +name: B.Octets) -> Maybe<&2, List<&2, Ext2Slot>>:
  match ss:
    case Nil{}:
      None{}
    case Con{+s, +t}:
      Ext2Slots.rm.pick(Ext2Slot.hit(s, name), prev, s, t, Ext2Slots.rm(t, s, name))

def Ext2Slots.remove.pick(hit: Bool, +s: Ext2Slot, +t: List<&2, Ext2Slot>, +name: B.Octets) -> Maybe<&2, List<&2, Ext2Slot>>:
  match hit:
    case True{}:
      Some{Con{Ext2Slot.unused(s), t}}
    case False{}:
      Ext2Slots.rm(t, s, name)

# the slots without the entry named name (None if there is none): its record
# goes to the slot before it, or (the first slot) it is marked unused
def Ext2Slots.remove(ss: List<&2, Ext2Slot>, +name: B.Octets) -> Maybe<&2, List<&2, Ext2Slot>>:
  match ss:
    case Nil{}:
      None{}
    case Con{+s, +t}:
      Ext2Slots.remove.pick(Ext2Slot.hit(s, name), s, t, name)

def Ext2Slot.target(s: Ext2Slot, +ino: U32, +ft: U32) -> Ext2Slot:
  match s:
    case Ext2Slot{i, r, f, n}:
      Ext2Slot{ino, r, ft, n}

def Ext2Slots.retarget.pick(hit: Bool, +s: Ext2Slot, t: List<&2, Ext2Slot>, +ino: U32, +ft: U32, r: Maybe<&2, List<&2, Ext2Slot>>) -> Maybe<&2, List<&2, Ext2Slot>>:
  match hit:
    case True{}:
      Some{Con{Ext2Slot.target(s, ino, ft), t}}
    case False{}:
      Ext2Slots.cons_some(s, r)

# the slots with the entry named name pointed at inode ino, type ft
def Ext2Slots.retarget(ss: List<&2, Ext2Slot>, +name: B.Octets, +ino: U32, +ft: U32) -> Maybe<&2, List<&2, Ext2Slot>>:
  match ss:
    case Nil{}:
      None{}
    case Con{+s, +t}:
      Ext2Slots.retarget.pick(Ext2Slot.hit(s, name), s, t, ino, ft, Ext2Slots.retarget(t, name, ino, ft))

# Blocks: slots read from and written to a block's bytes

def Ext2Slot.of(e: DR.Ext2Dirent) -> Ext2Slot:
  match e:
    case DR.Ext2Dirent{i, r, n, f, nm}:
      Ext2Slot{i, U32.to_nat(r), f, nm}

def Ext2Slot.dirent(s: Ext2Slot) -> DR.Ext2Dirent:
  match s:
    case Ext2Slot{i, r, f, +n}:
      DR.Ext2Dirent{i, U32.from_nat(r), U32.from_nat(B.Octets.len(n)), f, n}

def Ext2Slots.encode.go(ss: List<&2, Ext2Slot>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match ss:
    case Nil{}:
      List.reverse(&2, B.Octets, acc)
    case Con{s, t}:
      Ext2Slots.encode.go(t, Con{DR.Ext2Dirent.encode(Ext2Slot.dirent(s)), acc})

# the bytes of the slots (each entry padded to its record)
def Ext2Slots.encode(ss: List<&2, Ext2Slot>) -> B.Octets:
  B.Octets.concat(Ext2Slots.encode.go(ss, Nil{}))

# every slot of a block region of limit bytes (unused ones too), checked as
# the reader checks entries; ino and base for messages
def Ext2Slots.walk(fuel: Nat, st: DR.Ext2DirStep, +filetype: Bool, xs: B.Octets, +pos: Nat, +limit: Nat, +inodes: Nat, +ino: Nat, +base: Nat, acc: List<&2, Ext2Slot>) -> Result<&2, &2, E.Ext2Error, List<&2, Ext2Slot>>:
  match fuel st:
    case 0n _:
      Fail{E.Ext2BadDirent{ino, Nat.add(base, pos), "too many entries"}}
    case 1n+f DR.Ext2DirEnd{}:
      Done{List.reverse(&2, Ext2Slot, acc)}
    case 1n+f DR.Ext2DirBad{w}:
      Fail{E.Ext2BadDirent{ino, Nat.add(base, pos), w}}
    case 1n+f DR.Ext2DirEntry{e, +rec}:
      +ys = B.Octets.drop(rec, xs)
      +next = Nat.add(pos, rec)
      Ext2Slots.walk(f, DR.Ext2Dir.step(filetype, ys, next, limit, inodes), filetype, ys, next, limit, inodes, ino, base, Con{Ext2Slot.of(e), acc})

def Ext2Slots.parse(+filetype: Bool, +blk: B.Octets, +limit: Nat, +inodes: Nat, +ino: Nat, +base: Nat) -> Result<&2, &2, E.Ext2Error, List<&2, Ext2Slot>>:
  Ext2Slots.walk(Nat.add(Nat.div(limit, 8n), 2n), DR.Ext2Dir.step(filetype, blk, 0n, limit, inodes), filetype, blk, 0n, limit, inodes, ino, base, Nil{})

# Directories through the device

# what a directory edit does to the first block it applies to
type Ext2DirEdit is Data:
  # an entry put in the first slot with room
  Ext2DirAdd{slot: Ext2Slot}
  # the entry named name removed
  Ext2DirDel{name: B.Octets}
  # the entry named name pointed at another inode
  Ext2DirSet{name: B.Octets, inode: U32, file_type: U32}

# a block's slots after an edit, and the entry it took or changed
type Ext2Edited is Data:
  Ext2Edited{slots: List<&2, Ext2Slot>, old: Ext2Slot}

def Ext2Edited.with(m: Maybe<&2, List<&2, Ext2Slot>>, old: Ext2Slot) -> Maybe<&2, Ext2Edited>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{Ext2Edited{xs, old}}

def Ext2DirEdit.found(m: Maybe<&2, Ext2Slot>, +op: Ext2DirEdit, +ss: List<&2, Ext2Slot>) -> Maybe<&2, Ext2Edited>:
  match m op:
    case None{} _:
      None{}
    case Some{old} Ext2DirDel{n}:
      Ext2Edited.with(Ext2Slots.remove(ss, n), old)
    case Some{old} Ext2DirSet{n, i, f}:
      Ext2Edited.with(Ext2Slots.retarget(ss, n, i, f), old)
    case Some{old} Ext2DirAdd{s}:
      None{}

# the edit applied to a block's slots, if it applies there
def Ext2DirEdit.apply(+op: Ext2DirEdit, +ss: List<&2, Ext2Slot>) -> Maybe<&2, Ext2Edited>:
  match op:
    case Ext2DirAdd{+s}:
      Ext2Edited.with(Ext2Slots.insert(ss, s), s)
    case Ext2DirDel{+n}:
      Ext2DirEdit.found(Ext2Slots.lookup(ss, n), op, ss)
    case Ext2DirSet{+n, i, f}:
      Ext2DirEdit.found(Ext2Slots.lookup(ss, n), op, ss)

# the bytes of a block's entry region (limit bytes) and, with metadata_csum,
# the 12-byte tail
def Ext2DirW.limit(+fs: S.Ext2Fs) -> Nat:
  Nat.sub(S.Ext2Fs.block_size(fs), Nat.mul(12n, T.Ext2Meta.flag_bit(T.Ext2Meta.has_meta(fs))))

def Ext2DirW.tail.pick(on: Bool, +fs: S.Ext2Fs, +ino: Nat, +gen: U32, +body: B.Octets) -> B.Octets:
  match on:
    case True{}:
      +bs = S.Ext2Fs.block_size(fs)
      +c = K.Ext2Csum.dir_block(K.Ext2Csum.inode_seed(S.Ext2Fs.seed(fs), U32.from_nat(ino), gen), B.Octets.append(body, B.Octets.zeros(12n)), bs)
      B.Octets.append(body, B.Octets.append(B.Octets.of_list([0, 0, 0, 0, 12, 0, 0, 222]), B.Octets.le32(c)))
    case False{}:
      body

# a directory block holding the slots ss (which cover its region)
def Ext2DirW.block_bytes(+fs: S.Ext2Fs, +ino: Nat, +gen: U32, ss: List<&2, Ext2Slot>) -> B.Octets:
  Ext2DirW.tail.pick(T.Ext2Meta.has_meta(fs), fs, ino, gen, Ext2Slots.encode(ss))

def Ext2DirW.phys(m: Maybe<&2, Nat>, +ino: Nat, +k: Nat) -> Result<&2, &2, E.Ext2Error, Nat>:
  match m:
    case Some{p}:
      Done{p}
    case None{}:
      Fail{E.Ext2BadDirent{ino, k, "a hole in a directory"}}

def Ext2DirW.edit.store(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, m: Maybe<&2, Ext2Edited>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +gen: U32, +p: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, T.Ext2Out<Dv, Ext2Slot>>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{Ext2Edited{ss, old}}:
      Result.map(&2, &2, E.Ext2Error, Dv, Maybe<&2, T.Ext2Out<Dv, Ext2Slot>>, d2 => Some{T.Ext2Out{d2, old}}, T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, p, Ext2DirW.block_bytes(fs, ino, gen, ss)))

# the edit tried on block k of directory i
def Ext2DirW.edit.try(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +op: Ext2DirEdit, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +k: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, T.Ext2Out<Dv, Ext2Slot>>>:
  +ino = N.Ext2Inode.number_of(i)
  +bs = S.Ext2Fs.block_size(fs)
  do Result<&2, &2, E.Ext2Error, Maybe<&2, T.Ext2Out<Dv, Ext2Slot>>>:
    m : Maybe<&2, Nat> <- FL.Ext2File.map(~Dv, ~block_size, ~read_block, d, fs, i, k)
    +p : Nat <- Ext2DirW.phys(m, ino, k)
    +blk : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, p)
    x : Nat <- DR.Ext2Dir.region(S.Ext2Fs.verify_meta(fs), fs, i, blk, k)
    ss : List<&2, Ext2Slot> <- Ext2Slots.parse(S.Ext2Fs.has_incompat(fs, S.Ext2Super.incompat_filetype()), blk, Ext2DirW.limit(fs), S.Ext2Fs.inodes_count(fs), ino, Nat.mul(k, bs))
    Ext2DirW.edit.store(~Dv, ~block_size, ~read_block, ~write_block, Ext2DirEdit.apply(op, ss), d, fs, ino, N.Ext2Inode.generation(i), p)

# the edit applied to the first of count blocks from k on where it applies
# (r: what the block before answered)
def Ext2DirW.edit.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, count: Nat, r: Result<&2, &2, E.Ext2Error, Maybe<&2, T.Ext2Out<Dv, Ext2Slot>>>, +op: Ext2DirEdit, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +k: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, T.Ext2Out<Dv, Ext2Slot>>>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case _ Done{Some{out}}:
      Done{Some{out}}
    case 0n Done{None{}}:
      Done{None{}}
    case 1n+c Done{None{}}:
      Ext2DirW.edit.go(~Dv, ~block_size, ~read_block, ~write_block, c, Ext2DirW.edit.try(~Dv, ~block_size, ~read_block, ~write_block, op, d, fs, i, k), op, d, fs, i, Nat.add(k, 1n))

# whether a directory's record may be edited here: a directory, not
# hash-indexed, not inline
def Ext2DirW.check_dir(+i: N.Ext2Inode) -> Result<&2, &2, E.Ext2Error, Unit>:
  +ino = N.Ext2Inode.number_of(i)
  do Result<&2, &2, E.Ext2Error, Unit>:
    S.Ext2.require(N.Ext2Inode.is_dir(i), E.Ext2NotDir{ino})
    S.Ext2.require(Bool.not(N.Ext2Inode.has_flag(i, N.Ext2Inode.flag_index())), E.Ext2HtreeDir{ino})
    S.Ext2.require(Bool.not(N.Ext2Inode.has_flag(i, N.Ext2Inode.flag_inline_data())), E.Ext2InlineData{ino})

# The edit on a directory: its result (the entry taken or changed, if any
# block took the edit) and the directory's record, read once
type Ext2DirDone<-Dv: Data> is Data:
  Ext2DirDone{result: Maybe<&2, T.Ext2Out<Dv, Ext2Slot>>, raw: B.Octets}

def Ext2DirW.edit(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +op: Ext2DirEdit, +d: Dv, +fs: S.Ext2Fs, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Ext2DirDone<Dv>>:
  do Result<&2, &2, E.Ext2Error, Ext2DirDone<Dv>>:
    +raw : B.Octets <- IW.Ext2InodeW.read_raw(~Dv, ~block_size, ~read_block, d, fs, ino)
    +i : N.Ext2Inode = IW.Ext2IRaw.inode(fs, ino, raw)
    Ext2DirW.check_dir(i)
    r : Maybe<&2, T.Ext2Out<Dv, Ext2Slot>> <- Ext2DirW.edit.go(~Dv, ~block_size, ~read_block, ~write_block, FL.Ext2File.blocks_needed(fs, i), Done{None{}}, op, d, fs, i, 0n)
    return Ext2DirDone{r, raw}

# the file type an entry records for a kind (1 file, 2 directory, 7
# symbolic link, ...): with the filetype feature; 0 without it
def Ext2DirW.ftype(+fs: S.Ext2Fs, +code: U32) -> U32:
  U32.mul(code, Bool.to_u32(S.Ext2Fs.has_incompat(fs, S.Ext2Super.incompat_filetype())))

# a new directory's first block: "." (itself) and ".." (its parent)
def Ext2DirW.first_block(+fs: S.Ext2Fs, +ino: Nat, +gen: U32, +parent: Nat) -> B.Octets:
  +dt = Ext2DirW.ftype(fs, 2)
  Ext2DirW.block_bytes(fs, ino, gen, [Ext2Slot{U32.from_nat(ino), 12n, dt, B.Octets.of_string(".")}, Ext2Slot{U32.from_nat(parent), Nat.sub(Ext2DirW.limit(fs), 12n), dt, B.Octets.of_string("..")}])

# a directory's change and modification times set (its record written)
def Ext2DirW.touch(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, IW.Ext2IRaw.touch(raw, WO.Ext2WriteOptions.time(wo)))

def Ext2DirW.append.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, B.Octets>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match out:
    case T.Ext2Out{d2, raw2}:
      Ext2DirW.touch(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, wo, ino, raw2)

# a new block at the end of directory ino holding just the slot
def Ext2DirW.append(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets, +slot: Ext2Slot) -> Result<&2, &2, E.Ext2Error, Dv>:
  +i = IW.Ext2IRaw.inode(fs, ino, raw)
  +content = Ext2DirW.block_bytes(fs, ino, IW.Ext2IRaw.generation(raw), [Ext2Slot.with_rec_len(slot, Ext2DirW.limit(fs))])
  do Result<&2, &2, E.Ext2Error, Dv>:
    out : T.Ext2Out<Dv, B.Octets> <- FW.Ext2FileW.write(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, raw, Nat.mul(FL.Ext2File.blocks_needed(fs, i), S.Ext2Fs.block_size(fs)), content)
    Ext2DirW.append.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, ino)

def Ext2DirW.add.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, done: Ext2DirDone<Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +slot: Ext2Slot) -> Result<&2, &2, E.Ext2Error, Dv>:
  match done:
    case Ext2DirDone{Some{T.Ext2Out{d2, old}}, +raw}:
      Ext2DirW.touch(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, wo, ino, raw)
    case Ext2DirDone{None{}, +raw}:
      Ext2DirW.append(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, raw, slot)

# an entry (inode, file type, name) added to directory ino: in the first
# block with room, else in a new block at its end (the caller checks the
# name is not there yet)
def Ext2DirW.add(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +child: Nat, +ft: U32, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  +slot = {Ext2Slot{U32.from_nat(child), 0n, ft, name} : Ext2Slot}
  do Result<&2, &2, E.Ext2Error, Dv>:
    done : Ext2DirDone<Dv> <- Ext2DirW.edit(~Dv, ~block_size, ~read_block, ~write_block, Ext2DirAdd{slot}, d, fs, ino)
    Ext2DirW.add.fin(~Dv, ~block_size, ~read_block, ~write_block, done, d, fs, wo, ino, slot)

def Ext2DirW.changed(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, done: Ext2DirDone<Dv>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Slot>>:
  match done:
    case Ext2DirDone{Some{T.Ext2Out{d2, old}}, +raw}:
      Result.map(&2, &2, E.Ext2Error, Dv, T.Ext2Out<Dv, Ext2Slot>, d3 => T.Ext2Out{d3, old}, Ext2DirW.touch(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, wo, ino, raw))
    case Ext2DirDone{None{}, raw}:
      Fail{E.Ext2NotFound{B.Octets.to_string(name)}}

# the entry named name removed from directory ino: the entry it was
def Ext2DirW.remove(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Slot>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Slot>>:
    done : Ext2DirDone<Dv> <- Ext2DirW.edit(~Dv, ~block_size, ~read_block, ~write_block, Ext2DirDel{name}, d, fs, ino)
    Ext2DirW.changed(~Dv, ~block_size, ~read_block, ~write_block, done, fs, wo, ino, name)

# the entry named name in directory ino pointed at inode child, type ft:
# the entry it was
def Ext2DirW.retarget(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +name: B.Octets, +child: Nat, +ft: U32) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Slot>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Slot>>:
    done : Ext2DirDone<Dv> <- Ext2DirW.edit(~Dv, ~block_size, ~read_block, ~write_block, Ext2DirSet{name, U32.from_nat(child), ft}, d, fs, ino)
    Ext2DirW.changed(~Dv, ~block_size, ~read_block, ~write_block, done, fs, wo, ino, name)

def Ext2DirW.only_dots(es: List<&2, DR.Ext2Dirent>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, t}:
      +n = DR.Ext2Dirent.name(e)
      Bool.and(Bool.or(B.Octets.is_eq(n, B.Octets.of_string(".")), B.Octets.is_eq(n, B.Octets.of_string(".."))), Ext2DirW.only_dots(t))

# whether directory i holds nothing but "." and ".."
def Ext2DirW.is_empty(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext2Error, Bool>:
  Result.map(&2, &2, E.Ext2Error, List<&2, DR.Ext2Dirent>, Bool, es => Ext2DirW.only_dots(es), DR.Ext2Dir.entries(~Dv, ~block_size, ~read_block, d, fs, i))

# the file type code of an inode's kind (Ext2DirW.ftype maps it to what an
# entry records)
def Ext2DirW.code(k: N.Ext2Kind) -> U32:
  match k:
    case N.Ext2Regular{}:
      1
    case N.Ext2Directory{}:
      2
    case N.Ext2CharDev{}:
      3
    case N.Ext2BlockDev{}:
      4
    case N.Ext2Fifo{}:
      5
    case N.Ext2Socket{}:
      6
    case N.Ext2Symlink{}:
      7
    case N.Ext2Unknown{m}:
      0
