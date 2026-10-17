# bend-osdev-ext2: a read-only reader of ext2, ext3 and ext4 filesystems
# over blockdev's device interface. The entry file: opening a filesystem,
# and paths (lookup, listing, reading, symbolic links).
#
# Specifications: "The Second Extended File System: Internal Layout" (Dave
# Poirier) and the ext4 disk-layout documentation (kernel.org,
# Documentation/filesystems/ext4). See README.md for the files and the API.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./options.bend as O
import ./super.bend as S
import ./inode.bend as N
import ./file.bend as FL
import ./dir.bend as DR

# the filesystem on a device, checked, with these options
def Ext2.open(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +opts: O.Ext2Options) -> Result<&2, &2, E.Ext2Error, S.Ext2Fs>:
  S.Ext2Fs.open(~Dv, ~block_size, ~read_block, d, opts)

# the root directory's inode number
def Ext2.root_ino() -> Nat:
  2n

def Ext2.root(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, fs, Ext2.root_ino())

# Paths: byte strings, components separated by "/" (47); empty components
# are skipped, "." and ".." are the directories' own entries

def Ext2Path.flush(cur: List<&2, U32>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match cur:
    case Nil{}:
      acc
    case Con{h, t}:
      Con{B.Octets.of_list(List.reverse(&2, U32, Con{h, t})), acc}

def Ext2Path.split.pick(slash: Bool, h: U32, cur: List<&2, U32>, acc: List<&2, B.Octets>) -> List<&2, U32> & List<&2, B.Octets>:
  match slash:
    case True{}:
      (Nil{}, Ext2Path.flush(cur, acc))
    case False{}:
      (Con{h, cur}, acc)

def Ext2Path.split(xs: List<&2, U32>, st: List<&2, U32> & List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      (cur, acc) = st
      List.reverse(&2, B.Octets, Ext2Path.flush(cur, acc))
    case Con{+h, t}:
      (cur, acc) = st
      Ext2Path.split(t, Ext2Path.split.pick(U32.is_eq(h, 47), h, cur, acc))

# the components of a path
def Ext2Path.components(o: B.Octets) -> List<&2, B.Octets>:
  Ext2Path.split(B.Octets.to_list(o), (Nil{}, Nil{}))

def Ext2Path.is_absolute(+o: B.Octets) -> Bool:
  U32.is_eq(Maybe.default(&2, U32, B.Octets.at(o, 0n), 0), 47)

# Resolution, one step at a time

type Ext2PathStep is Data:
  Ext2PathAt{dir: N.Ext2Inode, rest: List<&2, B.Octets>, hops: Nat}
  Ext2PathLink{link: N.Ext2Inode, dir: N.Ext2Inode, rest: List<&2, B.Octets>, hops: Nat}
  Ext2PathDone{inode: N.Ext2Inode}
  Ext2PathErr{e: E.Ext2Error}

def Ext2Path.found(m: Maybe<&2, DR.Ext2Dirent>, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, DR.Ext2Dirent>:
  match m:
    case Some{e}:
      Done{e}
    case None{}:
      Fail{E.Ext2NotFound{B.Octets.to_string(name)}}

def Ext2Path.is_nil(xs: List<&2, B.Octets>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# a symbolic link that must be followed: with hops left, follow it; with
# none, refuse (Ext2SymlinkInPath when the options follow no links at all)
def Ext2Path.link.pick(hops: Nat, never: Bool, child: N.Ext2Inode, cur: N.Ext2Inode, rest: List<&2, B.Octets>) -> Ext2PathStep:
  match hops never:
    case 0n True{}:
      Ext2PathErr{E.Ext2SymlinkInPath{N.Ext2Inode.number_of(child)}}
    case 0n False{}:
      Ext2PathErr{E.Ext2SymlinkLoop{}}
    case 1n+h _:
      Ext2PathLink{child, cur, rest, 1n+h}

def Ext2Path.classify.follow(keep: Bool, hops: Nat, never: Bool, child: N.Ext2Inode, cur: N.Ext2Inode, rest: List<&2, B.Octets>) -> Ext2PathStep:
  match keep:
    case True{}:
      Ext2PathDone{child}
    case False{}:
      Ext2Path.link.pick(hops, never, child, cur, rest)

def Ext2Path.classify.pick(link: Bool, +rest: List<&2, B.Octets>, +follow_last: Bool, +hops: Nat, +never: Bool, child: N.Ext2Inode, cur: N.Ext2Inode) -> Ext2PathStep:
  match link:
    case True{}:
      Ext2Path.classify.follow(Bool.and(Ext2Path.is_nil(rest), Bool.not(follow_last)), hops, never, child, cur, rest)
    case False{}:
      Ext2PathAt{child, rest, hops}

# the step after finding child in directory cur, with the components rest
# still to go: a symbolic link is followed when more components follow it,
# or when it is the last and follow_last is set; otherwise it is the answer
def Ext2Path.classify(+child: N.Ext2Inode, cur: N.Ext2Inode, rest: List<&2, B.Octets>, +hops: Nat, +follow_last: Bool, +never: Bool) -> Ext2PathStep:
  Ext2Path.classify.pick(N.Ext2Inode.is_symlink(child), rest, follow_last, hops, never, child, cur)

def Ext2Path.after_link.pick(abs: Bool, +root: N.Ext2Inode, +dir: N.Ext2Inode, comps: List<&2, B.Octets>, rest: List<&2, B.Octets>, +h: Nat) -> Ext2PathStep:
  match abs:
    case True{}:
      Ext2PathAt{root, List.append(&2, B.Octets, comps, rest), h}
    case False{}:
      Ext2PathAt{dir, List.append(&2, B.Octets, comps, rest), h}

# where a link's target leads: from the root if it is absolute, else from
# the directory holding the link, its components before the rest
def Ext2Path.after_link(+target: B.Octets, +root: N.Ext2Inode, +dir: N.Ext2Inode, rest: List<&2, B.Octets>, hops: Nat) -> Ext2PathStep:
  Ext2Path.after_link.pick(Ext2Path.is_absolute(target), root, dir, Ext2Path.components(target), rest, Nat.sub(hops, 1n))

def Ext2Path.walk(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, fuel: Nat, st: Ext2PathStep, +d: Dv, +fs: S.Ext2Fs, +root: N.Ext2Inode, +follow_last: Bool, +never: Bool) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  match fuel st:
    case 0n _:
      Fail{E.Ext2SymlinkLoop{}}
    case 1n+f Ext2PathDone{i}:
      Done{i}
    case 1n+f Ext2PathErr{e}:
      Fail{e}
    case 1n+f Ext2PathAt{cur, Nil{}, h}:
      Done{cur}
    case 1n+f Ext2PathAt{+cur, Con{+c, rest}, +h}:
      do Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
        m : Maybe<&2, DR.Ext2Dirent> <- DR.Ext2Dir.find(~Dv, ~block_size, ~read_block, d, fs, cur, c)
        e : DR.Ext2Dirent <- Ext2Path.found(m, c)
        child : N.Ext2Inode <- N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, fs, U32.to_nat(DR.Ext2Dirent.inode(e)))
        Ext2Path.walk(~Dv, ~block_size, ~read_block, f, Ext2Path.classify(child, cur, rest, h, follow_last, never), d, fs, root, follow_last, never)
    case 1n+f Ext2PathLink{+link, dir, rest, h}:
      do Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
        target : B.Octets <- FL.Ext2File.readlink(~Dv, ~block_size, ~read_block, d, fs, link)
        Ext2Path.walk(~Dv, ~block_size, ~read_block, f, Ext2Path.after_link(target, root, dir, rest, h), d, fs, root, follow_last, never)

def Ext2Path.resolve(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets, +follow_last: Bool) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  +hops = O.Ext2Options.symlink_hops(S.Ext2Fs.opts(fs))
  +comps = Ext2Path.components(path)
  do Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
    +root : N.Ext2Inode <- Ext2.root(~Dv, ~block_size, ~read_block, d, fs)
    Ext2Path.walk(~Dv, ~block_size, ~read_block, Nat.add(Nat.add(List.length(&2, B.Octets, comps), Nat.mul(hops, 4100n)), 2n), Ext2PathAt{root, comps, hops}, d, fs, root, Bool.and(follow_last, Nat.is_lt(0n, hops)), Nat.is_eq(hops, 0n))

# The path interface

# the inode a path names, from the root. Symbolic links are followed as the
# options' symlink_hops allow (0, the default: a link in the middle of a
# path is refused with Ext2SymlinkInPath, and a link at the end is
# answered itself); a final link is followed too when hops are allowed.
def Ext2.lookup(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  Ext2Path.resolve(~Dv, ~block_size, ~read_block, d, fs, path, True{})

# the same, but a final symbolic link is answered itself, never followed
# (as lstat does)
def Ext2.lookup_link(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  Ext2Path.resolve(~Dv, ~block_size, ~read_block, d, fs, path, False{})

# the used entries of the directory a path names
def Ext2.list(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, List<&2, DR.Ext2Dirent>>:
  do Result<&2, &2, E.Ext2Error, List<&2, DR.Ext2Dirent>>:
    i : N.Ext2Inode <- Ext2.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    DR.Ext2Dir.entries(~Dv, ~block_size, ~read_block, d, fs, i)

# the whole content of the file a path names (small files: see
# Ext2File.read_all; stream larger ones with Ext2File.start and next)
def Ext2.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  do Result<&2, &2, E.Ext2Error, B.Octets>:
    i : N.Ext2Inode <- Ext2.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    FL.Ext2File.read_all(~Dv, ~block_size, ~read_block, d, fs, i)

# the target of the symbolic link a path names
def Ext2.readlink(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  do Result<&2, &2, E.Ext2Error, B.Octets>:
    i : N.Ext2Inode <- Ext2.lookup_link(~Dv, ~block_size, ~read_block, d, fs, path)
    FL.Ext2File.readlink(~Dv, ~block_size, ~read_block, d, fs, i)
