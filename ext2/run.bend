# bend-osdev-ext2: the writer's operations, checked. Ext2Op.run does an
# operation (ops.bend) and then checks its result as the write options ask
# (wopts.bend's check level) before answering it:
#
#   local  the bitmaps agree with the free counts (Ext2Fsck.counts), and the
#          operation did what it promised: a write reads back as written; a
#          truncate leaves the size asked for; creating, linking, removing
#          or renaming an entry leaves every other entry of the directories
#          it changed as it was, and the entry there (or gone)
#   full   all that, and the whole filesystem consistent (Ext2Fsck.full:
#          no block owned twice, every bitmap exact, every link count the
#          number of entries naming the inode)
#
# A result that fails its check is refused (Ext2CheckFailed): the caller's
# device is as it was. The laws (LAWS.bend) about Ext2Op.run hold for every
# input because of these checks.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./super.bend as S
import ./inode.bend as N
import ./file.bend as FL
import ./dir.bend as DR
import ./ext2.bend as X
import ./dirw.bend as DW
import ./fsck.bend as K
import ./wopts.bend as WO
import ./ops.bend as P

# The promises

def Ext2Guard.names(es: List<&2, DR.Ext2Dirent>, acc: List<&2, DW.Ext2Name>) -> List<&2, DW.Ext2Name>:
  match es:
    case Nil{}:
      List.reverse(&2, DW.Ext2Name, acc)
    case Con{DR.Ext2Dirent{i, r, n, f, nm}, t}:
      Ext2Guard.names(t, Con{DW.Ext2Name{i, f, nm}, acc})

# the entries (inode, type, name) of the directory a path names
def Ext2Guard.listing(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, List<&2, DW.Ext2Name>>:
  Result.map(&2, &2, E.Ext2Error, List<&2, DR.Ext2Dirent>, List<&2, DW.Ext2Name>, es => Ext2Guard.names(es, Nil{}), X.Ext2.list(~Dv, ~block_size, ~read_block, d, fs, path))

def Ext2Guard.without(ns: List<&2, B.Octets>, xs: List<&2, DW.Ext2Name>) -> List<&2, DW.Ext2Name>:
  match ns:
    case Nil{}:
      xs
    case Con{+n, t}:
      Ext2Guard.without(t, DW.Ext2Names.unname(xs, n))

def Ext2Guard.name_eq(a: DW.Ext2Name, b: DW.Ext2Name) -> Bool:
  match a b:
    case DW.Ext2Name{i, f, n} DW.Ext2Name{j, g, m}:
      Bool.and(U32.is_eq(i, j), Bool.and(U32.is_eq(f, g), B.Octets.is_eq(n, m)))

def Ext2Guard.eq(xs: List<&2, DW.Ext2Name>, ys: List<&2, DW.Ext2Name>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Ext2Guard.name_eq(x, y), Ext2Guard.eq(xt, yt))
    case _ _:
      False{}

# whether directory path holds, apart from the names ns, the same entries
# in d2 as in d, in the same order
def Ext2Guard.kept(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +d2: Dv, +fs: S.Ext2Fs, +path: B.Octets, +ns: List<&2, B.Octets>) -> Result<&2, &2, E.Ext2Error, Bool>:
  do Result<&2, &2, E.Ext2Error, Bool>:
    before : List<&2, DW.Ext2Name> <- Ext2Guard.listing(~Dv, ~block_size, ~read_block, d, fs, path)
    after : List<&2, DW.Ext2Name> <- Ext2Guard.listing(~Dv, ~block_size, ~read_block, d2, fs, path)
    return Ext2Guard.eq(Ext2Guard.without(ns, after), Ext2Guard.without(ns, before))

def Ext2Guard.is_some(m: Maybe<&2, DR.Ext2Dirent>) -> Bool:
  match m:
    case Some{e}:
      True{}
    case None{}:
      False{}

# whether directory path has an entry named name
def Ext2Guard.has(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, Bool>:
  do Result<&2, &2, E.Ext2Error, Bool>:
    i : N.Ext2Inode <- X.Ext2.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    m : Maybe<&2, DR.Ext2Dirent> <- DR.Ext2Dir.find(~Dv, ~block_size, ~read_block, d, fs, i, name)
    return Ext2Guard.is_some(m)

# whether the file at path holds data from byte off
def Ext2Guard.reads_back(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets, +off: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, Bool>:
  do Result<&2, &2, E.Ext2Error, Bool>:
    i : N.Ext2Inode <- X.Ext2.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    got : B.Octets <- FL.Ext2File.read_range(~Dv, ~block_size, ~read_block, d, fs, i, off, B.Octets.len(data))
    return B.Octets.is_eq(got, data)

# whether the file at path is size bytes long
def Ext2Guard.size_is(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets, +size: Nat) -> Result<&2, &2, E.Ext2Error, Bool>:
  Result.map(&2, &2, E.Ext2Error, N.Ext2Inode, Bool, i => Nat.is_eq(N.Ext2Inode.size_nat(i), size), X.Ext2.lookup(~Dv, ~block_size, ~read_block, d, fs, path))

def Ext2Guard.both(a: Result<&2, &2, E.Ext2Error, Bool>, b: Result<&2, &2, E.Ext2Error, Bool>) -> Result<&2, &2, E.Ext2Error, Bool>:
  Result.bind(&2, &2, E.Ext2Error, Bool, Bool, a, x => Result.map(&2, &2, E.Ext2Error, Bool, Bool, y => Bool.and(x, y), b))

def Ext2Guard.not(r: Result<&2, &2, E.Ext2Error, Bool>) -> Result<&2, &2, E.Ext2Error, Bool>:
  Result.map(&2, &2, E.Ext2Error, Bool, Bool, x => Bool.not(x), r)

# an entry made (made) or removed at a path: the other entries of its
# directory kept, and the entry there or gone
def Ext2Guard.entry(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, made: Bool, +d: Dv, +d2: Dv, +fs: S.Ext2Fs, pp: P.Ext2PathParts) -> Result<&2, &2, E.Ext2Error, Bool>:
  match made pp:
    case True{} P.Ext2PathParts{+parent, +name}:
      Ext2Guard.both(Ext2Guard.kept(~Dv, ~block_size, ~read_block, d, d2, fs, parent, [name]), Ext2Guard.has(~Dv, ~block_size, ~read_block, d2, fs, parent, name))
    case False{} P.Ext2PathParts{+parent, +name}:
      Ext2Guard.both(Ext2Guard.kept(~Dv, ~block_size, ~read_block, d, d2, fs, parent, [name]), Ext2Guard.not(Ext2Guard.has(~Dv, ~block_size, ~read_block, d2, fs, parent, name)))

def Ext2Guard.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, made: Bool, +d: Dv, +d2: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, Bool>:
  Result.bind(&2, &2, E.Ext2Error, P.Ext2PathParts, Bool, P.Ext2W.split(path), pp => Ext2Guard.entry(~Dv, ~block_size, ~read_block, made, d, d2, fs, pp))

def Ext2Guard.moved(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +d2: Dv, +fs: S.Ext2Fs, a: P.Ext2PathParts, b: P.Ext2PathParts) -> Result<&2, &2, E.Ext2Error, Bool>:
  match a b:
    case P.Ext2PathParts{+pa, +na} P.Ext2PathParts{+pb, +nb}:
      +ns = {[na, nb] : List<&2, B.Octets>}
      Ext2Guard.both(Ext2Guard.kept(~Dv, ~block_size, ~read_block, d, d2, fs, pa, ns), Ext2Guard.both(Ext2Guard.kept(~Dv, ~block_size, ~read_block, d, d2, fs, pb, ns), Ext2Guard.has(~Dv, ~block_size, ~read_block, d2, fs, pb, nb)))

# a rename: both directories keep their other entries, and the new name is
# there
def Ext2Guard.rename(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +d2: Dv, +fs: S.Ext2Fs, +from: B.Octets, +to: B.Octets) -> Result<&2, &2, E.Ext2Error, Bool>:
  do Result<&2, &2, E.Ext2Error, Bool>:
    a : P.Ext2PathParts <- P.Ext2W.split(from)
    b : P.Ext2PathParts <- P.Ext2W.split(to)
    Ext2Guard.moved(~Dv, ~block_size, ~read_block, d, d2, fs, a, b)

def Ext2Guard.appended(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +d2: Dv, +fs: S.Ext2Fs, +path: B.Octets, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, Bool>:
  do Result<&2, &2, E.Ext2Error, Bool>:
    i : N.Ext2Inode <- X.Ext2.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    Ext2Guard.reads_back(~Dv, ~block_size, ~read_block, d2, fs, path, N.Ext2Inode.size_nat(i), data)

# whether an operation did what it promised (d before it, d2 after)
def Ext2Guard.promise(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, op: P.Ext2Op, +d: Dv, +d2: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, Bool>:
  match op:
    case P.Ext2OpCreate{p, m}:
      Ext2Guard.at(~Dv, ~block_size, ~read_block, True{}, d, d2, fs, p)
    case P.Ext2OpMkdir{p, m}:
      Ext2Guard.at(~Dv, ~block_size, ~read_block, True{}, d, d2, fs, p)
    case P.Ext2OpSymlink{p, t}:
      Ext2Guard.at(~Dv, ~block_size, ~read_block, True{}, d, d2, fs, p)
    case P.Ext2OpLink{t, p}:
      Ext2Guard.at(~Dv, ~block_size, ~read_block, True{}, d, d2, fs, p)
    case P.Ext2OpUnlink{p}:
      Ext2Guard.at(~Dv, ~block_size, ~read_block, False{}, d, d2, fs, p)
    case P.Ext2OpRmdir{p}:
      Ext2Guard.at(~Dv, ~block_size, ~read_block, False{}, d, d2, fs, p)
    case P.Ext2OpRename{a, b}:
      Ext2Guard.rename(~Dv, ~block_size, ~read_block, d, d2, fs, a, b)
    case P.Ext2OpWrite{p, o, x}:
      Ext2Guard.reads_back(~Dv, ~block_size, ~read_block, d2, fs, p, o, x)
    case P.Ext2OpAppend{p, x}:
      Ext2Guard.appended(~Dv, ~block_size, ~read_block, d, d2, fs, p, x)
    case P.Ext2OpTruncate{p, n}:
      Ext2Guard.size_is(~Dv, ~block_size, ~read_block, d2, fs, p, n)

def Ext2Guard.kept_promise(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, op: P.Ext2Op, +d: Dv, +d2: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, Unit>:
  do Result<&2, &2, E.Ext2Error, Unit>:
    b : Bool <- Ext2Guard.promise(~Dv, ~block_size, ~read_block, op, d, d2, fs)
    S.Ext2.require(b, E.Ext2CheckFailed{"the operation did not do what it promised"})

# the checks the level asks of the result d2 of op on d
def Ext2Guard.post(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, level: WO.Ext2CheckLevel, op: P.Ext2Op, +d: Dv, +d2: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, Unit>:
  match level:
    case WO.Ext2CheckNone{}:
      Done{Unit{}}
    case WO.Ext2CheckLocal{}:
      do Result<&2, &2, E.Ext2Error, Unit>:
        K.Ext2Fsck.counts(~Dv, ~block_size, ~read_block, d2, fs)
        Ext2Guard.kept_promise(~Dv, ~block_size, ~read_block, op, d, d2, fs)
    case WO.Ext2CheckFull{}:
      do Result<&2, &2, E.Ext2Error, Unit>:
        K.Ext2Fsck.counts(~Dv, ~block_size, ~read_block, d2, fs)
        Ext2Guard.kept_promise(~Dv, ~block_size, ~read_block, op, d, d2, fs)
        K.Ext2Fsck.full(~Dv, ~block_size, ~read_block, d2, fs)

# a result checked: a device that fails the check k is refused
def Ext2Op.confirm(-Dv: Data, p: Result<&2, &2, E.Ext2Error, Unit>, d2: Dv) -> Result<&2, &2, E.Ext2Error, Dv>:
  match p:
    case Done{u}:
      Done{d2}
    case Fail{e}:
      Fail{e}

def Ext2Op.checked(-Dv: Data, r: Result<&2, &2, E.Ext2Error, Dv>, k: Dv -> Result<&2, &2, E.Ext2Error, Unit>) -> Result<&2, &2, E.Ext2Error, Dv>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+d2}:
      Ext2Op.confirm(Dv, k(d2), d2)

# an operation done and its result checked as the options ask: the device
# after it, or why it was refused
def Ext2Op.run(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +op: P.Ext2Op, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  Ext2Op.checked(Dv, P.Ext2Op.apply(~Dv, ~block_size, ~read_block, ~write_block, op, d, fs, wo), d2 => Ext2Guard.post(~Dv, ~block_size, ~read_block, WO.Ext2WriteOptions.check(wo), op, d, d2, fs))
