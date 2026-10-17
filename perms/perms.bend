# bend-osdev-perms: Unix file permission checks, as POSIX.1-2017 (XBD 4.5
# "File Access Permissions") and path_resolution(7) describe them.
#
# A process asks for read, write and execute (search) permission on a file.
# Its class is chosen first: owner if its (filesystem) user ID is the file's
# owner, else group if its (filesystem) group ID or a supplementary group is
# the file's group, else other; the class's three mode bits must contain the
# request. Privileges (CAP_DAC_OVERRIDE, CAP_DAC_READ_SEARCH) grant parts of a
# request on their own; what they do not grant, the mode bits must.
#
# mode.bend: permission triples, mode bits and the umask. acl.bend: POSIX.1e
# access ACLs. sticky.bend: deletion in a sticky directory.
import Base
import ./mode.bend as M

# Which privileges the process has. The usual source is its effective
# capability set (bend-osdev-caps): CAP_DAC_OVERRIDE, CAP_DAC_READ_SEARCH and
# CAP_FOWNER; a process whose filesystem user ID is 0 has all three.
type PermsPrivs is Data:
  PermsPrivs{dac_override: Bool, dac_read_search: Bool, fowner: Bool}

def PermsPrivs.none() -> PermsPrivs:
  PermsPrivs{False{}, False{}, False{}}

def PermsPrivs.all() -> PermsPrivs:
  PermsPrivs{True{}, True{}, True{}}

def PermsPrivs.fowner(pv: PermsPrivs) -> Bool:
  match pv:
    case PermsPrivs{o, r, f}:
      f

# A process: filesystem user and group IDs, supplementary groups, privileges
type PermsProc is Data:
  PermsProc{uid: U32, gid: U32, groups: List<&2, U32>, privs: PermsPrivs}

# A file: owner, group, mode, and whether it is a directory
type PermsFile is Data:
  PermsFile{uid: U32, gid: U32, mode: U32, is_dir: Bool}

type PermsClass is Data:
  PermsOwner{}
  PermsGroup{}
  PermsOther{}

def PermsProc.uid(p: PermsProc) -> U32:
  match p:
    case PermsProc{u, g, gs, pv}:
      u

def PermsProc.gid(p: PermsProc) -> U32:
  match p:
    case PermsProc{u, g, gs, pv}:
      g

def PermsProc.groups(p: PermsProc) -> List<&2, U32>:
  match p:
    case PermsProc{u, g, gs, pv}:
      gs

def PermsProc.privs(p: PermsProc) -> PermsPrivs:
  match p:
    case PermsProc{u, g, gs, pv}:
      pv

def PermsFile.uid(f: PermsFile) -> U32:
  match f:
    case PermsFile{u, g, m, d}:
      u

def PermsFile.gid(f: PermsFile) -> U32:
  match f:
    case PermsFile{u, g, m, d}:
      g

def PermsFile.mode(f: PermsFile) -> U32:
  match f:
    case PermsFile{u, g, m, d}:
      m

def PermsFile.is_dir(f: PermsFile) -> Bool:
  match f:
    case PermsFile{u, g, m, d}:
      d

def Perms.member(xs: List<&2, U32>, +g: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(U32.is_eq(h, g), Perms.member(t, g))

# whether the process is in group g: its group ID or a supplementary group
def Perms.in_group(p: PermsProc, +g: U32) -> Bool:
  match p:
    case PermsProc{u, pg, gs, pv}:
      Bool.or(U32.is_eq(pg, g), Perms.member(gs, g))

def Perms.class.go(owner: Bool, group: Bool) -> PermsClass:
  match owner:
    case True{}:
      PermsOwner{}
    case False{}:
      match group:
        case True{}:
          PermsGroup{}
        case False{}:
          PermsOther{}

# the class whose mode bits apply
def Perms.class(+p: PermsProc, +f: PermsFile) -> PermsClass:
  Perms.class.go(U32.is_eq(PermsProc.uid(p), PermsFile.uid(f)), Perms.in_group(p, PermsFile.gid(f)))

# the mode bits of a class
def Perms.class_bits(c: PermsClass, m: U32) -> M.PermsRwx:
  match c:
    case PermsOwner{}:
      M.Mode.owner(m)
    case PermsGroup{}:
      M.Mode.group(m)
    case PermsOther{}:
      M.Mode.other(m)

def Perms.exec_grant(is_dir: Bool, ovr: Bool, rs: Bool, any_exec: Bool) -> Bool:
  match is_dir:
    case True{}:
      Bool.or(ovr, rs)
    case False{}:
      Bool.and(ovr, any_exec)

# What privileges grant, whatever the mode bits (path_resolution(7)):
# CAP_DAC_OVERRIDE grants read and write, and execute when at least one
# execute bit is set (search, on a directory, always); CAP_DAC_READ_SEARCH
# grants read, and search on a directory.
def Perms.privileged(pv: PermsPrivs, is_dir: Bool, +m: U32) -> M.PermsRwx:
  match pv:
    case PermsPrivs{+ovr, +rs, fo}:
      M.PermsRwx{Bool.or(ovr, rs), ovr, Perms.exec_grant(is_dir, ovr, rs, M.Mode.any_exec(m))}

# the part of the request that the file's permission bits (or ACL) must grant
def Perms.needed(p: PermsProc, +f: PermsFile, req: M.PermsRwx) -> M.PermsRwx:
  M.PermsRwx.minus(req, Perms.privileged(PermsProc.privs(p), PermsFile.is_dir(f), PermsFile.mode(f)))

def Perms.mode_check(owner: Bool, group: Bool, m: U32, q: M.PermsRwx) -> Bool:
  match owner:
    case True{}:
      M.PermsRwx.covers(M.Mode.owner(m), q)
    case False{}:
      match group:
        case True{}:
          M.PermsRwx.covers(M.Mode.group(m), q)
        case False{}:
          M.PermsRwx.covers(M.Mode.other(m), q)

# whether the process may have the access req to the file, by its mode bits
def Perms.access(+p: PermsProc, +f: PermsFile, req: M.PermsRwx) -> Bool:
  Perms.mode_check(U32.is_eq(PermsProc.uid(p), PermsFile.uid(f)), Perms.in_group(p, PermsFile.gid(f)), PermsFile.mode(f), Perms.needed(p, f, req))

# the same, with access(2)'s mode (R_OK = 4, W_OK = 2, X_OK = 1)
def Perms.access_u32(p: PermsProc, f: PermsFile, req: U32) -> Bool:
  Perms.access(p, f, M.PermsRwx.of_u32(req))
