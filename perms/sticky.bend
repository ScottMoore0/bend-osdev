# bend-osdev-perms, sticky.bend: removing or renaming an entry of a
# directory (POSIX.1-2017 unlink() and rename(), and capabilities(7),
# CAP_FOWNER). The process needs write and search permission on the
# directory; if the directory is sticky (S_ISVTX), it must also own the file
# or the directory, or have CAP_FOWNER.
import Base
import ./mode.bend as M
import ./perms.bend as P

# the sticky rule alone
def Perms.sticky_ok(sticky: Bool, owns_file: Bool, owns_dir: Bool, fowner: Bool) -> Bool:
  match sticky:
    case False{}:
      True{}
    case True{}:
      Bool.or(owns_file, Bool.or(owns_dir, fowner))

# whether the process may remove (or rename) the entry for file from dir
def Perms.may_delete(+p: P.PermsProc, +dir: P.PermsFile, file: P.PermsFile) -> Bool:
  Bool.and(Perms.sticky_ok(M.Mode.sticky(P.PermsFile.mode(dir)), U32.is_eq(P.PermsProc.uid(p), P.PermsFile.uid(file)), U32.is_eq(P.PermsProc.uid(p), P.PermsFile.uid(dir)), P.PermsPrivs.fowner(P.PermsProc.privs(p))), P.Perms.access(p, dir, M.PermsRwx{False{}, True{}, True{}}))
