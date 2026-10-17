import Base
import ./mode.bend as M
import ./perms.bend as P
import ./acl.bend as A
import ./sticky.bend as S

def yn(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def show_err(r: Result<&2, &2, A.PermsError, A.PermsAcl>) -> String:
  match r:
    case Done{a}:
      "valid"
    case Fail{A.PermsAclNoUserObj{}}:
      "no ACL_USER_OBJ"
    case Fail{A.PermsAclNoGroupObj{}}:
      "no ACL_GROUP_OBJ"
    case Fail{A.PermsAclNoOther{}}:
      "no ACL_OTHER"
    case Fail{A.PermsAclDuplicateEntry{}}:
      "duplicate entry"
    case Fail{A.PermsAclDuplicateQualifier{}}:
      "duplicate qualifier"
    case Fail{A.PermsAclMaskRequired{}}:
      "ACL_MASK required"

def alice() -> P.PermsProc:
  P.PermsProc{1000, 1000, [4, 27], P.PermsPrivs.none()}

def root() -> P.PermsProc:
  P.PermsProc{0, 0, [], P.PermsPrivs.all()}

def reader() -> P.PermsProc:
  P.PermsProc{1001, 1001, [], P.PermsPrivs{False{}, True{}, False{}}}

def entry(t: A.PermsAclTag, q: U32, p: U32) -> A.PermsAclEntry:
  A.PermsAclEntry{t, q, M.PermsRwx.of_u32(p)}

# user::rw-, user:1001:rwx, group::r--, group:27:rw-, mask::r-x, other::---
def acl() -> List<&2, A.PermsAclEntry>:
  [entry(A.PermsAclUserObj{}, 0, 6), entry(A.PermsAclUser{}, 1001, 7), entry(A.PermsAclGroupObj{}, 0, 4), entry(A.PermsAclGroup{}, 27, 6), entry(A.PermsAclMask{}, 0, 5), entry(A.PermsAclOther{}, 0, 0)]

def acl_access(r: Result<&2, &2, A.PermsError, A.PermsAcl>, p: P.PermsProc, f: P.PermsFile, q: U32) -> String:
  match r:
    case Done{a}:
      yn(A.Perms.access_acl(a, p, f, M.PermsRwx.of_u32(q)))
    case Fail{e}:
      "invalid"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(M.Mode.show(M.Mode.create(438, 18)) ++ " " ++ M.Mode.show(M.Mode.create(511, 18)) ++ " " ++ U32.show(M.Mode.create(4095, 63)))
    # /etc/shadow: root:shadow 0640
    IO.print(yn(P.Perms.access_u32(alice(), P.PermsFile{0, 42, 416, False{}}, 4)) ++ " " ++ yn(P.Perms.access_u32(P.PermsProc{1000, 1000, [42], P.PermsPrivs.none()}, P.PermsFile{0, 42, 416, False{}}, 4)) ++ " " ++ yn(P.Perms.access_u32(root(), P.PermsFile{0, 42, 416, False{}}, 6)))
    # the owner class decides even when it grants less than the others: 0077
    IO.print(yn(P.Perms.access_u32(alice(), P.PermsFile{1000, 1000, 63, False{}}, 4)) ++ " " ++ yn(P.Perms.access_u32(alice(), P.PermsFile{1001, 4, 63, False{}}, 4)))
    # root may not execute a file with no execute bit, but may search any directory
    IO.print(yn(P.Perms.access_u32(root(), P.PermsFile{1000, 1000, 420, False{}}, 1)) ++ " " ++ yn(P.Perms.access_u32(root(), P.PermsFile{1000, 1000, 1, False{}}, 1)) ++ " " ++ yn(P.Perms.access_u32(root(), P.PermsFile{1000, 1000, 0, True{}}, 1)))
    # CAP_DAC_READ_SEARCH: read anything, search directories, but not write or execute files
    IO.print(yn(P.Perms.access_u32(reader(), P.PermsFile{0, 0, 0, False{}}, 4)) ++ " " ++ yn(P.Perms.access_u32(reader(), P.PermsFile{0, 0, 0, True{}}, 5)) ++ " " ++ yn(P.Perms.access_u32(reader(), P.PermsFile{0, 0, 0, False{}}, 6)) ++ " " ++ yn(P.Perms.access_u32(reader(), P.PermsFile{0, 0, 448, False{}}, 1)))
    IO.print(show_err(A.PermsAcl.of_entries(acl())))
    # the owner (rw-), the named user (rwx masked to r-x), the named group (rw- masked to r--), others
    IO.print(acl_access(A.PermsAcl.of_entries(acl()), P.PermsProc{1000, 1000, [], P.PermsPrivs.none()}, P.PermsFile{1000, 50, 384, False{}}, 6) ++ " " ++ acl_access(A.PermsAcl.of_entries(acl()), P.PermsProc{1001, 1001, [], P.PermsPrivs.none()}, P.PermsFile{1000, 50, 384, False{}}, 5) ++ " " ++ acl_access(A.PermsAcl.of_entries(acl()), P.PermsProc{1001, 1001, [], P.PermsPrivs.none()}, P.PermsFile{1000, 50, 384, False{}}, 2) ++ " " ++ acl_access(A.PermsAcl.of_entries(acl()), P.PermsProc{1002, 27, [], P.PermsPrivs.none()}, P.PermsFile{1000, 50, 384, False{}}, 4) ++ " " ++ acl_access(A.PermsAcl.of_entries(acl()), P.PermsProc{1002, 27, [], P.PermsPrivs.none()}, P.PermsFile{1000, 50, 384, False{}}, 2) ++ " " ++ acl_access(A.PermsAcl.of_entries(acl()), P.PermsProc{1003, 1003, [], P.PermsPrivs.none()}, P.PermsFile{1000, 50, 384, False{}}, 4))
    # the mode bits of that ACL: rw-r-x---
    IO.print(M.Mode.show(A.PermsAcl.to_mode(Result.default(&2, &2, A.PermsError, A.PermsAcl, A.PermsAcl.of_entries(acl()), A.PermsAcl.of_mode(0)), 0)))
    IO.print(show_err(A.PermsAcl.of_entries([entry(A.PermsAclUserObj{}, 0, 7), entry(A.PermsAclGroupObj{}, 0, 5)])) ++ ", " ++ show_err(A.PermsAcl.of_entries([entry(A.PermsAclUserObj{}, 0, 7), entry(A.PermsAclGroup{}, 4, 4), entry(A.PermsAclGroupObj{}, 0, 5), entry(A.PermsAclOther{}, 0, 0)])) ++ ", " ++ show_err(A.PermsAcl.of_entries([entry(A.PermsAclUserObj{}, 0, 7), entry(A.PermsAclUserObj{}, 0, 7)])))
    # /tmp (root, 01777): alice may delete her own file, not bob's; root may
    IO.print(yn(S.Perms.may_delete(alice(), P.PermsFile{0, 0, 1023, True{}}, P.PermsFile{1000, 1000, 420, False{}})) ++ " " ++ yn(S.Perms.may_delete(alice(), P.PermsFile{0, 0, 1023, True{}}, P.PermsFile{1001, 1001, 420, False{}})) ++ " " ++ yn(S.Perms.may_delete(root(), P.PermsFile{0, 0, 1023, True{}}, P.PermsFile{1001, 1001, 420, False{}})) ++ " " ++ yn(S.Perms.may_delete(alice(), P.PermsFile{0, 0, 511, True{}}, P.PermsFile{1001, 1001, 420, False{}})))

#|rw-r--r-- rwxr-xr-x 4032
#|no yes yes
#|no yes
#|no yes yes
#|yes yes no no
#|valid
#|yes yes no yes no no
#|rw-r-x---
#|no ACL_OTHER, ACL_MASK required, duplicate entry
#|yes no yes yes
