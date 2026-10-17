# bend-osdev-perms, acl.bend: POSIX.1e access ACLs, as acl(5) describes
# them: the entry tags, the rules for a valid ACL, the access check
# algorithm, and the correspondence between an ACL and the mode bits.
import Base
import ./mode.bend as M
import ./perms.bend as P

type PermsAclTag is Data:
  PermsAclUserObj{}
  PermsAclUser{}
  PermsAclGroupObj{}
  PermsAclGroup{}
  PermsAclMask{}
  PermsAclOther{}

# An entry: its tag, its qualifier (a user or group ID; ignored for the
# other tags) and its permissions
type PermsAclEntry is Data:
  PermsAclEntry{tag: PermsAclTag, qual: U32, perms: M.PermsRwx}

# A named entry (ACL_USER or ACL_GROUP)
type PermsAclId is Data:
  PermsAclId{qual: U32, perms: M.PermsRwx}

# An access ACL: ACL_USER_OBJ, the ACL_USER entries, ACL_GROUP_OBJ, the
# ACL_GROUP entries, the ACL_MASK entry if there is one, and ACL_OTHER
type PermsAcl is Data:
  PermsAcl{user_obj: M.PermsRwx, users: List<&2, PermsAclId>, group_obj: M.PermsRwx, groups: List<&2, PermsAclId>, mask: Maybe<&2, M.PermsRwx>, other: M.PermsRwx}

# Why a list of entries is not a valid ACL (acl(5), "VALID ACLs")
type PermsError is Data:
  PermsAclNoUserObj{}
  PermsAclNoGroupObj{}
  PermsAclNoOther{}
  PermsAclDuplicateEntry{}
  PermsAclDuplicateQualifier{}
  PermsAclMaskRequired{}

def PermsAcl.user_obj(a: PermsAcl) -> M.PermsRwx:
  match a:
    case PermsAcl{uo, us, go, gs, mk, ot}:
      uo

def PermsAcl.mask(a: PermsAcl) -> Maybe<&2, M.PermsRwx>:
  match a:
    case PermsAcl{uo, us, go, gs, mk, ot}:
      mk

# the ACL with its mask entry replaced
def PermsAcl.with_mask(a: PermsAcl, m: Maybe<&2, M.PermsRwx>) -> PermsAcl:
  match a:
    case PermsAcl{uo, us, go, gs, mk, ot}:
      PermsAcl{uo, us, go, gs, m, ot}

# the minimal ACL of a mode: the three base entries, from its permission bits
def PermsAcl.of_mode(+m: U32) -> PermsAcl:
  PermsAcl{M.Mode.owner(m), Nil{}, M.Mode.group(m), Nil{}, None{}, M.Mode.other(m)}

def PermsAcl.group_class(go: M.PermsRwx, mk: Maybe<&2, M.PermsRwx>) -> M.PermsRwx:
  match mk:
    case None{}:
      go
    case Some{m}:
      m

# the mode m with the permission bits the ACL implies (acl(5),
# "CORRESPONDENCE BETWEEN ACL ENTRIES AND FILE PERMISSION BITS"): the owner
# class is ACL_USER_OBJ, the group class ACL_MASK if there is one and
# ACL_GROUP_OBJ if not, the other class ACL_OTHER
def PermsAcl.to_mode(a: PermsAcl, m: U32) -> U32:
  match a:
    case PermsAcl{uo, us, go, gs, mk, ot}:
      M.Mode.with_perms(m, uo, PermsAcl.group_class(go, mk), ot)

# The entries, in the usual order

def PermsAcl.named(+t: PermsAclTag, xs: List<&2, PermsAclId>, rest: List<&2, PermsAclEntry>) -> List<&2, PermsAclEntry>:
  match xs:
    case Nil{}:
      rest
    case Con{PermsAclId{q, p}, xt}:
      Con{PermsAclEntry{t, q, p}, PermsAcl.named(t, xt, rest)}

def PermsAcl.mask_entry(mk: Maybe<&2, M.PermsRwx>, rest: List<&2, PermsAclEntry>) -> List<&2, PermsAclEntry>:
  match mk:
    case None{}:
      rest
    case Some{m}:
      Con{PermsAclEntry{PermsAclMask{}, 0, m}, rest}

def PermsAcl.to_entries(a: PermsAcl) -> List<&2, PermsAclEntry>:
  match a:
    case PermsAcl{uo, us, go, gs, mk, ot}:
      Con{PermsAclEntry{PermsAclUserObj{}, 0, uo}, PermsAcl.named(PermsAclUser{}, us, Con{PermsAclEntry{PermsAclGroupObj{}, 0, go}, PermsAcl.named(PermsAclGroup{}, gs, PermsAcl.mask_entry(mk, Con{PermsAclEntry{PermsAclOther{}, 0, ot}, Nil{}}))})}

# Reading a list of entries, checking acl(5)'s rules: exactly one
# ACL_USER_OBJ, ACL_GROUP_OBJ and ACL_OTHER; at most one ACL_MASK; unique
# qualifiers among the ACL_USER entries and among the ACL_GROUP entries; an
# ACL_MASK whenever there is an ACL_USER or ACL_GROUP entry.

type PermsAclAcc is Data:
  PermsAclAcc{uo: Maybe<&2, M.PermsRwx>, us: List<&2, PermsAclId>, go: Maybe<&2, M.PermsRwx>, gs: List<&2, PermsAclId>, mk: Maybe<&2, M.PermsRwx>, ot: Maybe<&2, M.PermsRwx>}

def PermsAcl.has_qual(xs: List<&2, PermsAclId>, +q: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{PermsAclId{h, p}, t}:
      Bool.or(U32.is_eq(h, q), PermsAcl.has_qual(t, q))

def PermsAcl.append(xs: List<&2, PermsAclId>, x: PermsAclId) -> List<&2, PermsAclId>:
  List.append(&2, PermsAclId, xs, Con{x, Nil{}})

# set a base entry that must not be there yet
def PermsAcl.once(old: Maybe<&2, M.PermsRwx>, p: M.PermsRwx) -> Result<&2, &2, PermsError, Maybe<&2, M.PermsRwx>>:
  match old:
    case None{}:
      Done{Some{p}}
    case Some{x}:
      Fail{PermsAclDuplicateEntry{}}

def PermsAcl.add_named(dup: Bool, xs: List<&2, PermsAclId>, x: PermsAclId) -> Result<&2, &2, PermsError, List<&2, PermsAclId>>:
  match dup:
    case True{}:
      Fail{PermsAclDuplicateQualifier{}}
    case False{}:
      Done{PermsAcl.append(xs, x)}

def PermsAcl.set_uo(r: Result<&2, &2, PermsError, Maybe<&2, M.PermsRwx>>, a: PermsAclAcc) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match r a:
    case Fail{e} a:
      Fail{e}
    case Done{v} PermsAclAcc{uo, us, go, gs, mk, ot}:
      Done{PermsAclAcc{v, us, go, gs, mk, ot}}

def PermsAcl.set_go(r: Result<&2, &2, PermsError, Maybe<&2, M.PermsRwx>>, a: PermsAclAcc) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match r a:
    case Fail{e} a:
      Fail{e}
    case Done{v} PermsAclAcc{uo, us, go, gs, mk, ot}:
      Done{PermsAclAcc{uo, us, v, gs, mk, ot}}

def PermsAcl.set_mk(r: Result<&2, &2, PermsError, Maybe<&2, M.PermsRwx>>, a: PermsAclAcc) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match r a:
    case Fail{e} a:
      Fail{e}
    case Done{v} PermsAclAcc{uo, us, go, gs, mk, ot}:
      Done{PermsAclAcc{uo, us, go, gs, v, ot}}

def PermsAcl.set_ot(r: Result<&2, &2, PermsError, Maybe<&2, M.PermsRwx>>, a: PermsAclAcc) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match r a:
    case Fail{e} a:
      Fail{e}
    case Done{v} PermsAclAcc{uo, us, go, gs, mk, ot}:
      Done{PermsAclAcc{uo, us, go, gs, mk, v}}

def PermsAcl.set_us(r: Result<&2, &2, PermsError, List<&2, PermsAclId>>, a: PermsAclAcc) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match r a:
    case Fail{e} a:
      Fail{e}
    case Done{v} PermsAclAcc{uo, us, go, gs, mk, ot}:
      Done{PermsAclAcc{uo, v, go, gs, mk, ot}}

def PermsAcl.set_gs(r: Result<&2, &2, PermsError, List<&2, PermsAclId>>, a: PermsAclAcc) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match r a:
    case Fail{e} a:
      Fail{e}
    case Done{v} PermsAclAcc{uo, us, go, gs, mk, ot}:
      Done{PermsAclAcc{uo, us, go, v, mk, ot}}

def PermsAcl.step.go(t: PermsAclTag, +q: U32, p: M.PermsRwx, acc: PermsAclAcc, uo: Maybe<&2, M.PermsRwx>, +us: List<&2, PermsAclId>, go: Maybe<&2, M.PermsRwx>, +gs: List<&2, PermsAclId>, mk: Maybe<&2, M.PermsRwx>, ot: Maybe<&2, M.PermsRwx>) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match t:
    case PermsAclUserObj{}:
      PermsAcl.set_uo(PermsAcl.once(uo, p), acc)
    case PermsAclUser{}:
      PermsAcl.set_us(PermsAcl.add_named(PermsAcl.has_qual(us, q), us, PermsAclId{q, p}), acc)
    case PermsAclGroupObj{}:
      PermsAcl.set_go(PermsAcl.once(go, p), acc)
    case PermsAclGroup{}:
      PermsAcl.set_gs(PermsAcl.add_named(PermsAcl.has_qual(gs, q), gs, PermsAclId{q, p}), acc)
    case PermsAclMask{}:
      PermsAcl.set_mk(PermsAcl.once(mk, p), acc)
    case PermsAclOther{}:
      PermsAcl.set_ot(PermsAcl.once(ot, p), acc)

def PermsAcl.step(e: PermsAclEntry, a: PermsAclAcc) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match e a:
    case PermsAclEntry{t, +q, p} PermsAclAcc{+uo, +us, +go, +gs, +mk, +ot}:
      PermsAcl.step.go(t, q, p, PermsAclAcc{uo, us, go, gs, mk, ot}, uo, us, go, gs, mk, ot)

def PermsAcl.scan(xs: List<&2, PermsAclEntry>, r: Result<&2, &2, PermsError, PermsAclAcc>) -> Result<&2, &2, PermsError, PermsAclAcc>:
  match xs:
    case Nil{}:
      r
    case Con{e, t}:
      match r:
        case Fail{err}:
          Fail{err}
        case Done{a}:
          PermsAcl.scan(t, PermsAcl.step(e, a))

def PermsAcl.is_nil(xs: List<&2, PermsAclId>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def PermsAcl.finish.mask(named: Bool, a: PermsAcl) -> Result<&2, &2, PermsError, PermsAcl>:
  match named a:
    case False{} a:
      Done{a}
    case True{} PermsAcl{uo, us, go, gs, None{}, ot}:
      Fail{PermsAclMaskRequired{}}
    case True{} PermsAcl{uo, us, go, gs, Some{m}, ot}:
      Done{PermsAcl{uo, us, go, gs, Some{m}, ot}}

def PermsAcl.finish(a: PermsAclAcc) -> Result<&2, &2, PermsError, PermsAcl>:
  match a:
    case PermsAclAcc{None{}, us, go, gs, mk, ot}:
      Fail{PermsAclNoUserObj{}}
    case PermsAclAcc{Some{uo}, us, None{}, gs, mk, ot}:
      Fail{PermsAclNoGroupObj{}}
    case PermsAclAcc{Some{uo}, us, Some{go}, gs, mk, None{}}:
      Fail{PermsAclNoOther{}}
    case PermsAclAcc{Some{uo}, +us, Some{go}, +gs, mk, Some{ot}}:
      PermsAcl.finish.mask(Bool.not(Bool.and(PermsAcl.is_nil(us), PermsAcl.is_nil(gs))), PermsAcl{uo, us, go, gs, mk, ot})

def PermsAcl.finish.r(r: Result<&2, &2, PermsError, PermsAclAcc>) -> Result<&2, &2, PermsError, PermsAcl>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      PermsAcl.finish(a)

# the ACL these entries make, or why they make none: in a duplicate entry or
# qualifier, the first found in list order; then a missing ACL_USER_OBJ,
# ACL_GROUP_OBJ, ACL_OTHER; then a missing ACL_MASK
def PermsAcl.of_entries(xs: List<&2, PermsAclEntry>) -> Result<&2, &2, PermsError, PermsAcl>:
  PermsAcl.finish.r(PermsAcl.scan(xs, Done{PermsAclAcc{None{}, Nil{}, None{}, Nil{}, None{}, None{}}}))

def PermsAcl.valid.r(r: Result<&2, &2, PermsError, PermsAcl>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{a}:
      True{}

def PermsAcl.valid(xs: List<&2, PermsAclEntry>) -> Bool:
  PermsAcl.valid.r(PermsAcl.of_entries(xs))

# The access check (acl(5), "ACCESS CHECK ALGORITHM")

def PermsAcl.find_user.pick(hit: Bool, p: M.PermsRwx, rest: Maybe<&2, M.PermsRwx>) -> Maybe<&2, M.PermsRwx>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      rest

def PermsAcl.find_user(xs: List<&2, PermsAclId>, +u: U32) -> Maybe<&2, M.PermsRwx>:
  match xs:
    case Nil{}:
      None{}
    case Con{PermsAclId{q, p}, t}:
      PermsAcl.find_user.pick(U32.is_eq(q, u), p, PermsAcl.find_user(t, u))

# whether a named group entry matches the process
def PermsAcl.group_match(xs: List<&2, PermsAclId>, +p: P.PermsProc) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{PermsAclId{q, r}, t}:
      Bool.or(P.Perms.in_group(p, q), PermsAcl.group_match(t, p))

# whether a named group entry that matches the process contains q
def PermsAcl.group_covers(xs: List<&2, PermsAclId>, +p: P.PermsProc, +q: M.PermsRwx) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{PermsAclId{g, r}, t}:
      Bool.or(Bool.and(P.Perms.in_group(p, g), M.PermsRwx.covers(r, q)), PermsAcl.group_covers(t, p, q))

def PermsAcl.mask_covers(mk: Maybe<&2, M.PermsRwx>, q: M.PermsRwx) -> Bool:
  match mk:
    case None{}:
      True{}
    case Some{m}:
      M.PermsRwx.covers(m, q)

# acl(5)'s algorithm, on the decisions it takes in turn:
#   owner: the process's user ID is the file's owner: ACL_USER_OBJ decides;
#   user: the ACL_USER entry naming the process's user ID: it and the mask
#     decide;
#   gmatch: the process's group ID or a supplementary group is the file's
#     group or names an ACL_GROUP entry: with a mask, the mask and any
#     matching group entry (gany) decide; without, ACL_GROUP_OBJ decides;
#   else ACL_OTHER decides.
def PermsAcl.decide(owner: Bool, user: Maybe<&2, M.PermsRwx>, gmatch: Bool, gany: Bool, +q: M.PermsRwx, uo: M.PermsRwx, go: M.PermsRwx, mk: Maybe<&2, M.PermsRwx>, ot: M.PermsRwx) -> Bool:
  match owner:
    case True{}:
      M.PermsRwx.covers(uo, q)
    case False{}:
      match user:
        case Some{up}:
          Bool.and(M.PermsRwx.covers(up, q), PermsAcl.mask_covers(mk, q))
        case None{}:
          match gmatch:
            case True{}:
              match mk:
                case Some{m}:
                  Bool.and(M.PermsRwx.covers(m, q), gany)
                case None{}:
                  M.PermsRwx.covers(go, q)
            case False{}:
              M.PermsRwx.covers(ot, q)

# whether the ACL grants q to the process, for a file owned by fuid:fgid
def PermsAcl.check(a: PermsAcl, +p: P.PermsProc, +f: P.PermsFile, +q: M.PermsRwx) -> Bool:
  match a:
    case PermsAcl{+uo, us, +go, +gs, mk, ot}:
      +ingroup = P.Perms.in_group(p, P.PermsFile.gid(f))
      PermsAcl.decide(U32.is_eq(P.PermsProc.uid(p), P.PermsFile.uid(f)), PermsAcl.find_user(us, P.PermsProc.uid(p)), Bool.or(PermsAcl.group_match(gs, p), ingroup), Bool.or(Bool.and(ingroup, M.PermsRwx.covers(go, q)), PermsAcl.group_covers(gs, p, q)), q, uo, go, mk, ot)

# whether the process may have the access req to a file with this access
# ACL: privileges first, as for the mode bits (P.Perms.needed), then the ACL
def Perms.access_acl(a: PermsAcl, +p: P.PermsProc, +f: P.PermsFile, req: M.PermsRwx) -> Bool:
  PermsAcl.check(a, p, f, P.Perms.needed(p, f, req))
