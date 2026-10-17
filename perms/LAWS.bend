# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input (every process, file, mode, umask, ACL and
# request):
#   the umask never adds a permission bit;
#   the owner class is chosen whenever the process's user ID is the file's
#     owner, and then only the owner bits (or ACL_USER_OBJ) decide;
#   a minimal ACL (the three base entries made from the mode) gives exactly
#     the answer the mode bits give, for every request; it is a valid ACL, and
#     its mode bits are the mode's;
#   a mask entry never grants more than the same ACL with a mask of rwx (that
#     is, than the named user and group entries themselves);
#   the documented overrides: CAP_DAC_READ_SEARCH grants read on any file and
#     search on any directory, CAP_DAC_OVERRIDE grants read and write, but
#     execute on a regular file needs at least one execute bit;
#   deletion: never without write and search permission on the directory; in
#     a directory that is not sticky, or by the file's owner, exactly that.
#
# Vectors: umask 022 on 0666 and 0777, and ACL validity cases from acl(5).
import Base
import ./mode.bend as M
import ./perms.bend as P
import ./acl.bend as A
import ./sticky.bend as S

# umask(2): "permissions in the umask are turned off from the mode argument"
law umask_never_adds:
  for +mode: U32
  for +umask: U32
  {U32.and(M.Mode.create(mode, umask), U32.not(mode)) == 0 : U32}

law umask_022_file:
  {M.Mode.create(438, 18) == 420 : U32}

law umask_022_dir:
  {M.Mode.create(511, 18) == 493 : U32}

# the set-ID and sticky bits pass through the umask
law umask_keeps_special:
  {M.Mode.create(4095, 511) == 3584 : U32}

law owner_class:
  for +p: P.PermsProc
  for +f: P.PermsFile
  for h: {U32.is_eq(P.PermsProc.uid(p), P.PermsFile.uid(f)) == True{} : Bool}
  {P.Perms.class(p, f) == P.PermsOwner{} : P.PermsClass}

law owner_bits_decide:
  for +p: P.PermsProc
  for +f: P.PermsFile
  for +req: M.PermsRwx
  for h: {U32.is_eq(P.PermsProc.uid(p), P.PermsFile.uid(f)) == True{} : Bool}
  {P.Perms.access(p, f, req) == M.PermsRwx.covers(M.Mode.owner(P.PermsFile.mode(f)), P.Perms.needed(p, f, req)) : Bool}

law acl_owner_decides:
  for +a: A.PermsAcl
  for +p: P.PermsProc
  for +f: P.PermsFile
  for +req: M.PermsRwx
  for h: {U32.is_eq(P.PermsProc.uid(p), P.PermsFile.uid(f)) == True{} : Bool}
  {A.Perms.access_acl(a, p, f, req) == M.PermsRwx.covers(A.PermsAcl.user_obj(a), P.Perms.needed(p, f, req)) : Bool}

law minimal_acl_is_mode:
  for +p: P.PermsProc
  for +f: P.PermsFile
  for +req: M.PermsRwx
  {A.Perms.access_acl(A.PermsAcl.of_mode(P.PermsFile.mode(f)), p, f, req) == P.Perms.access(p, f, req) : Bool}

law minimal_acl_valid:
  for +m: U32
  {A.PermsAcl.of_entries(A.PermsAcl.to_entries(A.PermsAcl.of_mode(m))) == Done{A.PermsAcl.of_mode(m)} : Result<&2, &2, A.PermsError, A.PermsAcl>}

law minimal_acl_mode_bits:
  for +m: U32
  {A.PermsAcl.to_mode(A.PermsAcl.of_mode(m), m) == m : U32}

law mask_only_restricts:
  for +a: A.PermsAcl
  for +m: M.PermsRwx
  for +p: P.PermsProc
  for +f: P.PermsFile
  for +req: M.PermsRwx
  {Bool.or(Bool.not(A.Perms.access_acl(A.PermsAcl.with_mask(a, Some{m}), p, f, req)), A.Perms.access_acl(A.PermsAcl.with_mask(a, Some{M.PermsRwx.all()}), p, f, req)) == True{} : Bool}

# path_resolution(7): CAP_DAC_READ_SEARCH "grants read and search permission
# on directories, and read permission on ordinary files"
law read_search_reads:
  for +u: U32
  for +g: U32
  for +gs: List<&2, U32>
  for +ovr: Bool
  for +fo: Bool
  for +f: P.PermsFile
  {P.Perms.access(P.PermsProc{u, g, gs, P.PermsPrivs{ovr, True{}, fo}}, f, M.PermsRwx{True{}, False{}, False{}}) == True{} : Bool}

law read_search_searches:
  for +u: U32
  for +g: U32
  for +gs: List<&2, U32>
  for +ovr: Bool
  for +fo: Bool
  for +fu: U32
  for +fg: U32
  for +m: U32
  {P.Perms.access(P.PermsProc{u, g, gs, P.PermsPrivs{ovr, True{}, fo}}, P.PermsFile{fu, fg, m, True{}}, M.PermsRwx{True{}, False{}, True{}}) == True{} : Bool}

# CAP_DAC_OVERRIDE "overrides all permission checking, but grants execute
# permission only when at least one of the file's three execute permission
# bits is set"
law override_read_write:
  for +u: U32
  for +g: U32
  for +gs: List<&2, U32>
  for +rs: Bool
  for +fo: Bool
  for +f: P.PermsFile
  {P.Perms.access(P.PermsProc{u, g, gs, P.PermsPrivs{True{}, rs, fo}}, f, M.PermsRwx{True{}, True{}, False{}}) == True{} : Bool}

law exec_needs_an_exec_bit:
  for +p: P.PermsProc
  for +fu: U32
  for +fg: U32
  for +m: U32
  for h: {M.Mode.any_exec(m) == False{} : Bool}
  {P.Perms.access(p, P.PermsFile{fu, fg, m, False{}}, M.PermsRwx{False{}, False{}, True{}}) == False{} : Bool}

# Deletion
law delete_needs_write_search:
  for +p: P.PermsProc
  for +d: P.PermsFile
  for +f: P.PermsFile
  {Bool.or(Bool.not(S.Perms.may_delete(p, d, f)), P.Perms.access(p, d, M.PermsRwx{False{}, True{}, True{}})) == True{} : Bool}

law delete_not_sticky:
  for +p: P.PermsProc
  for +d: P.PermsFile
  for +f: P.PermsFile
  for h: {M.Mode.sticky(P.PermsFile.mode(d)) == False{} : Bool}
  {S.Perms.may_delete(p, d, f) == P.Perms.access(p, d, M.PermsRwx{False{}, True{}, True{}}) : Bool}

law delete_by_owner:
  for +p: P.PermsProc
  for +d: P.PermsFile
  for +f: P.PermsFile
  for h: {U32.is_eq(P.PermsProc.uid(p), P.PermsFile.uid(f)) == True{} : Bool}
  {S.Perms.may_delete(p, d, f) == P.Perms.access(p, d, M.PermsRwx{False{}, True{}, True{}}) : Bool}

# ACL validity (acl(5), "VALID ACLs")

law acl_mask_required:
  {A.PermsAcl.of_entries([A.PermsAclEntry{A.PermsAclUserObj{}, 0, M.PermsRwx.all()}, A.PermsAclEntry{A.PermsAclUser{}, 1000, M.PermsRwx.all()}, A.PermsAclEntry{A.PermsAclGroupObj{}, 0, M.PermsRwx.none()}, A.PermsAclEntry{A.PermsAclOther{}, 0, M.PermsRwx.none()}]) == Fail{A.PermsAclMaskRequired{}} : Result<&2, &2, A.PermsError, A.PermsAcl>}

law acl_duplicate_user:
  {A.PermsAcl.of_entries([A.PermsAclEntry{A.PermsAclUserObj{}, 0, M.PermsRwx.all()}, A.PermsAclEntry{A.PermsAclUser{}, 1000, M.PermsRwx.all()}, A.PermsAclEntry{A.PermsAclUser{}, 1000, M.PermsRwx.none()}, A.PermsAclEntry{A.PermsAclGroupObj{}, 0, M.PermsRwx.none()}, A.PermsAclEntry{A.PermsAclMask{}, 0, M.PermsRwx.all()}, A.PermsAclEntry{A.PermsAclOther{}, 0, M.PermsRwx.none()}]) == Fail{A.PermsAclDuplicateQualifier{}} : Result<&2, &2, A.PermsError, A.PermsAcl>}

law acl_no_other:
  {A.PermsAcl.of_entries([A.PermsAclEntry{A.PermsAclUserObj{}, 0, M.PermsRwx.all()}, A.PermsAclEntry{A.PermsAclGroupObj{}, 0, M.PermsRwx.none()}]) == Fail{A.PermsAclNoOther{}} : Result<&2, &2, A.PermsError, A.PermsAcl>}

law acl_two_masks:
  {A.PermsAcl.of_entries([A.PermsAclEntry{A.PermsAclUserObj{}, 0, M.PermsRwx.all()}, A.PermsAclEntry{A.PermsAclMask{}, 0, M.PermsRwx.all()}, A.PermsAclEntry{A.PermsAclGroupObj{}, 0, M.PermsRwx.none()}, A.PermsAclEntry{A.PermsAclMask{}, 0, M.PermsRwx.none()}, A.PermsAclEntry{A.PermsAclOther{}, 0, M.PermsRwx.none()}]) == Fail{A.PermsAclDuplicateEntry{}} : Result<&2, &2, A.PermsError, A.PermsAcl>}

# a named user with rw-, masked to r--: read is granted, write is not
law acl_mask_limits_user:
  {A.Perms.access_acl(A.PermsAcl{M.PermsRwx.all(), [A.PermsAclId{1000, M.PermsRwx{True{}, True{}, False{}}}], M.PermsRwx.none(), [], Some{M.PermsRwx{True{}, False{}, False{}}}, M.PermsRwx.none()}, P.PermsProc{1000, 1000, [], P.PermsPrivs.none()}, P.PermsFile{0, 0, 448, False{}}, M.PermsRwx{True{}, True{}, False{}}) == False{} : Bool}

# Witnesses: every hypothesis of the laws above holds for some input, so no
# law is vacuous.

# the process's user ID is the file's owner (owner_class, owner_bits_decide,
# acl_owner_decides, delete_by_owner)
law witness_owner:
  {U32.is_eq(P.PermsProc.uid(P.PermsProc{1000, 1000, [4], P.PermsPrivs.none()}), P.PermsFile.uid(P.PermsFile{1000, 50, 420, False{}})) == True{} : Bool}

# a mode with no execute bit: 0644 (exec_needs_an_exec_bit)
law witness_no_exec_bit:
  {M.Mode.any_exec(420) == False{} : Bool}

# a directory that is not sticky: 0755 (delete_not_sticky)
law witness_not_sticky:
  {M.Mode.sticky(P.PermsFile.mode(P.PermsFile{0, 0, 493, True{}})) == False{} : Bool}
