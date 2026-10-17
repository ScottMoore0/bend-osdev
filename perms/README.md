# bend-osdev-perms

Unix file permission checks, written from the public specifications:

* POSIX.1-2017, XBD 4.5 "File Access Permissions" (the owner, group and other
  classes; appropriate privileges and execute), `<sys/stat.h>` (the mode
  bits), and `unlink()` / `rename()` (the sticky directory, `S_ISVTX`);
* path_resolution(7), "Permissions" and "Bypassing permission checks:
  superuser and capabilities" (`CAP_DAC_OVERRIDE`, `CAP_DAC_READ_SEARCH`,
  and that execute needs at least one execute bit); capabilities(7) for
  `CAP_FOWNER` and the sticky bit;
* umask(2): the umask applied to a creation mode;
* acl(5): POSIX.1e access ACLs, their entry tags (`ACL_USER_OBJ`,
  `ACL_USER`, `ACL_GROUP_OBJ`, `ACL_GROUP`, `ACL_MASK`, `ACL_OTHER`), the
  rules for a valid ACL, the access check algorithm, and the correspondence
  between ACL entries and the mode bits.

The package is policy logic, so its point is its laws: properties of the
checks for every input, proved in `PROOF.bend` (see Laws).

## Files

| File | Holds |
|---|---|
| `perms.bend` | processes (`PermsProc`), files (`PermsFile`), privileges (`PermsPrivs`), the class choice and the mode-bit check (`Perms.access`) |
| `mode.bend` | permission triples (`PermsRwx`), the fields of a mode, the umask (`Mode.create`) |
| `acl.bend` | access ACLs (`PermsAcl`), reading and validating a list of entries (`PermsAcl.of_entries`), the ACL check (`Perms.access_acl`) |
| `sticky.bend` | removing an entry from a directory (`Perms.may_delete`) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/proof.py`, `gen/wordgen.py` | the generator of `PROOF.bend`'s generated regions (the umask lemma, the cases of `rwx.covers_all`, and the proof of `exec_needs_an_exec_bit`, between `# BEGIN GENERATED` and `# END GENERATED` lines); `python3 gen/proof.py` rewrites them, `--check` checks they are up to date |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh`, `ref/.gitignore` | the differential test (`cases.bend` and `expected.txt` are generated, and ignored) |

## API

`mode.bend`:

| Def | Meaning |
|---|---|
| `PermsRwx{r, w, x}`, `PermsRwx.none`, `PermsRwx.all`, `.r`, `.w`, `.x` | a permission triple (x is search, for a directory) |
| `PermsRwx.covers(p, q)` | every permission of q is in p |
| `PermsRwx.minus(q, g)`, `PermsRwx.of_u32`, `PermsRwx.to_u32`, `PermsRwx.show` | q less g; access(2)'s `R_OK = 4, W_OK = 2, X_OK = 1`; `"r-x"` |
| `Mode.owner`, `Mode.group`, `Mode.other`, `Mode.setuid`, `Mode.setgid`, `Mode.sticky`, `Mode.any_exec` | the fields of a mode (a `U32`) |
| `Mode.with_perms(m, o, g, t)`, `Mode.of_perms(o, g, t)`, `Mode.show` | the nine permission bits replaced; built; `"rwxr-x---"` |
| `Mode.create(mode, umask)` | the mode a file is created with: `mode & 07777 & ~(umask & 0777)` |

`perms.bend`:

| Def | Meaning |
|---|---|
| `PermsPrivs{dac_override, dac_read_search, fowner}`, `PermsPrivs.none`, `PermsPrivs.all`, `PermsPrivs.fowner` | the privileges that bypass checks |
| `PermsProc{uid, gid, groups, privs}` | a process: filesystem user and group IDs, supplementary groups, privileges |
| `PermsFile{uid, gid, mode, is_dir}` | a file |
| `PermsClass` (`PermsOwner`, `PermsGroup`, `PermsOther`), `Perms.class(p, f)`, `Perms.class_bits` | the class whose bits apply |
| `Perms.in_group(p, g)` | g is the process's group ID or a supplementary group |
| `Perms.privileged(privs, is_dir, mode)`, `Perms.needed(p, f, req)` | what privileges grant on their own; the part of a request left to the permission bits |
| `Perms.access(p, f, req)`, `Perms.access_u32(p, f, mask)` | the check by mode bits |

`acl.bend`:

| Def | Meaning |
|---|---|
| `PermsAclTag` (`PermsAclUserObj`, `PermsAclUser`, `PermsAclGroupObj`, `PermsAclGroup`, `PermsAclMask`, `PermsAclOther`), `PermsAclEntry{tag, qual, perms}` | an entry |
| `PermsAcl{user_obj, users, group_obj, groups, mask, other}`, `PermsAclId{qual, perms}` | an access ACL |
| `PermsAcl.of_entries(xs)` | `Result<&2, &2, PermsError, PermsAcl>`: the ACL, or `PermsAclNoUserObj`, `PermsAclNoGroupObj`, `PermsAclNoOther`, `PermsAclDuplicateEntry`, `PermsAclDuplicateQualifier`, `PermsAclMaskRequired` |
| `PermsAcl.valid(xs)`, `PermsAcl.to_entries(a)` | validity; the entries in the usual order |
| `PermsAcl.of_mode(m)`, `PermsAcl.to_mode(a, m)` | the minimal ACL of a mode; the mode bits an ACL implies |
| `PermsAcl.with_mask(a, mask)`, `PermsAcl.user_obj`, `PermsAcl.mask` | |
| `PermsAcl.check(a, p, f, q)`, `Perms.access_acl(a, p, f, req)` | acl(5)'s algorithm; the check with privileges first |

`sticky.bend`: `Perms.sticky_ok(sticky, owns_file, owns_dir, fowner)` and
`Perms.may_delete(p, dir, file)`: write and search permission on the
directory, and in a sticky directory, ownership of the file or the
directory, or `CAP_FOWNER`.

### How the specifications are read

* A request (any of r, w, x) is granted when every requested permission is
  granted. The privileges of path_resolution(7) each grant some permissions
  outright: `CAP_DAC_OVERRIDE` read and write, and execute when the mode has
  an execute bit (search on a directory always); `CAP_DAC_READ_SEARCH` read,
  and search on a directory. The rest of the request (`Perms.needed`) must be
  granted by the mode bits or the ACL. So, for example, read-and-write with
  only `CAP_DAC_READ_SEARCH` needs the write bit.
* The user and group IDs are the filesystem IDs (path_resolution(7): Linux
  checks the fsuid and fsgid); the caller passes them.
* acl(5)'s step for groups: a matching entry must contain all requested
  permissions on its own; with a mask, the mask must too. Without a mask,
  only `ACL_GROUP_OBJ` is consulted, as acl(5) says (a valid ACL with named
  group entries always has a mask).
* The execute override looks at the mode's three execute bits (for a file
  with an ACL, the group bits are the mask's, per acl(5)).
* Not modelled: default ACLs and their inheritance, read-only mounts,
  immutable files, `CAP_FOWNER` on the other operations it covers.

## Extension points

* **Privileges are a parameter record**, `PermsPrivs`, set by the caller. The
  usual source is the effective capability set: with bend-osdev-caps,
  `PermsPrivs{CapSet.has(e, 1), CapSet.has(e, 2), CapSet.has(e, 3)}`
  (`CAP_DAC_OVERRIDE`, `CAP_DAC_READ_SEARCH`, `CAP_FOWNER`). `PermsPrivs.all`
  is a filesystem user ID of 0; `PermsPrivs.none` an ordinary process. This
  package does not import caps, so it serves systems with other privilege
  models.
* **What a privilege grants** is one def, `Perms.privileged`; the class
  choice is `Perms.class` and the decision `Perms.mode_check`; the ACL
  algorithm is `PermsAcl.decide`, on the decisions `PermsAcl.check` computes.
  Each can be replaced alone; the laws say which properties must survive.
* **Types are open**: `PermsRwx`, `PermsProc`, `PermsFile`, `PermsAcl` and
  the entries are plain records.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer). **For every
input** (process, file, mode, umask, ACL, request):

* the umask never adds a permission bit: `Mode.create(mode, umask) & ~mode == 0`;
* the owner class is chosen whenever the process's user ID is the file's
  owner, and then the owner bits alone decide (and, with an ACL,
  `ACL_USER_OBJ` alone);
* a minimal ACL (the three base entries made from the mode) gives exactly the
  mode bits' answer for every request and process; it is valid
  (`of_entries(to_entries(of_mode(m))) == Done{of_mode(m)}`), and its mode
  bits are the mode's;
* a mask never grants more: whatever the ACL and mask, the answer with that
  mask implies the answer with a mask of rwx (the named entries unmasked);
* `CAP_DAC_READ_SEARCH` grants read of any file and search of any
  directory; `CAP_DAC_OVERRIDE` grants read and write of any file; with no
  execute bit, execute of a regular file is refused whatever the privileges;
* deletion never succeeds without write and search permission on the
  directory, and in a directory that is not sticky, or by the file's owner,
  it is exactly that permission.

**Witnesses:** every hypothesis of a law holds for some input, so no law is
vacuous: vector laws show a process that owns a file (the owner laws and
`delete_by_owner`), a mode with no execute bit (`exec_needs_an_exec_bit`),
and a directory that is not sticky (`delete_not_sticky`).

**Vectors:** umask 022 on 0666 and 0777, the special bits through a full
umask, four invalid ACLs from acl(5)'s rules, and a mask limiting a named
user.

## Tests

`ref/run.sh` compares (on this machine) 6080 cases:

* 5080 against the **kernel**: `os.access` for every request on 40 temporary
  files and directories with random modes set by `os.chmod` (the owner
  class), and on system files of other users and groups under `/etc`,
  `/usr/bin`, `/var/log` and similar (the group and other classes; files with
  ACLs, and writes on read-only mounts, are skipped). The test user has no
  capabilities, so no override is exercised against the kernel. The count
  depends on the machine;
* 1000 against an **independent Python model** written from the same
  documents (`ref/gen.py`): 300 mode checks with random privileges, 100
  umasks, 300 ACL checks, 150 ACL validity cases (well-formed ACLs, and ones
  broken in each way), 150 deletions. Every kernel answer is also checked
  against the model.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 6080 cases match (also with seeds 1, 99 and
31337), `scripts/deps.sh perms` ok.
