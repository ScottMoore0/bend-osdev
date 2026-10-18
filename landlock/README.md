# bend-osdev-landlock

Landlock rule evaluation: what a Landlock domain (a stack of enforced
rulesets) allows a process to do, written from Landlock's documented user
API. It models rulesets, path-beneath and net-port rules, domains of up to 16
layers, the ABI versions 1 to 6, the REFER rules for renaming and linking
across directories, and IPC scoping, and answers, for an operation (open,
execve, mkdir, unlink, rename, link, bind, connect, kill, ...), what the
kernel would: allowed, `EACCES`, `EXDEV` or `EPERM`. Paths are a model (lists
of components with a parent relation), not real files.

The package is policy logic, so its point is its laws: properties of the
evaluation for every input, proved in `PROOF.bend` (see Laws).

## Specification

Clean room: written from documentation and from black-box behaviour of the
running kernel, never from kernel source (no Linux source, UAPI header or
sample was opened).

* landlock(7), landlock_create_ruleset(2), landlock_add_rule(2),
  landlock_restrict_self(2): the man pages of man-pages 6.7 (2023-10-31), as
  installed in WSL Ubuntu. They cover ABI 1 to 3: the filesystem rights,
  rulesets, path-beneath rules, layers ("A sandboxed thread can only access a
  file path if all its enforced policy layers grant the access"), the REFER
  conditions and their errors, and the errors of the three calls.
* The kernel's userspace-api/landlock document (Documentation/userspace-api/
  landlock.rst, "Landlock: unprivileged access control"), which is
  documentation. It was not available offline here, so the parts only it
  covers are written from its published text as known: ABI 4 (the network
  rights `BIND_TCP` and `CONNECT_TCP` and net-port rules), ABI 5
  (`IOCTL_DEV`), ABI 6 (IPC scoping: `SCOPE_ABSTRACT_UNIX_SOCKET`,
  `SCOPE_SIGNAL`), the limit of 16 stacked rulesets, and the best-effort
  advice. The kernel tested has ABI 3, so these parts are checked only
  against the Python model (which shares an author with the package); the
  16-layer limit was checked on the kernel.
* Experiments on Linux 6.6.87.2 (WSL2, Landlock ABI 3; `landlock_create_ruleset`
  with `LANDLOCK_CREATE_RULESET_VERSION` answers 3, and fs bits 0 to 14 are
  accepted, bit 15 refused with `EINVAL`), each in a forked child on a
  scratch tree, for what the documentation leaves open (see below).

### How the documentation is read, and what the experiments settled

* **Layers.** A layer refuses a right it handles unless some rule on the path
  or one of its ancestors allows it; it never refuses a right it does not
  handle; an access is allowed only when every layer allows it.
* **REFER.** landlock(7): REFER "is the only access right which is denied by
  default by any ruleset, even if the right is not specified as handled".
  The package reads "any ruleset" as any ruleset that handles a filesystem
  right: such a ruleset handles REFER (`LandlockRuleset.handles`), and only a
  rule allowing REFER, which needs REFER explicitly handled, grants it. A
  ruleset handling no filesystem right (only network rights or scoping) does
  not restrict the filesystem at all. Observed: a ruleset handling only
  `EXECUTE` refuses a cross-directory rename (`EXDEV`) and allows one within
  a directory. A network-only ruleset needs ABI 4, so that half is a choice.
* **The REFER conditions.** A missing REFER on either directory is `EXDEV`
  (observed; the man page names no error for it). "Gain more access rights":
  for a directory every right is compared, for any other file only the
  rights a file can receive (`EXECUTE`, `WRITE_FILE`, `READ_FILE`,
  `TRUNCATE`, `IOCTL_DEV`): a regular file moved where `MAKE_DIR`,
  `REMOVE_DIR` or `READ_DIR` is granted gains nothing, one moved where
  `READ_FILE`, `WRITE_FILE`, `EXECUTE` or `TRUNCATE` is granted does (all
  observed). The comparison is per layer, on what each layer grants on the
  two directories (observed with two layers). `EACCES` takes precedence over
  `EXDEV` across layers too (observed, with the layers in either order).
  Link needs no `REMOVE_*` right (observed).
* **execve** needs `READ_FILE` as well as `EXECUTE` (observed: with
  `READ_FILE` handled and not granted, `execve` fails with `EACCES`).
* **Which path a right is checked on**, from landlock(7): `READ_DIR` and the
  file rights on the file or directory itself (and everything beneath a
  rule's directory); `MAKE_*` and `REMOVE_*` on the directory that holds the
  entry (observed: `rmdir d` needs `REMOVE_DIR` on d's parent, not on d).
* **Rules on files** may allow only the file rights (`EINVAL` otherwise,
  observed for `READ_DIR` and `REFER`).
* **The layer limit** is 16 (the kernel's document; a 17th
  `landlock_restrict_self` fails with `E2BIG`, observed); the man page's "64"
  is out of date. The limit is an option.
* **Scoping.** A layer that scopes an action refuses it towards a process
  whose domain does not contain that layer (the same domain or one nested in
  it is inside; a parent, a sibling or an unsandboxed process is outside).
  Layers are named by caller-supplied identities (the kernel uses object
  identity).
* **Error order** in `landlock_add_rule`: no right (`ENOMSG`), a right not
  handled (`EINVAL`), a directory right on a file (`EINVAL`), a port above
  65535 (`EINVAL`); the man page fixes no order, and only the first and the
  rest differ in errno.
* **Not modelled:** file descriptors opened before sandboxing (they keep
  their access), `ftruncate` on an existing descriptor, rename over an
  existing name and `RENAME_EXCHANGE`, ptrace restrictions, bind mounts (a
  rule applies to the name it is given: give one rule per name), and
  filesystem state (a rule stays on its path when the path is renamed).

## Files

| File | Holds |
|---|---|
| `landlock.bend` | the entry: `LandlockOptions` (ABI, compatibility, layer limit) and its default; `Landlock.create_ruleset`, `add_path`, `add_port`, `restrict_self` as a program calls them; `LandlockThread`; the operations (`LandlockOp`) and `Landlock.check` |
| `rights.bend` | filesystem rights (`LandlockFsRight`), sets of them (`LandlockFs`), the kernel masks, file kinds (`LandlockFileKind`) and the rights they need; `LandlockBits`, the Bool-list operations every set uses |
| `net.bend` | network rights (`LandlockNetRight`), sets (`LandlockNet`), net-port rules (`LandlockNetRule`) |
| `scope.bend` | scoped actions (`LandlockScopeRight`), sets (`LandlockScope`), the scoping check of one layer |
| `abi.bend` | ABI versions: the rights each knows, `LandlockCompat`, best-effort clipping |
| `path.bend` | the hierarchy (`LandlockPath`): components, parent, join, beneath, text |
| `ruleset.bend` | rulesets (`LandlockRuleset`, `LandlockPathRule`): creation and rules as the kernel checks them, and one layer's answer |
| `domain.bend` | domains (`LandlockDomain`, `LandlockLayer`): stacking, the limit, and the answers of all layers together |
| `refer.bend` | decisions (`LandlockDecision`) and rename and link (`LandlockRefer`) |
| `error.bend` | `LandlockError`, with names and errnos |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/sets.py` | the generator of the sets' repetitive parts (the right tables, in `rights.bend`, `net.bend`, `scope.bend`) and of `PROOF.bend`'s per-set lemmas, between `# BEGIN GENERATED by gen/sets.py: <name>` and `# END GENERATED: <name>` lines; `python3 gen/sets.py` rewrites them, `--check` checks they are up to date |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/head.bend`, `ref/run.sh`, `ref/.gitignore` | the differential test (`cases-*.bend` and `expected.txt` are generated, and ignored) |

## API

Rights and sets (`rights.bend`; `net.bend` and `scope.bend` have the same
defs for `LandlockNet`/`LandlockNetRight` and `LandlockScope`/`LandlockScopeRight`):

| Def | Meaning |
|---|---|
| `LandlockExecute{}` … `LandlockIoctlDev{}` | the sixteen filesystem rights, in bit order (`LandlockBindTcp`, `LandlockConnectTcp`; `LandlockScopeAbstractUnix`, `LandlockScopeSignal`) |
| `LandlockFsRight.index`, `.name`, `.all` | bit number; kernel name less `LANDLOCK_ACCESS_FS_`; every right |
| `LandlockFs{execute, …, ioctl_dev}` | a set: one Bool per right |
| `LandlockFs.has`, `none`, `all`, `single`, `add`, `of_list`, `to_list`, `union`, `inter`, `minus`, `subset`, `is_empty`, `is_eq`, `show` | set operations; `show` is `"READ_FILE\|READ_DIR"`, `"0"` for none |
| `LandlockFs.bools`, `of_bools` | the set as one Bool per right, and back |
| `LandlockFs.to_mask`, `of_mask`, `to_u32` | the kernel's `__u64` mask (`W64`), and back (`LandlockUnknownAccess` for a bit no ABI defines) |
| `LandlockFs.file_rights()` | the rights a file can receive |
| `LandlockFileKind` (`LandlockReg`, `LandlockDir`, `LandlockChr`, `LandlockBlk`, `LandlockFifo`, `LandlockSock`, `LandlockSym`), `.make_right`, `.remove_right`, `.carried`, `.is_dir`, `.name` | file types; the right to create one in a directory, to remove one, and the rights compared when one is reparented |
| `LandlockNetRule{port, allowed}`, `LandlockNet.granted(rules, port)`, `LandlockNet.max_port()` | net-port rules; what they grant on a port; 65535 |
| `LandlockScope.member(ids, id)`, `LandlockScope.layer_allows(scoped, id, target, x)` | the scoping check of one layer named id towards a target domain's layer names |

ABI (`abi.bend`):

| Def | Meaning |
|---|---|
| `LandlockAbi.latest()` | 6 |
| `LandlockAbi.fs_since`, `net_since`, `scope_since` | the version a right appears in |
| `LandlockAbi.knows_fs(v, r)`, `knows_net`, `knows_scope` | version v knows the right |
| `LandlockAbi.fs(v)`, `net(v)`, `scope(v)`, `has_net_rules(v)` | the sets version v knows |
| `LandlockAbi.clip_fs(v, s)`, `clip_net`, `clip_scope` | the part of a set version v knows |
| `LandlockCompat` (`LandlockBestEffort`, `LandlockStrict`) | what to do with a right the ABI lacks |

Paths (`path.bend`): `LandlockPath{names}`, `root`, `of_names`, `names`,
`join(p, q)`, `child(p, name)`, `parent`, `depth`, `is_eq`, `is_beneath(p,
q)` (p is q or beneath it), `name_eq`, `names_eq`, `prefix`, `of_string`
(`"/usr//lib/"` is `/usr/lib`), `show`.

Rulesets (`ruleset.bend`), each fallible call answering
`Result<&2, &2, LandlockError, LandlockRuleset>`:

| Def | Meaning |
|---|---|
| `LandlockRuleset{handled_fs, handled_net, scoped, paths, ports}`, accessors, `LandlockPathRule{beneath, allowed}` | a ruleset |
| `LandlockRuleset.make(f, n, s)`, `none()`, `is_none` | a ruleset without rules (unchecked); the one handling nothing |
| `LandlockRuleset.create(v, f, n, s)` | landlock_create_ruleset on ABI v: `LandlockNotSupported` (v = 0), `LandlockUnknownAccess`, `LandlockEmptyRuleset` |
| `LandlockRuleset.add_path(rs, q, is_dir, a)`, `add_port(rs, port, a)` | landlock_add_rule: `LandlockEmptyRule`, `LandlockRuleNotHandled`, `LandlockDirRightOnFile`, `LandlockBadPort` |
| `LandlockRuleset.with_path`, `with_port` | a rule added without checks |
| `LandlockRuleset.handles(rs, r)`, `handles_net`, `scopes` | the ruleset restricts the right (REFER: see above) |
| `LandlockRuleset.beneath(rules, p)`, `granted(rs, p)`, `granted_net(rs, port)` | what rules grant on a path or a port |
| `LandlockRuleset.allows(rs, p, r)`, `allows_all(req, rs, p)`, `allows_net(rs, port, r)` | one layer's answer |

Domains (`domain.bend`):

| Def | Meaning |
|---|---|
| `LandlockDomain{layers}`, `LandlockLayer{id, ruleset}`, `none`, `layers`, `push(d, id, rs)`, `depth`, `ids` | a domain, newest layer first |
| `LandlockDomain.restrict(max, d, id, rs)` | landlock_restrict_self: `LandlockTooManyLayers` at max layers; a ruleset handling nothing leaves d as it is |
| `LandlockDomain.allows(d, p, req)`, `allows_net(d, port, r)`, `allows_scope(d, target, x)` | every layer's answer |

Rename and link (`refer.bend`):

| Def | Meaning |
|---|---|
| `LandlockDecision` (`LandlockAllowed`, `LandlockDeniedAccess`, `LandlockDeniedReparent`, `LandlockDeniedScope`), `is_allowed`, `show` (`OK`, `EACCES`, `EXDEV`, `EPERM`), `of_bool`, `worse` | answers, and two answers together |
| `LandlockRefer.rename(d, src, dst, k)`, `link(d, src, dst, k)` | moving or linking a file of kind k from directory src to directory dst |
| `LandlockRefer.layer`, `reparent_ok`, `no_gain`, `decide`, `go` | the same for one layer, and its parts |

The entry (`landlock.bend`):

| Def | Meaning |
|---|---|
| `LandlockOptions{abi, compat, max_layers}`, `LandlockOptions.default()` (ABI 6, best effort, 16), accessors, `with_abi`, `with_compat`, `with_max_layers` | the choices |
| `Landlock.create_ruleset(o, f, n, s)`, `Landlock.best_effort(v, f, n, s)`, `Landlock.ok(r)` | create, strictly or best effort (which never fails: a ruleset of the rights the ABI knows) |
| `Landlock.add_path(o, rs, q, is_dir, a)`, `Landlock.add_port(o, rs, port, a)` | add a rule; best effort drops the rights the ABI lacks, and the rule when that is all of them |
| `LandlockThread{domain, no_new_privs, cap_sys_admin}`, `LandlockThread.new()`, `.domain` | a thread |
| `Landlock.restrict_self(o, t, id, rs)` | enforce: `LandlockNoNewPrivs` (EPERM) without no_new_privs or CAP_SYS_ADMIN |
| `LandlockOp` (`LandlockOpOpen{path, read, write, truncate}`, `LandlockOpReadDir`, `LandlockOpExec`, `LandlockOpTruncate`, `LandlockOpIoctl`, `LandlockOpCreate{dir, kind}`, `LandlockOpRemove`, `LandlockOpRename{src, dst, kind}`, `LandlockOpLink`, `LandlockOpBind{port}`, `LandlockOpConnect`, `LandlockOpSignal{target}`, `LandlockOpConnectAbstract`) | operations |
| `Landlock.open_rights(r, w, t)`, `Landlock.check(d, op)` | the rights open needs; the domain's answer to an operation |

`LandlockError` (`error.bend`): `LandlockNotSupported` (EOPNOTSUPP),
`LandlockUnknownAccess`, `LandlockRuleNotHandled`, `LandlockDirRightOnFile`,
`LandlockBadPort` (EINVAL), `LandlockEmptyRuleset`, `LandlockEmptyRule`
(ENOMSG), `LandlockTooManyLayers` (E2BIG), `LandlockNoNewPrivs` (EPERM);
`LandlockError.name`, `.errno`.

Masks are `W64` because the kernel's fields are `__u64`; ports are `U32`
(only 0 to 65535 are valid ports, and the kernel's `__u64` port field has no
other valid values). Nothing here holds byte strings, so `bytes` is not a
dependency.

## Streaming

Not applicable as such: nothing arrives as a byte stream. A ruleset is built
incrementally, as the kernel's is (create, then one `add_path` or `add_port`
per rule, then `restrict_self`), and a domain grows one layer at a time.

## Extension points

* **`LandlockOptions`**: the ABI version (0 for no Landlock), strict or best
  effort, and the layer limit; `LandlockOptions.default()` is ABI 6, best
  effort, 16 layers. The lower files take the same choices as plain
  parameters (`LandlockRuleset.create(v, …)`, `LandlockDomain.restrict(max,
  …)`), so a caller can use them without the options record.
* **A new right or ABI version**: a row in `gen/sets.py`'s tables (then
  `python3 gen/sets.py`), its version in `abi.bend`'s `*_since` and set
  defs, and, for a filesystem right, `LandlockFs.file_rights` if a file can
  receive it. Every law and proof is written for every right, so they need
  no change beyond the generated cases.
* **The readings of the documentation** are each one small def, so a
  different kernel behaviour changes one place, and the laws say which
  properties must survive: REFER's implicit handling
  (`LandlockRuleset.handles`), the rights compared on reparenting
  (`LandlockFileKind.carried`), the error precedence
  (`LandlockRefer.decide`, `LandlockDecision.worse`), the rights each
  operation needs (`Landlock.check`, `Landlock.open_rights`, e.g. execve's
  `READ_FILE`), what a rule on a path covers (`LandlockPath.is_beneath`).
* **Faster evaluation**: a layer scans its rules (`LandlockRuleset.beneath`);
  an index by path could replace it, kept equal to the scan, since the laws
  speak only of `allows`, `granted` and the decisions.
* **Paths** are lists of names; bind mounts are modelled by one rule per
  name, and a richer hierarchy (inodes with several names) would replace
  `path.bend` behind `is_beneath`.

## Laws

`LAWS.bend`: 72 laws, 33 for
every input, 20 witnesses and 19 vectors, proved in `PROOF.bend` by
induction on the layers, the rules and the paths. Set facts are proved once
for lists of Bools (`LandlockBits`) and carried to each set by a generated
16-case (or 2-case) lemma.

**For every input** (every domain, ruleset, path, port, right, operation,
ABI and options):

* restriction is monotone: if a domain with one more layer allows an
  operation, the domain without it does, for all thirteen operations
  (`push_monotone`), and so through `landlock_restrict_self`
  (`restrict_monotone`);
* a ruleset handling nothing changes no answer (`empty_changes_nothing`),
  and `restrict` with it leaves the domain as it is
  (`empty_restrict_unchanged`);
* a right a layer does not handle is never refused by that layer
  (`unhandled_fs_not_refused`, `unhandled_net_not_refused`,
  `unscoped_not_refused`: the answer with the layer is the answer without
  it); REFER is handled by every ruleset that handles a filesystem right
  (`refer_always_handled`) and then refused unless REFER is handled
  explicitly (`refer_refused_unless_handled`);
* inheritance: a rule added on q (by `add_path`, checked) allows its rights
  on every path beneath q (`rule_applies_beneath`); whatever a domain allows
  on a path it allows on every path beneath it (`allowed_inherited`); a
  net-port rule allows its rights on its port (`port_rule_applies`);
* rename and link within one directory need exactly the REMOVE_* and MAKE_*
  rights there (`rename_same_dir`, `link_same_dir`); across directories, a
  layer that handles filesystem rights but not REFER refuses them
  (`reparent_needs_refer_rename`, `_link`: ABI 1's behaviour); an allowed
  reparenting never gains: every carried right the domain allows in the new
  directory it allowed in the old one (`reparent_no_gain_rename`, `_link`);
* ABI: a later version knows every right an earlier one does
  (`abi_later_knows_fs`, `_net`, `_scope`); strict mode refuses a ruleset
  with a right the ABI lacks (`strict_refuses_unknown_fs`, `_net`, `_scope`);
  best effort never refuses (`best_effort_never_refuses`) and handles
  exactly the rights asked for that the ABI knows
  (`best_effort_keeps_known_fs`, `_net`, `_scope`);
* the layer limit: restrict keeps a domain within it (`restrict_bounded`)
  and refuses a layer at it (`restrict_full_refused`);
* scoping: a process may always act on its own domain
  (`scope_same_domain`) and on domains nested in it (`scope_nested_allowed`),
  and a scoping layer refuses an unsandboxed target
  (`scope_refuses_outside`).

**Witnesses:** each law with a hypothesis has a witness law showing inputs
that satisfy all its hypotheses (an allowed operation after a push and after
`restrict_self`, unhandled rights, an ABI 1 ruleset and two different
directories, a successful `add_path` and `add_port`, an allowed reparenting
that keeps `READ_FILE`, rights unknown to ABIs 3 and 5, a domain within and
one at the limit, a scoping ruleset).

**Vectors:** the ABI masks of landlock(7)'s table and example (0x1FFF,
0x3FFF, 0x7FFF; 0xFFFF at ABI 5; the network and scope masks), a mask round
trip and an unknown bit, landlock(7)'s `/usr` example, and the rename and
link cases observed on the kernel (ABI 1 reparenting, a gain of `READ_FILE`,
a loss, `EACCES` first).

## Tests

`check.bend` runs the documented flow (create, add a rule, restrict) on both
choices, the errors of each call, the landlock(7) example, rename and link
across and within directories, network and scoping cases, and the 16-layer
limit.

`ref/run.sh` compares 663 cases (in six files of at most 120) with an
independent Python model of the documentation (`ref/gen.py`, written here,
on the kernel's bit masks rather than the package's records; it shares an
author with the package), and with the running kernel where it has
Landlock:

* 260 filesystem cases on random domains of one to three layers (random
  handled rights, up to six rules on directories and files of a scratch
  tree) and random operations: open for read, write and truncate, readdir,
  execve of a static program, truncate, mknod, mkdir, mkfifo, symlink, bind
  of a UNIX socket, unlink, rmdir, rename and link of files and directories
  within and across directories;
* 80 more filesystem cases on every ABI, every file type and `IOCTL_DEV`;
  80 network cases (bind and connect against port rules); 60 scoping cases
  (targets in the same, a nested, the parent, a sibling and no domain);
* 70 `landlock_create_ruleset`, 70 path-beneath and 40 net-port
  `landlock_add_rule` cases on every ABI, strict and best effort; and the
  layer limit (15, 16 and 17 layers).

On this machine (Linux 6.6.87.2, WSL2: **Landlock ABI 3**) 338 of the cases
also ran on the kernel (all 260 filesystem cases, the creates and adds the
kernel can express, the limit), each in a forked child, and every errno
matched the model; `gen.py` fails on any disagreement. Network rules
(ABI 4), `IOCTL_DEV` (ABI 5) and scoping (ABI 6) are checked only against
the model. Seeds 2026 (the default), 1, 99 and 31337 all match. CI needs
only `python3` (no extra packages); on a kernel without Landlock the test
runs against the model alone.

## Speed and sizes

Native builds (Bend 2.0.37, WSL2): `check.bend` builds in 6 s (230 MB) to a
430 KB binary that runs in under 0.01 s in 2.7 MB; a case file of 120 cases
builds in 9 s (460 MB) and runs in under 0.01 s. A layer's answer is linear
in its rules: 100 checks of a path six components deep against 16 layers of
1,001 rules each (1.6 million rule tests) took 3.9 s in 13.6 MB, about
2.4 µs per rule, most of it the set union through Bool lists.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 663 cases match (338 on the kernel, ABI 3),
all as native binaries (`VERDICT=1 scripts/check.sh landlock`: no
JavaScript-lane fallback); `scripts/deps.sh landlock` ok; `python3
gen/sets.py --check` ok.
