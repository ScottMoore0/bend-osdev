# bend-osdev-caps

Linux capability sets, and the rules by which `execve(2)`, `capset(2)` and
`prctl(2)` change them, written from the man pages:

* capabilities(7): the capability numbers, the thread's permitted,
  inheritable, effective, bounding and ambient sets, file capabilities,
  "Transformation of capabilities during execve()", "Safety checking for
  capability-dumb binaries", "Capabilities and execution of programs by root",
  "Set-user-ID-root programs that have file capabilities", "Capability
  bounding set", "Programmatically adjusting capability sets", and the
  securebits `SECBIT_NOROOT` and `SECBIT_NO_CAP_AMBIENT_RAISE`;
* execve(2): the set-user-ID bit, the saved set-user-ID, and when set-ID bits
  and file capabilities are ignored (`no_new_privs`, `nosuid`, ptrace);
* capset(2) and prctl(2) (`PR_CAPBSET_READ`, `PR_CAPBSET_DROP`,
  `PR_CAP_AMBIENT`): the operations and their errors.

The package is policy logic, so its point is its laws: properties of the
rules for every input, proved in `PROOF.bend` (see Laws).

## Files

| File | Holds |
|---|---|
| `caps.bend` | capability numbers and names; capability sets; the thread's sets (`CapState`), credentials (`CapCred`), a file's capabilities (`CapFile`, `CapFileSets`); the kernel's choices (`CapsKernel`); the error type (`CapsError`) |
| `exec.bend` | `Caps.execve` and `Caps.execve.sets`: the transformation during execve |
| `adjust.bend` | `Caps.capset`, `Caps.bset_read`, `Caps.bset_drop`, `Caps.ambient_raise`, `Caps.ambient_lower`, `Caps.ambient_is_set`, `Caps.ambient_clear_all` |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/proof.py`, `gen/wordgen.py` | the generator of `PROOF.bend`'s generated regions (the per-bit lemmas and the law proofs, between `# BEGIN GENERATED` and `# END GENERATED` lines); `python3 gen/proof.py` rewrites them, `--check` checks they are up to date |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh`, `ref/.gitignore` | the differential test (`cases.bend` and `expected.txt` are generated, and ignored) |

## API

Capabilities and sets (`caps.bend`):

| Def | Meaning |
|---|---|
| `Cap.chown()` … `Cap.checkpoint_restore()` | the capability numbers, 0 to 40 |
| `Cap.name(k)`, `Cap.of_name(s)` | `"CAP_CHOWN"` and back (`Maybe`) |
| `Cap.valid(k)` | k is 0 to 40 |
| `CapSet()` | a set: an open type, `Word(41n)`, bit k is capability k |
| `CapSet.empty`, `CapSet.full`, `CapSet.of(k)`, `CapSet.from_list`, `CapSet.to_list` | building and listing sets (`of` is empty for k > 40) |
| `CapSet.union`, `inter`, `minus`, `add`, `del`, `has`, `subset`, `is_eq` | set operations |
| `CapSet.to_w64`, `CapSet.from_w64`, `CapSet.show` | the 64-bit mask, as `capget(2)`; 16 hex digits, as `/proc/<pid>/status` |
| `CapBits.*` | the same operations for every width n (the proofs use them) |
| `CapState{permitted, inheritable, effective, bounding, ambient}` | a thread's sets, with accessors, `with_bounding`, `with_ambient`, and `valid` (effective within permitted, ambient within permitted and inheritable) |
| `CapCred{ruid, euid, suid, noroot, no_ambient_raise, sets}` | credentials: user IDs, the two securebits, the sets |
| `CapFileSets{permitted, inheritable, effective}`, `CapFile{uid, setuid, setgid, caps}` | a file's capabilities; an executable |
| `CapsKernel{last_cap, file_caps}`, `CapsKernel.linux()` | the kernel's choices (see Extension points) |
| `CapsError`, `CapsError.errno` | `CapsInvalidCap` (EINVAL), `CapsPermittedGrows`, `CapsEffectiveNotPermitted`, `CapsInheritableNotBounded`, `CapsInheritableNotPermitted`, `CapsNoSetpcap`, `CapsAmbientRaiseLocked`, `CapsAmbientNotAllowed`, `CapsCapabilityDumb` (EPERM) |
| `Caps.or(r, c)`, `Caps.sets_or(r, s)` | the credentials (sets) after a call, or the old ones if it failed |

Operations (each answers `Result<&2, &2, CapsError, CapCred>`):

| Def | Meaning |
|---|---|
| `Caps.execve(k, c, f, ign)` | execve of `f`; `ign`: set-ID bits and file capabilities are ignored (`no_new_privs`, `nosuid`, ptrace). New euid and saved set-user-ID; `CapsCapabilityDumb` if a file with the effective bit does not get all of its permitted set |
| `Caps.execve.sets(k, c, f, ign)` | the sets after the transformation (what `execve` answers when it succeeds) |
| `Caps.capset(c, e, p, i)` | new effective, permitted, inheritable; ambient capabilities no longer permitted and inheritable are lowered |
| `Caps.bset_drop(k, c, x)`, `Caps.bset_read(k, c, x)` | `PR_CAPBSET_DROP` (needs `CAP_SETPCAP` in the effective set), `PR_CAPBSET_READ` |
| `Caps.ambient_raise`, `Caps.ambient_lower`, `Caps.ambient_is_set` (`k, c, x`), `Caps.ambient_clear_all(c)` | `PR_CAP_AMBIENT` |

### How the documented rules are read

* The transformation is capabilities(7)'s formula, with the file's sets
  replaced by all ones, and its effective bit by one, as "Capabilities and
  execution of programs by root" says: rule (1) when the real or (new)
  effective UID is 0, except for a set-user-ID-root program with file
  capabilities run by a non-root real UID; rule (2) when the effective UID is
  0. `SECBIT_NOROOT` turns both off.
* A privileged file (one that clears the ambient set) has file capabilities or
  the set-user-ID or set-group-ID bit; ignored bits and ignored file
  capabilities count as absent.
* The capability-dumb check compares the file's own permitted set (not the
  notional all-ones set) with the new permitted set; it applies whenever the
  file's capabilities are honoured and its effective bit is set.
* `capset` checks its rules in this order, and the first failure names the
  error: permitted within the old permitted set; effective within the new
  permitted set; inheritable within the old inheritable and bounding sets;
  without `CAP_SETPCAP` in the effective set, inheritable within the old
  inheritable and permitted sets. capset(2) does not fix an order.
* `bset_drop` checks the capability number (EINVAL) before `CAP_SETPCAP`
  (EPERM); prctl(2) does not fix an order.
* Not modelled: user namespaces, `SECBIT_KEEP_CAPS` and the effect of
  `setuid(2)`-family calls, version-3 (namespaced) file capabilities, the
  set-group-ID effective GID.

## Extension points

* **`CapsKernel`**: the highest capability the kernel supports (EINVAL above
  it; `/proc/sys/kernel/cap_last_cap`) and whether file capabilities are on
  (`no_file_caps`). `CapsKernel.linux()` is Linux 5.9 and later: 40, on.
  Sets stay 41 bits wide; a kernel with fewer capabilities simply never sets
  the top bits.
* **The numbering** is Linux's ABI, fixed in `caps.bend`. A later capability
  (41 and up) means widening `CapSet` to `Word(n)` for a larger n: the set
  operations (`CapBits`) and every per-bit lemma in `PROOF.bend` are already
  written for every width.
* **The rules** are small, separate defs (`CapExec.flags.go` for the root
  rules, `CapExec.sets` for the formula, `CapAdjust.capset.r1`…`r4` for the
  capset rules), so a variant policy changes one def; the laws say which
  properties must survive.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer). **For every
input** (every kernel record, credential, file, request and capability
number), proved by induction on the width of the sets:

* execve: the effective set is within the permitted set; the ambient set is
  within the permitted set, and within the inheritable set when it was
  before; the whole invariant (`CapState.valid`) is preserved; the bounding
  and inheritable sets are unchanged; the new permitted set is within the old
  bounding ∪ inheritable ∪ ambient sets (and within bounding ∪ inheritable
  when ambient was within inheritable), so a capability in none of them never
  becomes permitted; execve answers either `CapsCapabilityDumb` or exactly
  `Caps.execve.sets`.
* The documented root and non-root cases, for every set: with real and
  effective UID 0 (no `SECBIT_NOROOT`) and any file that is not
  set-user-ID, P'(permitted) = P'(effective) = P(inheritable) | P(bounding);
  with nonzero real and effective UIDs and a plain file, P'(permitted) =
  P'(effective) = P(ambient).
* capset: the permitted set never grows; the bounding set is unchanged; the
  invariant holds afterwards.
* `PR_CAPBSET_DROP`: the bounding set never grows; no other set changes.
* `PR_CAP_AMBIENT`: raising and lowering preserve the invariant and change no
  other set; clearing empties the ambient set.

The task's draft law "a capability outside the bounding set (and not already
permitted) never enters permitted through execve" is false as stated:
capabilities(7) says the bounding set does not mask the inheritable set, so a
capability that is inheritable (in the thread and the file) enters permitted
whatever the bounding set. The law proved instead is the bound above
(bounding ∪ inheritable ∪ ambient).

**Witnesses:** every hypothesis of a law holds for some input, so no law is
vacuous: vector laws show a concrete valid state (with a nonempty ambient
set), ambient within inheritable for a credential's sets and for a state, and
a nonzero user ID (the non-root laws' hypotheses).

**Vectors:** the first and last capability names, a number beyond them,
`CAP_SYS_ADMIN` = 21, the text form of two sets, a capability-dumb binary
failing, a set-user-ID-root program with and without file capabilities, the
set-user-ID bit ignored, a capset that adds to the permitted set, an ambient
raise of a capability that is not inheritable, and a drop of capability 41.

## Tests

`ref/run.sh` compares 717 cases (300 execve, 150 capset, 80
`PR_CAPBSET_DROP`, 80 `PR_CAP_AMBIENT_RAISE`, 60 `PR_CAP_AMBIENT_LOWER`, 42
names, 5 sets of the running process) with:

* an independent Python model of the same rules (`ref/gen.py`), written from
  the man pages, on random credentials, files and requests, including states
  that break the invariants; every result is compared field by field, and
  errors by name;
* `capsh --decode` (libcap's tool), for the name of every capability number;
* the kernel's `/proc/self/status` (`CapInh` … `CapAmb`), for the text form
  of a set.

A cross-check against the real kernel would need privileges (setting file
capabilities, running as root), so there is none.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 717 cases match (also with seeds 1, 99 and 31337),
`scripts/deps.sh caps` ok.
