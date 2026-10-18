# bend-osdev-apparmor

AppArmor policy as a pure model: loading profiles from their text (the
apparmor.d(5) language: profiles, children and hats, includes over a file
map, variables, aliases, flags) and answering what a profile allows: file
access, capabilities, networking, signals, ptrace, mount, dbus and
change_profile, with deny rules, audit and owner qualifiers and the profile
modes, and where an exec goes (the exec transitions ix, px, cx, ux and their
fallbacks, with attachment matching). Globs are explicit matchers, a fast
one and a backtracking reference, with laws tying both to a list model.
Byte strings at the entry point are `Octets` (bend-osdev-bytes).

This is a clean-room package: it was written from documentation and from
the black-box behaviour of `apparmor_parser`, never from the source of the
kernel's AppArmor module, apparmor_parser or libapparmor.

## Specification

Documents used: the manual pages of AppArmor 4.0.1, installed in WSL, read
in full (so the package was written from their text, not from memory).
There was no network, so the AppArmor wiki and the published papers were
not available, and nothing was taken from them or from memory of them:

* **apparmor.d(5)** (`/usr/share/man/man5/apparmor.d.5.gz`): the grammar
  (FORMAT), "Profile Head" (names, attachments, flags, modes), "Access
  Modes" and "Access Modes Details" (r w a l k m, the exec transitions and
  their fallbacks, deny x, directed transitions with ->), leading and
  trailing permissions, "Network Rules", "Mount Rules", "PTrace rules",
  "Signal rules", "DBus rules", "change_profile rules", "Variables", "Alias
  rules", "Globbing (AARE)", "Rule Qualifiers" and qualifier blocks, the
  "#include mechanism", and its EXAMPLE;
* **apparmor(7)**: enforce and complain modes ("deny rules will still
  result in denials" in complain mode), force audit mode (the audit flag),
  deny audit quieting, the DENIED and ALLOWED log tags;
* **apparmor_parser(8)**: `-Q` (skip the kernel load), `-K` (no cache),
  `--base` and `-I`, `-D`/`--dump` (`rule-exprs`, `expanded-variables`).

Where the documents are silent or ambiguous the package follows what
`apparmor_parser` 4.0.1 does, observed as a black box (it was run, never
read): `apparmor_parser -Q -K` accepts or rejects a profile without loading
it, and `-D rule-exprs` prints the regular expression each pattern compiles
to. Loading needs root, so the kernel's runtime decisions could not be
observed: the evaluation side is a model of the documents, tested against
an independent Python model of the same documents, not against a kernel.
Every experiment is listed under Experiments; every choice made without one
is listed under "How the documents are read".

## Files

| File | Holds |
|---|---|
| `apparmor.bend` | the entry point: `Aa.load` from a file map of `Octets`, the queries by profile name, `Aa.exec` |
| `glob.bend` | AARE globs: parsing a pattern's text, brace expansion, the fast matcher `AaGSeq.run`, the backtracking reference `AaGSeq.matches`, the list model `AaGSeq.model`, attachment ranks |
| `token.bend` | the tokens of the profile language, and the terms (words, strings, lists, key=value conditions, ->) rules are written in |
| `parse.bend` | loading: statements and blocks, includes, the preamble (variables, aliases), variable expansion, profile heads and flags, qualifiers, rule dispatch, building profiles |
| `rule_file.bend` | file rules: patterns, access modes, exec modes, targets, owner; the file query |
| `rule_capability.bend` | capability rules (names and numbers from bend-osdev-caps) |
| `rule_network.bend` | network rules: domain, type, protocol |
| `rule_signal.bend` | signal rules: access, signal set, peer |
| `rule_ptrace.bend` | ptrace rules: access, peer |
| `rule_mount.bend` | mount, remount and umount rules: fstype, options = and in, source, mountpoint |
| `rule_dbus.bend` | dbus rules: message, service and eavesdrop forms |
| `rule_change_profile.bend` | change_profile rules: exec condition, safe or unsafe, target |
| `rule.bend` | what the rule kinds share: patterns and name lists from terms, matching helpers |
| `perm.bend` | permission sets (`AaPerms`), qualifiers (`AaQual`), grants (`AaGrant`) |
| `eval.bend` | the decision engine (`AaEval.decide`) and the decision for each rule kind on a profile |
| `transitions.bend` | exec transitions and attachment matching (`AaTrans.exec`) |
| `profile.bend` | modes and flags, the rules of a profile by kind, profiles, children, hats, policies, lookup by full name |
| `options.bend` | `AaOptions`: the caller's choices, with documented defaults |
| `error.bend` | `AaError`, why a policy fails to load, with file and line |
| `text.bend` | byte-list helpers |
| `example.bend` | a profile built from the types, and two policy texts with their file maps (a larger one for check.bend, a small one for the laws' vectors), for users too |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh`, `ref/.gitignore` | the differential test (`cases-*.bend`, `expected.txt` and `edges.txt` are generated, and ignored) |

## Dependencies

`DEPS`: bytes (`Octets`, at the entry point and in the examples) and caps
(the capability names and numbers, `Cap.of_name` and `Cap.name`, so that
capability rules and queries use the numbers bend-osdev-caps uses).

## API

The public interface is what this section lists; everything else is
internal. Below the entry file, the files work on byte lists
(`List<&2, U32>`, what `Octets.to_list` gives): the laws are stated over
them, and a caller that already holds lists need not convert. Their types
are open (plain records) unless marked opaque.

`apparmor.bend`:

| Def | Meaning |
|---|---|
| `AaSource{name, text}` | a file of the file map (both `Octets`); `name` as includes name it: `abstractions/base` for `<abstractions/base>` and for `"abstractions/base"` |
| `Aa.load(opts, sources, main)`, `Aa.load_default(sources, main)` | `Result<&2, &2, AaError, AaPolicy>`: the policy the file `main` defines |
| `Aa.profile(pol, name)` | the profile with that full name (`foo`, `foo//child`, `foo//hat`), or `None` |
| `Aa.file(opts, pol, profile, path, owner, req)` | `Maybe<&2, AaDecision>` (`None` for an unknown profile): may the profile access `path` with `req` (owner: the task's fsuid owns the file) |
| `Aa.capability(opts, pol, profile, cap)` | capability number `cap` (CAP_CHOWN is 0) |
| `Aa.network(opts, pol, profile, domain, type, protocol)` | a socket (`inet`, `stream`, `tcp`; empty protocol for none) |
| `Aa.signal(opts, pol, profile, req, signal, peer)`, `Aa.ptrace(opts, pol, profile, req, peer)` | `req` from `AaSignal.send/receive` or `AaPtrace.read/trace/readby/tracedby` bits |
| `Aa.mount(opts, pol, profile, q)`, `Aa.dbus(opts, pol, profile, q)` | with an `AaMountQuery` or `AaDbusQuery` |
| `Aa.change_profile(opts, pol, profile, exec, target)` | a change to `target`, now (`exec` None) or at the exec of a program |
| `Aa.exec(opts, pol, profile, path, owner)`, `Aa.exec_unconfined(pol, path)` | `AaExecResult`: where an exec goes |

`options.bend`: `AaOptions{complain_deny, depth, vars}`, `AaOptions.default()`
(deny rules apply in complain mode, includes nest 32 deep, no predefined
variables), `with_complain_deny`, `with_vars`, accessors; `AaVar{name, values}`.

`eval.bend`:

| Def | Meaning |
|---|---|
| `AaDecision`: `AaAllow`, `AaAudit`, `AaComplain`, `AaDeny{logged}`, `AaKill`; `AaDecision.allowed`, `AaDecision.show` | allowed silently; allowed and logged AUDIT; allowed in complain mode and logged ALLOWED; denied (logged DENIED unless quieted); denied and the task killed |
| `AaEval.decide(opts, flags, req, grants)` | the engine: the decision on `req` given the grants of the matching rules |
| `AaEval.granted(grants)`, `AaEval.denied(grants)`, `AaEval.deny_applies(opts, mode)` | what the grants allow less what they deny; what they deny; whether deny rules decide in a mode |
| `AaEval.file`, `capability`, `network`, `signal`, `ptrace`, `mount`, `dbus`, `change_profile` (`opts, profile, query`) | the decision for one rule kind on a profile |
| `AaAcc` and `AaAcc.empty/join/single/add/from/of/granted` | the accumulation of grants (allowed, denied, audited, quieted) |

`transitions.bend`: `AaTrans.exec(opts, pol, name, owner, path)`,
`AaTrans.exec_unconfined(pol, path)`, `AaTrans.is_unconfined(mode)`;
`AaExecResult` (`AaExecOk{target, scrub, decision}`, `AaExecErr{why}`),
`AaExecResult.ok`, `AaExecResult.show`; `AaTarget` (`AaTStay`,
`AaTProfile{name}`, `AaTUnconfined`); `AaExecWhy` (`AaExecDenied{decision}`,
`AaExecNoProfile`, `AaExecConflict`, `AaExecAmbiguous`, `AaExecUnknown`);
`AaAttach.best(profiles, path, prefix, best)` (the attachment choice).

`profile.bend`: `AaMode` (`AaModeEnforce`, `AaModeComplain`, `AaModeKill`,
`AaModeUnconfined`, `AaModeDefaultAllow`, `AaModePrompt`), `AaMode.enforcing`,
`AaMode.is_complain`, `AaMode.show`; `AaFlags{mode, audit}`,
`AaFlags.default/mode/audit`; `AaRules{files, caps, nets, signals, ptraces,
mounts, dbus, changes}`, `AaRules.empty/append`, the accessors and one-rule
constructors (`AaRules.file`, `cap`, `net`, `signal`, `ptrace`, `mount`,
`dbus_rule`, `change`, `with_files`); `AaProfile{name, attach, flags,
rules, children, hats}`, `AaProfile.new/include/prepend/add_child/add_hat/find`
and accessors (`include` adds rules after a profile's, `prepend` before); `AaPolicy{profiles}`, `AaPolicy.profiles/lookup`.

`glob.bend`: `AaGTok` (`AaGChar{c}`, `AaGAny`, `AaGClass{neg, ranges}`,
`AaGStar`, `AaGStar2`), `AaGRange{lo, hi}`, `AaGlob{alts, literal}`;
`AaGlob.parse(text)` (`None` if malformed), `AaGlob.matches(g, s)`,
`AaGlob.matches_ref(g, s)`,
`AaGlob.match_text(pattern, s)`, `AaGlob.model(g, s)`, `AaGlob.rank(g, s)`,
`AaGlob.is_literal`, `AaGlob.literal(bytes)`, `AaGlob.all()`;
`AaGSeq.run(seq, s)` (the fast matcher, which `AaGlob.matches` uses),
`AaGSeq.matches(seq, s)` (the backtracking reference, which
`AaGlob.matches_ref` uses), `AaGSeq.model(seq, s)` (the list model), and
what the model is built from: `AaGTok.piece`, `AaGCuts.all`
(every way to cut a path into n pieces), `AaGSeq.fits`, `AaGSeq.fits_any`,
`AaGSeq.len`, `AaGCuts.empty_first/grow/append`, `AaGPiece.no_slash/one/first`,
`AaGClass.has`.

The rule files: each has its rule type (`AaFileRule`, `AaCapRule`,
`AaNetRule`, `AaSignalRule`, `AaPtraceRule`, `AaMountRule`, `AaDbusRule`,
`AaChangeRule`), its query type (`AaFileQuery`, `AaCapQuery`, `AaNetQuery`,
`AaSignalQuery`, `AaPtraceQuery`, `AaMountQuery`, `AaDbusQuery`,
`AaChangeQuery`), a parser from terms (`AaFile.parse`, `AaCap.parse`,
`AaNet.parse`, `AaSignal.parse`, `AaPtrace.parse`, `AaMount.parse`,
`AaDbus.parse`, `AaChange.parse`), and `matches(rule, query)`,
`matching(rules, query)`, `grants(rules, query)`, `grants.of(rules)`,
`append`, the query's `req`. Also: `AaXMode` (`AaXIx`, `AaXUx{scrub}`,
`AaXPx{scrub, fb}`, `AaXCx{scrub, fb}`), `AaXFallback`, `AaXMode.eq/show`,
`AaFile.perms("rw")` (a request from letters), the file bits
`AaFile.r() ... AaFile.x()`, `AaFileQuery.req/path`; `AaCap.of_name`,
`AaCap.name`; `AaNet.domains/types/protos`; `AaSignal.names`,
`AaSignal.send/receive`; `AaPtrace.read/trace/readby/tracedby`;
`AaMountOp`, `AaMountOpts`, `AaMount.flags`; `AaDbus.send/receive/bind/eavesdrop`.

`perm.bend`: `AaPerms{bits}` (bit i is permission i of a rule kind),
`AaPerms.none/bit/of_bits/bits/union/minus/any/covers/meets/has/add/show`
and the same on bit lists (`AaBits.*`); `AaQual{audit, deny, owner}`;
`AaGrant{audit, deny, perms}`, `AaGrant.of`, `AaGrant.append`.

`parse.bend`: `AaParse.load(opts, files, main)` on `AaSrcFile{name, text}`
byte lists (what `Aa.load` calls); `AaParse.items`, `AaParse.expand`
(includes), `AaVars.expand(text, env, profile_name)` (variables).
`token.bend`: `AaTok.lex(text)`, `AaTerm.of_toks(tokens)`, `AaTok`, `AaTerm`.
`error.bend`: `AaError` (below), `AaError.line`, `AaError.name`, `AaSrc`.
`example.bend`: `AaExample.*` (the example profile `profile(mode)`,
`policy()`, `query(path, perms)`; the policy text `files()`, `loaded()`,
`pol()`, `file(...)`, `exec(...)`; the small one `small_files()`,
`small()`, `small_file(...)`, `small_exec(...)`). `text.bend`: `AaText.of_string`, `eq`,
`is`, `to_string` and the other list helpers.

### Errors

`AaError`, each with the file and line: `AaErrLex` (an unterminated quote,
unbalanced parentheses), `AaErrSyntax`, `AaErrGlob` (a malformed pattern),
`AaErrName` (an unknown capability, network domain, type or protocol, signal
or mount option, or a forbidden combination of them), `AaErrPerms` (w with
a, two exec modes, an exec mode in a deny rule, a bare x in an allow rule, a
target without an exec mode, a leading l with a target), `AaErrUnsupported`
(a rule kind outside the model), `AaErrInclude`, `AaErrIncludeDepth`,
`AaErrVarUndefined`, `AaErrVarRedefined` (= twice, or += before =),
`AaErrPreamble` (a variable or alias after the first profile or inside one),
`AaErrFlag`, `AaErrDuplicate` (two profiles, or two children or hats of one
profile, with one name), `AaErrExecConflict` (two exec rules on one literal
path with different modes or targets, or change_profile rules with exec
conditions that differ on safe and unsafe).

## How the documents are read

The model, rule by rule; [E…] refers to Experiments.

* **Loading.** A file is a preamble (variable assignments, aliases, abi,
  includes) then profiles; a variable or alias after the first profile is an
  error [E22]. Includes are textual and are expanded at most once in each
  block (the top level, each profile, hat or qualifier block), so including
  a file twice is including it once and include cycles end [E07, F03,
  I01-I14]. `<name>` and `"name"` both look up `name` in the file map; a
  missing file is an error unless the include says `if exists` [E24]. The
  directory form of include is not modelled.
* **Variables** are assigned with `=` (an error if already assigned [E09,
  F01, F02]) and extended with `+=` (an error if not assigned [M01]); an
  assignment ends at the end of its line and takes no comma [M01]. A
  reference expands to its one value, or to `{v1,v2,...}`, values may
  refer to other variables, assigned before or after [F16], and a value's
  trailing `/` is dropped before a `/` [G01, G03]. `@{profile_name}` is the
  full name of the profile being built (the page says "the profile name";
  the package chooses the full name, `parent//child`). An empty value `""`
  expands to nothing [F15].
* **Aliases**: `alias /from/ -> /to/,` adds, for each file rule whose
  pattern text (after variable expansion) starts with `/from/`, a copy
  starting with `/to/`; the original stays [F13]. Patterns that begin with
  a brace or a variable's alternatives are not rewritten.
* **Profiles.** `profile NAME [ATTACHMENT] [FLAGS] {`, `PATH [FLAGS] {`
  (the path is name and attachment), children (`profile` inside a profile,
  nested to any depth [E16]), hats (`^NAME` or `hat NAME`, nested [E15]),
  qualifier blocks (`audit {`, `deny {`, `owner {` ...) [E44, E45]. Names
  start with a letter, digit or `/` (the page's rule; apparmor_parser also
  takes `-foo` [F06]); a hat's with a letter or digit. A name that is an
  absolute path is its attachment. Children and hats share one namespace
  [R01]; top-level names are unique [E39]. Flags: one mode (enforce,
  complain, kill, unconfined, default_allow, prompt; two different ones are
  an error [E14E]) and audit; mediate_deleted, attach_disconnected,
  chroot_relative, debug, interruptible, kill.signal= and
  attach_disconnected.path= are accepted and not modelled; `flags=` may be
  left out [E14F]. A child or hat does not inherit its parent's mode
  (apparmor(7)). xattr attachment conditions are not modelled.
* **Qualifiers** come in the order `[audit] [allow|deny] [owner]` [R01];
  allow and deny conflict, also against an enclosing block. owner is only
  for file rules [R01].
* **File rules.** Permissions lead or trail the pattern [E47]; `file` may
  come first [E46]; `file,` alone means every path with r w a l k m and ix
  (a deny rule: all of them and x) (the page gives no meaning; this is a
  stated choice). The letters may repeat [E53] and mix in any order [E31];
  w and a conflict [E06]; at most one exec mode [E54]; a bare x only in deny
  rules and an exec mode only outside them [E04, E05]. w implies a: a w
  rule grants (and a deny w rule denies) append, as apparmor_parser compiles
  w to the write and append bits [M01]. A target after `->` needs an exec
  mode (apparmor_parser also takes `/a rw -> b,` [R01]: a stated, stricter
  choice), and with the permissions leading, l and a target are a link rule,
  refused [R02]. A pattern must start with `/` after expansion (the page's
  rule; apparmor_parser also takes `foo r,` [E27]). Link rules (`link`,
  `l /a -> /b`) are not modelled.
* **The decision.** The grants of the matching rules accumulate as a union
  (the page: rules "are accumulated", order does not matter); granted is
  allowed less denied, so a deny rule always wins; a request is granted
  when all of its permissions are. Enforce and prompt deny what is not
  granted (prompt's upcall is not modelled), kill denies and kills,
  default_allow allows all that no deny rule meets, unconfined allows
  everything, and complain allows what is not granted except what a deny
  rule meets: apparmor(7) says deny rules still deny in complain mode, so
  that is the default; `AaOptions.complain_deny = False` makes complain
  allow everything. An allowed request is audited with the audit flag or an
  audit rule granting a requested permission; a denial is logged unless
  every refused permission is quieted by a deny rule without audit
  (apparmor(7), "deny audit quieting").
* **Exec.** The profile must grant x. The exec mode comes from the
  matching allow rules with exec modes: rules on literal patterns decide
  over pattern rules, and those that decide must agree; this is what
  apparmor_parser enforces at compile time [E02, E03, E40-E43, R01], and
  the package checks the literal case at load and the pattern case when
  the exec happens (`AaExecConflict`), since it does not intersect
  patterns. ix stays, ux and Ux leave confinement, px and Px go to the
  profile named after `->` (a full name) or else to the top-level profile
  whose attachment best matches the path, cx and Cx the same among the
  profile's children (and a target names a child); the i and u forms fall
  back to ix, ux or Ux, the others fail (a missing target is not a load
  error [E17]). Upper case scrubs the environment, except an ix fallback.
  Attachments: a literal one wins, then the longest literal run before the
  first wildcard among the matching alternatives; a tie fails (the page:
  "If the heuristic can not determine a winner ... the exec will be
  denied"; the exact kernel heuristic is undocumented, so this ranking is a
  stated choice, in one def, `AaGlob.rank`). A complain-mode exec without x
  (allowed, logged) and an exec granted by no exec rule (default_allow)
  stay in the profile; a profile in unconfined mode executes as an
  unconfined task (the page: unconfined tasks use a pix transition).
* **Capability**: names in lower case without CAP_ [E19, R01], or all.
* **Network**: `[domain] [type | protocol]` [R01]; a protocol only with
  inet, inet6 or no domain, and not icmp with inet6 [R02]; rules accumulate.
  The access lists and the ip, port and peer conditions of AppArmor 4 are
  outside the model (`AaErrUnsupported`). netlink with a type other than
  dgram or raw is accepted, as apparmor_parser accepts it [R02], though the
  page says otherwise.
* **Signal and ptrace**: the access list, signal set and peer in any order
  [R01], peer once [R01], signal names from the page [R01]. With no access
  list all permissions are implied. r, read, w, write and rw mean receive,
  send and both for signal (the page gives these synonyms for dbus only);
  for ptrace the page gives r, w and rw without meaning: the package reads
  r as read, w as trace, rw as both (a stated choice).
* **Mount**: `options=` is an exact set, `options in` any subset; several
  options conditions each grant their set (as the page documents; its
  KNOWN BUGS say apparmor_parser merges them); fstypes are patterns; a
  query's options are names as mount(8) takes them. An exact set with both
  of an opposed pair (ro and rw, atime and noatime, ...) is refused, as
  apparmor_parser refuses it [R02]. remount and umount take one path, the
  mountpoint, and no `->` [R01].
* **DBus**: message, service and eavesdrop rules with the page's
  restrictions [R01]; values in parentheses are taken as one pattern.
* **change_profile**: an exec mode needs an exec condition [R01]; a rule
  with an exec condition applies only to a change at the exec of a matching
  program (a stated choice). apparmor_parser refuses overlapping exec
  conditions that differ on safe and unsafe [R03]; the package, which does
  not intersect patterns, refuses any two allow rules with exec conditions
  that differ (stricter, and recorded as a known disagreement).
* **Globs** (apparmor.d(5) "Globbing (AARE)", and [G01-G03] where the page
  is silent): `*` any run without `/`, `**` any run, `?` one character but
  `/`, `[...]` and `[^...]` a set (a negated set may match `/`), `{a,b}`
  alternatives (at least two; `{a}` and `{}` are errors), `\c` the character
  c. A `*` that is a whole path segment (after a `/`, before a `/` or the
  end) matches one or more characters, and a `**` after a `/` and before a
  `/`, a `*` or the end matches one or more, the first not `/`: so `/tmp/*`
  and `/tmp/**` do not match `/tmp/` (as the page's examples say), while
  `/a/*b` matches `/a/b` and `/a/{b,*}` matches `/a/`. Runs of `/` collapse
  to one, except a leading `//`. A class may not start with `]` or end with
  `-`; `\` in a class is refused here (apparmor_parser reads `[a\-z]` as a
  range [G02]: refused as a stated, stricter choice). `\x41` and `\101`
  escapes are read by apparmor_parser as hex and octal [G03]; here `\x` is
  `x`.
* **Not modelled**: unix, pivot_root, rlimit, mqueue, io_uring, userns,
  link and all rules, network access and address conditions, xattr
  attachments, `prompt` upcalls, policy namespaces, the implicit rules
  apparmor_parser adds to profiles with hats [I02].

## Experiments

All with apparmor_parser 4.0.1 in WSL (Ubuntu), as `apparmor_parser -Q -K
--base DIR -I DIR FILE` (accept: exit 0) and `-D rule-exprs` /
`-D expanded-variables` (the compiled patterns), on profiles written for
the purpose; the scratch profiles are not kept, but the edge texts of
`ref/gen.py` re-run the deciding ones against apparmor_parser on every
reference run.

| | Profile (inside `profile foo { }` unless shown) | apparmor_parser | Used for |
|---|---|---|---|
| E02 | `/usr/bin/** ix, /usr/bin/foo px,` | accepts | a literal exec rule decides over a pattern one |
| E03, E40 | `/a ix, /a px,` | rejects: conflicting x modifiers | literal exec rules must agree |
| E04 | `deny /x ix,` | rejects | exec modes only outside deny |
| E05 | `/x x,` | rejects | bare x only in deny |
| E06 | `/x wa,` | rejects | w and a conflict |
| E07 | `#include <t>` twice, t assigning `@{HOME}` | accepts | include once per block |
| E08 | `@{NOPE}/x r,` | rejects | undefined variable |
| E09 | `@{A} = /x` then `@{A} = /y` | rejects | no redefinition |
| E14E | `flags=(complain enforce)` | rejects | one mode |
| E14F | `profile foo (complain) {` | accepts | `flags=` optional |
| E15, E16 | hats in hats, children in children | accepts | nesting |
| E17 | `/bin/x cx -> nochild,` | accepts | missing targets are not load errors |
| E19 | `capability bogus,` | rejects | names checked |
| E22 | a variable assignment after a profile | rejects | preamble before profiles |
| E24 | `include if exists <missing>` / `include <missing>` | accepts / rejects | include |
| E27 | `foo r,` | accepts | (the package refuses: patterns start with `/`) |
| E31, E53, E54 | `rmix`, `mrix`, `ixr`; `rr`; `ix px` | accept; accept; reject | permission strings |
| E39 | two profiles named foo | rejects | duplicate names |
| E41, E42, E43 | `/a/* ix, /a/b px` / `/a/* ix, /a/b* px` / `/a/{b,c} ix, /a/b px` | accepts / rejects / rejects | braces make a pattern; patterns must agree |
| E44, E45 | `audit { ... }`, `deny { ... }` | accept | qualifier blocks |
| F01, F02 | the same assignment twice, in one file or two | rejects | `=` twice is an error even when equal |
| F03 | two files including each other | accepts | cycles end |
| F06 | `profile -foo {` | accepts | (the package requires a letter, digit or `/`) |
| F13 | `alias /usr/ -> /mnt/usr/,` with `/usr/** w` | compiles both `/usr/**` and `/mnt/usr/**` | alias adds a copy |
| F15, F16 | `@{A} = ""`; `@{A}` defined from a later `@{B}` | `/x@{A}/y` is `/x/y`; expands | variables |
| I01-I14 | an include holding a hat, included twice in one profile, in two profiles, nested, in a hat | accepted (once per block; again in each block) | include scope |
| I05 | an included hat and the same hat written out | rejects | an include really adds its hat |
| G01-G03 | 80 patterns through `-D rule-exprs` | `*` is `[^/]*`, but `[^/][^/]*` as a whole segment; `**` is `.*`, but `[^/].*` after a `/` and before `/`, `*` or the end; `?` is `[^/]`; `[^b]` stays (matches `/`); `//` collapses except leading; `{a}`, `{}`, `[]]`, `[a-]`, `[!x]` rejected; `\x41`, `\101` are escapes; a variable's trailing `/` merges with a following `/` | the glob semantics |
| M01 | `/x w,` and the other modes through `-D rule-exprs` | w's mask holds write and append | w implies a |
| M01 | `@{A} += /y` alone; `@{A} = /x,` | reject | variable statements |
| R01 | 110 rule texts (qualifier orders, network, signal, ptrace, mount, dbus, change_profile forms, `uX`, `/a rw -> b`) | see the edge texts | the rule grammar |
| R02 | network domain x type x protocol; mount option pairs; `lpx /x -> foo` vs `/x lpx -> foo` | protocols only with inet/inet6/none (not inet6 icmp); opposed exact options rejected; leading l with a target rejected | network, mount, link |
| R03 | change_profile with safe, unsafe and default modes, with and without targets | overlapping exec conditions differing on safe/unsafe rejected, default is safe | change_profile |

## Extension points

* **Options** (`AaOptions`): whether deny rules apply in complain mode,
  include depth, variables predefined for every file (a system's tunables).
* **The file map** is the caller's: `Aa.load` reads nothing but the
  `AaSource` list, so policies can come from anywhere.
* **One def per choice**, each replaceable alone: the decision per mode
  (`AaEval.decide.mode`), what a grant contributes (`AaAcc.single`), the
  attachment ranking (`AaGlob.rank`, `AaAttach.better`), the exec mode
  choice among matching rules (`AaXPick.rules`), what each rule kind
  matches (`*.matches`), the glob semantics (`glob.bend`'s lexer: the star
  treatment and slash collapse are each one def). The laws say which
  properties a replacement must keep.
* **New rule kinds**: a `rule_x.bend` with a rule type, a parser from
  terms, `matching` and `grants`; a field in `AaRules`; a branch in
  `AaParse.keyword`/`dispatch`; an `AaEval.x`. The decision engine and its
  laws are shared by every kind.
* **Types are open**: profiles, rules and queries are plain records, so a
  policy can be built without text (`example.bend` does), and queried
  through `AaEval` directly.
* **Streaming** is not offered: a policy is loaded whole, since includes,
  variables and aliases need the whole file map and preamble before any
  rule can be read; each query is one pure call on a loaded policy.

## Laws

`LAWS.bend`. **For every
input**, proved by induction in `PROOF.bend`:

* `glob_seq_model`: the backtracking matcher agrees with the list model,
  for every brace-free sequence and path. The list model enumerates every
  way to cut the path into one piece per token (`AaGCuts.all`) and checks
  each piece against its token;
* `glob_run`: the fast matcher (the set of active positions, moved a byte
  at a time) agrees with the backtracking one, for every sequence and path;
  so `glob_model` (what evaluation uses, `AaGlob.matches`) and
  `glob_ref_model` (`AaGlob.matches_ref`) agree with the list model for
  every pattern and path;
* `granted_never_denied`: for every set of grants, what is granted never
  meets what is denied;
* `deny_wins`: for every options, flags, request and grants, a request that
  a deny grant meets is not allowed, in every mode where deny rules apply;
  `file_deny_wins`: the same for file rules on any profile and query;
* `unmatched_denied`: with no grants, a nonempty request is denied in
  enforce, kill and prompt modes; `file_unmatched_denied`: a path no file
  rule of the profile matches is denied;
* `complain_decided_by_deny`: in complain mode a request is allowed exactly
  when no applicable deny rule meets it; `complain_never_denies`: with
  `complain_deny` off, complain mode never denies;
* `include_idempotent_file`, `_capability`, `_network`, `_signal`,
  `_ptrace`, `_mount`, `_dbus`, `_change_profile`: adding a set of rules to
  a profile twice gives every request of every kind the decision adding it
  once gives (the text-level include is idempotent by construction: it is
  expanded once per block);
* `exec_needs_x`: an exec the profile does not grant x for fails.

The repetitive parts of `PROOF.bend` (the five token cases of the glob
theorem, the per-kind include proofs, and the full case splits of the
propositional identities the fast matcher's step comes to) were written by
small scripts and are kept as plain text, to be edited by hand.

**Witnesses** (the `*_sat` laws and the examples after them): every
hypothesis above holds for some input, on the example profile of
`example.bend`, and the laws' conclusions hold there (deny, allow, audit,
unmatched, complain with and without `complain_deny`, kill). **Vectors**:
globs as apparmor_parser compiles them (15 laws), and 6 decisions and 2
execs on a small policy text loaded through `Aa.load` (a tunable, an
abstraction included twice, a variable, a deny rule, a px exec into a
complain-mode profile). The larger example policy is in `check.bend`
instead: the `--verdict` kernel runs out of fuel evaluating its parse (it
reports a "mismatch"), while the checker accepts it.

## Tests

`ref/run.sh` (20 random policies by default; `POLICIES=n` and `SEED=s`
change them) compares the package with an **independent Python model**
written here from the same documents (`ref/gen.py`; it shares an author
with the package, so it guards against slips, not against a shared
misreading). The model holds each policy as data and renders it to text:
the package parses the text, the model evaluates the data; the model
matches globs with the `re` module of Python, through its own translation
to regular expressions, not with either of the package's matchers. Each
policy has a main profile (a random mode and audit flag, 4 to 11 rules of
every kind, an include of an abstraction, sometimes twice, variables,
sometimes an alias), a child, a hat and attached profiles; each gets 26
random queries of every kind (file with and without owner, capability,
network, signal, ptrace, mount, dbus, change_profile, exec): 520 queries
and 20 loads by default. It also loads 63 edge texts and checks the package
accepts or rejects each as expected.

With **apparmor_parser** installed (it is in WSL; Ubuntu package
`apparmor`), run.sh also checks, as a black box, that apparmor_parser
accepts every generated policy (all of which the package must load), and
runs the edge texts through it: 53 agree, and 10 are known, listed
disagreements, each where the package is stricter (`/a rw -> b`, `foo r,`,
`uX`, `profile -e`, the unix, pivot_root, rlimit and link rules outside the
model, `abi` without the system's abi files, and change_profile safe and
unsafe on disjoint exec conditions). A disagreement outside the list fails
the test. Runtime decisions could not be compared with the kernel: loading
a profile needs root, and none was used.

Run on the JavaScript lane with 80 policies (2,080 queries) each, seeds
2026, 1, 3, 5, 7, 99, 31337 and 11 to 22 all match, and apparmor_parser
accepted every generated policy. The first runs found five generated
policies apparmor_parser rejected (a protocol with a domain other than
inet or inet6; opposed exact mount options; a leading l with an exec target;
change_profile safe and unsafe on overlapping exec conditions); the package
now rejects those too (experiments R02, R03), and the generator no longer
produces them.

`check.bend` runs the example policy of `example.bend` (19 file,
capability, network and signal decisions, 8 execs), 13 loads (12 of them
errors), 5 globs
(one with four `**` on a 27-segment path), and a 600-rule profile with a
2,200-byte path.

## Speed and size

Measured on native builds (Bend 2.0.37, clang, WSL2), loading one profile
of n `/data/dI/** r` and `deny /data/dI/secret w` rules and answering four
file queries, one on a 110 KB path:

| Rules | Text | Time | Peak memory |
|---|---|---|---|
| 2,000 | 47 KB | 0.43 s | 17 MB |
| 10,000 | 240 KB | 0.47 s | 35 MB |
| 100,000 | 2.5 MB | 4.4 s | 309 MB |

A query matches the request against every rule of its kind; each match
runs the fast glob matcher, which does a fixed amount of work per byte and
pattern position and stops when no position is left, so a query costs at
worst about the total length of the patterns times the path. Bend
evaluates every argument of a call, so the backtracking matcher (the
reference) explores every branch: a pattern with six `*` on an 8-segment
path took 36 s with it on the JavaScript lane, and is immediate with the
fast one. For the same reason the loader avoids work in branches it does
not take (an include already seen, a text without variables).

Loading is linear in the text: the lexer, the statement splitter, include
expansion and profile building are tail-recursive loops, rules are put at
the front of their list, and the exec-conflict check compares only literal
exec rules with each other. `check.bend` builds in 14 s and runs in 0.09 s;
`ref/run.sh` takes about a minute natively (three case files of about 20 s
of build each).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes (native), `ref/run.sh` 20 policies, 520 queries and 63
edge texts match, with apparmor_parser accepting every generated policy
(53 edge texts agree, 10 known disagreements), `scripts/deps.sh apparmor`
ok.
