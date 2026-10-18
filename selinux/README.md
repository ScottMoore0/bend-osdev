# bend-osdev-selinux

SELinux policy loading and evaluation, as a pure model: a policy written in
CIL is read, compiled and checked (neverallow, conflicting transitions),
and then answers the security server's questions: the access vectors for a
source context, a target context and a class; the decision on a request,
in enforcing or permissive mode; and the context of a new object or of a
process after exec.

The package is policy logic, so its point is its laws: properties of the
evaluation for every policy and every query, proved in `PROOF.bend` (see
Laws).

**Clean room.** The kernel's SELinux security server, libsepol and
checkpolicy are GPL or LGPL. None of their source, nor any quotation of it,
was opened, read or searched while writing this package. It was written from
documentation only (see Specification), **from memory of that
documentation**: the machine it was written on had no network, so no
document was open while writing. Every fact below names the document it
comes from, and every place where the documentation (or the memory of it)
does not settle a question names the choice made. This is what lets the
package be MIT.

**No binary policy.** The kernel's binary policy format (`policy.33` and its
relatives) is not read or written: its exact layout is defined only by GPL
code (libsepol), not by a published specification. The input is CIL text.

## Specification

Documents used (all read before, and remembered, not consulted while
writing; none is a source file):

* [N] The SELinux Notebook (Richard Haines; CC BY-SA 4.0): "SELinux
  Overview", "Security Context", "Type Enforcement", "Role-Based Access
  Control", "Multi-Level and Multi-Category Security", "Conditional Policy",
  "Constraints", "Computing Security Contexts", "Access Vector Cache",
  "SELinux Permissive and Enforcing Modes", "Object Classes and
  Permissions", "The CIL Policy Language".
* [C] The CIL Reference Guide (the SELinux project's CIL documentation):
  the statements of the subset below, their argument forms, and the
  expression operators.
* [M] The man pages, read as documentation: secilc(8), checkpolicy(8),
  security_compute_av(3), security_compute_create(3) (with
  security_compute_relabel and security_compute_member), avc_has_perm(3),
  selinux(8), setenforce(8), setsebool(8), getsebool(8).
* [S] secilc 3.5, run as a black box only (its output and error messages
  on small policies, never its source), to find which policies it refuses.
* [P] The papers: Smalley, Vance and Salamon, "Implementing SELinux as a
  Linux Security Module" (NAI Labs Report 01-043, 2001); Spencer, Smalley,
  Loscocco, Hibler, Andersen and Lepreau, "The Flask Security Architecture:
  System Support for Diverse Security Policies" (USENIX Security 1999);
  Loscocco and Smalley, "Integrating Flexible Support for Security Policies
  into the Linux Operating System" (FREENIX 2001).

Three sections were read again later, when `ref/run.sh` first ran with
secilc installed and found policies secilc refuses that the package loaded:
[C] "Constraint Statements", "Conditional Statements" and "Type
Statements", and [N] "Type Statements" (documentation, not source).

Each fact the model relies on, and its source:

| Fact | Source |
|---|---|
| A security context is user, role, type and (with MLS) a range low-high of levels; text form `user:role:type:range` | [N] Security Context; [P] Flask |
| The security server computes access vectors for (source context, target context, class): allowed, auditallow, auditdeny (and decided, not modelled) | [M] security_compute_av(3); [P] Flask, LSM report |
| A permission is allowed when an allow rule names the source type, the target type (or `self`, the source type itself) and the class with that permission | [N] Type Enforcement; [C] allow |
| auditallow rules audit granted permissions; dontaudit rules silence denials (auditdeny is every permission less those) | [N] Access Vector Rules, AVC; [C] auditallow, dontaudit |
| A constraint names a class and permissions; a named permission is removed when the expression (over u1 r1 t1 u2 r2 t2, names, and with MLS l1 h1 l2 h2) is false | [N] Constraints; [C] constrain, mlsconstrain |
| In a constraint, u1 r1 t1 are the source context's and u2 r2 t2 the target's, in the forms `(op u1 u2)`, `(op t1 t2)`, `(op t2 type_id)`, ...; so t1 cannot stand on the right, and u3 r3 t3 belong to validatetrans | [C] constrain; [S] |
| A typetransition with an object name (a name transition) is not allowed inside a conditional | [C] typetransition; [N] type_transition ("no name transitions" in conditionals) |
| Two type rules (or roletransition rules) giving different answers to the same question are refused, unless they are the two branches of one condition | [S] (not in [C] or [N]) |
| MLS constraints apply only when the policy enables MLS | [N] MLS; [C] mls |
| l1 dominates l2 when its sensitivity is at least l2's and its categories include l2's; domby, eq, incomp follow | [N] MLS ("dom", "domby", "incomp") |
| Sensitivities are ordered by sensitivityorder, categories by categoryorder; a range's high level dominates its low | [C] sensitivityorder, categoryorder, levelrange; [N] MLS |
| Booleans have defaults and current values; a booleanif applies its true list or its false list by its condition (and, or, xor, not, eq, neq) | [N] Conditional Policy; [C] booleanif; [M] setsebool(8) |
| neverallow rules are checked when the policy is compiled; a policy with an allow rule (in either branch of a conditional) granting what one forbids is refused | [M] checkpolicy(8), secilc(8) (`-N` turns the check off); [N] |
| Enforcing mode refuses denied requests; permissive mode logs them and allows; typepermissive makes one domain permissive | [N] Permissive and Enforcing Modes; [M] setenforce(8); [C] typepermissive |
| A request is granted when every requested permission is allowed; a denial is audited when the denied permissions meet auditdeny, a grant when the request meets auditallow | [M] avc_has_perm(3); [N] AVC |
| typetransition gives the type of a new object (a file in a directory: target = the directory), or of a process after exec (class process, target = the file); a rule with an object name applies only to that name and wins over one without | [N] Computing Security Contexts; [C] typetransition |
| Without a rule, a new object takes the target's (parent's) type, the source's user, the role object_r and the source's low level; a process keeps its user, role, type and range | [N] Computing Security Contexts |
| roletransition gives the role of a process after exec; roleallow says which role changes are allowed | [N] RBAC; [C] roletransition, roleallow |
| typechange gives the type on relabel, typemember the type of a polyinstantiated member | [M] security_compute_relabel, security_compute_member; [C] typechange, typemember |
| Types and attributes share one namespace; an attribute stands for its members; typeattributeset takes names or an expression (and, or, xor, not, all) and may name other attributes; typealias/typealiasactual name a type again | [C] typeattribute, typeattributeset, typealias |
| A class may take a common's permissions (classcommon), which come first | [C] classcommon; [N] Object Classes and Permissions |
| object_r is predefined and holds every type; a context is valid when the user holds the role, the role holds the type, and the range is within the user's | [N] Security Context, RBAC; [C] role, userrole, userrange |

### Where the documentation does not settle it, and the choice made

* **CIL forms, from memory.** The argument forms of the subset (for example
  `(all)` as an operator applied to nothing, `(range c0 c3)`, a
  typetransition's object name as a quoted string before the result) follow
  the CIL Reference Guide as remembered. `ref/run.sh` compiles every
  generated policy with secilc, as a black box, and it accepts exactly the
  ones the package loads (see Tests).
* **Anonymous type sets in rules.** CIL wants a name in a rule's source and
  target; the package also accepts an expression there (a superset).
* **Conflicting transitions.** secilc refuses two type rules of the same
  kind (typetransition, typechange, typemember) that give different types
  for some source, target and class in common (and the same object name,
  or none), attributes expanded; and two roletransition rules that give
  different roles for some role, type and class in common. So does the
  package, after the neverallow check (`SeTe.transitions_ok`;
  `SeErrTypeConflict` and `SeErrRoleTransConflict` name the first pair).
  The documents do not describe this check; what follows was observed from
  secilc. Rules that can be in force together conflict whatever their
  conditions say: an unconditional rule and a conditional one (whatever the
  boolean defaults), two rules in one branch, two rules in different
  booleanifs. Only the two branches of one condition are exclusive. The
  package takes two conditions to be one when they are written the same,
  after one outer `not` is taken off (swapping that condition's branches):
  `b` and `(not b)` are one condition, with branches swapped. secilc also
  takes some differently written conditions to be one (`(and b0 b0)` and
  `b0`; `(or b0 b1)` and `(or b1 b0)`), so the package refuses a few
  policies secilc accepts (rules in opposite branches of conditions written
  in two such ways); it never accepts one that secilc refuses for this.
  With no conflicts, which matching rule `SeTe.new_type` meets first no
  longer matters.
* **Name transitions in a booleanif** are refused (`SeErrBadStatement`,
  "booleanif: typetransition with an object name"), as [C] says and secilc
  does.
* **Constraint operand words.** In a constraint expression, `u1 u2 u3 r1 r2
  r3 t1 t2 t3 l1 l2 h1 h2` are always operands, never a user, role or type
  of that name (a policy may declare a type `t1`, but `(eq t2 t1)` compares
  with the source type, not with it). A right operand that is one of these
  words must be the left operand's partner (`u2` after `u1`, `r2` after
  `r1`, `t2` after `t1`, or a level after a level); any other is refused
  (`SeErrBadStatement`, "constraint operand t1"), as secilc refuses it. In
  a list (`(eq u1 (u0 u1))`) they are names.
* **neverallow and conditional rules.** The check covers the allow rules of
  both branches of every booleanif, whatever the booleans: a policy is
  refused if some boolean state would let it grant what a neverallow
  forbids. neverallow rules inside a booleanif are refused by the compiler
  (CIL does not allow them there).
* **Attribute cycles.** Attributes that name each other in a cycle are
  refused (`SeErrAttributeCycle`), as secilc does.
* **A class the policy does not define** gets empty vectors (the kernel's
  handleunknown setting, not modelled, decides this for the real kernel).
  handleunknown is read and ignored.
* **decided** (the fourth vector of security_compute_av) is not modelled:
  every vector here is fully decided.
* **Roles in constraints**: `(eq r1 r2)`, `(neq ...)` and role names are
  supported; role dominance (`dom r1 r2`) is not. `u3 r3 t3`
  (validatetrans) are not.
* **Levels as text** show categories as a comma list of every member
  (`s0:c0,c1,c2`); the kernel's text form compresses runs as `c0.c2`. Both
  are read.
* **A context without a range** (`u:r:t`) reads as the level s0 (sensitivity
  0, no categories).
* **The process class** is the class named `process` (the kernel's fixed
  class for exec transitions).
* **The default role of a new object** is object_r (role 0) unless a
  roletransition names the class; **relabel and member** keep the target's
  user, role and range and change only the type.
* **sensitivitycategory** is read and kept (`SeDecl.sens_cats`), but context
  validity does not check categories against it.
* **Permission numbering** within a class is the common's permissions, then
  the class's own, each in declaration order (`SeBits.to_u32` gives the
  vector as a kernel-style 32-bit mask).

## The CIL subset

Read and compiled (`SeCil.keywords` is the table):

* declarations: `class`, `common`, `classcommon`, `type`, `typeattribute`,
  `typeattributeset`, `typealias`, `typealiasactual`, `role`, `roletype`,
  `user`, `userrole`, `userlevel`, `userrange`, `sensitivity`,
  `sensitivityorder`, `sensitivitycategory`, `category`, `categoryorder`,
  `level`, `levelrange`, `context`, `boolean`, `mls`, `typepermissive`;
* rules: `allow`, `auditallow`, `dontaudit`, `neverallow`,
  `typetransition` (with an optional object name), `typechange`,
  `typemember`, `booleanif` (with `true` and `false` branches holding
  access vector and type rules, but no name transitions), `roleallow`, `roletransition`,
  `constrain`, `mlsconstrain`;
* expressions: sets of types, permissions and categories as a name, a list
  of names, or `(and a b)`, `(or a ...)`, `(xor a b)`, `(not a)`, `(all)`,
  and for categories `(range c0 c3)`; conditions with `and or xor not eq
  neq`; constraint expressions with `and or not` over `(eq|neq x y)` for
  users, roles and types (`u1 u2`, `t1 t2`, `t1 names`, ...) and
  `(dom|domby|incomp|eq|neq l h)` for levels;
* read and ignored: `classorder`, `handleunknown`, `policycap`, `sid`,
  `sidorder`, `sidcontext`, and the labeling statements (`filecon`,
  `fsuse`, `genfscon`, `portcon`, `nodecon`, `netifcon`, `ioportcon`,
  `iomemcon`, `pirqcon`, `pcidevicecon`, `devicetreecon`, `ibpkeycon`,
  `ibendportcon`, `selinuxuser`, `selinuxuserdefault`, `userprefix`),
  which do not change access decisions;
* refused as unsupported (`SeErrUnsupported`): `block`, `blockinherit`,
  `blockabstract`, `in`, `macro`, `call`, `optional`, `tunable`,
  `tunableif`, `classpermission`, `classpermissionset`, `classmap`,
  `classmapping`, role and user attributes, `typebounds`, `rolebounds`,
  `userbounds`, `rangetransition`, `validatetrans`, `mlsvalidatetrans`,
  the extended-permission rules, the `default*` statements,
  `expandtypeattribute`, and category and sensitivity aliases; any other
  keyword is `SeErrUnknownStatement`.

## Files

| File | Holds |
|---|---|
| `selinux.bend` | the entry: `Selinux.load` (CIL text to a checked policy), contexts as text, the questions by name |
| `bits.bend` | `SeBits`: sets of small numbers (types, permissions, categories, roles, booleans) as lists of bits |
| `mls.bend` | levels (`SeLevel`), ranges (`SeRange`), dominance |
| `contexts.bend` | security contexts (`SeContext`) |
| `constraints.bend` | constraint expressions (`SeCexpr`), constraints (`SeConstraint`), their evaluation (`SeConstraints.permits`) and their application to a vector (`SeConstraints.apply`) |
| `policy.bend` | the policy model (`SePolicy`: declarations, rules, MLS, boolean state), its error type (`SeError`), names, context validity |
| `te.bend` | type enforcement: which rules cover an access, the rules in force under the booleans, the neverallow check, type and role transitions, the conflicting-transitions check |
| `avc.bend` | access vectors (`SeAvc.compute`), decisions (`SeAvc.check`, `SeOptions`), new contexts (`SeAvc.compute_create`, `compute_relabel`, `compute_member`) |
| `cil.bend` | the CIL reader (`SeCil.read`) and compiler (`SeCil.compile`, `SeCil.load`) |
| `example.bend` | a policy built in the model (`SeExample.policy`), contexts for it, and a CIL policy (`SeExample.cil`) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh`, `ref/.gitignore` | the differential test (`cases.bend`, `expected.txt` and `cil/` are generated, and ignored) |

## API

Numbers stand for names throughout: types and attributes (one namespace),
roles (object_r is 0), users, classes, permissions (per class), booleans,
sensitivities and categories (by their order). `SePolicy.lookup(p,
"t:name")` and the `Selinux.*` defs translate.

`selinux.bend`:

| Def | Meaning |
|---|---|
| `Selinux.load(o)`, `Selinux.load_string(s)` | a CIL policy (`Octets` or `String`) compiled and checked: `Result<&2, &2, SeError, SePolicy>` |
| `Selinux.validate(p)` | the load-time checks of a policy built otherwise: `SeErrNeverallow{never, allow}` names the first neverallow rule and allow rule that conflict; then `SeErrTypeConflict{first, second}` the first two type rules, or `SeErrRoleTransConflict{first, second}` the first two roletransition rules, that conflict |
| `Selinux.context(p, s)`, `Selinux.level`, `Selinux.range` | text to `SeContext`, `SeLevel`, `SeRange` (`SeErrBadContext`, `SeErrUndeclared`) |
| `Selinux.context_show(p, c)`, `level_show`, `range_show`, `perms_show(p, cls, set)` | and back; a permission set as `{ read write }` |
| `Selinux.id(p, key)`, `Selinux.class(p, name)`, `Selinux.perms(p, cls, names)` | numbers of names |
| `Selinux.compute_av(p, scon, tcon, cls)` | the access vectors, by name |
| `Selinux.check(opts, p, scon, tcon, cls, perms)` | the decision on a request, by name |
| `Selinux.create(p, scon, tcon, cls, name)` | the new context, as text |
| `Selinux.set_bool(p, name, v)` | the policy with a boolean set |
| `SeError.show(e)` | an error as text |

`avc.bend`:

| Def | Meaning |
|---|---|
| `SeAvd{allowed, auditallow, auditdeny}` | the access vectors (`SeBits` over the class's permissions) |
| `SeAvc.compute(p, s, t, c)` | security_compute_av |
| `SeAvc.allowed(p, s, t, c)`, `SeAvc.rules_av(p, kind, st, tt, c)`, `SeAvc.nperms(p, c)` | the allowed vector; the union of the permissions of the rules in force of one kind; the class's size |
| `SeOptions{enforcing, permissive_types}`, `SeOptions.default()`, `SeOptions.permissive()` | the mode, and whether typepermissive is honoured |
| `SeDecision{granted, denied, audited}`, `SeAvc.check(o, p, s, t, c, req)`, `SeAvc.lenient(o, p, s)` | avc_has_perm: the request's decision; whether a denial is let through |
| `SeAvc.compute_create(p, s, t, c, name)`, `SeAvc.compute_relabel`, `SeAvc.compute_member`, `SeAvc.is_process(p, c)` | security_compute_create, _relabel, _member; the process class |

`te.bend`:

| Def | Meaning |
|---|---|
| `SeTe.rule_matches(r, kind, st, tt, c)`, `SeTe.rule_covers(r, kind, st, tt, c, k)`, `SeTe.any_covers(rs, ...)` | a rule matches a type pair and class; covers a permission; some rule of a list does |
| `SeTe.active_av(p)`, `SeTe.covers(p, kind, st, tt, c, k)` | the access vector rules in force (unconditional, and of each booleanif the chosen branch); one of them covers the permission (the specification `SeAvc.compute` is proved to meet) |
| `SeTe.branch_av(cd, bs)`, `SeTe.cond_av(cs, bs)`, `SeTe.cond_all_av(cs)`, `SeTe.all_av(p)` | a booleanif's chosen rules; all chosen; both branches of all; every rule |
| `SeTe.cond_mentions(p, kind, st, tt, c, k)`, `SeTe.ever_covers(...)`, `SeTe.never_covers(p, st, tt, c, k)` | a conditional rule covers it; some rule in some boolean state does; a neverallow rule forbids it |
| `SeTe.conflict(n, a)`, `SeTe.types_meet(n, a)`, `SeTe.meet_tt`, `meet_ts`, `meet_st`, `meet_ss` | a neverallow rule and an allow rule grant something in common |
| `SeTe.never_ok_one(ars, n)`, `SeTe.never_ok(ns, ars)`, `SeTe.neverallow_ok(p)`, `SeTe.first_conflict(p)` | the neverallow check |
| `SeTe.ty_matches`, `SeTe.name_ok`, `SeTe.find_ty`, `SeTe.branch_ty`, `SeTe.cond_ty`, `SeTe.active_ty(p)`, `SeTe.new_type(p, kind, st, tt, c, name)`, `SeTe.ty_gives(rs, kind, st, tt, c, x)` | type rules: in force, the type a rule gives, and the specification of it |
| `SeTe.role_allowed(p, r1, r2)`, `SeTe.role_trans(p, r, tt, c)` | roleallow and roletransition |
| `SeTyPlace` (`SeTyUncond`, `SeTyIn{cond, branch}`), `SeTyPlace.of(e, branch)`, `SeTyPlace.exclusive(a, b)`, `SeTyPlaced{place, rule}`, `SeTyPlaced.rule`, `SeTe.placed_ty(p)` | where a type rule sits (a condition `(not e)` taken as `e`, branches swapped); whether two places are the two branches of one condition; every type rule with its place |
| `SeTe.name_eq`, `SeTe.ty_meet(a, b)`, `SeTe.ty_clash(a, b)`, `SeTe.placed_clash(x, y)`, `SeTe.role_clash(a, b)` | two rules match a question in common and answer it differently (placed rules: and can be in force together) |
| `SeTransConflict` (`SeTyClash{first, second}`, `SeRoleClash{first, second}`), `SeTe.first_trans_conflict(p)`, `SeTe.transitions_ok(p)` | the conflicting-transitions check |

`policy.bend`: the types `SeAvKind` (`SeAllow`, `SeAuditallow`,
`SeDontaudit`, `SeNeverallow`), `SeAvRule{kind, src, tgt, self, cls,
perms}`, `SeTyKind`, `SeTyRule{kind, src, tgt, self, cls, name, result}`,
`SeBexpr` (`SeBVar`, `SeBNot`, `SeBAnd`, `SeBOr`, `SeBXor`, `SeBEq`,
`SeBNeq`), `SeBexpr.eval(e, bs)` and `SeBexpr.is_eq(a, b)` (written the
same), `SeCond{expr, tav, tty, fav, fty}`,
`SeRoleAllow`, `SeRoleTrans`, `SeTypeDef{name, attr, members}`,
`SeClass{name, perms}`, `SeRole{name, types}`, `SeUser{name, roles, level,
range}`, `SeSym`, `SeCtxDef`, `SeConflict`, `SeDecl`, `SeRules`,
`SePolicy{decl, rules, mls, state}` (all with accessors), and `SeError`
(`SeErrSyntax`, `SeErrUnknownStatement`, `SeErrBadStatement`,
`SeErrUndeclared`, `SeErrDuplicate`, `SeErrAttributeCycle`,
`SeErrUnsupported`, `SeErrBadContext`, `SeErrNeverallow`,
`SeErrTypeConflict`, `SeErrRoleTransConflict`). Defs:
`SePolicy.av`, `ty`, `conds`, `constraints`, `permissive`, `classes`,
`syms`, `lookup`, `with_bools`, `set_bool`, `with_mls`, `context_valid`,
`type_name`, `role_name`, `user_name`, `class_name`, `class_perms`,
`sens_name`, `cat_name`, `bool_name`; `SeAvKind.is_eq`, `SeTyKind.is_eq`.

`constraints.bend`: `SeCattr` (`SeCUser`, `SeCRole`, `SeCType`), `SeCside`
(`SeCSource`, `SeCTarget`), `SeLsel` (`SeL1`, `SeH1`, `SeL2`, `SeH2`),
`SeLop` (`SeLDom`, `SeLDomby`, `SeLIncomp`, `SeLEq`, `SeLNeq`), `SeCexpr`
(`SeCNot`, `SeCAnd`, `SeCOr`, `SeCPair`, `SeCSet`, `SeCLevel`),
`SeConstraint{mls, cls, perms, expr}`; `SeCexpr.eval(e, s, t)`,
`SeConstraint.applies`, `holds`, `holds_kind`, `SeConstraints.permits(cs,
mls_on, s, t, c, k)`, `SeConstraints.permits_kind(cs, want_mls, ...)`,
`SeConstraints.apply(cs, mls_on, s, t, c, av)`.

`mls.bend`: `SeLevel{sens, cats}`, `SeRange{low, high}`, `SeLevel.make`,
`canonical`, `has_cat`, `dom`, `domby`, `eq`, `incomp`, `SeRange.single`,
`valid`, `contains`, `within`, `is_eq`. `contexts.bend`:
`SeContext{user, role, typ, range}`, `low`, `high`, `with_type`,
`with_role`, `with_range`, `is_eq`. `bits.bend`: `SeBits.empty`, `has`,
`single`, `full`, `or`, `and`, `andnot`, `xor`, `of_list`, `any`, `subset`,
`set`, `last`, `is_norm`, `norm`, `to_list`, `to_u32`. `cil.bend`:
`SeSexp` (`SeAtom`, `SeList`), `SeSexp.show`, `SeCil.read`, `SeCil.compile`,
`SeCil.load`, `SeCil.keywords`. Everything else (`SeAvc.add`, `SeAvc.collect`,
`SeAvc.collect_conds`, `SeAvc.decide`, `SeAvc.create.go`, the `SeCil.*` helpers,
the `*.go`, `*.hit`, `*.step` defs) is internal.

## Extension points

* **Options.** `SeOptions` holds the real choices of a decision: enforcing
  or permissive, and whether permissive types are honoured, with
  `SeOptions.default()` (enforcing, honoured) and `SeOptions.permissive()`.
  MLS on or off comes from the policy and can be changed with
  `SePolicy.with_mls`; booleans with `SePolicy.set_bool` and
  `with_bools`.
* **Other front ends.** The model (`policy.bend`) has no CIL in it: a policy
  built directly, as `example.bend` does, or by another front end (a
  kernel-policy-language reader, say), is evaluated and checked the same way
  (`Selinux.validate`).
* **More CIL.** A statement is added by an entry in `SeCil.keywords` and a
  case in the compiler's pass that handles its kind
  (`SeCil.rule.step` for rules); the unsupported list says what is missing.
* **The specification and the implementation.** `SeAvc.compute` folds over
  the rules and constraints; `SeTe.covers` and `SeConstraints.permits` say
  declaratively what it must answer, and a law ties them for every input,
  so a faster implementation (an index by source type, a cache in front of
  `SeAvc.compute` as the kernel's AVC is) can replace the fold and be proved
  against the same specification.
* **Defaults of new contexts.** `SeAvc.create.go` holds the Notebook's
  defaults; CIL's `defaulttype`, `defaultrole`, `defaultuser` and
  `defaultrange` would be parameters there.

Streaming: none. A policy is loaded whole: CIL statements may come in any
order, names are resolved and attributes expanded across the whole text,
and the neverallow check needs every rule. The reader is a single pass over
the bytes, a byte at a time, so a streaming reader would be a small step if
a use appears.

## Laws

`LAWS.bend`, every law proved
in `PROOF.bend` for every input:

* **access** (`av_allowed_exact`): permission k is in the allowed vector of
  `SeAvc.compute(p, s, t, c)` exactly when an allow rule in force covers it
  (`SeTe.covers`) and every constraint holds (`SeConstraints.permits`, MLS
  constraints only with MLS on). From it: `allowed_needs_allow`,
  `allowed_needs_constraints` (every plain constraint holds) and
  `allowed_needs_mls` (with MLS on, every MLS constraint holds: MLS
  dominance as the policy states it); `av_auditallow_exact` and
  `av_auditdeny_exact` say the same of the audit vectors;
* **modes**: in enforcing mode, for a source type that is not permissive, a
  single permission is granted exactly when it is allowed
  (`granted_enforcing`); permissive mode, and a permissive source type,
  grant every request (`permissive_grants`, `permissive_type_grants`);
* **booleans**: an access no conditional rule mentions gets the same answer
  in every boolean state (`bool_only_conditional`, `bool_av_independent`);
  with `av_allowed_exact`, whose `SeTe.covers` is over the unconditional rules
  and the chosen branch of each booleanif, booleans switch exactly the
  conditional rules;
* **neverallow**: a policy that passes the check never grants, under any
  booleans, what a neverallow rule forbids (`neverallow_sound`,
  `neverallow_never_allowed`); `Selinux.load` answers a policy only if it
  passes (`load_checks_neverallow`), and `Selinux.validate` refuses one that
  fails (`validate_refuses`);
* **conflicting transitions**: `Selinux.load` answers a policy only if it
  passes the transition check (`load_checks_transitions`), and
  `Selinux.validate` refuses one that fails it
  (`validate_refuses_transitions`, witness
  `witness_transitions_conflict`);
* **MLS**: dominance is reflexive, transitive and antisymmetric on canonical
  levels (`dom_refl`, `dom_trans`, `dom_antisym`), a partial order;
  `SeLevel.make` builds canonical levels (`level_make_canonical`);
* **transitions**: the type `SeTe.new_type` gives comes from a matching rule
  in force (`new_type_sound`), and is the new context's type
  (`create_by_rule`); without a rule an object takes the target's type and
  a process keeps its own (`create_object_default`,
  `create_process_default`);
* **sets**: membership of `or`, `and`, `andnot`, `single`, `full`, `norm`;
  `norm` is canonical; `subset` of a singleton; `any` and `subset` against
  membership.

Every law with a hypothesis has a witness law (an input from
`example.bend`, or a CIL text, that satisfies it), so none is vacuous.

Four vector laws, small CIL texts proved by computation: the load refuses a
misused constraint operand (`load_refuses_operand_word`: `(eq t2 t1)` with
a type named t1), a name transition in a booleanif
(`load_refuses_name_transition_in_booleanif`) and two typetransition rules
that disagree (`load_refuses_conflicting_transitions`), and accepts two
that disagree in the two branches of one booleanif
(`load_branch_transitions`).

The seven laws added on 2026-10-18 (the two transition laws, the witness
and the four vectors) carry the DRAFT line until the maintainer reviews
them.

The CIL compiler is otherwise covered by `check.bend` and the differential
test, not by a for-all law. A for-all law for it (CIL text
printed and read back) would need a printer for the model and reasoning
about text a character at a time; it is not attempted.

The proofs are by induction over the rules, constraints and bit lists, with
the decisions as Bool parameters matched in lemmas ("convoy" style); no
proof uses another package's internals (the package uses only `bytes`'
`Octets.of_string` and `Octets.to_list`, and its proofs nothing of
`bytes`).

## Tests

* `check.bend`: the CIL example policy (`SeExample.cil`): load errors
  (neverallow, in a conditional too; undeclared names and permissions;
  unknown and unsupported statements; duplicates; unbalanced text;
  attribute cycles; a misused constraint operand, beside a proper pair; a
  name transition in a booleanif; conflicting type rules, through an
  attribute and in two booleanifs on one condition; conflicting role
  transitions), access vectors with and without a boolean, MLS
  read-down and write-up, exec and file transitions (named, and in the two
  branches of a booleanif), role transitions, decisions in enforcing and permissive mode and for a
  permissive type, context validity, roleallow, relabel, attribute members.
* `ref/run.sh`: 30 random small CIL policies (types, attributes with
  expressions, aliases, roles, users, booleans and booleanifs, commons,
  constraints and MLS constraints, transitions, permissive types, and
  sometimes a neverallow), each loaded, then asked about 25 random
  questions (access vectors, aimed and random; decisions under the three
  modes; new contexts, named and not; relabel and member; vectors after
  setting a boolean): 724 cases at the default seed (24 policies load; 4
  are refused for a neverallow violation, 1 for a misused constraint
  operand, 1 for conflicting type rules), compared with `ref/gen.py`. The
  generator only rarely uses a name that is an operand word in a
  constraint, or a name transition in a booleanif, so that most policies
  load and those refusals are still exercised. **`gen.py` is an independent Python model written from the
  same documentation by the same author as the package**: independent code
  (its own reader and compiler, from the CIL text), but not an independent
  reading of the documents. No third-party tool answers these questions in
  this environment:
  * With `secilc` on the path (apt package **`secilc`**), `run.sh` also
    compiles every generated policy with it, as a black box only: it must
    accept exactly the policies the package loads, which checks that the
    CIL subset as written here is CIL, and that the package refuses what
    secilc refuses. secilc 3.5 agrees on all 30 policies at the default
    seed and at seeds 1 to 5; on the 1,200 policies of seeds 1 to 40,
    `gen.py`'s model (which the package must match) agrees with it too. `checkpolicy` (the kernel
    policy language) is not used yet.
  * Neither secilc nor checkpolicy computes access decisions; the kernel's
    own decisions would need a running SELinux system.

## Speed and sizes

Measured natively (Bend 2.0.37, WSL2), loading a generated policy (5
classes of 8 permissions, MLS) and asking access vectors:

| Policy | Load and check | 100 access vectors | Peak RAM |
|---|---|---|---|
| 200 types, 20 attributes, 2,000 allow rules, 20 booleanifs | 0.10 s | 0.35 s | 14 MB |
| the same with 20 neverallow rules | 0.45 s | | 14 MB |
| 400 types, 40 attributes, 4,000 allow rules, 40 booleanifs | | 2.5 s (with the load) | 27 MB |

`check.bend` runs in 0.02 s natively; `ref/run.sh` in about 47 s, most of it
building `cases.bend`. The first version of the neverallow check compared
every rule with every rule, whatever its kind: 33 s for the 2,000-rule
policy; it now skips rules of other kinds first.

Numbers are `Nat`s and sets are lists of bits, so a query costs time
linear in the number of rules times the size of the type numbers: fine for
policies of a few thousand rules; a reference policy (tens of thousands of
types, a hundred thousand rules) would want an index and a native
representation (see Extension points). Every loop over the input bytes and
the statements is tail-recursive or structural over short lists; a policy
text is read in one pass. String literals of more than a few kilobytes
overflow the checker, so long policies are built from pieces
(`String.concat`) or read from a file as `Octets`.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 724 cases match and secilc 3.5 agrees on
all 30 policies (seeds 2026 and 1 to 5), `scripts/deps.sh` passes.
