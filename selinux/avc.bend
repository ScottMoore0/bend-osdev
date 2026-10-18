# bend-osdev-selinux: access decisions and new contexts.
#
# The security server's two questions (Smalley, Vance and Salamon,
# "Implementing SELinux as a Linux Security Module"; the SELinux Notebook,
# "Access Vector Cache" and "Computing Security Contexts"; the libselinux
# man pages security_compute_av(3), security_compute_create(3),
# avc_has_perm(3)):
#
# * the access vectors for a source context, a target context and a class:
#   the permissions allowed (an allow rule in force covers them and every
#   constraint holds), audited when granted (auditallow), and audited when
#   denied (all but those a dontaudit rule covers);
# * the context of a new object, or of a process after exec.
#
# SeAvc.check turns a vector into a decision under SeOptions: in enforcing
# mode a denied permission is refused, in permissive mode (or for a
# permissive source type) it is granted and still reported as a denial.
import Base
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C
import ./constraints.bend as K
import ./policy.bend as P
import ./te.bend as T

type SeAvd is Data:
  SeAvd{allowed: List<&2, Bool>, auditallow: List<&2, Bool>, auditdeny: List<&2, Bool>}

def SeAvd.allowed(x: SeAvd) -> List<&2, Bool>:
  match x:
    case SeAvd{v, _, _}:
      v

def SeAvd.auditallow(x: SeAvd) -> List<&2, Bool>:
  match x:
    case SeAvd{_, v, _}:
      v

def SeAvd.auditdeny(x: SeAvd) -> List<&2, Bool>:
  match x:
    case SeAvd{_, _, v}:
      v

# enforcing: refuse what the policy denies; permissive_types: grant what it
# denies a source type named by typepermissive
type SeOptions is Data:
  SeOptions{enforcing: Bool, permissive_types: Bool}

def SeOptions.enforcing(x: SeOptions) -> Bool:
  match x:
    case SeOptions{v, _}:
      v

def SeOptions.permissive_types(x: SeOptions) -> Bool:
  match x:
    case SeOptions{_, v}:
      v

# enforcing, with permissive types honoured (the kernel's behaviour)
def SeOptions.default() -> SeOptions:
  SeOptions{True{}, True{}}

# permissive mode: every denial is reported, none refused
def SeOptions.permissive() -> SeOptions:
  SeOptions{False{}, True{}}

# The access vectors

def SeAvc.add.go(m: Bool, perms: List<&2, Bool>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match m:
    case True{}:
      Bits.SeBits.or(acc, perms)
    case False{}:
      acc

def SeAvc.add(+r: P.SeAvRule, kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, acc: List<&2, Bool>) -> List<&2, Bool>:
  SeAvc.add.go(T.SeTe.rule_matches(r, kind, st, tt, c), P.SeAvRule.perms(r), acc)

# the union of the permissions of the matching rules
def SeAvc.collect(rs: List<&2, P.SeAvRule>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, acc: List<&2, Bool>) -> List<&2, Bool>:
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      SeAvc.collect(t, kind, st, tt, c, SeAvc.add(r, kind, st, tt, c, acc))

def SeAvc.collect_conds(cs: List<&2, P.SeCond>, +bs: List<&2, Bool>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, acc: List<&2, Bool>) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      acc
    case Con{cd, t}:
      SeAvc.collect_conds(t, bs, kind, st, tt, c, SeAvc.collect(T.SeTe.branch_av(cd, bs), kind, st, tt, c, acc))

# the permissions rules in force of one kind give from type st to type tt
def SeAvc.rules_av(+p: P.SePolicy, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat) -> List<&2, Bool>:
  SeAvc.collect_conds(P.SePolicy.conds(p), P.SePolicy.state(p), kind, st, tt, c, SeAvc.collect(P.SePolicy.av(p), kind, st, tt, c, Nil{}))

# the allowed vector: the allow rules' permissions, less those a constraint
# forbids
def SeAvc.allowed(+p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat) -> List<&2, Bool>:
  K.SeConstraints.apply(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, SeAvc.rules_av(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c))

def SeAvc.nperms(+p: P.SePolicy, c: Nat) -> Nat:
  List.length(&2, String, P.SePolicy.class_perms(p, c))

# the access vectors of source s, target t, class c (security_compute_av)
def SeAvc.compute(+p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat) -> SeAvd:
  SeAvd{SeAvc.allowed(p, s, t, c), SeAvc.rules_av(p, P.SeAuditallow{}, C.SeContext.typ(s), C.SeContext.typ(t), c), Bits.SeBits.andnot(Bits.SeBits.full(SeAvc.nperms(p, c)), SeAvc.rules_av(p, P.SeDontaudit{}, C.SeContext.typ(s), C.SeContext.typ(t), c))}

# Decisions

# granted: the access proceeds; denied: the policy denies some requested
# permission; audited: the decision is logged
type SeDecision is Data:
  SeDecision{granted: Bool, denied: Bool, audited: Bool}

def SeDecision.granted(x: SeDecision) -> Bool:
  match x:
    case SeDecision{v, _, _}:
      v

def SeDecision.denied(x: SeDecision) -> Bool:
  match x:
    case SeDecision{_, v, _}:
      v

def SeDecision.audited(x: SeDecision) -> Bool:
  match x:
    case SeDecision{_, _, v}:
      v

# a denial is not refused: permissive mode, or a permissive source type
def SeAvc.lenient(+o: SeOptions, +p: P.SePolicy, +s: C.SeContext) -> Bool:
  Bool.or(Bool.not(SeOptions.enforcing(o)), Bool.and(SeOptions.permissive_types(o), Bits.SeBits.has(P.SePolicy.permissive(p), C.SeContext.typ(s))))

def SeAvc.decide(ok: Bool, lenient: Bool, +req: List<&2, Bool>, +avd: SeAvd) -> SeDecision:
  match ok:
    case True{}:
      SeDecision{True{}, False{}, Bits.SeBits.any(Bits.SeBits.and(req, SeAvd.auditallow(avd)))}
    case False{}:
      SeDecision{lenient, True{}, Bits.SeBits.any(Bits.SeBits.and(Bits.SeBits.andnot(req, SeAvd.allowed(avd)), SeAvd.auditdeny(avd)))}

# the decision on the requested permissions req of class c (avc_has_perm)
def SeAvc.check(+o: SeOptions, +p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat, +req: List<&2, Bool>) -> SeDecision:
  +avd = SeAvc.compute(p, s, t, c)
  SeAvc.decide(Bits.SeBits.subset(req, SeAvd.allowed(avd)), SeAvc.lenient(o, p, s), req, avd)

# New contexts

def SeAvc.is_process.go(m: Maybe<&2, Nat>, c: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{i}:
      Nat.is_eq(i, c)

# class c is the process class
def SeAvc.is_process(+p: P.SePolicy, +c: Nat) -> Bool:
  SeAvc.is_process.go(P.SePolicy.lookup(p, "c:process"), c)

def SeAvc.create.go(proc: Bool, +p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat, +name: Maybe<&2, String>) -> C.SeContext:
  match proc:
    case True{}:
      C.SeContext{C.SeContext.user(s), Maybe.default(&2, Nat, T.SeTe.role_trans(p, C.SeContext.role(s), C.SeContext.typ(t), c), C.SeContext.role(s)), Maybe.default(&2, Nat, T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, name), C.SeContext.typ(s)), C.SeContext.range(s)}
    case False{}:
      C.SeContext{C.SeContext.user(s), Maybe.default(&2, Nat, T.SeTe.role_trans(p, C.SeContext.role(s), C.SeContext.typ(t), c), 0n), Maybe.default(&2, Nat, T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, name), C.SeContext.typ(t)), M.SeRange.single(C.SeContext.low(s))}

# The context of a new object of class c that s creates in t (t is the
# parent, for a file), or, for the process class, of s after it executes a
# file labelled t (security_compute_create). The type comes from a
# typetransition rule in force (one naming the object first), else from t
# for an object and from s for a process; the role from a roletransition
# rule, else object_r for an object and s's role for a process; the user is
# s's; the range is s's for a process and s's low level for an object.
def SeAvc.compute_create(+p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat, +name: Maybe<&2, String>) -> C.SeContext:
  SeAvc.create.go(SeAvc.is_process(p, c), p, s, t, c, name)

# the context of t relabelled by s (security_compute_relabel): t with the
# type a typechange rule gives
def SeAvc.compute_relabel(+p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat) -> C.SeContext:
  C.SeContext.with_type(t, Maybe.default(&2, Nat, T.SeTe.new_type(p, P.SeTyChange{}, C.SeContext.typ(s), C.SeContext.typ(t), c, None{}), C.SeContext.typ(t)))

# the context of a member of t for s (security_compute_member): t with the
# type a typemember rule gives
def SeAvc.compute_member(+p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat) -> C.SeContext:
  C.SeContext.with_type(t, Maybe.default(&2, Nat, T.SeTe.new_type(p, P.SeTyMember{}, C.SeContext.typ(s), C.SeContext.typ(t), c, None{}), C.SeContext.typ(t)))
