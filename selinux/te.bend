# bend-osdev-selinux: type enforcement and role rules.
#
# Which rules apply to an access, which rules are active under the current
# booleans, the neverallow check, type transitions, and role allow and
# role transitions (SELinux Notebook, "Type Enforcement", "Conditional
# Policy", "Computing Security Contexts"; the CIL reference, "Access Vector
# Rules", "Type Statements", "Role Statements").
#
# A rule with source set S, target set T and the self flag matches source
# type s and target type t when s is in S and either t is in T, or the rule
# names self and t is s.
import Base
import ./bits.bend as Bits
import ./policy.bend as P

# Access vector rules

def SeTe.rule_matches(r: P.SeAvRule, kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat) -> Bool:
  match r:
    case P.SeAvRule{rk, src, tgt, self, cls, perms}:
      Bool.and(P.SeAvKind.is_eq(kind, rk), Bool.and(Bits.SeBits.has(src, st), Bool.and(Bool.or(Bits.SeBits.has(tgt, tt), Bool.and(self, Nat.is_eq(st, tt))), Nat.is_eq(cls, c))))

# the rule, of this kind, covers permission k of class c from st to tt
def SeTe.rule_covers(+r: P.SeAvRule, kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, k: Nat) -> Bool:
  Bool.and(SeTe.rule_matches(r, kind, st, tt, c), Bits.SeBits.has(P.SeAvRule.perms(r), k))

# some rule of the list covers it
def SeTe.any_covers(rs: List<&2, P.SeAvRule>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{r, t}:
      Bool.or(SeTe.rule_covers(r, kind, st, tt, c, k), SeTe.any_covers(t, kind, st, tt, c, k))

def SeTe.pick(-A: Data, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

# the access vector rules of the branch the booleans bs choose
def SeTe.branch_av(cd: P.SeCond, +bs: List<&2, Bool>) -> List<&2, P.SeAvRule>:
  match cd:
    case P.SeCond{e, tav, tty, fav, fty}:
      SeTe.pick(List<&2, P.SeAvRule>, P.SeBexpr.eval(e, bs), tav, fav)

def SeTe.cond_av(cs: List<&2, P.SeCond>, +bs: List<&2, Bool>) -> List<&2, P.SeAvRule>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{cd, t}:
      List.append(&2, P.SeAvRule, SeTe.branch_av(cd, bs), SeTe.cond_av(t, bs))

# The rules in force: the unconditional rules, and of each booleanif the
# branch its condition chooses under the policy's booleans. This is what
# "booleans switch exactly the conditional rules" means; SeAvc.compute is
# proved to answer by these rules.
def SeTe.active_av(+p: P.SePolicy) -> List<&2, P.SeAvRule>:
  List.append(&2, P.SeAvRule, P.SePolicy.av(p), SeTe.cond_av(P.SePolicy.conds(p), P.SePolicy.state(p)))

# a rule in force covers permission k of class c from st to tt
def SeTe.covers(+p: P.SePolicy, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat) -> Bool:
  SeTe.any_covers(SeTe.active_av(p), kind, st, tt, c, k)

# the access vector rules of both branches of every booleanif
def SeTe.cond_all_av(cs: List<&2, P.SeCond>) -> List<&2, P.SeAvRule>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+cd, t}:
      List.append(&2, P.SeAvRule, List.append(&2, P.SeAvRule, P.SeCond.tav(cd), P.SeCond.fav(cd)), SeTe.cond_all_av(t))

# some conditional rule (in either branch) covers it
def SeTe.cond_mentions(+p: P.SePolicy, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat) -> Bool:
  SeTe.any_covers(SeTe.cond_all_av(P.SePolicy.conds(p)), kind, st, tt, c, k)

# every access vector rule, whatever the booleans
def SeTe.all_av(+p: P.SePolicy) -> List<&2, P.SeAvRule>:
  List.append(&2, P.SeAvRule, P.SePolicy.av(p), SeTe.cond_all_av(P.SePolicy.conds(p)))

# some rule, in some boolean state, covers it
def SeTe.ever_covers(+p: P.SePolicy, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat) -> Bool:
  SeTe.any_covers(SeTe.all_av(p), kind, st, tt, c, k)

# Neverallow

# The two rules' type pairs meet: some source s and target t match both.
# With S the sources both name: both name targets in common; or a names
# self and n names a target in S; or n names self and a names a target in
# S; or both name self.

def SeTe.meet_tt(+nsrc: List<&2, Bool>, +asrc: List<&2, Bool>, ntgt: List<&2, Bool>, atgt: List<&2, Bool>) -> Bool:
  Bool.and(Bits.SeBits.any(Bits.SeBits.and(nsrc, asrc)), Bits.SeBits.any(Bits.SeBits.and(ntgt, atgt)))

def SeTe.meet_ts(nsrc: List<&2, Bool>, asrc: List<&2, Bool>, ntgt: List<&2, Bool>, aself: Bool) -> Bool:
  Bool.and(aself, Bits.SeBits.any(Bits.SeBits.and(Bits.SeBits.and(nsrc, asrc), ntgt)))

def SeTe.meet_st(nsrc: List<&2, Bool>, asrc: List<&2, Bool>, atgt: List<&2, Bool>, nself: Bool) -> Bool:
  Bool.and(nself, Bits.SeBits.any(Bits.SeBits.and(Bits.SeBits.and(nsrc, asrc), atgt)))

def SeTe.meet_ss(nsrc: List<&2, Bool>, asrc: List<&2, Bool>, nself: Bool, aself: Bool) -> Bool:
  Bool.and(nself, Bool.and(aself, Bits.SeBits.any(Bits.SeBits.and(nsrc, asrc))))

def SeTe.types_meet(n: P.SeAvRule, a: P.SeAvRule) -> Bool:
  match n:
    case P.SeAvRule{nk, +nsrc, +ntgt, +nself, ncls, nperms}:
      match a:
        case P.SeAvRule{ak, +asrc, +atgt, +aself, acls, aperms}:
          Bool.or(SeTe.meet_tt(nsrc, asrc, ntgt, atgt), Bool.or(SeTe.meet_ts(nsrc, asrc, ntgt, aself), Bool.or(SeTe.meet_st(nsrc, asrc, atgt, nself), SeTe.meet_ss(nsrc, asrc, nself, aself))))

# the neverallow rule n and the allow rule a grant something in common
def SeTe.conflict(+n: P.SeAvRule, +a: P.SeAvRule) -> Bool:
  Bool.and(P.SeAvKind.is_eq(P.SeNeverallow{}, P.SeAvRule.kind(n)), Bool.and(P.SeAvKind.is_eq(P.SeAllow{}, P.SeAvRule.kind(a)), Bool.and(Nat.is_eq(P.SeAvRule.cls(n), P.SeAvRule.cls(a)), Bool.and(Bits.SeBits.any(Bits.SeBits.and(P.SeAvRule.perms(n), P.SeAvRule.perms(a))), SeTe.types_meet(n, a)))))

def SeTe.never_ok_one.step(is_allow: Bool, +n: P.SeAvRule, +a: P.SeAvRule, rest: Bool) -> Bool:
  match is_allow:
    case True{}:
      Bool.and(Bool.not(SeTe.conflict(n, a)), rest)
    case False{}:
      rest

# n conflicts with none of the allow rules of ars (rules of other kinds are
# skipped without comparing their sets)
def SeTe.never_ok_one(ars: List<&2, P.SeAvRule>, +n: P.SeAvRule) -> Bool:
  match ars:
    case Nil{}:
      True{}
    case Con{+a, t}:
      SeTe.never_ok_one.step(P.SeAvKind.is_eq(P.SeAllow{}, P.SeAvRule.kind(a)), n, a, SeTe.never_ok_one(t, n))

def SeTe.never_ok.step(is_never: Bool, +n: P.SeAvRule, +ars: List<&2, P.SeAvRule>, rest: Bool) -> Bool:
  match is_never:
    case True{}:
      Bool.and(SeTe.never_ok_one(ars, n), rest)
    case False{}:
      rest

# every neverallow rule of ns conflicts with none of ars
def SeTe.never_ok(ns: List<&2, P.SeAvRule>, +ars: List<&2, P.SeAvRule>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, t}:
      SeTe.never_ok.step(P.SeAvKind.is_eq(P.SeNeverallow{}, P.SeAvRule.kind(n)), n, ars, SeTe.never_ok(t, ars))

# some neverallow rule forbids permission k of class c from st to tt
def SeTe.never_covers(+p: P.SePolicy, +st: Nat, +tt: Nat, +c: Nat, +k: Nat) -> Bool:
  SeTe.any_covers(P.SePolicy.av(p), P.SeNeverallow{}, st, tt, c, k)

# no neverallow rule conflicts with any allow rule, unconditional or in
# either branch of a booleanif: the check made at load time
def SeTe.neverallow_ok(+p: P.SePolicy) -> Bool:
  SeTe.never_ok(P.SePolicy.av(p), SeTe.all_av(p))

def SeTe.first_conflict.hit(b: Bool, n: P.SeAvRule, a: P.SeAvRule, rest: Maybe<&2, P.SeConflict>) -> Maybe<&2, P.SeConflict>:
  match b:
    case True{}:
      Some{P.SeConflict{n, a}}
    case False{}:
      rest

def SeTe.first_conflict.one(ars: List<&2, P.SeAvRule>, +n: P.SeAvRule) -> Maybe<&2, P.SeConflict>:
  match ars:
    case Nil{}:
      None{}
    case Con{+a, t}:
      SeTe.first_conflict.hit(Bool.and(P.SeAvKind.is_eq(P.SeAllow{}, P.SeAvRule.kind(a)), SeTe.conflict(n, a)), n, a, SeTe.first_conflict.one(t, n))

def SeTe.first_conflict.pick(is_never: Bool, +n: P.SeAvRule, +ars: List<&2, P.SeAvRule>, rest: Maybe<&2, P.SeConflict>) -> Maybe<&2, P.SeConflict>:
  match is_never:
    case True{}:
      Maybe.or(&2, P.SeConflict, SeTe.first_conflict.one(ars, n), rest)
    case False{}:
      rest

def SeTe.first_conflict.go(ns: List<&2, P.SeAvRule>, +ars: List<&2, P.SeAvRule>) -> Maybe<&2, P.SeConflict>:
  match ns:
    case Nil{}:
      None{}
    case Con{+n, t}:
      SeTe.first_conflict.pick(P.SeAvKind.is_eq(P.SeNeverallow{}, P.SeAvRule.kind(n)), n, ars, SeTe.first_conflict.go(t, ars))

# the first neverallow rule and allow rule that conflict, if any (for the
# load-time error)
def SeTe.first_conflict(+p: P.SePolicy) -> Maybe<&2, P.SeConflict>:
  SeTe.first_conflict.go(P.SePolicy.av(p), SeTe.all_av(p))

# Type rules (type_transition, type_change, type_member)

def SeTe.ty_matches(r: P.SeTyRule, kind: P.SeTyKind, +st: Nat, +tt: Nat, +c: Nat) -> Bool:
  match r:
    case P.SeTyRule{rk, src, tgt, self, cls, nm, res}:
      Bool.and(P.SeTyKind.is_eq(kind, rk), Bool.and(Bits.SeBits.has(src, st), Bool.and(Bool.or(Bits.SeBits.has(tgt, tt), Bool.and(self, Nat.is_eq(st, tt))), Nat.is_eq(cls, c))))

# a rule's object name against the object's: in the named pass a rule that
# names exactly this object, in the unnamed pass a rule without a name
def SeTe.name_ok(rn: Maybe<&2, String>, on: Maybe<&2, String>, named: Bool) -> Bool:
  match rn:
    case None{}:
      Bool.not(named)
    case Some{x}:
      match on:
        case None{}:
          False{}
        case Some{y}:
          Bool.and(named, String.eq(x, y))

def SeTe.find_ty.hit(b: Bool, x: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

def SeTe.find_ty(rs: List<&2, P.SeTyRule>, +kind: P.SeTyKind, +st: Nat, +tt: Nat, +c: Nat, +on: Maybe<&2, String>, +named: Bool) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case Con{+r, t}:
      SeTe.find_ty.hit(Bool.and(SeTe.ty_matches(r, kind, st, tt, c), SeTe.name_ok(P.SeTyRule.name(r), on, named)), P.SeTyRule.result(r), SeTe.find_ty(t, kind, st, tt, c, on, named))

def SeTe.branch_ty(cd: P.SeCond, +bs: List<&2, Bool>) -> List<&2, P.SeTyRule>:
  match cd:
    case P.SeCond{e, tav, tty, fav, fty}:
      SeTe.pick(List<&2, P.SeTyRule>, P.SeBexpr.eval(e, bs), tty, fty)

def SeTe.cond_ty(cs: List<&2, P.SeCond>, +bs: List<&2, Bool>) -> List<&2, P.SeTyRule>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{cd, t}:
      List.append(&2, P.SeTyRule, SeTe.branch_ty(cd, bs), SeTe.cond_ty(t, bs))

# the type rules in force under the policy's booleans
def SeTe.active_ty(+p: P.SePolicy) -> List<&2, P.SeTyRule>:
  List.append(&2, P.SeTyRule, P.SePolicy.ty(p), SeTe.cond_ty(P.SePolicy.conds(p), P.SePolicy.state(p)))

# the type a rule in force gives (a rule naming the object first), if any
def SeTe.new_type(+p: P.SePolicy, +kind: P.SeTyKind, +st: Nat, +tt: Nat, +c: Nat, +on: Maybe<&2, String>) -> Maybe<&2, Nat>:
  Maybe.or(&2, Nat, SeTe.find_ty(SeTe.active_ty(p), kind, st, tt, c, on, True{}), SeTe.find_ty(SeTe.active_ty(p), kind, st, tt, c, on, False{}))

# some rule of the list matches and gives type x
def SeTe.ty_gives(rs: List<&2, P.SeTyRule>, +kind: P.SeTyKind, +st: Nat, +tt: Nat, +c: Nat, +x: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{+r, t}:
      Bool.or(Bool.and(SeTe.ty_matches(r, kind, st, tt, c), Nat.is_eq(P.SeTyRule.result(r), x)), SeTe.ty_gives(t, kind, st, tt, c, x))

# Roles

def SeTe.roleallow_any(rs: List<&2, P.SeRoleAllow>, +r1: Nat, +r2: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{ra, t}:
      match ra:
        case P.SeRoleAllow{src, tgt}:
          Bool.or(Bool.and(Bits.SeBits.has(src, r1), Bits.SeBits.has(tgt, r2)), SeTe.roleallow_any(t, r1, r2))

# a process may change from role r1 to role r2: the same role, or a
# roleallow rule
def SeTe.role_allowed(+p: P.SePolicy, +r1: Nat, +r2: Nat) -> Bool:
  Bool.or(Nat.is_eq(r1, r2), SeTe.roleallow_any(P.SeRules.roleallow(P.SePolicy.rules(p)), r1, r2))

def SeTe.role_trans.go(rs: List<&2, P.SeRoleTrans>, +r: Nat, +tt: Nat, +c: Nat) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case Con{rt, t}:
      match rt:
        case P.SeRoleTrans{src, tgt, cls, res}:
          SeTe.find_ty.hit(Bool.and(Bits.SeBits.has(src, r), Bool.and(Bits.SeBits.has(tgt, tt), Nat.is_eq(cls, c))), res, SeTe.role_trans.go(t, r, tt, c))

# the role a roletransition gives role r on target type tt, class c
def SeTe.role_trans(+p: P.SePolicy, +r: Nat, +tt: Nat, +c: Nat) -> Maybe<&2, Nat>:
  SeTe.role_trans.go(P.SeRules.roletrans(P.SePolicy.rules(p)), r, tt, c)
