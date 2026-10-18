# bend-osdev-selinux: the policy model.
#
# A policy, as the CIL compiler (cil.bend) builds it, with every name
# resolved to a number: types and attributes (one namespace, numbered in
# declaration order; an attribute's members are expanded to the types they
# stand for), roles, users, classes with their permissions (a class's common
# permissions first, then its own, as the kernel numbers them), booleans,
# sensitivities and categories (numbered by sensitivityorder and
# categoryorder). Rules hold their type sets as SeBits over type numbers,
# with attributes already expanded, and self as a flag.
#
# The loaded policy also holds the current value of each boolean: the
# conditional rules of a booleanif apply in one branch or the other by those
# values (SELinux Notebook, "Conditional Policy").
import Base
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C
import ./constraints.bend as K

type SeAvKind is Data:
  SeAllow{}
  SeAuditallow{}
  SeDontaudit{}
  SeNeverallow{}

# an access vector rule: kind src tgt (self) class perms
type SeAvRule is Data:
  SeAvRule{kind: SeAvKind, src: List<&2, Bool>, tgt: List<&2, Bool>, self: Bool, cls: Nat, perms: List<&2, Bool>}

def SeAvRule.kind(x: SeAvRule) -> SeAvKind:
  match x:
    case SeAvRule{v, _, _, _, _, _}:
      v

def SeAvRule.src(x: SeAvRule) -> List<&2, Bool>:
  match x:
    case SeAvRule{_, v, _, _, _, _}:
      v

def SeAvRule.tgt(x: SeAvRule) -> List<&2, Bool>:
  match x:
    case SeAvRule{_, _, v, _, _, _}:
      v

def SeAvRule.self(x: SeAvRule) -> Bool:
  match x:
    case SeAvRule{_, _, _, v, _, _}:
      v

def SeAvRule.cls(x: SeAvRule) -> Nat:
  match x:
    case SeAvRule{_, _, _, _, v, _}:
      v

def SeAvRule.perms(x: SeAvRule) -> List<&2, Bool>:
  match x:
    case SeAvRule{_, _, _, _, _, v}:
      v

type SeTyKind is Data:
  SeTyTransition{}
  SeTyChange{}
  SeTyMember{}

# a type rule: kind src tgt (self) class [object name] result type
type SeTyRule is Data:
  SeTyRule{kind: SeTyKind, src: List<&2, Bool>, tgt: List<&2, Bool>, self: Bool, cls: Nat, name: Maybe<&2, String>, result: Nat}

def SeTyRule.kind(x: SeTyRule) -> SeTyKind:
  match x:
    case SeTyRule{v, _, _, _, _, _, _}:
      v

def SeTyRule.src(x: SeTyRule) -> List<&2, Bool>:
  match x:
    case SeTyRule{_, v, _, _, _, _, _}:
      v

def SeTyRule.tgt(x: SeTyRule) -> List<&2, Bool>:
  match x:
    case SeTyRule{_, _, v, _, _, _, _}:
      v

def SeTyRule.self(x: SeTyRule) -> Bool:
  match x:
    case SeTyRule{_, _, _, v, _, _, _}:
      v

def SeTyRule.cls(x: SeTyRule) -> Nat:
  match x:
    case SeTyRule{_, _, _, _, v, _, _}:
      v

def SeTyRule.name(x: SeTyRule) -> Maybe<&2, String>:
  match x:
    case SeTyRule{_, _, _, _, _, v, _}:
      v

def SeTyRule.result(x: SeTyRule) -> Nat:
  match x:
    case SeTyRule{_, _, _, _, _, _, v}:
      v

# a condition over the booleans (booleanif)
type SeBexpr is Data:
  SeBVar{id: Nat}
  SeBNot{e: SeBexpr}
  SeBAnd{a: SeBexpr, b: SeBexpr}
  SeBOr{a: SeBexpr, b: SeBexpr}
  SeBXor{a: SeBexpr, b: SeBexpr}
  SeBEq{a: SeBexpr, b: SeBexpr}
  SeBNeq{a: SeBexpr, b: SeBexpr}

# a booleanif: the rules of the true branch and of the false branch
type SeCond is Data:
  SeCond{expr: SeBexpr, tav: List<&2, SeAvRule>, tty: List<&2, SeTyRule>, fav: List<&2, SeAvRule>, fty: List<&2, SeTyRule>}

def SeCond.expr(x: SeCond) -> SeBexpr:
  match x:
    case SeCond{v, _, _, _, _}:
      v

def SeCond.tav(x: SeCond) -> List<&2, SeAvRule>:
  match x:
    case SeCond{_, v, _, _, _}:
      v

def SeCond.tty(x: SeCond) -> List<&2, SeTyRule>:
  match x:
    case SeCond{_, _, v, _, _}:
      v

def SeCond.fav(x: SeCond) -> List<&2, SeAvRule>:
  match x:
    case SeCond{_, _, _, v, _}:
      v

def SeCond.fty(x: SeCond) -> List<&2, SeTyRule>:
  match x:
    case SeCond{_, _, _, _, v}:
      v

# roleallow: a role of src may change to a role of tgt
type SeRoleAllow is Data:
  SeRoleAllow{src: List<&2, Bool>, tgt: List<&2, Bool>}

def SeRoleAllow.src(x: SeRoleAllow) -> List<&2, Bool>:
  match x:
    case SeRoleAllow{v, _}:
      v

def SeRoleAllow.tgt(x: SeRoleAllow) -> List<&2, Bool>:
  match x:
    case SeRoleAllow{_, v}:
      v

# roletransition: a role of src, on a type of tgt, class cls, gets result
type SeRoleTrans is Data:
  SeRoleTrans{src: List<&2, Bool>, tgt: List<&2, Bool>, cls: Nat, result: Nat}

def SeRoleTrans.src(x: SeRoleTrans) -> List<&2, Bool>:
  match x:
    case SeRoleTrans{v, _, _, _}:
      v

def SeRoleTrans.tgt(x: SeRoleTrans) -> List<&2, Bool>:
  match x:
    case SeRoleTrans{_, v, _, _}:
      v

def SeRoleTrans.cls(x: SeRoleTrans) -> Nat:
  match x:
    case SeRoleTrans{_, _, v, _}:
      v

def SeRoleTrans.result(x: SeRoleTrans) -> Nat:
  match x:
    case SeRoleTrans{_, _, _, v}:
      v

type SeTypeDef is Data:
  SeTypeDef{name: String, attr: Bool, members: List<&2, Bool>}

def SeTypeDef.name(x: SeTypeDef) -> String:
  match x:
    case SeTypeDef{v, _, _}:
      v

def SeTypeDef.attr(x: SeTypeDef) -> Bool:
  match x:
    case SeTypeDef{_, v, _}:
      v

def SeTypeDef.members(x: SeTypeDef) -> List<&2, Bool>:
  match x:
    case SeTypeDef{_, _, v}:
      v

type SeClass is Data:
  SeClass{name: String, perms: List<&2, String>}

def SeClass.name(x: SeClass) -> String:
  match x:
    case SeClass{v, _}:
      v

def SeClass.perms(x: SeClass) -> List<&2, String>:
  match x:
    case SeClass{_, v}:
      v

type SeRole is Data:
  SeRole{name: String, types: List<&2, Bool>}

def SeRole.name(x: SeRole) -> String:
  match x:
    case SeRole{v, _}:
      v

def SeRole.types(x: SeRole) -> List<&2, Bool>:
  match x:
    case SeRole{_, v}:
      v

type SeUser is Data:
  SeUser{name: String, roles: List<&2, Bool>, level: M.SeLevel, range: M.SeRange}

def SeUser.name(x: SeUser) -> String:
  match x:
    case SeUser{v, _, _, _}:
      v

def SeUser.roles(x: SeUser) -> List<&2, Bool>:
  match x:
    case SeUser{_, v, _, _}:
      v

def SeUser.level(x: SeUser) -> M.SeLevel:
  match x:
    case SeUser{_, _, v, _}:
      v

def SeUser.range(x: SeUser) -> M.SeRange:
  match x:
    case SeUser{_, _, _, v}:
      v

# a name in the symbol table (Map keys "t:" type or attribute, "r:" role,
# "u:" user, "c:" class, "p:<class>:" permission, "b:" boolean, "s:"
# sensitivity, "g:" category, "l:" level, "n:" level range, "x:" context)
type SeSym is Data:
  SeSymNone{}
  SeSymId{id: Nat}
  SeSymAttr{id: Nat}

# a named context (CIL context)
type SeCtxDef is Data:
  SeCtxDef{name: String, ctx: C.SeContext}

def SeCtxDef.name(x: SeCtxDef) -> String:
  match x:
    case SeCtxDef{v, _}:
      v

def SeCtxDef.ctx(x: SeCtxDef) -> C.SeContext:
  match x:
    case SeCtxDef{_, v}:
      v

# a neverallow rule and an allow rule that grant something in common
type SeConflict is Data:
  SeConflict{never: SeAvRule, allow: SeAvRule}

def SeConflict.never(x: SeConflict) -> SeAvRule:
  match x:
    case SeConflict{v, _}:
      v

def SeConflict.allow(x: SeConflict) -> SeAvRule:
  match x:
    case SeConflict{_, v}:
      v

# the declarations: names and what they stand for
type SeDecl is Data:
  SeDecl{types: List<&2, SeTypeDef>, roles: List<&2, SeRole>, users: List<&2, SeUser>, classes: List<&2, SeClass>, bools: List<&2, String>, sens: List<&2, String>, cats: List<&2, String>, sens_cats: List<&2, List<&2, Bool>>, syms: Map<&2, SeSym>, contexts: List<&2, SeCtxDef>}

def SeDecl.types(x: SeDecl) -> List<&2, SeTypeDef>:
  match x:
    case SeDecl{v, _, _, _, _, _, _, _, _, _}:
      v

def SeDecl.roles(x: SeDecl) -> List<&2, SeRole>:
  match x:
    case SeDecl{_, v, _, _, _, _, _, _, _, _}:
      v

def SeDecl.users(x: SeDecl) -> List<&2, SeUser>:
  match x:
    case SeDecl{_, _, v, _, _, _, _, _, _, _}:
      v

def SeDecl.classes(x: SeDecl) -> List<&2, SeClass>:
  match x:
    case SeDecl{_, _, _, v, _, _, _, _, _, _}:
      v

def SeDecl.bools(x: SeDecl) -> List<&2, String>:
  match x:
    case SeDecl{_, _, _, _, v, _, _, _, _, _}:
      v

def SeDecl.sens(x: SeDecl) -> List<&2, String>:
  match x:
    case SeDecl{_, _, _, _, _, v, _, _, _, _}:
      v

def SeDecl.cats(x: SeDecl) -> List<&2, String>:
  match x:
    case SeDecl{_, _, _, _, _, _, v, _, _, _}:
      v

def SeDecl.sens_cats(x: SeDecl) -> List<&2, List<&2, Bool>>:
  match x:
    case SeDecl{_, _, _, _, _, _, _, v, _, _}:
      v

def SeDecl.syms(x: SeDecl) -> Map<&2, SeSym>:
  match x:
    case SeDecl{_, _, _, _, _, _, _, _, v, _}:
      v

def SeDecl.contexts(x: SeDecl) -> List<&2, SeCtxDef>:
  match x:
    case SeDecl{_, _, _, _, _, _, _, _, _, v}:
      v

# the rules
type SeRules is Data:
  SeRules{av: List<&2, SeAvRule>, ty: List<&2, SeTyRule>, conds: List<&2, SeCond>, roleallow: List<&2, SeRoleAllow>, roletrans: List<&2, SeRoleTrans>, constraints: List<&2, K.SeConstraint>, permissive: List<&2, Bool>}

def SeRules.av(x: SeRules) -> List<&2, SeAvRule>:
  match x:
    case SeRules{v, _, _, _, _, _, _}:
      v

def SeRules.ty(x: SeRules) -> List<&2, SeTyRule>:
  match x:
    case SeRules{_, v, _, _, _, _, _}:
      v

def SeRules.conds(x: SeRules) -> List<&2, SeCond>:
  match x:
    case SeRules{_, _, v, _, _, _, _}:
      v

def SeRules.roleallow(x: SeRules) -> List<&2, SeRoleAllow>:
  match x:
    case SeRules{_, _, _, v, _, _, _}:
      v

def SeRules.roletrans(x: SeRules) -> List<&2, SeRoleTrans>:
  match x:
    case SeRules{_, _, _, _, v, _, _}:
      v

def SeRules.constraints(x: SeRules) -> List<&2, K.SeConstraint>:
  match x:
    case SeRules{_, _, _, _, _, v, _}:
      v

def SeRules.permissive(x: SeRules) -> List<&2, Bool>:
  match x:
    case SeRules{_, _, _, _, _, _, v}:
      v

# a policy: its declarations, its rules, whether MLS is enabled, and the
# current value of each boolean
type SePolicy is Data:
  SePolicy{decl: SeDecl, rules: SeRules, mls: Bool, state: List<&2, Bool>}

def SePolicy.decl(x: SePolicy) -> SeDecl:
  match x:
    case SePolicy{v, _, _, _}:
      v

def SePolicy.rules(x: SePolicy) -> SeRules:
  match x:
    case SePolicy{_, v, _, _}:
      v

def SePolicy.mls(x: SePolicy) -> Bool:
  match x:
    case SePolicy{_, _, v, _}:
      v

def SePolicy.state(x: SePolicy) -> List<&2, Bool>:
  match x:
    case SePolicy{_, _, _, v}:
      v

# Errors: of the CIL reader and compiler, of context strings, and of the
# load-time checks

type SeError is Data:
  SeErrSyntax{msg: String}
  SeErrUnknownStatement{name: String}
  SeErrBadStatement{name: String}
  SeErrUndeclared{name: String}
  SeErrDuplicate{name: String}
  SeErrAttributeCycle{name: String}
  SeErrUnsupported{name: String}
  SeErrBadContext{text: String}
  SeErrNeverallow{never: SeAvRule, allow: SeAvRule}
  SeErrTypeConflict{first: SeTyRule, second: SeTyRule}
  SeErrRoleTransConflict{first: SeRoleTrans, second: SeRoleTrans}

def SeAvKind.is_eq(a: SeAvKind, b: SeAvKind) -> Bool:
  match a:
    case SeAllow{}:
      match b:
        case SeAllow{}:
          True{}
        case o:
          False{}
    case SeAuditallow{}:
      match b:
        case SeAuditallow{}:
          True{}
        case o:
          False{}
    case SeDontaudit{}:
      match b:
        case SeDontaudit{}:
          True{}
        case o:
          False{}
    case SeNeverallow{}:
      match b:
        case SeNeverallow{}:
          True{}
        case o:
          False{}

def SeTyKind.is_eq(a: SeTyKind, b: SeTyKind) -> Bool:
  match a:
    case SeTyTransition{}:
      match b:
        case SeTyTransition{}:
          True{}
        case o:
          False{}
    case SeTyChange{}:
      match b:
        case SeTyChange{}:
          True{}
        case o:
          False{}
    case SeTyMember{}:
      match b:
        case SeTyMember{}:
          True{}
        case o:
          False{}

# the condition's value under the boolean values bs (a SeBits set: the
# booleans that are true)
def SeBexpr.eval(e: SeBexpr, +bs: List<&2, Bool>) -> Bool:
  match e:
    case SeBVar{i}:
      Bits.SeBits.has(bs, i)
    case SeBNot{a}:
      Bool.not(SeBexpr.eval(a, bs))
    case SeBAnd{a, b}:
      Bool.and(SeBexpr.eval(a, bs), SeBexpr.eval(b, bs))
    case SeBOr{a, b}:
      Bool.or(SeBexpr.eval(a, bs), SeBexpr.eval(b, bs))
    case SeBXor{a, b}:
      Bool.xor(SeBexpr.eval(a, bs), SeBexpr.eval(b, bs))
    case SeBEq{a, b}:
      Bool.not(Bool.xor(SeBexpr.eval(a, bs), SeBexpr.eval(b, bs)))
    case SeBNeq{a, b}:
      Bool.xor(SeBexpr.eval(a, bs), SeBexpr.eval(b, bs))

# the two conditions are written the same (the same tree of operators over
# the same booleans)
def SeBexpr.is_eq(a: SeBexpr, b: SeBexpr) -> Bool:
  match a:
    case SeBVar{i}:
      match b:
        case SeBVar{j}:
          Nat.is_eq(i, j)
        case o:
          False{}
    case SeBNot{x}:
      match b:
        case SeBNot{y}:
          SeBexpr.is_eq(x, y)
        case o:
          False{}
    case SeBAnd{x1, x2}:
      match b:
        case SeBAnd{y1, y2}:
          Bool.and(SeBexpr.is_eq(x1, y1), SeBexpr.is_eq(x2, y2))
        case o:
          False{}
    case SeBOr{x1, x2}:
      match b:
        case SeBOr{y1, y2}:
          Bool.and(SeBexpr.is_eq(x1, y1), SeBexpr.is_eq(x2, y2))
        case o:
          False{}
    case SeBXor{x1, x2}:
      match b:
        case SeBXor{y1, y2}:
          Bool.and(SeBexpr.is_eq(x1, y1), SeBexpr.is_eq(x2, y2))
        case o:
          False{}
    case SeBEq{x1, x2}:
      match b:
        case SeBEq{y1, y2}:
          Bool.and(SeBexpr.is_eq(x1, y1), SeBexpr.is_eq(x2, y2))
        case o:
          False{}
    case SeBNeq{x1, x2}:
      match b:
        case SeBNeq{y1, y2}:
          Bool.and(SeBexpr.is_eq(x1, y1), SeBexpr.is_eq(x2, y2))
        case o:
          False{}

# Accessors

def SePolicy.av(p: SePolicy) -> List<&2, SeAvRule>:
  SeRules.av(SePolicy.rules(p))

def SePolicy.ty(p: SePolicy) -> List<&2, SeTyRule>:
  SeRules.ty(SePolicy.rules(p))

def SePolicy.conds(p: SePolicy) -> List<&2, SeCond>:
  SeRules.conds(SePolicy.rules(p))

def SePolicy.constraints(p: SePolicy) -> List<&2, K.SeConstraint>:
  SeRules.constraints(SePolicy.rules(p))

def SePolicy.permissive(p: SePolicy) -> List<&2, Bool>:
  SeRules.permissive(SePolicy.rules(p))

def SePolicy.classes(p: SePolicy) -> List<&2, SeClass>:
  SeDecl.classes(SePolicy.decl(p))

def SePolicy.syms(p: SePolicy) -> Map<&2, SeSym>:
  SeDecl.syms(SePolicy.decl(p))

# the policy with every boolean set as in bs
def SePolicy.with_bools(p: SePolicy, bs: List<&2, Bool>) -> SePolicy:
  match p:
    case SePolicy{d, r, m, old}:
      SePolicy{d, r, m, bs}

# the policy with boolean b set to v
def SePolicy.set_bool(p: SePolicy, b: Nat, v: Bool) -> SePolicy:
  match p:
    case SePolicy{d, r, m, old}:
      SePolicy{d, r, m, Bits.SeBits.set(b, old, v)}

# the policy with MLS enabled or not
def SePolicy.with_mls(p: SePolicy, m: Bool) -> SePolicy:
  match p:
    case SePolicy{d, r, old, bs}:
      SePolicy{d, r, m, bs}

# Names

def SeNames.at(xs: List<&2, String>, i: Nat) -> String:
  match xs:
    case Nil{}:
      "?"
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          SeNames.at(t, p)

def SeTypeDef.names(xs: List<&2, SeTypeDef>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{SeTypeDef.name(h), SeTypeDef.names(t)}

def SeRole.names(xs: List<&2, SeRole>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{SeRole.name(h), SeRole.names(t)}

def SeUser.names(xs: List<&2, SeUser>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{SeUser.name(h), SeUser.names(t)}

def SeClass.names(xs: List<&2, SeClass>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{SeClass.name(h), SeClass.names(t)}

def SeClass.find(xs: List<&2, SeClass>, i: Nat) -> SeClass:
  match xs:
    case Nil{}:
      SeClass{"?", Nil{}}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          SeClass.find(t, p)

def SePolicy.type_name(p: SePolicy, i: Nat) -> String:
  SeNames.at(SeTypeDef.names(SeDecl.types(SePolicy.decl(p))), i)

def SePolicy.role_name(p: SePolicy, i: Nat) -> String:
  SeNames.at(SeRole.names(SeDecl.roles(SePolicy.decl(p))), i)

def SePolicy.user_name(p: SePolicy, i: Nat) -> String:
  SeNames.at(SeUser.names(SeDecl.users(SePolicy.decl(p))), i)

def SePolicy.class_name(p: SePolicy, i: Nat) -> String:
  SeNames.at(SeClass.names(SePolicy.classes(p)), i)

def SePolicy.class_perms(p: SePolicy, i: Nat) -> List<&2, String>:
  SeClass.perms(SeClass.find(SePolicy.classes(p), i))

def SePolicy.sens_name(p: SePolicy, i: Nat) -> String:
  SeNames.at(SeDecl.sens(SePolicy.decl(p)), i)

def SePolicy.cat_name(p: SePolicy, i: Nat) -> String:
  SeNames.at(SeDecl.cats(SePolicy.decl(p)), i)

def SePolicy.bool_name(p: SePolicy, i: Nat) -> String:
  SeNames.at(SeDecl.bools(SePolicy.decl(p)), i)

def SeSym.to_maybe(s: SeSym) -> Maybe<&2, Nat>:
  match s:
    case SeSymNone{}:
      None{}
    case SeSymId{i}:
      Some{i}
    case SeSymAttr{i}:
      Some{i}

# the number of a name, by kind prefix ("t:", "r:", ...)
def SePolicy.lookup(p: SePolicy, key: String) -> Maybe<&2, Nat>:
  SeSym.to_maybe(Pair.snd(Map<&2, SeSym>, SeSym, Map.get(SeSym, SeSymNone{}, SePolicy.syms(p), key)))


# Validity of a context (SELinux Notebook, "Security Context"): the user may
# hold the role, the role may hold the type (object_r, role 0, holds every
# type), the type is not an attribute, and with MLS on, the range is valid
# and within the user's range

def SeRole.find(xs: List<&2, SeRole>, i: Nat) -> SeRole:
  match xs:
    case Nil{}:
      SeRole{"?", Nil{}}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          SeRole.find(t, p)

def SeUser.find(xs: List<&2, SeUser>, i: Nat) -> Maybe<&2, SeUser>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      match i:
        case 0n:
          Some{h}
        case 1n+p:
          SeUser.find(t, p)

def SeTypeDef.find(xs: List<&2, SeTypeDef>, i: Nat) -> Maybe<&2, SeTypeDef>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      match i:
        case 0n:
          Some{h}
        case 1n+p:
          SeTypeDef.find(t, p)

def SePolicy.type_ok(m: Maybe<&2, SeTypeDef>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{d}:
      Bool.not(SeTypeDef.attr(d))

def SePolicy.user_ok(m: Maybe<&2, SeUser>, +mls: Bool, +r: Nat, +rg: M.SeRange) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{u}:
      match u:
        case SeUser{n, roles, l, urg}:
          Bool.and(Bool.or(Nat.is_eq(r, 0n), Bits.SeBits.has(roles, r)), Bool.or(Bool.not(mls), Bool.and(M.SeRange.valid(rg), M.SeRange.within(urg, rg))))

def SePolicy.context_valid(+p: SePolicy, c: C.SeContext) -> Bool:
  match c:
    case C.SeContext{u, +r, +t, rg}:
      Bool.and(SePolicy.user_ok(SeUser.find(SeDecl.users(SePolicy.decl(p)), u), SePolicy.mls(p), r, rg), Bool.and(SePolicy.type_ok(SeTypeDef.find(SeDecl.types(SePolicy.decl(p)), t)), Bits.SeBits.has(SeRole.types(SeRole.find(SeDecl.roles(SePolicy.decl(p)), r)), t)))
