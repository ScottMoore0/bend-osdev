# bend-osdev-selinux: SELinux policy loading and evaluation, as a pure model.
#
# The entry file: load a CIL policy (SeCil.load, then the neverallow and
# transition checks), read and show security contexts as text, and ask the
# security server's questions by name. The model itself is in the other files: policy.bend
# (the policy), te.bend (type enforcement and roles), constraints.bend,
# mls.bend, contexts.bend, avc.bend (decisions and new contexts) and
# cil.bend (the CIL subset).
import Base
import ../bytes/bytes.bend as B
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C
import ./constraints.bend as K
import ./policy.bend as P
import ./te.bend as T
import ./avc.bend as A
import ./cil.bend as L

# Loading

def Selinux.validate.fail(m: Maybe<&2, P.SeConflict>) -> Result<&2, &2, P.SeError, P.SePolicy>:
  match m:
    case None{}:
      Fail{P.SeErrSyntax{"neverallow"}}
    case Some{c}:
      match c:
        case P.SeConflict{n, a}:
          Fail{P.SeErrNeverallow{n, a}}

def Selinux.validate.trans_fail(m: Maybe<&2, T.SeTransConflict>) -> Result<&2, &2, P.SeError, P.SePolicy>:
  match m:
    case None{}:
      Fail{P.SeErrSyntax{"transition conflict"}}
    case Some{c}:
      match c:
        case T.SeTyClash{a, b}:
          Fail{P.SeErrTypeConflict{a, b}}
        case T.SeRoleClash{a, b}:
          Fail{P.SeErrRoleTransConflict{a, b}}

def Selinux.validate.trans(ok: Bool, +p: P.SePolicy) -> Result<&2, &2, P.SeError, P.SePolicy>:
  match ok:
    case True{}:
      Done{p}
    case False{}:
      Selinux.validate.trans_fail(T.SeTe.first_trans_conflict(p))

def Selinux.validate.go(ok: Bool, +p: P.SePolicy) -> Result<&2, &2, P.SeError, P.SePolicy>:
  match ok:
    case True{}:
      Selinux.validate.trans(T.SeTe.transitions_ok(p), p)
    case False{}:
      Selinux.validate.fail(T.SeTe.first_conflict(p))

# the load-time checks: a policy one of whose allow rules (unconditional, or
# in either branch of a booleanif) grants something a neverallow rule
# forbids is refused, with the first such pair of rules; then a policy two
# of whose type rules, or two of whose roletransition rules, give different
# answers to the same question (T.SeTe.transitions_ok) is refused, with the
# first such pair
def Selinux.validate(+p: P.SePolicy) -> Result<&2, &2, P.SeError, P.SePolicy>:
  Selinux.validate.go(T.SeTe.neverallow_ok(p), p)

def Selinux.validated(r: Result<&2, &2, P.SeError, P.SePolicy>) -> Result<&2, &2, P.SeError, P.SePolicy>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{p}:
      Selinux.validate(p)

# load a policy written in CIL
def Selinux.load(o: B.Octets) -> Result<&2, &2, P.SeError, P.SePolicy>:
  Selinux.validated(L.SeCil.load(o))

def Selinux.load_string(s: String) -> Result<&2, &2, P.SeError, P.SePolicy>:
  Selinux.load(B.Octets.of_string(s))

# Names

def Selinux.id.go(m: Maybe<&2, Nat>, key: String) -> Result<&2, &2, P.SeError, Nat>:
  match m:
    case None{}:
      Fail{P.SeErrUndeclared{key}}
    case Some{i}:
      Done{i}

# the number of a name, by kind prefix ("t:", "r:", "u:", "c:", "b:", "s:",
# "g:", or "p:class:" for a permission)
def Selinux.id(+p: P.SePolicy, +key: String) -> Result<&2, &2, P.SeError, Nat>:
  Selinux.id.go(P.SePolicy.lookup(p, key), key)

def Selinux.class(+p: P.SePolicy, name: String) -> Result<&2, &2, P.SeError, Nat>:
  Selinux.id(p, "c:" ++ name)

# the set of the named permissions of a class
def Selinux.perms(+p: P.SePolicy, +cls: String, xs: List<&2, String>) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{n, t}:
      do Result<&2, &2, P.SeError, List<&2, Bool>>:
        i : Nat <- Selinux.id(p, "p:" ++ cls ++ ":" ++ n)
        r : List<&2, Bool> <- Selinux.perms(p, cls, t)
        return Bits.SeBits.or(Bits.SeBits.single(i), r)

def Selinux.names.go(xs: List<&2, Nat>, +names: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      Con{P.SeNames.at(names, i), Selinux.names.go(t, names)}

def Selinux.braces(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      "{ }"
    case Con{h, t}:
      "{ " ++ String.join(Con{h, t}, " ") ++ " }"

# the names of a class's permissions in a set, as "{ read write }"
def Selinux.perms_show(+p: P.SePolicy, c: Nat, b: List<&2, Bool>) -> String:
  Selinux.braces(Selinux.names.go(Bits.SeBits.to_list(b), P.SePolicy.class_perms(p, c)))

# Contexts as text: user:role:type:sensitivity[:categories][-sensitivity[:categories]]
# (categories c0,c2.c5: a list, with ranges written lo.hi)

def Selinux.cat_item.go(xs: List<&2, String>, +p: P.SePolicy, s: String) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match xs:
    case Con{a, Nil{}}:
      do Result<&2, &2, P.SeError, List<&2, Bool>>:
        i : Nat <- Selinux.id(p, "g:" ++ a)
        return Bits.SeBits.single(i)
    case Con{a, Con{b, Nil{}}}:
      do Result<&2, &2, P.SeError, List<&2, Bool>>:
        i : Nat <- Selinux.id(p, "g:" ++ a)
        j : Nat <- Selinux.id(p, "g:" ++ b)
        return Bits.SeBits.andnot(Bits.SeBits.full(1n+j), Bits.SeBits.full(i))
    case other:
      Fail{P.SeErrBadContext{s}}

def Selinux.cats(xs: List<&2, String>, +p: P.SePolicy) -> Result<&2, &2, P.SeError, List<&2, Bool>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{+x, t}:
      do Result<&2, &2, P.SeError, List<&2, Bool>>:
        a : List<&2, Bool> <- Selinux.cat_item.go(String.split(x, '.'), p, x)
        b : List<&2, Bool> <- Selinux.cats(t, p)
        return Bits.SeBits.or(a, b)

def Selinux.level.go(xs: List<&2, String>, +p: P.SePolicy, s: String) -> Result<&2, &2, P.SeError, M.SeLevel>:
  match xs:
    case Con{sens, Nil{}}:
      do Result<&2, &2, P.SeError, M.SeLevel>:
        i : Nat <- Selinux.id(p, "s:" ++ sens)
        return M.SeLevel{i, Nil{}}
    case Con{sens, Con{cs, Nil{}}}:
      do Result<&2, &2, P.SeError, M.SeLevel>:
        i : Nat <- Selinux.id(p, "s:" ++ sens)
        b : List<&2, Bool> <- Selinux.cats(String.split(cs, ','), p)
        return M.SeLevel.make(i, b)
    case other:
      Fail{P.SeErrBadContext{s}}

# a level: s0, s0:c0,c3.c5
def Selinux.level(+p: P.SePolicy, +s: String) -> Result<&2, &2, P.SeError, M.SeLevel>:
  Selinux.level.go(String.split(s, ':'), p, s)

def Selinux.range.go(xs: List<&2, String>, +p: P.SePolicy, s: String) -> Result<&2, &2, P.SeError, M.SeRange>:
  match xs:
    case Con{lo, Nil{}}:
      do Result<&2, &2, P.SeError, M.SeRange>:
        +l : M.SeLevel <- Selinux.level(p, lo)
        return M.SeRange{l, l}
    case Con{lo, Con{hi, Nil{}}}:
      do Result<&2, &2, P.SeError, M.SeRange>:
        l : M.SeLevel <- Selinux.level(p, lo)
        h : M.SeLevel <- Selinux.level(p, hi)
        return M.SeRange{l, h}
    case other:
      Fail{P.SeErrBadContext{s}}

# a range: low, or low-high
def Selinux.range(+p: P.SePolicy, +s: String) -> Result<&2, &2, P.SeError, M.SeRange>:
  Selinux.range.go(String.split(s, '-'), p, s)

def Selinux.context.range(rest: List<&2, String>, +p: P.SePolicy) -> Result<&2, &2, P.SeError, M.SeRange>:
  match rest:
    case Nil{}:
      Done{M.SeRange{M.SeLevel{0n, Nil{}}, M.SeLevel{0n, Nil{}}}}
    case Con{h, t}:
      Selinux.range(p, String.join(Con{h, t}, ":"))

def Selinux.context.go(xs: List<&2, String>, +p: P.SePolicy, s: String) -> Result<&2, &2, P.SeError, C.SeContext>:
  match xs:
    case Con{u, Con{r, Con{t, rest}}}:
      do Result<&2, &2, P.SeError, C.SeContext>:
        ui : Nat <- Selinux.id(p, "u:" ++ u)
        ri : Nat <- Selinux.id(p, "r:" ++ r)
        ti : Nat <- Selinux.id(p, "t:" ++ t)
        g : M.SeRange <- Selinux.context.range(rest, p)
        return C.SeContext{ui, ri, ti, g}
    case other:
      Fail{P.SeErrBadContext{s}}

# a security context from its text, user:role:type[:range] (no range: the
# level s0)
def Selinux.context(+p: P.SePolicy, +s: String) -> Result<&2, &2, P.SeError, C.SeContext>:
  Selinux.context.go(String.split(s, ':'), p, s)

def Selinux.cats_show(+p: P.SePolicy, b: List<&2, Bool>) -> String:
  String.join(Selinux.names.go(Bits.SeBits.to_list(b), P.SeDecl.cats(P.SePolicy.decl(p))), ",")

def Selinux.level_show.go(some: Bool, +p: P.SePolicy, s: Nat, cats: List<&2, Bool>) -> String:
  match some:
    case False{}:
      P.SePolicy.sens_name(p, s)
    case True{}:
      P.SePolicy.sens_name(p, s) ++ ":" ++ Selinux.cats_show(p, cats)

# a level as text: s0, s1:c0,c3
def Selinux.level_show(+p: P.SePolicy, l: M.SeLevel) -> String:
  match l:
    case M.SeLevel{s, +cats}:
      Selinux.level_show.go(Bits.SeBits.any(cats), p, s, cats)

def Selinux.range_show.go(same: Bool, +p: P.SePolicy, lo: M.SeLevel, hi: M.SeLevel) -> String:
  match same:
    case True{}:
      Selinux.level_show(p, lo)
    case False{}:
      Selinux.level_show(p, lo) ++ "-" ++ Selinux.level_show(p, hi)

# a range as text: low, or low-high when they differ
def Selinux.range_show(+p: P.SePolicy, r: M.SeRange) -> String:
  match r:
    case M.SeRange{+lo, +hi}:
      Selinux.range_show.go(M.SeLevel.eq(lo, hi), p, lo, hi)

# a context as text
def Selinux.context_show(+p: P.SePolicy, c: C.SeContext) -> String:
  match c:
    case C.SeContext{u, r, t, g}:
      P.SePolicy.user_name(p, u) ++ ":" ++ P.SePolicy.role_name(p, r) ++ ":" ++ P.SePolicy.type_name(p, t) ++ ":" ++ Selinux.range_show(p, g)

# Questions by name

# the access vectors for two contexts and a class, given as text
def Selinux.compute_av(+p: P.SePolicy, scon: String, tcon: String, cls: String) -> Result<&2, &2, P.SeError, A.SeAvd>:
  do Result<&2, &2, P.SeError, A.SeAvd>:
    s : C.SeContext <- Selinux.context(p, scon)
    t : C.SeContext <- Selinux.context(p, tcon)
    c : Nat <- Selinux.class(p, cls)
    return A.SeAvc.compute(p, s, t, c)

# the decision on the named permissions
def Selinux.check(+o: A.SeOptions, +p: P.SePolicy, scon: String, tcon: String, +cls: String, perms: List<&2, String>) -> Result<&2, &2, P.SeError, A.SeDecision>:
  do Result<&2, &2, P.SeError, A.SeDecision>:
    s : C.SeContext <- Selinux.context(p, scon)
    t : C.SeContext <- Selinux.context(p, tcon)
    c : Nat <- Selinux.class(p, cls)
    req : List<&2, Bool> <- Selinux.perms(p, cls, perms)
    return A.SeAvc.check(o, p, s, t, c, req)

# the context of a new object (or of a process after exec), as text
def Selinux.create(+p: P.SePolicy, scon: String, tcon: String, cls: String, name: Maybe<&2, String>) -> Result<&2, &2, P.SeError, String>:
  do Result<&2, &2, P.SeError, String>:
    s : C.SeContext <- Selinux.context(p, scon)
    t : C.SeContext <- Selinux.context(p, tcon)
    c : Nat <- Selinux.class(p, cls)
    return Selinux.context_show(p, A.SeAvc.compute_create(p, s, t, c, name))

# the policy with the named boolean set
def Selinux.set_bool(+p: P.SePolicy, name: String, v: Bool) -> Result<&2, &2, P.SeError, P.SePolicy>:
  do Result<&2, &2, P.SeError, P.SePolicy>:
    b : Nat <- Selinux.id(p, "b:" ++ name)
    return P.SePolicy.set_bool(p, b, v)

# errors as text
def SeError.show(e: P.SeError) -> String:
  match e:
    case P.SeErrSyntax{m}:
      "syntax: " ++ m
    case P.SeErrUnknownStatement{n}:
      "unknown statement: " ++ n
    case P.SeErrBadStatement{n}:
      "bad statement: " ++ n
    case P.SeErrUndeclared{n}:
      "undeclared: " ++ n
    case P.SeErrDuplicate{n}:
      "duplicate: " ++ n
    case P.SeErrAttributeCycle{n}:
      "attribute cycle: " ++ n
    case P.SeErrUnsupported{n}:
      "unsupported: " ++ n
    case P.SeErrBadContext{t}:
      "bad context: " ++ t
    case P.SeErrNeverallow{n, a}:
      "neverallow violated"
    case P.SeErrTypeConflict{a, b}:
      "type rule conflict"
    case P.SeErrRoleTransConflict{a, b}:
      "role transition conflict"
