# bend-osdev-selinux: constraints and MLS constraints.
#
# A constraint (CIL constrain, mlsconstrain) names a class and some of its
# permissions, and an expression over the two contexts of an access: u1, r1,
# t1 (and l1, h1) of the source, u2, r2, t2 (and l2, h2) of the target. A
# permission the constraint names is granted only if the expression holds
# (SELinux Notebook, "Constraint statements"; the CIL reference, "Constraint
# Statements"). An MLS constraint applies only when the policy enables MLS.
import Base
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C

# which part of a context an expression compares
type SeCattr is Data:
  SeCUser{}
  SeCRole{}
  SeCType{}

# which context: 1 (the source) or 2 (the target)
type SeCside is Data:
  SeCSource{}
  SeCTarget{}

# a level of the source or the target: l1, h1, l2, h2
type SeLsel is Data:
  SeL1{}
  SeH1{}
  SeL2{}
  SeH2{}

type SeLop is Data:
  SeLDom{}
  SeLDomby{}
  SeLIncomp{}
  SeLEq{}
  SeLNeq{}

type SeCexpr is Data:
  SeCNot{e: SeCexpr}
  SeCAnd{a: SeCexpr, b: SeCexpr}
  SeCOr{a: SeCexpr, b: SeCexpr}
  # (eq u1 u2) when eq is True, (neq u1 u2) when it is False
  SeCPair{attr: SeCattr, eq: Bool}
  # (eq t1 names), (neq t2 names): the side's attribute is (is not) in the set
  SeCSet{attr: SeCattr, side: SeCside, eq: Bool, set: List<&2, Bool>}
  # (dom l1 h2) and the other level comparisons
  SeCLevel{op: SeLop, l: SeLsel, r: SeLsel}

type SeConstraint is Data:
  SeConstraint{mls: Bool, cls: Nat, perms: List<&2, Bool>, expr: SeCexpr}

def SeConstraint.mls(x: SeConstraint) -> Bool:
  match x:
    case SeConstraint{v, _, _, _}:
      v

def SeConstraint.cls(x: SeConstraint) -> Nat:
  match x:
    case SeConstraint{_, v, _, _}:
      v

def SeConstraint.perms(x: SeConstraint) -> List<&2, Bool>:
  match x:
    case SeConstraint{_, _, v, _}:
      v

def SeConstraint.expr(x: SeConstraint) -> SeCexpr:
  match x:
    case SeConstraint{_, _, _, v}:
      v

def SeCattr.of(a: SeCattr, c: C.SeContext) -> Nat:
  match a:
    case SeCUser{}:
      C.SeContext.user(c)
    case SeCRole{}:
      C.SeContext.role(c)
    case SeCType{}:
      C.SeContext.typ(c)

def SeCside.pick(side: SeCside, s: C.SeContext, t: C.SeContext) -> C.SeContext:
  match side:
    case SeCSource{}:
      s
    case SeCTarget{}:
      t

def SeLsel.of(l: SeLsel, s: C.SeContext, t: C.SeContext) -> M.SeLevel:
  match l:
    case SeL1{}:
      C.SeContext.low(s)
    case SeH1{}:
      C.SeContext.high(s)
    case SeL2{}:
      C.SeContext.low(t)
    case SeH2{}:
      C.SeContext.high(t)

def SeLop.eval(op: SeLop, +a: M.SeLevel, +b: M.SeLevel) -> Bool:
  match op:
    case SeLDom{}:
      M.SeLevel.dom(a, b)
    case SeLDomby{}:
      M.SeLevel.domby(a, b)
    case SeLIncomp{}:
      M.SeLevel.incomp(a, b)
    case SeLEq{}:
      M.SeLevel.eq(a, b)
    case SeLNeq{}:
      Bool.not(M.SeLevel.eq(a, b))

# x for eq, not x for neq
def SeCexpr.sense(eq: Bool, x: Bool) -> Bool:
  match eq:
    case True{}:
      x
    case False{}:
      Bool.not(x)

# the expression, for source context s and target context t
def SeCexpr.eval(e: SeCexpr, +s: C.SeContext, +t: C.SeContext) -> Bool:
  match e:
    case SeCNot{a}:
      Bool.not(SeCexpr.eval(a, s, t))
    case SeCAnd{a, b}:
      Bool.and(SeCexpr.eval(a, s, t), SeCexpr.eval(b, s, t))
    case SeCOr{a, b}:
      Bool.or(SeCexpr.eval(a, s, t), SeCexpr.eval(b, s, t))
    case SeCPair{+attr, eq}:
      SeCexpr.sense(eq, Nat.is_eq(SeCattr.of(attr, s), SeCattr.of(attr, t)))
    case SeCSet{attr, side, eq, set}:
      SeCexpr.sense(eq, Bits.SeBits.has(set, SeCattr.of(attr, SeCside.pick(side, s, t))))
    case SeCLevel{op, l, r}:
      SeLop.eval(op, SeLsel.of(l, s, t), SeLsel.of(r, s, t))

# the constraint applies to permission k of class c, now: it names them, and
# it is not an MLS constraint while MLS is off
def SeConstraint.applies(con: SeConstraint, mls_on: Bool, +c: Nat, +k: Nat) -> Bool:
  match con:
    case SeConstraint{m, cls, perms, e}:
      Bool.and(Bool.or(Bool.not(m), mls_on), Bool.and(Nat.is_eq(cls, c), Bits.SeBits.has(perms, k)))

# the constraint does not forbid permission k of class c
def SeConstraint.holds(+con: SeConstraint, mls_on: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, +k: Nat) -> Bool:
  Bool.or(Bool.not(SeConstraint.applies(con, mls_on, c, k)), SeCexpr.eval(SeConstraint.expr(con), s, t))

# every constraint allows permission k of class c (with MLS on or off)
def SeConstraints.permits(cs: List<&2, SeConstraint>, +mls_on: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, +k: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{con, rest}:
      Bool.and(SeConstraint.holds(con, mls_on, s, t, c, k), SeConstraints.permits(rest, mls_on, s, t, c, k))

# every constraint of one kind (MLS when want is True, plain when False)
# that names permission k of class c holds
def SeConstraint.holds_kind(con: SeConstraint, want: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, +k: Nat) -> Bool:
  match con:
    case SeConstraint{m, cls, perms, e}:
      Bool.or(Bool.not(Bool.and(Bool.not(Bool.xor(m, want)), Bool.and(Nat.is_eq(cls, c), Bits.SeBits.has(perms, k)))), SeCexpr.eval(e, s, t))

def SeConstraints.permits_kind(cs: List<&2, SeConstraint>, +want: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, +k: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{con, rest}:
      Bool.and(SeConstraint.holds_kind(con, want, s, t, c, k), SeConstraints.permits_kind(rest, want, s, t, c, k))

# the implementation: an access vector less the permissions a failing
# constraint names (what SeAvc.compute applies)
def SeConstraints.apply.go(fails: Bool, av: List<&2, Bool>, perms: List<&2, Bool>) -> List<&2, Bool>:
  match fails:
    case True{}:
      Bits.SeBits.andnot(av, perms)
    case False{}:
      av

def SeConstraints.apply.one(con: SeConstraint, mls_on: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, av: List<&2, Bool>) -> List<&2, Bool>:
  match con:
    case SeConstraint{m, cls, +perms, e}:
      SeConstraints.apply.go(Bool.and(Bool.or(Bool.not(m), mls_on), Bool.and(Nat.is_eq(cls, c), Bool.not(SeCexpr.eval(e, s, t)))), av, perms)

def SeConstraints.apply(cs: List<&2, SeConstraint>, +mls_on: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, av: List<&2, Bool>) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      av
    case Con{con, rest}:
      SeConstraints.apply(rest, mls_on, s, t, c, SeConstraints.apply.one(con, mls_on, s, t, c, av))
