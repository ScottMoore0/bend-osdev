# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input (every policy, context, class, permission,
# boolean state and set):
#
#   Access: permission k is in the allowed vector exactly when an allow rule
#     in force covers it and every constraint holds (MLS constraints only
#     with MLS on). So an access is allowed only if some allow rule covers
#     it, every plain constraint holds, and, with MLS on, every MLS
#     constraint (the policy's statement of MLS dominance) holds; in
#     enforcing mode, for a source type that is not permissive, a single
#     permission is granted exactly when it is allowed. The audit vectors
#     are exactly what the auditallow and dontaudit rules in force say.
#   Booleans: an access no conditional rule mentions (in either branch) gets
#     the same answer under every boolean state; the rules in force are the
#     unconditional rules and, of each booleanif, the branch its condition
#     chooses (SeTe.active_av, which the access law above is stated over).
#   Neverallow: a policy that passes the load-time check never allows, in
#     any boolean state, an access a neverallow rule forbids; Selinux.load
#     answers a policy only if it passes the check.
#   MLS: dominance is reflexive, transitive and antisymmetric (on canonical
#     levels, which SeLevel.make builds), so a partial order.
#   Transitions: the type a typetransition (typechange, typemember) gives is
#     the result of a rule in force that matches; without one, a new object
#     takes the target's type and a process keeps its own.
#   Sets: membership of union, intersection, difference, singletons, full
#     sets and the canonical form; subsets.
#
# Every law with a hypothesis has a witness below: an input, from
# example.bend, that satisfies the hypothesis.
#
# Vectors: none here; check.bend and the differential test (ref/) exercise
# the CIL compiler, whose for-all laws (a round trip of CIL text) are not
# attempted (see README.md).
import Base
import ../bytes/bytes.bend as B
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C
import ./constraints.bend as K
import ./policy.bend as P
import ./te.bend as T
import ./avc.bend as A
import ./selinux.bend as S
import ./example.bend as X

# Sets

law bits_has_or:
  for +a: List<&2, Bool>
  for +b: List<&2, Bool>
  for +k: Nat
  {Bits.SeBits.has(Bits.SeBits.or(a, b), k) == Bool.or(Bits.SeBits.has(a, k), Bits.SeBits.has(b, k)) : Bool}

law bits_has_and:
  for +a: List<&2, Bool>
  for +b: List<&2, Bool>
  for +k: Nat
  {Bits.SeBits.has(Bits.SeBits.and(a, b), k) == Bool.and(Bits.SeBits.has(a, k), Bits.SeBits.has(b, k)) : Bool}

law bits_has_andnot:
  for +a: List<&2, Bool>
  for +b: List<&2, Bool>
  for +k: Nat
  {Bits.SeBits.has(Bits.SeBits.andnot(a, b), k) == Bool.and(Bits.SeBits.has(a, k), Bool.not(Bits.SeBits.has(b, k))) : Bool}

law bits_has_single:
  for +i: Nat
  for +k: Nat
  {Bits.SeBits.has(Bits.SeBits.single(i), k) == Nat.is_eq(i, k) : Bool}

law bits_has_full:
  for +n: Nat
  for +k: Nat
  {Bits.SeBits.has(Bits.SeBits.full(n), k) == Nat.is_lt(k, n) : Bool}

law bits_has_norm:
  for +b: List<&2, Bool>
  for +k: Nat
  {Bits.SeBits.has(Bits.SeBits.norm(b), k) == Bits.SeBits.has(b, k) : Bool}

law bits_norm_canonical:
  for +b: List<&2, Bool>
  {Bits.SeBits.is_norm(Bits.SeBits.norm(b)) == True{} : Bool}

law bits_subset_single:
  for +k: Nat
  for +b: List<&2, Bool>
  {Bits.SeBits.subset(Bits.SeBits.single(k), b) == Bits.SeBits.has(b, k) : Bool}

law bits_any_has:
  for +b: List<&2, Bool>
  for +k: Nat
  for +h: {Bits.SeBits.has(b, k) == True{} : Bool}
  {Bits.SeBits.any(b) == True{} : Bool}

law bits_subset_has:
  for +a: List<&2, Bool>
  for +b: List<&2, Bool>
  for +k: Nat
  for +h1: {Bits.SeBits.subset(a, b) == True{} : Bool}
  for +h2: {Bits.SeBits.has(a, k) == True{} : Bool}
  {Bits.SeBits.has(b, k) == True{} : Bool}

# MLS dominance: a partial order

law dom_refl:
  for +l: M.SeLevel
  {M.SeLevel.dom(l, l) == True{} : Bool}

law dom_trans:
  for +a: M.SeLevel
  for +b: M.SeLevel
  for +c: M.SeLevel
  for +h1: {M.SeLevel.dom(a, b) == True{} : Bool}
  for +h2: {M.SeLevel.dom(b, c) == True{} : Bool}
  {M.SeLevel.dom(a, c) == True{} : Bool}

law dom_antisym:
  for +a: M.SeLevel
  for +b: M.SeLevel
  for +h1: {M.SeLevel.dom(a, b) == True{} : Bool}
  for +h2: {M.SeLevel.dom(b, a) == True{} : Bool}
  for +ca: {M.SeLevel.canonical(a) == True{} : Bool}
  for +cb: {M.SeLevel.canonical(b) == True{} : Bool}
  {a == b : M.SeLevel}

law level_make_canonical:
  for +s: Nat
  for +cats: List<&2, Bool>
  {M.SeLevel.canonical(M.SeLevel.make(s, cats)) == True{} : Bool}

# Access

law av_allowed_exact:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  {Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k) == Bool.and(T.SeTe.covers(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k), K.SeConstraints.permits(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, k)) : Bool}

law allowed_needs_allow:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  for +h: {Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k) == True{} : Bool}
  {T.SeTe.covers(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k) == True{} : Bool}

law allowed_needs_constraints:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  for +h: {Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k) == True{} : Bool}
  {K.SeConstraints.permits_kind(P.SePolicy.constraints(p), False{}, s, t, c, k) == True{} : Bool}

law allowed_needs_mls:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  for +m: {P.SePolicy.mls(p) == True{} : Bool}
  for +h: {Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k) == True{} : Bool}
  {K.SeConstraints.permits_kind(P.SePolicy.constraints(p), True{}, s, t, c, k) == True{} : Bool}

law av_auditallow_exact:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  {Bits.SeBits.has(A.SeAvd.auditallow(A.SeAvc.compute(p, s, t, c)), k) == T.SeTe.covers(p, P.SeAuditallow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k) : Bool}

law av_auditdeny_exact:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  {Bits.SeBits.has(A.SeAvd.auditdeny(A.SeAvc.compute(p, s, t, c)), k) == Bool.and(Nat.is_lt(k, A.SeAvc.nperms(p, c)), Bool.not(T.SeTe.covers(p, P.SeDontaudit{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k))) : Bool}

# Enforcing and permissive

law granted_enforcing:
  for +o: A.SeOptions
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  for +h: {A.SeAvc.lenient(o, p, s) == False{} : Bool}
  {A.SeDecision.granted(A.SeAvc.check(o, p, s, t, c, Bits.SeBits.single(k))) == Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k) : Bool}

law permissive_grants:
  for +o: A.SeOptions
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +req: List<&2, Bool>
  for +h: {A.SeOptions.enforcing(o) == False{} : Bool}
  {A.SeDecision.granted(A.SeAvc.check(o, p, s, t, c, req)) == True{} : Bool}

law permissive_type_grants:
  for +o: A.SeOptions
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +req: List<&2, Bool>
  for +h1: {A.SeOptions.permissive_types(o) == True{} : Bool}
  for +h2: {Bits.SeBits.has(P.SePolicy.permissive(p), C.SeContext.typ(s)) == True{} : Bool}
  {A.SeDecision.granted(A.SeAvc.check(o, p, s, t, c, req)) == True{} : Bool}

# Booleans

law bool_only_conditional:
  for +p: P.SePolicy
  for +bs: List<&2, Bool>
  for +kind: P.SeAvKind
  for +st: Nat
  for +tt: Nat
  for +c: Nat
  for +k: Nat
  for +h: {T.SeTe.cond_mentions(p, kind, st, tt, c, k) == False{} : Bool}
  {T.SeTe.covers(P.SePolicy.with_bools(p, bs), kind, st, tt, c, k) == T.SeTe.covers(p, kind, st, tt, c, k) : Bool}

law bool_av_independent:
  for +p: P.SePolicy
  for +bs: List<&2, Bool>
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  for +h: {T.SeTe.cond_mentions(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k) == False{} : Bool}
  {Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(P.SePolicy.with_bools(p, bs), s, t, c)), k) == Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k) : Bool}

# Neverallow

law neverallow_sound:
  for +p: P.SePolicy
  for +st: Nat
  for +tt: Nat
  for +c: Nat
  for +k: Nat
  for +ok: {T.SeTe.neverallow_ok(p) == True{} : Bool}
  for +h: {T.SeTe.never_covers(p, st, tt, c, k) == True{} : Bool}
  {T.SeTe.ever_covers(p, P.SeAllow{}, st, tt, c, k) == False{} : Bool}

law neverallow_never_allowed:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +k: Nat
  for +ok: {T.SeTe.neverallow_ok(p) == True{} : Bool}
  for +h: {T.SeTe.never_covers(p, C.SeContext.typ(s), C.SeContext.typ(t), c, k) == True{} : Bool}
  {Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k) == False{} : Bool}

law load_checks_neverallow:
  for o: B.Octets
  for +p: P.SePolicy
  for +h: {S.Selinux.load(o) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}
  {T.SeTe.neverallow_ok(p) == True{} : Bool}

law validate_refuses:
  for +p: P.SePolicy
  for +h: {T.SeTe.neverallow_ok(p) == False{} : Bool}
  {Result.is_fail(&2, &2, P.SeError, P.SePolicy, S.Selinux.validate(p)) == True{} : Bool}

# Transitions

law new_type_sound:
  for +p: P.SePolicy
  for +kind: P.SeTyKind
  for +st: Nat
  for +tt: Nat
  for +c: Nat
  for +on: Maybe<&2, String>
  for +x: Nat
  for +h: {T.SeTe.new_type(p, kind, st, tt, c, on) == Some{x} : Maybe<&2, Nat>}
  {T.SeTe.ty_gives(T.SeTe.active_ty(p), kind, st, tt, c, x) == True{} : Bool}

law create_by_rule:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +on: Maybe<&2, String>
  for +x: Nat
  for +h: {T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, on) == Some{x} : Maybe<&2, Nat>}
  {C.SeContext.typ(A.SeAvc.compute_create(p, s, t, c, on)) == x : Nat}

law create_object_default:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +on: Maybe<&2, String>
  for +hp: {A.SeAvc.is_process(p, c) == False{} : Bool}
  for +h: {T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, on) == None{} : Maybe<&2, Nat>}
  {C.SeContext.typ(A.SeAvc.compute_create(p, s, t, c, on)) == C.SeContext.typ(t) : Nat}

law create_process_default:
  for +p: P.SePolicy
  for +s: C.SeContext
  for +t: C.SeContext
  for +c: Nat
  for +on: Maybe<&2, String>
  for +hp: {A.SeAvc.is_process(p, c) == True{} : Bool}
  for +h: {T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, on) == None{} : Maybe<&2, Nat>}
  {C.SeContext.typ(A.SeAvc.compute_create(p, s, t, c, on)) == C.SeContext.typ(s) : Nat}

# Witnesses: each hypothesis above holds for some input

# a set with a member (bits_any_has, bits_subset_has)
law witness_has:
  {Bits.SeBits.has([False{}, True{}], 1n) == True{} : Bool}

law witness_subset:
  {Bits.SeBits.subset([False{}, True{}], [True{}, True{}]) == True{} : Bool}

# levels s1:c0 dom s0:c0 dom s0 (dom_trans), and s0:c0 both ways (dom_antisym)
law witness_dom_ab:
  {M.SeLevel.dom(M.SeLevel{1n, [True{}]}, M.SeLevel{0n, [True{}]}) == True{} : Bool}

law witness_dom_bc:
  {M.SeLevel.dom(M.SeLevel{0n, [True{}]}, M.SeLevel{0n, Nil{}}) == True{} : Bool}

law witness_dom_ba:
  {M.SeLevel.dom(M.SeLevel{0n, [True{}]}, M.SeLevel{0n, [True{}]}) == True{} : Bool}

law witness_canonical:
  {M.SeLevel.canonical(M.SeLevel{0n, [True{}]}) == True{} : Bool}

# the example allows a_t to read b_t (allowed_needs_*), with MLS on
law witness_allowed:
  {Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(X.SeExample.policy(), X.SeExample.source(), X.SeExample.target(), 0n)), 0n) == True{} : Bool}

law witness_mls_on:
  {P.SePolicy.mls(X.SeExample.policy()) == True{} : Bool}

# enforcing, and a_t is not permissive (granted_enforcing)
law witness_not_lenient:
  {A.SeAvc.lenient(A.SeOptions.default(), X.SeExample.policy(), X.SeExample.source()) == False{} : Bool}

# permissive mode (permissive_grants), and b_t is a permissive type
# (permissive_type_grants)
law witness_permissive_mode:
  {A.SeOptions.enforcing(A.SeOptions.permissive()) == False{} : Bool}

law witness_permissive_types_on:
  {A.SeOptions.permissive_types(A.SeOptions.default()) == True{} : Bool}

law witness_permissive_type:
  {Bits.SeBits.has(P.SePolicy.permissive(X.SeExample.policy()), C.SeContext.typ(X.SeExample.permissive_source())) == True{} : Bool}

# no conditional rule mentions a_t reading b_t (bool_*)
law witness_unconditional:
  {T.SeTe.cond_mentions(X.SeExample.policy(), P.SeAllow{}, 0n, 1n, 0n, 0n) == False{} : Bool}

# the example passes the neverallow check, and forbids a_t writing b_t
# (neverallow_*)
law witness_neverallow_ok:
  {T.SeTe.neverallow_ok(X.SeExample.policy()) == True{} : Bool}

law witness_never_covers:
  {T.SeTe.never_covers(X.SeExample.policy(), 0n, 1n, 0n, 1n) == True{} : Bool}

# a policy that fails the check: the example with flag's rule letting a_t
# write b_t (validate_refuses)
law witness_neverallow_violated:
  {T.SeTe.neverallow_ok(P.SePolicy{X.SeExample.decl(), P.SeRules{P.SeRules.av(X.SeExample.rules()), Nil{}, [P.SeCond{P.SeBVar{0n}, Nil{}, Nil{}, [P.SeAvRule{P.SeAllow{}, [True{}], [False{}, True{}], False{}, 0n, [True{}, True{}]}], Nil{}}], Nil{}, Nil{}, Nil{}, Nil{}}, True{}, Nil{}}) == False{} : Bool}

# a CIL text that loads (load_checks_neverallow)
law witness_load:
  exs p: P.SePolicy
  {S.Selinux.load(B.Octets.of_string("(class file (read)) (type a_t) (allow a_t a_t (file (read)))")) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}

# typetransition a_t b_t file a_t (new_type_sound, create_by_rule)
law witness_new_type:
  {T.SeTe.new_type(X.SeExample.policy(), P.SeTyTransition{}, 0n, 1n, 0n, None{}) == Some{0n} : Maybe<&2, Nat>}

# no rule for b_t creating a file in a_t; file is not the process class
# (create_object_default); process is (create_process_default)
law witness_no_rule:
  {T.SeTe.new_type(X.SeExample.policy(), P.SeTyTransition{}, 1n, 0n, 0n, None{}) == None{} : Maybe<&2, Nat>}

law witness_not_process:
  {A.SeAvc.is_process(X.SeExample.policy(), 0n) == False{} : Bool}

law witness_no_rule_process:
  {T.SeTe.new_type(X.SeExample.policy(), P.SeTyTransition{}, 1n, 0n, 1n, None{}) == None{} : Maybe<&2, Nat>}

law witness_process:
  {A.SeAvc.is_process(X.SeExample.policy(), 1n) == True{} : Bool}
