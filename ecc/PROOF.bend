import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../bignum/bignum.bend as N
import ../bignum/LAWS.bend as NL
import ../bignum/PROOF.bend as NP
import ./ecc.bend as E
import ./ecdh.bend as D
import ./ecdsa.bend as S
import ./LAWS.bend as Laws

def ep.bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ep.absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : ep.bdisc(_)
  Unit{}

def and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ep.absurd(h))

def and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, ep.absurd(h))

def nat_eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, ep.absurd(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, ep.absurd(h))
    case 1n+p 1n+q:
      %nat_eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# Point-validation soundness: decoding accepts only what its on-curve check
# accepted, and full validation includes the on-curve check

def on_go(form: Bool, oncurve: Bool, +c: E.EcCurve, +x: N.BnNat, +y: N.BnNat, +ho: {E.ec.on.aff(c, x, y) == oncurve : Bool}) -> {Result.map(&2, &2, E.EcError, E.EcPoint, Bool, p => E.EcCurve.on_curve(c, p), E.ec.pt.go(form, oncurve, x, y)) == Result.map(&2, &2, E.EcError, E.EcPoint, Bool, p => True{}, E.ec.pt.go(form, oncurve, x, y)) : Result<&2, &2, E.EcError, Bool>}:
  match form oncurve:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      %Equal.sym(Bool, E.ec.on.aff(c, x, y), True{}, ho) : {Done{_} == Done{True{}} : Result<&2, &2, E.EcError, Bool>}
      {==}

def Laws.point_of_on_curve(c, o):
  on_go(Bool.and(B.Octets.is_eq(B.Octets.take(1n, o), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)))), E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), {==})

def Laws.validate_on_curve(c, p, h):
  and_l(E.EcCurve.on_curve(c, p), N.BnNat.is_zero(E.EcJac.z(E.ec.mul.jac(c, E.EcCurve.n(c), p))), h)

# A point's bytes, written back, decode to the same point: each
# coordinate's bytes come back from its number (bignum's
# octets_round_trip), and the decoding takes them apart at the same places

def rt_ok(+c: E.EcCurve, +o: B.Octets, +lx: {B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))) == E.EcCurve.field_len(c) : Nat}, +ly: {B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))) == E.EcCurve.field_len(c) : Nat}, +hbx: {Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)) == True{} : Bool}, +hby: {Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)) == True{} : Bool}, +ho: {E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) == True{} : Bool}) -> {E.EcCurve.point_of(c, E.EcCurve.point_to(c, E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))})) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}:
  %lx : {E.EcCurve.point_of(c, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(Maybe.default(&2, B.Octets, N.BnNat.to_octets(N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), _), B.Octets.zeros(E.EcCurve.field_len(c))), Maybe.default(&2, B.Octets, N.BnNat.to_octets(N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), B.Octets.zeros(E.EcCurve.field_len(c)))))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(Maybe<&2, B.Octets>, N.BnNat.to_octets(N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), Some{B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))}, NL.octets_round_trip(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) : {E.EcCurve.point_of(c, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(Maybe.default(&2, B.Octets, _, B.Octets.zeros(E.EcCurve.field_len(c))), Maybe.default(&2, B.Octets, N.BnNat.to_octets(N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), B.Octets.zeros(E.EcCurve.field_len(c)))))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %ly : {E.EcCurve.point_of(c, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), Maybe.default(&2, B.Octets, N.BnNat.to_octets(N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), _), B.Octets.zeros(E.EcCurve.field_len(c)))))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(Maybe<&2, B.Octets>, N.BnNat.to_octets(N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), Some{B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))}, NL.octets_round_trip(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) : {E.EcCurve.point_of(c, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), Maybe.default(&2, B.Octets, _, B.Octets.zeros(E.EcCurve.field_len(c)))))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(B.Octets.of_list([4])), B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))), B.Octets.of_list([4]), BL.octets_take_append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))) : {E.ec.pt.go(Bool.and(B.Octets.is_eq(_, B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))))), E.EcCurve.field_len(c)))), E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))))))), N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))))))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(B.Octets.of_list([4])), B.Octets.append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), BL.octets_drop_append(B.Octets.of_list([4]), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))) : {E.ec.pt.go(Bool.and(B.Octets.is_eq(B.Octets.of_list([4]), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), _)), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), _)), E.EcCurve.field_len(c)))), E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), _)), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), _))), N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), _)), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), _))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %lx : {E.ec.pt.go(Bool.and(B.Octets.is_eq(B.Octets.of_list([4]), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(B.Octets.take(_, B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(_, B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))), E.EcCurve.field_len(c)))), E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(_, B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))), N.BnNat.of_octets(B.Octets.drop(_, B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))))), N.BnNat.of_octets(B.Octets.take(_, B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))), N.BnNat.of_octets(B.Octets.drop(_, B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), BL.octets_take_append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) : {E.ec.pt.go(Bool.and(B.Octets.is_eq(B.Octets.of_list([4]), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(_), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))))), E.EcCurve.field_len(c)))), E.ec.on.aff(c, N.BnNat.of_octets(_), N.BnNat.of_octets(B.Octets.drop(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))))), N.BnNat.of_octets(_), N.BnNat.of_octets(B.Octets.drop(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), B.Octets.append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), BL.octets_drop_append(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o)), B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) : {E.ec.pt.go(Bool.and(B.Octets.is_eq(B.Octets.of_list([4]), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(_), E.EcCurve.field_len(c)))), E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(_)), N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(_)) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), True{}, hbx) : {E.ec.pt.go(Bool.and(B.Octets.is_eq(B.Octets.of_list([4]), B.Octets.of_list([4])), Bool.and(_, Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)))), E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), True{}, hby) : {E.ec.pt.go(Bool.and(B.Octets.is_eq(B.Octets.of_list([4]), B.Octets.of_list([4])), Bool.and(True{}, _)), E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  %Equal.sym(Bool, E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), True{}, ho) : {E.ec.pt.go(Bool.and(B.Octets.is_eq(B.Octets.of_list([4]), B.Octets.of_list([4])), Bool.and(True{}, True{})), _, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) == Done{E.EcAff{N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))}} : Result<&2, &2, E.EcError, E.EcPoint>}
  {==}

def rt_go(form: Bool, oncurve: Bool, +c: E.EcCurve, +o: B.Octets, +hf: {Bool.and(B.Octets.is_eq(B.Octets.take(1n, o), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)))) == form : Bool}, +ho: {E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) == oncurve : Bool}) -> {Result.bind(&2, &2, E.EcError, E.EcPoint, E.EcPoint, E.ec.pt.go(form, oncurve, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), p => E.EcCurve.point_of(c, E.EcCurve.point_to(c, p))) == E.ec.pt.go(form, oncurve, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))) : Result<&2, &2, E.EcError, E.EcPoint>}:
  match form oncurve:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      +hxy = and_r(B.Octets.is_eq(B.Octets.take(1n, o), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c))), hf)
      +hbx = and_l(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), hxy)
      +hby = and_r(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), hxy)
      rt_ok(c, o, nat_eq_true(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c), hbx), nat_eq_true(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c), hby), hbx, hby, ho)

def Laws.point_round_trip(c, o):
  rt_go(Bool.and(B.Octets.is_eq(B.Octets.take(1n, o), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)), Nat.is_eq(B.Octets.len(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), E.EcCurve.field_len(c)))), E.ec.on.aff(c, N.BnNat.of_octets(B.Octets.take(E.EcCurve.field_len(c), B.Octets.drop(1n, o))), N.BnNat.of_octets(B.Octets.drop(E.EcCurve.field_len(c), B.Octets.drop(1n, o)))), c, o, {==}, {==})

# Vectors

def Laws.toy_check():
  {==}

# Small-parameter exhaustive laws

# BEGIN GENERATED by gen/exhaustive.py: exhaustive
def ex.bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ex.absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : ex.bdisc(_)
  Unit{}

def ex.toy_ecdh.c0_0() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c0_1() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c0_2() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c0_3() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c0_4() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c0_5() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c1_0() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c1_1() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c1_2() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c1_3() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c1_4() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c1_5() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c2_0() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c2_1() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c2_2() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c2_3() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c2_4() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c2_5() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c3_0() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c3_1() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c3_2() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c3_3() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c3_4() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c3_5() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c4_0() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c4_1() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c4_2() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c4_3() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c4_4() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c4_5() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c5_0() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c5_1() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c5_2() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c5_3() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c5_4() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def ex.toy_ecdh.c5_5() -> {D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) : Result<&2, &2, E.EcError, B.Octets>}:
  {==}

def Laws.toy_ecdh(a, b, ha, hb):
  match a:
    case 0n:
      match b:
        case 0n:
          ex.toy_ecdh.c0_0()
        case 1n+b0:
          match b0:
            case 0n:
              ex.toy_ecdh.c0_1()
            case 1n+b1:
              match b1:
                case 0n:
                  ex.toy_ecdh.c0_2()
                case 1n+b2:
                  match b2:
                    case 0n:
                      ex.toy_ecdh.c0_3()
                    case 1n+b3:
                      match b3:
                        case 0n:
                          ex.toy_ecdh.c0_4()
                        case 1n+b4:
                          match b4:
                            case 0n:
                              ex.toy_ecdh.c0_5()
                            case 1n+b5:
                              match b5:
                                case 0n:
                                  Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                                case 1n+bz:
                                  Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(0n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
    case 1n+a0:
      match a0:
        case 0n:
          match b:
            case 0n:
              ex.toy_ecdh.c1_0()
            case 1n+b0:
              match b0:
                case 0n:
                  ex.toy_ecdh.c1_1()
                case 1n+b1:
                  match b1:
                    case 0n:
                      ex.toy_ecdh.c1_2()
                    case 1n+b2:
                      match b2:
                        case 0n:
                          ex.toy_ecdh.c1_3()
                        case 1n+b3:
                          match b3:
                            case 0n:
                              ex.toy_ecdh.c1_4()
                            case 1n+b4:
                              match b4:
                                case 0n:
                                  ex.toy_ecdh.c1_5()
                                case 1n+b5:
                                  match b5:
                                    case 0n:
                                      Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                                    case 1n+bz:
                                      Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(1n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
        case 1n+a1:
          match a1:
            case 0n:
              match b:
                case 0n:
                  ex.toy_ecdh.c2_0()
                case 1n+b0:
                  match b0:
                    case 0n:
                      ex.toy_ecdh.c2_1()
                    case 1n+b1:
                      match b1:
                        case 0n:
                          ex.toy_ecdh.c2_2()
                        case 1n+b2:
                          match b2:
                            case 0n:
                              ex.toy_ecdh.c2_3()
                            case 1n+b3:
                              match b3:
                                case 0n:
                                  ex.toy_ecdh.c2_4()
                                case 1n+b4:
                                  match b4:
                                    case 0n:
                                      ex.toy_ecdh.c2_5()
                                    case 1n+b5:
                                      match b5:
                                        case 0n:
                                          Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                                        case 1n+bz:
                                          Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(2n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
            case 1n+a2:
              match a2:
                case 0n:
                  match b:
                    case 0n:
                      ex.toy_ecdh.c3_0()
                    case 1n+b0:
                      match b0:
                        case 0n:
                          ex.toy_ecdh.c3_1()
                        case 1n+b1:
                          match b1:
                            case 0n:
                              ex.toy_ecdh.c3_2()
                            case 1n+b2:
                              match b2:
                                case 0n:
                                  ex.toy_ecdh.c3_3()
                                case 1n+b3:
                                  match b3:
                                    case 0n:
                                      ex.toy_ecdh.c3_4()
                                    case 1n+b4:
                                      match b4:
                                        case 0n:
                                          ex.toy_ecdh.c3_5()
                                        case 1n+b5:
                                          match b5:
                                            case 0n:
                                              Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                                            case 1n+bz:
                                              Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(3n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                case 1n+a3:
                  match a3:
                    case 0n:
                      match b:
                        case 0n:
                          ex.toy_ecdh.c4_0()
                        case 1n+b0:
                          match b0:
                            case 0n:
                              ex.toy_ecdh.c4_1()
                            case 1n+b1:
                              match b1:
                                case 0n:
                                  ex.toy_ecdh.c4_2()
                                case 1n+b2:
                                  match b2:
                                    case 0n:
                                      ex.toy_ecdh.c4_3()
                                    case 1n+b3:
                                      match b3:
                                        case 0n:
                                          ex.toy_ecdh.c4_4()
                                        case 1n+b4:
                                          match b4:
                                            case 0n:
                                              ex.toy_ecdh.c4_5()
                                            case 1n+b5:
                                              match b5:
                                                case 0n:
                                                  Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                                                case 1n+bz:
                                                  Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(4n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                    case 1n+a4:
                      match a4:
                        case 0n:
                          match b:
                            case 0n:
                              ex.toy_ecdh.c5_0()
                            case 1n+b0:
                              match b0:
                                case 0n:
                                  ex.toy_ecdh.c5_1()
                                case 1n+b1:
                                  match b1:
                                    case 0n:
                                      ex.toy_ecdh.c5_2()
                                    case 1n+b2:
                                      match b2:
                                        case 0n:
                                          ex.toy_ecdh.c5_3()
                                        case 1n+b3:
                                          match b3:
                                            case 0n:
                                              ex.toy_ecdh.c5_4()
                                            case 1n+b4:
                                              match b4:
                                                case 0n:
                                                  ex.toy_ecdh.c5_5()
                                                case 1n+b5:
                                                  match b5:
                                                    case 0n:
                                                      Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                                                    case 1n+bz:
                                                      Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+bz), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(5n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(hb))
                        case 1n+a5:
                          match a5:
                            case 0n:
                              Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(b))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(b), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(6n))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(ha))
                            case 1n+az:
                              Empty.absurd({D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+az), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(b))) == D.EcDh.primitive(Laws.ecclaw.toy(), Laws.ecclaw.nat1(b), D.EcDh.public(Laws.ecclaw.toy(), Laws.ecclaw.nat1(7n+az))) : Result<&2, &2, E.EcError, B.Octets>}, ex.absurd(ha))

def ex.toy_ecdsa.c0_0() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(0n), Laws.ecclaw.nat1(0n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c0_1() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(0n), Laws.ecclaw.nat1(1n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c0_2() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(0n), Laws.ecclaw.nat1(2n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c0_3() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(0n), Laws.ecclaw.nat1(3n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c0_4() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(0n), Laws.ecclaw.nat1(4n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c0_5() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(0n), Laws.ecclaw.nat1(5n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c1_0() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(1n), Laws.ecclaw.nat1(0n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c1_1() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(1n), Laws.ecclaw.nat1(1n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c1_2() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(1n), Laws.ecclaw.nat1(2n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c1_3() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(1n), Laws.ecclaw.nat1(3n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c1_4() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(1n), Laws.ecclaw.nat1(4n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c1_5() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(1n), Laws.ecclaw.nat1(5n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c2_0() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(2n), Laws.ecclaw.nat1(0n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c2_1() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(2n), Laws.ecclaw.nat1(1n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c2_2() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(2n), Laws.ecclaw.nat1(2n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c2_3() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(2n), Laws.ecclaw.nat1(3n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c2_4() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(2n), Laws.ecclaw.nat1(4n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c2_5() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(2n), Laws.ecclaw.nat1(5n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c3_0() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(3n), Laws.ecclaw.nat1(0n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c3_1() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(3n), Laws.ecclaw.nat1(1n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c3_2() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(3n), Laws.ecclaw.nat1(2n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c3_3() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(3n), Laws.ecclaw.nat1(3n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c3_4() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(3n), Laws.ecclaw.nat1(4n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c3_5() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(3n), Laws.ecclaw.nat1(5n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c4_0() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(4n), Laws.ecclaw.nat1(0n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c4_1() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(4n), Laws.ecclaw.nat1(1n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c4_2() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(4n), Laws.ecclaw.nat1(2n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c4_3() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(4n), Laws.ecclaw.nat1(3n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c4_4() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(4n), Laws.ecclaw.nat1(4n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c4_5() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(4n), Laws.ecclaw.nat1(5n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c5_0() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(5n), Laws.ecclaw.nat1(0n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c5_1() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(5n), Laws.ecclaw.nat1(1n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c5_2() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(5n), Laws.ecclaw.nat1(2n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c5_3() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(5n), Laws.ecclaw.nat1(3n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c5_4() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(5n), Laws.ecclaw.nat1(4n)) == True{} : Bool}:
  {==}

def ex.toy_ecdsa.c5_5() -> {Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(5n), Laws.ecclaw.nat1(5n)) == True{} : Bool}:
  {==}

def Laws.toy_ecdsa(d, k, hd, hk):
  match d:
    case 0n:
      match k:
        case 0n:
          ex.toy_ecdsa.c0_0()
        case 1n+k0:
          match k0:
            case 0n:
              ex.toy_ecdsa.c0_1()
            case 1n+k1:
              match k1:
                case 0n:
                  ex.toy_ecdsa.c0_2()
                case 1n+k2:
                  match k2:
                    case 0n:
                      ex.toy_ecdsa.c0_3()
                    case 1n+k3:
                      match k3:
                        case 0n:
                          ex.toy_ecdsa.c0_4()
                        case 1n+k4:
                          match k4:
                            case 0n:
                              ex.toy_ecdsa.c0_5()
                            case 1n+k5:
                              match k5:
                                case 0n:
                                  Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(0n), Laws.ecclaw.nat1(6n)) == True{} : Bool}, ex.absurd(hk))
                                case 1n+kz:
                                  Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(0n), Laws.ecclaw.nat1(7n+kz)) == True{} : Bool}, ex.absurd(hk))
    case 1n+d0:
      match d0:
        case 0n:
          match k:
            case 0n:
              ex.toy_ecdsa.c1_0()
            case 1n+k0:
              match k0:
                case 0n:
                  ex.toy_ecdsa.c1_1()
                case 1n+k1:
                  match k1:
                    case 0n:
                      ex.toy_ecdsa.c1_2()
                    case 1n+k2:
                      match k2:
                        case 0n:
                          ex.toy_ecdsa.c1_3()
                        case 1n+k3:
                          match k3:
                            case 0n:
                              ex.toy_ecdsa.c1_4()
                            case 1n+k4:
                              match k4:
                                case 0n:
                                  ex.toy_ecdsa.c1_5()
                                case 1n+k5:
                                  match k5:
                                    case 0n:
                                      Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(1n), Laws.ecclaw.nat1(6n)) == True{} : Bool}, ex.absurd(hk))
                                    case 1n+kz:
                                      Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(1n), Laws.ecclaw.nat1(7n+kz)) == True{} : Bool}, ex.absurd(hk))
        case 1n+d1:
          match d1:
            case 0n:
              match k:
                case 0n:
                  ex.toy_ecdsa.c2_0()
                case 1n+k0:
                  match k0:
                    case 0n:
                      ex.toy_ecdsa.c2_1()
                    case 1n+k1:
                      match k1:
                        case 0n:
                          ex.toy_ecdsa.c2_2()
                        case 1n+k2:
                          match k2:
                            case 0n:
                              ex.toy_ecdsa.c2_3()
                            case 1n+k3:
                              match k3:
                                case 0n:
                                  ex.toy_ecdsa.c2_4()
                                case 1n+k4:
                                  match k4:
                                    case 0n:
                                      ex.toy_ecdsa.c2_5()
                                    case 1n+k5:
                                      match k5:
                                        case 0n:
                                          Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(2n), Laws.ecclaw.nat1(6n)) == True{} : Bool}, ex.absurd(hk))
                                        case 1n+kz:
                                          Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(2n), Laws.ecclaw.nat1(7n+kz)) == True{} : Bool}, ex.absurd(hk))
            case 1n+d2:
              match d2:
                case 0n:
                  match k:
                    case 0n:
                      ex.toy_ecdsa.c3_0()
                    case 1n+k0:
                      match k0:
                        case 0n:
                          ex.toy_ecdsa.c3_1()
                        case 1n+k1:
                          match k1:
                            case 0n:
                              ex.toy_ecdsa.c3_2()
                            case 1n+k2:
                              match k2:
                                case 0n:
                                  ex.toy_ecdsa.c3_3()
                                case 1n+k3:
                                  match k3:
                                    case 0n:
                                      ex.toy_ecdsa.c3_4()
                                    case 1n+k4:
                                      match k4:
                                        case 0n:
                                          ex.toy_ecdsa.c3_5()
                                        case 1n+k5:
                                          match k5:
                                            case 0n:
                                              Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(3n), Laws.ecclaw.nat1(6n)) == True{} : Bool}, ex.absurd(hk))
                                            case 1n+kz:
                                              Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(3n), Laws.ecclaw.nat1(7n+kz)) == True{} : Bool}, ex.absurd(hk))
                case 1n+d3:
                  match d3:
                    case 0n:
                      match k:
                        case 0n:
                          ex.toy_ecdsa.c4_0()
                        case 1n+k0:
                          match k0:
                            case 0n:
                              ex.toy_ecdsa.c4_1()
                            case 1n+k1:
                              match k1:
                                case 0n:
                                  ex.toy_ecdsa.c4_2()
                                case 1n+k2:
                                  match k2:
                                    case 0n:
                                      ex.toy_ecdsa.c4_3()
                                    case 1n+k3:
                                      match k3:
                                        case 0n:
                                          ex.toy_ecdsa.c4_4()
                                        case 1n+k4:
                                          match k4:
                                            case 0n:
                                              ex.toy_ecdsa.c4_5()
                                            case 1n+k5:
                                              match k5:
                                                case 0n:
                                                  Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(4n), Laws.ecclaw.nat1(6n)) == True{} : Bool}, ex.absurd(hk))
                                                case 1n+kz:
                                                  Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(4n), Laws.ecclaw.nat1(7n+kz)) == True{} : Bool}, ex.absurd(hk))
                    case 1n+d4:
                      match d4:
                        case 0n:
                          match k:
                            case 0n:
                              ex.toy_ecdsa.c5_0()
                            case 1n+k0:
                              match k0:
                                case 0n:
                                  ex.toy_ecdsa.c5_1()
                                case 1n+k1:
                                  match k1:
                                    case 0n:
                                      ex.toy_ecdsa.c5_2()
                                    case 1n+k2:
                                      match k2:
                                        case 0n:
                                          ex.toy_ecdsa.c5_3()
                                        case 1n+k3:
                                          match k3:
                                            case 0n:
                                              ex.toy_ecdsa.c5_4()
                                            case 1n+k4:
                                              match k4:
                                                case 0n:
                                                  ex.toy_ecdsa.c5_5()
                                                case 1n+k5:
                                                  match k5:
                                                    case 0n:
                                                      Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(5n), Laws.ecclaw.nat1(6n)) == True{} : Bool}, ex.absurd(hk))
                                                    case 1n+kz:
                                                      Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(5n), Laws.ecclaw.nat1(7n+kz)) == True{} : Bool}, ex.absurd(hk))
                        case 1n+d5:
                          match d5:
                            case 0n:
                              Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(6n), Laws.ecclaw.nat1(k)) == True{} : Bool}, ex.absurd(hd))
                            case 1n+dz:
                              Empty.absurd({Laws.ecclaw.signs_verify(Laws.ecclaw.nat1(7n+dz), Laws.ecclaw.nat1(k)) == True{} : Bool}, ex.absurd(hd))
# END GENERATED: exhaustive
