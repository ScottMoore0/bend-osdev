# Proofs for bend-osdev-oid: the DER form. An Oid's octets are an OBJECT
# IDENTIFIER element that DER rules accept, so they decode to it (asn1's
# decode_encode and oid_round_trip); octets decoded to an Oid are the ones
# it encodes to (asn1's der_unique and oid_canonical); every Oid read, from
# octets or text, is valid.
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/rules.bend as AR
import ../asn1/encode.bend as AEn
import ../asn1/asn1.bend as A
import ../asn1/oidval.bend as AO
import ../asn1/LAWS.bend as AL
import ../asn1/PROOF.bend as AP
import ./oid.bend as O
import ./text.bend as T
import ./proof_nat.bend as ON
import ./proof_text.bend as OT

# Results told apart

def od.dob(r: Result<&2, &2, O.OidError, B.Octets>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def od.fob(-x: O.OidError, -y: B.Octets, e: {Fail{x} == Done{y} : Result<&2, &2, O.OidError, B.Octets>}) -> Empty:
  %e : od.dob(_)
  Unit{}

def od.doo(r: Result<&2, &2, O.OidError, O.Oid>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def od.foo(-x: O.OidError, -y: O.Oid, e: {Fail{x} == Done{y} : Result<&2, &2, O.OidError, O.Oid>}) -> Empty:
  %e : od.doo(_)
  Unit{}

def od.vb(r: Result<&2, &2, O.OidError, B.Octets>) -> B.Octets:
  match r:
    case Fail{x}:
      B.Octets.empty()
    case Done{y}:
      y

def od.vo(r: Result<&2, &2, O.OidError, O.Oid>) -> O.Oid:
  match r:
    case Fail{x}:
      O.Oid{Nil{}}
    case Done{y}:
      y

# An Oid made from arcs

def od.mk_eq(ok: Bool, +arcs: List<&2, Nat>, -o: O.Oid, +e: {O.oid.mk(ok, arcs) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid{arcs} == o : O.Oid}:
  match ok:
    case False{}:
      Empty.absurd({O.Oid{arcs} == o : O.Oid}, od.foo(O.OidBadArcs{}, o, e))
    case True{}:
      Equal.cong(Result<&2, &2, O.OidError, O.Oid>, O.Oid, z => od.vo(z), Done{O.Oid{arcs}}, Done{o}, e)

def od.mk_t(ok: Bool, +arcs: List<&2, Nat>, -o: O.Oid, +e: {O.oid.mk(ok, arcs) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {ok == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, od.foo(O.OidBadArcs{}, o, e))
    case True{}:
      {==}

def od.mk_ok(+arcs: List<&2, Nat>, -o: O.Oid, +e: {O.Oid.of_arcs(arcs) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid.valid(o) == True{} : Bool}:
  +q : {O.Oid{arcs} == o : O.Oid} = od.mk_eq(O.Oid.valid_arcs(arcs), arcs, o, e)
  %q : {O.Oid.valid(_) == True{} : Bool}
  od.mk_t(O.Oid.valid_arcs(arcs), arcs, o, e)

# Octets written decode back

def od.rt_q(q: Result<&2, &2, AE.Asn1Error, B.Octets>, +c: B.Octets, -b: B.Octets, +arcs: List<&2, Nat>, +hc: {AO.Asn1.oid_content(arcs) == Done{c} : Result<&2, &2, AE.Asn1Error, B.Octets>}, +hv: {O.Oid.valid_arcs(arcs) == True{} : Bool}, +hq: {AEn.Asn1.encode(AN.Asn1Prim{AT.Asn1Tag.oid(), c}) == q : Result<&2, &2, AE.Asn1Error, B.Octets>}, +e: {O.oid.wrap(q) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}) -> {O.Oid.of_der(b) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}:
  match q:
    case Fail{x}:
      Empty.absurd({O.Oid.of_der(b) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}, od.fob(O.OidAsn1{x}, b, e))
    case Done{+b2}:
      +eb : {b2 == b : B.Octets} = Equal.cong(Result<&2, &2, O.OidError, B.Octets>, B.Octets, z => od.vb(z), Done{b2}, Done{b}, e)
      %eb : {O.Oid.of_der(_) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}
      +n : AN.Asn1Node = AN.Asn1Prim{AT.Asn1Tag.oid(), c}
      %Equal.sym(Result<&2, &2, AE.Asn1Error, AN.Asn1Node>, A.Asn1.decode(AR.Asn1Rules.der(), b2), Done{n}, AL.decode_encode(AR.Asn1Rules.der(), n, b2, hq, {==})) : {O.oid.of_der.r(_) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}
      %Equal.sym(Result<&2, &2, AE.Asn1Error, List<&2, Nat>>, AO.Asn1.oid_of_content(c), Done{arcs}, AL.oid_round_trip(arcs, c, hc)) : {O.oid.of_arcs_r(_) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}
      %Equal.sym(Bool, O.Oid.valid_arcs(arcs), True{}, hv) : {O.oid.mk(_, arcs) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}
      {==}

def od.rt_c(r: Result<&2, &2, AE.Asn1Error, B.Octets>, -b: B.Octets, +arcs: List<&2, Nat>, +hr: {AO.Asn1.oid_content(arcs) == r : Result<&2, &2, AE.Asn1Error, B.Octets>}, +hv: {O.Oid.valid_arcs(arcs) == True{} : Bool}, +e: {O.oid.wrap(O.oid.der.of(r)) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}) -> {O.Oid.of_der(b) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}:
  match r:
    case Fail{x}:
      Empty.absurd({O.Oid.of_der(b) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}, od.fob(O.OidAsn1{x}, b, e))
    case Done{+c}:
      od.rt_q(AEn.Asn1.encode(AN.Asn1Prim{AT.Asn1Tag.oid(), c}), c, b, arcs, hr, hv, {==}, e)

def od.rt(ok: Bool, +arcs: List<&2, Nat>, -b: B.Octets, +hv: {O.Oid.valid_arcs(arcs) == ok : Bool}, +e: {O.oid.to_der.pick(ok, arcs) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}) -> {O.Oid.of_der(b) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}:
  match ok:
    case False{}:
      Empty.absurd({O.Oid.of_der(b) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}, od.fob(O.OidBadArcs{}, b, e))
    case True{}:
      od.rt_c(AO.Asn1.oid_content(arcs), b, arcs, {==}, hv, e)

def od.der_rt(o: O.Oid, -b: B.Octets, +e: {O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}) -> {O.Oid.of_der(b) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}:
  match o:
    case O.Oid{+arcs}:
      od.rt(O.Oid.valid_arcs(arcs), arcs, b, {==}, e)

# Octets read are the octets written

def od.can_q(q: Result<&2, &2, AE.Asn1Error, List<&2, Nat>>, +c: B.Octets, +b: B.Octets, -o: O.Oid, +hq: {AO.Asn1.oid_of_content(c) == q : Result<&2, &2, AE.Asn1Error, List<&2, Nat>>}, +hn: {AEn.Asn1.encode(AN.Asn1Prim{AT.Asn1Tag.oid(), c}) == Done{b} : Result<&2, &2, AE.Asn1Error, B.Octets>}, +e: {O.oid.of_arcs_r(q) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}:
  match q:
    case Fail{x}:
      Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{x}, o, e))
    case Done{+arcs}:
      %od.mk_eq(O.Oid.valid_arcs(arcs), arcs, o, e) : {O.Oid.to_der(_) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}
      %Equal.sym(Bool, O.Oid.valid_arcs(arcs), True{}, od.mk_t(O.Oid.valid_arcs(arcs), arcs, o, e)) : {O.oid.to_der.pick(_, arcs) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}
      %Equal.sym(Result<&2, &2, AE.Asn1Error, B.Octets>, AO.Asn1.oid_content(arcs), Done{c}, AL.oid_canonical(c, arcs, hq)) : {O.oid.wrap(O.oid.der.of(_)) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}
      %Equal.sym(Result<&2, &2, AE.Asn1Error, B.Octets>, AEn.Asn1.encode(AN.Asn1Prim{AT.Asn1Tag.oid(), c}), Done{b}, hn) : {O.oid.wrap(_) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}
      {==}

def od.can_n(n: AN.Asn1Node, +b: B.Octets, -o: O.Oid, +hr: {A.Asn1.decode(AR.Asn1Rules.der(), b) == Done{n} : Result<&2, &2, AE.Asn1Error, AN.Asn1Node>}, +e: {O.oid.of_arcs_r(AO.Asn1.get_oid(n)) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}:
  match n:
    case AN.Asn1Cons{t, xs}:
      Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
    case AN.Asn1Prim{t, +c}:
      match t:
        case AT.Asn1Tag{cl, num}:
          match cl:
            case AT.Asn1Application{}:
              Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
            case AT.Asn1Context{}:
              Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
            case AT.Asn1Private{}:
              Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
            case AT.Asn1Universal{}:
              match num:
                case 0n:
                  Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
                case 1n+k1:
                  match k1:
                    case 0n:
                      Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
                    case 1n+k2:
                      match k2:
                        case 0n:
                          Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
                        case 1n+k3:
                          match k3:
                            case 0n:
                              Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
                            case 1n+k4:
                              match k4:
                                case 0n:
                                  Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
                                case 1n+k5:
                                  match k5:
                                    case 0n:
                                      Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))
                                    case 1n+k6:
                                      match k6:
                                        case 0n:
                                          od.can_q(AO.Asn1.oid_of_content(c), c, b, o, {==}, AL.der_unique(b, AN.Asn1Prim{AT.Asn1Tag.oid(), c}, hr), e)
                                        case 1n+k7:
                                          Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{AE.Asn1Unexpected{}}, o, e))

def od.can_r(r: Result<&2, &2, AE.Asn1Error, AN.Asn1Node>, +b: B.Octets, -o: O.Oid, +hr: {A.Asn1.decode(AR.Asn1Rules.der(), b) == r : Result<&2, &2, AE.Asn1Error, AN.Asn1Node>}, +e: {O.oid.of_der.r(r) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}:
  match r:
    case Fail{x}:
      Empty.absurd({O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}, od.foo(O.OidAsn1{x}, o, e))
    case Done{+n}:
      od.can_n(n, b, o, hr, e)

def od.can(+b: B.Octets, -o: O.Oid, +e: {O.Oid.of_der(b) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}:
  od.can_r(A.Asn1.decode(AR.Asn1Rules.der(), b), b, o, {==}, e)

# Every Oid read is valid

def od.vt(ok: Bool, +arcs: List<&2, Nat>, -b: B.Octets, +e: {O.oid.to_der.pick(ok, arcs) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}) -> {ok == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, od.fob(O.OidBadArcs{}, b, e))
    case True{}:
      {==}

def od.valid_to_der(o: O.Oid, -b: B.Octets, +e: {O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}) -> {O.Oid.valid(o) == True{} : Bool}:
  match o:
    case O.Oid{+arcs}:
      od.vt(O.Oid.valid_arcs(arcs), arcs, b, e)

def od.valid_der(+b: B.Octets, +o: O.Oid, +e: {O.Oid.of_der(b) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid.valid(o) == True{} : Bool}:
  od.valid_to_der(o, b, od.can(b, o, e))

def od.go_ok(m: Maybe<&2, List<&2, Nat>>, -o: O.Oid, +e: {T.oid.of_text.go(m) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid.valid(o) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({O.Oid.valid(o) == True{} : Bool}, od.foo(O.OidBadText{}, o, e))
    case Some{+arcs}:
      od.mk_ok(arcs, o, e)

def od.valid_text(r: T.OidTextRules, +s: String, -o: O.Oid, +e: {T.Oid.of_text(r, s) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {O.Oid.valid(o) == True{} : Bool}:
  match r:
    case T.OidTextRules{+lz}:
      od.go_ok(T.oid.arcs(T.oid.split(s), lz), o, e)

# Text and DER composed

def od.text_rt(+r: T.OidTextRules, o: O.Oid, +hv: {O.Oid.valid(o) == True{} : Bool}) -> {T.Oid.of_text(r, T.Oid.to_text(o)) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}:
  match o:
    case O.Oid{+arcs}:
      OT.ot.text_rt(r, arcs, hv)

def od.der_text_der(+r: T.OidTextRules, +b: B.Octets, +o: O.Oid, +e: {O.Oid.of_der(b) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {Result.bind(&2, &2, O.OidError, O.Oid, B.Octets, T.Oid.of_text(r, T.Oid.to_text(o)), x => O.Oid.to_der(x)) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}:
  %Equal.sym(Result<&2, &2, O.OidError, O.Oid>, T.Oid.of_text(r, T.Oid.to_text(o)), Done{o}, od.text_rt(r, o, od.valid_der(b, o, e))) : {Result.bind(&2, &2, O.OidError, O.Oid, B.Octets, _, x => O.Oid.to_der(x)) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}
  od.can(b, o, e)

def od.tdt_q(q: Result<&2, &2, AE.Asn1Error, B.Octets>, +c: B.Octets, +arcs: List<&2, Nat>, +hc: {AO.Asn1.oid_content(arcs) == Done{c} : Result<&2, &2, AE.Asn1Error, B.Octets>}, +hv: {O.Oid.valid_arcs(arcs) == True{} : Bool}, +hq: {AEn.Asn1.encode(AN.Asn1Prim{AT.Asn1Tag.oid(), c}) == q : Result<&2, &2, AE.Asn1Error, B.Octets>}, +hd: {O.oid.done(q) == True{} : Bool}) -> {Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.oid.wrap(q), x => O.Oid.of_der(x)) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}:
  match q:
    case Fail{x}:
      Empty.absurd({Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.oid.wrap(Fail{x}), x => O.Oid.of_der(x)) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}, ON.on.ft(hd))
    case Done{+b}:
      od.rt_q(Done{b}, c, b, arcs, hc, hv, hq, {==})

def od.tdt_c(r: Result<&2, &2, AE.Asn1Error, B.Octets>, +arcs: List<&2, Nat>, +hr: {AO.Asn1.oid_content(arcs) == r : Result<&2, &2, AE.Asn1Error, B.Octets>}, +hv: {O.Oid.valid_arcs(arcs) == True{} : Bool}, +hd: {O.oid.done(O.oid.der.of(r)) == True{} : Bool}) -> {Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.oid.wrap(O.oid.der.of(r)), x => O.Oid.of_der(x)) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}:
  match r:
    case Fail{x}:
      Empty.absurd({Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.oid.wrap(Fail{x}), x => O.Oid.of_der(x)) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}, ON.on.ft(hd))
    case Done{+c}:
      od.tdt_q(AEn.Asn1.encode(AN.Asn1Prim{AT.Asn1Tag.oid(), c}), c, arcs, hr, hv, {==}, hd)

def od.tdt(o: O.Oid, +hv: {O.Oid.valid(o) == True{} : Bool}) -> {Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.Oid.to_der(o), x => O.Oid.of_der(x)) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}:
  match o:
    case O.Oid{+arcs}:
      +hd = ON.on.and_r(O.oid.text_ok(arcs), O.oid.done(O.oid.der(arcs)), hv)
      %Equal.sym(Bool, O.Oid.valid_arcs(arcs), True{}, hv) : {Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.oid.to_der.pick(_, arcs), x => O.Oid.of_der(x)) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}
      od.tdt_c(AO.Asn1.oid_content(arcs), arcs, {==}, hv, hd)

def od.text_der_text(+r: T.OidTextRules, +s: String, +o: O.Oid, +e: {T.Oid.of_text(r, s) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}) -> {Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.Oid.to_der(o), x => O.Oid.of_der(x)) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}:
  od.tdt(o, od.valid_text(r, s, o, e))
