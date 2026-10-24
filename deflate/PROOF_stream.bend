# Proofs of LAWS_stream.bend: the streaming inflater is the one-shot one.
#
# Both run the same driver (inflate.bend, drv.go) over the same bytes; the
# streaming one hands its output out after each feed and goes on with an
# empty output list. The resumption invariant: the driver's output list is
# only ever added to, so running it from an output list acc is running it
# from the empty list and putting acc after what it adds (st.go_lift; a
# full driver stays full). So handing the output out between feeds changes
# only where the bytes are joined (st.rel, st.comp). And the output never
# passes the maximum (st.go_inv: output plus room is the maximum), so the
# one-shot form's final check always passes (st.fin).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./error.bend as E
import ./window.bend as W
import ./inflate.bend as I
import ./zlib.bend as Z
import ./adler32.bend as A
import ./eq.bend as Q
import ./LAWS_stream.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP

# Logic and lists

def st.bt(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def st.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : st.bt(_)
  Unit{}

def st.app_assoc(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {B.append(B.append(a, b), c) == B.append(a, B.append(b, c)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %st.app_assoc(t, b, c) : {Con{h, B.append(B.append(t, b), c)} == Con{h, _} : List<&2, U32>}
      {==}

def st.app_nil(+a: List<&2, U32>) -> {B.append(a, Nil{}) == a : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %st.app_nil(t) : {Con{h, B.append(t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def st.mask_app(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.append(B.mask(a), B.mask(b)) == B.mask(B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %st.mask_app(t, b) : {Con{B.byte(h), B.append(B.mask(t), B.mask(b))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

# reversing onto acc is reversing, then acc
def st.onto(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.rev_onto(xs, acc) == B.append(B.rev(xs), acc) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, U32>, B.rev_onto(t, Con{h, acc}), B.append(B.rev(t), Con{h, acc}), st.onto(t, Con{h, acc})) : {_ == B.append(B.rev_onto(t, Con{h, Nil{}}), acc) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.rev_onto(t, Con{h, Nil{}}), B.append(B.rev(t), Con{h, Nil{}}), st.onto(t, Con{h, Nil{}})) : {B.append(B.rev(t), Con{h, acc}) == B.append(_, acc) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.append(B.append(B.rev(t), Con{h, Nil{}}), acc), B.append(B.rev(t), B.append(Con{h, Nil{}}, acc)), st.app_assoc(B.rev(t), Con{h, Nil{}}, acc)) : {B.append(B.rev(t), Con{h, acc}) == _ : List<&2, U32>}
      {==}

def st.onto_app(+x: List<&2, U32>, +y: List<&2, U32>, +acc: List<&2, U32>) -> {B.rev_onto(B.append(x, y), acc) == B.rev_onto(y, B.rev_onto(x, acc)) : List<&2, U32>}:
  match x:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      st.onto_app(t, y, Con{h, acc})

def st.rev_app(+x: List<&2, U32>, +y: List<&2, U32>) -> {B.rev(B.append(x, y)) == B.append(B.rev(y), B.rev(x)) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.rev(B.append(x, y)), B.rev_onto(y, B.rev(x)), B.append(B.rev(y), B.rev(x)), st.onto_app(x, y, Nil{}), st.onto(y, B.rev(x)))

def st.len_onto(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.len(B.rev_onto(xs, acc)) == Nat.add(B.len(xs), B.len(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, B.len(B.rev_onto(t, Con{h, acc})), Nat.add(B.len(t), B.len(Con{h, acc})), st.len_onto(t, Con{h, acc})) : {_ == 1n+Nat.add(B.len(t), B.len(acc)) : Nat}
      UL.nat_add_succ(B.len(t), B.len(acc))

# Octets from lists

def st.of_mask(+z: List<&2, U32>) -> {B.Octets.of_list(B.mask(z)) == B.Octets.of_list(z) : B.Octets}:
  %BL.octets_to_of(z) : {B.Octets.of_list(_) == B.Octets.of_list(z) : B.Octets}
  BL.octets_of_list_idempotent(z)

def st.masks(+u: List<&2, U32>, +v: List<&2, U32>) -> {B.append(B.Octets.to_list(B.Octets.of_list(u)), B.Octets.to_list(B.Octets.of_list(v))) == B.append(B.mask(u), B.mask(v)) : List<&2, U32>}:
  %BL.octets_to_of(u) : {B.append(B.Octets.to_list(B.Octets.of_list(u)), B.Octets.to_list(B.Octets.of_list(v))) == B.append(_, B.mask(v)) : List<&2, U32>}
  %BL.octets_to_of(v) : {B.append(B.Octets.to_list(B.Octets.of_list(u)), B.Octets.to_list(B.Octets.of_list(v))) == B.append(B.Octets.to_list(B.Octets.of_list(u)), _) : List<&2, U32>}
  {==}

def st.oct_app(+u: List<&2, U32>, +v: List<&2, U32>) -> {B.Octets.of_list(B.append(u, v)) == B.Octets.append(B.Octets.of_list(u), B.Octets.of_list(v)) : B.Octets}:
  +r = B.Octets.append(B.Octets.of_list(u), B.Octets.of_list(v))
  +e1 = Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(r)), r, BL.octets_of_to(r))
  +e2l = Equal.trans(List<&2, U32>, B.Octets.to_list(r), B.append(B.Octets.to_list(B.Octets.of_list(u)), B.Octets.to_list(B.Octets.of_list(v))), B.append(B.mask(u), B.mask(v)), BL.octets_append_list(B.Octets.of_list(u), B.Octets.of_list(v)), st.masks(u, v))
  +e2 = Equal.cong(List<&2, U32>, B.Octets, z => B.Octets.of_list(z), B.Octets.to_list(r), B.append(B.mask(u), B.mask(v)), e2l)
  +e3 = Equal.cong(List<&2, U32>, B.Octets, z => B.Octets.of_list(z), B.append(B.mask(u), B.mask(v)), B.mask(B.append(u, v)), st.mask_app(u, v))
  +e4 = st.of_mask(B.append(u, v))
  +all = Equal.trans(B.Octets, r, B.Octets.of_list(B.Octets.to_list(r)), B.Octets.of_list(B.append(u, v)), e1, Equal.trans(B.Octets, B.Octets.of_list(B.Octets.to_list(r)), B.Octets.of_list(B.append(B.mask(u), B.mask(v))), B.Octets.of_list(B.append(u, v)), e2, Equal.trans(B.Octets, B.Octets.of_list(B.append(B.mask(u), B.mask(v))), B.Octets.of_list(B.mask(B.append(u, v))), B.Octets.of_list(B.append(u, v)), e3, e4)))
  Equal.sym(B.Octets, r, B.Octets.of_list(B.append(u, v)), all)

# the output of two runs, joined: the earlier output a2 is reversed first
def st.out_join(+p: B.Octets, +a1: List<&2, U32>, +a2: List<&2, U32>) -> {B.Octets.append(p, B.Octets.of_list(B.rev(B.append(a1, a2)))) == B.Octets.append(B.Octets.append(p, B.Octets.of_list(B.rev(a2))), B.Octets.of_list(B.rev(a1))) : B.Octets}:
  %Equal.sym(List<&2, U32>, B.rev(B.append(a1, a2)), B.append(B.rev(a2), B.rev(a1)), st.rev_app(a1, a2)) : {B.Octets.append(p, B.Octets.of_list(_)) == B.Octets.append(B.Octets.append(p, B.Octets.of_list(B.rev(a2))), B.Octets.of_list(B.rev(a1))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.append(B.rev(a2), B.rev(a1))), B.Octets.append(B.Octets.of_list(B.rev(a2)), B.Octets.of_list(B.rev(a1))), st.oct_app(B.rev(a2), B.rev(a1))) : {B.Octets.append(p, _) == B.Octets.append(B.Octets.append(p, B.Octets.of_list(B.rev(a2))), B.Octets.of_list(B.rev(a1))) : B.Octets}
  Equal.sym(B.Octets, B.Octets.append(B.Octets.append(p, B.Octets.of_list(B.rev(a2))), B.Octets.of_list(B.rev(a1))), B.Octets.append(p, B.Octets.append(B.Octets.of_list(B.rev(a2)), B.Octets.of_list(B.rev(a1)))), BL.octets_append_assoc(p, B.Octets.of_list(B.rev(a2)), B.Octets.of_list(B.rev(a1))))

# The driver from an output list acc: the driver from the empty list, acc
# after what it adds

def st.applift(r: I.DflApp, +acc: List<&2, U32>) -> I.DflApp:
  match r:
    case I.DflAppOk{x, q}:
      I.DflAppOk{B.append(x, acc), q}
    case I.DflAppFull{}:
      I.DflAppFull{}

def st.alift(d: I.DflDrv, +acc: List<&2, U32>) -> I.DflDrv:
  match d:
    case I.DflRun{c, a, r}:
      I.DflRun{c, B.append(a, acc), r}
    case I.DflFull{}:
      I.DflFull{}

def st.con_lift(+b: U32, r: I.DflApp, +acc: List<&2, U32>) -> {I.drv.app.con(b, st.applift(r, acc)) == st.applift(I.drv.app.con(b, r), acc) : I.DflApp}:
  match r:
    case I.DflAppFull{}:
      {==}
    case I.DflAppOk{x, q}:
      match q:
        case 0n:
          {==}
        case 1n+qq:
          {==}

def st.app_acc(em: List<&2, U32>, +a: List<&2, U32>, +acc: List<&2, U32>, +r: Nat) -> {I.drv.app(em, B.append(a, acc), r) == st.applift(I.drv.app(em, a, r), acc) : I.DflApp}:
  match em:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(I.DflApp, I.drv.app(t, B.append(a, acc), r), st.applift(I.drv.app(t, a, r), acc), st.app_acc(t, a, acc, r)) : {I.drv.app.con(b, _) == st.applift(I.drv.app.con(b, I.drv.app(t, a, r)), acc) : I.DflApp}
      st.con_lift(b, I.drv.app(t, a, r), acc)

def st.put_lift(r: I.DflApp, +s: I.DflSt, +win: W.DflWin, +acc: List<&2, U32>) -> {I.drv.put(st.applift(r, acc), s, win) == st.alift(I.drv.put(r, s, win), acc) : I.DflDrv}:
  match r:
    case I.DflAppFull{}:
      {==}
    case I.DflAppOk{x, q}:
      {==}

def st.core_lift(c: I.DflCore, +a: List<&2, U32>, +acc: List<&2, U32>, +r: Nat) -> {I.drv.core(c, B.append(a, acc), r) == st.alift(I.drv.core(c, a, r), acc) : I.DflDrv}:
  match c:
    case I.DflCore{+s, +win, +em}:
      %Equal.sym(I.DflApp, I.drv.app(em, B.append(a, acc), r), st.applift(I.drv.app(em, a, r), acc), st.app_acc(em, a, acc, r)) : {I.drv.put(_, s, win) == st.alift(I.drv.put(I.drv.app(em, a, r), s, win), acc) : I.DflDrv}
      st.put_lift(I.drv.app(em, a, r), s, win, acc)

def st.byte_lift(d: I.DflDrv, +acc: List<&2, U32>, +h: U32) -> {I.drv.byte(st.alift(d, acc), h) == st.alift(I.drv.byte(d, h), acc) : I.DflDrv}:
  match d:
    case I.DflFull{}:
      {==}
    case I.DflRun{c, a, r}:
      st.core_lift(I.inf.byte(c, h), a, acc, r)

def st.go_lift(xs: List<&2, U32>, +d: I.DflDrv, +acc: List<&2, U32>) -> {I.drv.go(xs, st.alift(d, acc)) == st.alift(I.drv.go(xs, d), acc) : I.DflDrv}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(I.DflDrv, I.drv.byte(st.alift(d, acc), h), st.alift(I.drv.byte(d, h), acc), st.byte_lift(d, acc, h)) : {I.drv.go(t, _) == st.alift(I.drv.go(t, I.drv.byte(d, h)), acc) : I.DflDrv}
      st.go_lift(t, I.drv.byte(d, h), acc)

def st.full(xs: List<&2, U32>) -> {I.drv.go(xs, I.DflFull{}) == I.DflFull{} : I.DflDrv}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      st.full(t)

def st.go_append(xs: List<&2, U32>, +ys: List<&2, U32>, +d: I.DflDrv) -> {I.drv.go(B.append(xs, ys), d) == I.drv.go(ys, I.drv.go(xs, d)) : I.DflDrv}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      st.go_append(t, ys, I.drv.byte(d, h))

# The output never passes the maximum: output plus room is the maximum

def st.appinv(r: I.DflApp, +m: Nat) -> Type:
  match r:
    case I.DflAppFull{}:
      Unit
    case I.DflAppOk{x, q}:
      {Nat.add(B.len(x), q) == m : Nat}

def st.inv(d: I.DflDrv, +m: Nat) -> Type:
  match d:
    case I.DflFull{}:
      Unit
    case I.DflRun{c, a, r}:
      {Nat.add(B.len(a), r) == m : Nat}

def st.con_inv(+b: U32, r: I.DflApp, +m: Nat, i: st.appinv(r, m)) -> st.appinv(I.drv.app.con(b, r), m):
  match r:
    case I.DflAppFull{}:
      Unit{}
    case I.DflAppOk{+x, q}:
      match q:
        case 0n:
          Unit{}
        case 1n+ +qq:
          Equal.trans(Nat, 1n+Nat.add(B.len(x), qq), Nat.add(B.len(x), 1n+qq), m, Equal.sym(Nat, Nat.add(B.len(x), 1n+qq), 1n+Nat.add(B.len(x), qq), UL.nat_add_succ(B.len(x), qq)), i)

def st.app_inv(em: List<&2, U32>, +a: List<&2, U32>, +r: Nat, +m: Nat, +h: {Nat.add(B.len(a), r) == m : Nat}) -> st.appinv(I.drv.app(em, a, r), m):
  match em:
    case Nil{}:
      h
    case Con{+b, +t}:
      st.con_inv(b, I.drv.app(t, a, r), m, st.app_inv(t, a, r, m, h))

def st.put_inv(r: I.DflApp, +s: I.DflSt, +win: W.DflWin, +m: Nat, i: st.appinv(r, m)) -> st.inv(I.drv.put(r, s, win), m):
  match r:
    case I.DflAppFull{}:
      Unit{}
    case I.DflAppOk{x, q}:
      i

def st.core_inv(c: I.DflCore, +a: List<&2, U32>, +r: Nat, +m: Nat, +h: {Nat.add(B.len(a), r) == m : Nat}) -> st.inv(I.drv.core(c, a, r), m):
  match c:
    case I.DflCore{+s, +win, +em}:
      st.put_inv(I.drv.app(em, a, r), s, win, m, st.app_inv(em, a, r, m, h))

def st.byte_inv(d: I.DflDrv, +h: U32, +m: Nat, i: st.inv(d, m)) -> st.inv(I.drv.byte(d, h), m):
  match d:
    case I.DflFull{}:
      Unit{}
    case I.DflRun{c, a, r}:
      st.core_inv(I.inf.byte(c, h), a, r, m, i)

def st.go_inv(xs: List<&2, U32>, +d: I.DflDrv, +m: Nat, i: st.inv(d, m)) -> st.inv(I.drv.go(xs, d), m):
  match xs:
    case Nil{}:
      i
    case Con{+h, +t}:
      st.go_inv(t, I.drv.byte(d, h), m, st.byte_inv(d, h, m, i))

# The final answers agree

def st.fr(d: I.DflDrv) -> Result<&2, &2, E.DeflateError, I.DflInflated>:
  I.inf.finish.of(I.drv.result(d))

def st.guard_t(b: Bool, +out: B.Octets, +rest: List<&2, U32>, e: {b == True{} : Bool}) -> {I.inf.split.guard(b, out, rest) == Done{I.DflInflated{out, B.Octets.of_list(rest)}} : Result<&2, &2, E.DeflateError, I.DflInflated>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({I.inf.split.guard(False{}, out, rest) == Done{I.DflInflated{out, B.Octets.of_list(rest)}} : Result<&2, &2, E.DeflateError, I.DflInflated>}, st.ft(e))

def st.within(+a: List<&2, U32>, +r: Nat, +max: U32, +i: {Nat.add(B.len(a), r) == U32.to_nat(max) : Nat}) -> {Nat.is_le(B.Octets.len(B.Octets.of_list(B.rev(a))), U32.to_nat(max)) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(B.rev(a))), B.len(B.rev(a)), BL.octets_len_of_list(B.rev(a))) : {Nat.is_le(_, U32.to_nat(max)) == True{} : Bool}
  %Equal.sym(Nat, B.len(B.rev(a)), Nat.add(B.len(a), 0n), st.len_onto(a, Nil{})) : {Nat.is_le(_, U32.to_nat(max)) == True{} : Bool}
  %i : {Nat.is_le(Nat.add(B.len(a), 0n), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(B.len(a), 0n), B.len(a), UL.nat_add_zero(B.len(a))) : {Nat.is_le(_, Nat.add(B.len(a), r)) == True{} : Bool}
  UO.nat_le_add_r(B.len(a), r)

def st.fin_st(+s: I.DflSt, +a: List<&2, U32>, +max: U32, +ok: {Nat.is_le(B.Octets.len(B.Octets.of_list(B.rev(a))), U32.to_nat(max)) == True{} : Bool}) -> {Laws.stream_last(I.inf.finish.of(I.drv.end(s, a)), B.Octets.empty()) == I.inf.split.of(I.inf.out(I.drv.end(s, a)), max) : Result<&2, &2, E.DeflateError, I.DflInflated>}:
  match s:
    case I.DflEnd{+rest}:
      %Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), B.Octets.of_list(B.rev(a))), B.Octets.of_list(B.rev(a)), BL.octets_append_empty_l(B.Octets.of_list(B.rev(a)))) : {Done{I.DflInflated{_, B.Octets.of_list(B.rev(rest))}} == I.inf.split.of(I.inf.out(I.drv.end(I.DflEnd{rest}, a)), max) : Result<&2, &2, E.DeflateError, I.DflInflated>}
      Equal.sym(Result<&2, &2, E.DeflateError, I.DflInflated>, I.inf.split.guard(Nat.is_le(B.Octets.len(B.Octets.of_list(B.rev(a))), U32.to_nat(max)), B.Octets.of_list(B.rev(a)), B.rev(rest)), Done{I.DflInflated{B.Octets.of_list(B.rev(a)), B.Octets.of_list(B.rev(rest))}}, st.guard_t(Nat.is_le(B.Octets.len(B.Octets.of_list(B.rev(a))), U32.to_nat(max)), B.Octets.of_list(B.rev(a)), B.rev(rest), ok))
    case I.DflBad{e}:
      {==}
    case I.DflField{left, sh, v, k}:
      {==}
    case I.DflSym{node, k}:
      {==}
    case I.DflAlign{final}:
      {==}
    case I.DflStoredLen{n, v, final}:
      {==}
    case I.DflStored{left, final}:
      {==}

def st.fin(d: I.DflDrv, +max: U32, i: st.inv(d, U32.to_nat(max))) -> {Laws.stream_last(st.fr(d), B.Octets.empty()) == I.inf.split.of(I.inf.out(I.drv.result(d)), max) : Result<&2, &2, E.DeflateError, I.DflInflated>}:
  match d:
    case I.DflFull{}:
      {==}
    case I.DflRun{c, +a, +r}:
      match c:
        case I.DflCore{+s, win, em}:
          st.fin_st(s, a, max, st.within(a, r, max, i))

# Handing the output out between feeds

def st.last_st(+s: I.DflSt, +a1: List<&2, U32>, +a2: List<&2, U32>, +p: B.Octets) -> {Laws.stream_last(I.inf.finish.of(I.drv.end(s, B.append(a1, a2))), p) == Laws.stream_last(I.inf.finish.of(I.drv.end(s, a1)), B.Octets.append(p, B.Octets.of_list(B.rev(a2)))) : Result<&2, &2, E.DeflateError, I.DflInflated>}:
  match s:
    case I.DflEnd{+rest}:
      %st.out_join(p, a1, a2) : {Done{I.DflInflated{B.Octets.append(p, B.Octets.of_list(B.rev(B.append(a1, a2)))), B.Octets.of_list(B.rev(rest))}} == Done{I.DflInflated{_, B.Octets.of_list(B.rev(rest))}} : Result<&2, &2, E.DeflateError, I.DflInflated>}
      {==}
    case I.DflBad{e}:
      {==}
    case I.DflField{left, sh, v, k}:
      {==}
    case I.DflSym{node, k}:
      {==}
    case I.DflAlign{final}:
      {==}
    case I.DflStoredLen{n, v, final}:
      {==}
    case I.DflStored{left, final}:
      {==}

def st.last_lift(y: I.DflDrv, +a2: List<&2, U32>, +p: B.Octets) -> {Laws.stream_last(st.fr(st.alift(y, a2)), p) == Laws.stream_last(st.fr(y), B.Octets.append(p, B.Octets.of_list(B.rev(a2)))) : Result<&2, &2, E.DeflateError, I.DflInflated>}:
  match y:
    case I.DflFull{}:
      {==}
    case I.DflRun{c, +a1, r}:
      match c:
        case I.DflCore{+s, win, em}:
          st.last_st(s, a1, a2, p)

# what a flush keeps, and what it hands out
def st.kept(d: I.DflDrv) -> I.DflDrv:
  match d:
    case I.DflFull{}:
      I.DflFull{}
    case I.DflRun{c, a, r}:
      I.DflRun{c, Nil{}, r}

def st.out(d: I.DflDrv) -> B.Octets:
  match d:
    case I.DflFull{}:
      B.Octets.empty()
    case I.DflRun{c, a, r}:
      B.Octets.of_list(B.rev(a))

def st.flush_eta(d: I.DflDrv, +max: U32, +ignore: Bool) -> {I.inf.flush(d, max, ignore) == I.DflFed{I.Inflater{st.kept(d), max, ignore}, st.out(d)} : I.DflFed}:
  match d:
    case I.DflFull{}:
      {==}
    case I.DflRun{c, a, r}:
      {==}

def st.rel(+e: I.DflDrv, +l: List<&2, U32>, +p: B.Octets) -> {Laws.stream_last(st.fr(I.drv.go(l, st.kept(e))), B.Octets.append(p, st.out(e))) == Laws.stream_last(st.fr(I.drv.go(l, e)), p) : Result<&2, &2, E.DeflateError, I.DflInflated>}:
  match e:
    case I.DflFull{}:
      %Equal.sym(I.DflDrv, I.drv.go(l, I.DflFull{}), I.DflFull{}, st.full(l)) : {Laws.stream_last(st.fr(_), B.Octets.append(p, B.Octets.empty())) == Laws.stream_last(st.fr(_), p) : Result<&2, &2, E.DeflateError, I.DflInflated>}
      {==}
    case I.DflRun{+c, +a, +r}:
      %Equal.sym(I.DflDrv, I.drv.go(l, st.alift(I.DflRun{c, Nil{}, r}, a)), st.alift(I.drv.go(l, I.DflRun{c, Nil{}, r}), a), st.go_lift(l, I.DflRun{c, Nil{}, r}, a)) : {Laws.stream_last(st.fr(I.drv.go(l, I.DflRun{c, Nil{}, r})), B.Octets.append(p, B.Octets.of_list(B.rev(a)))) == Laws.stream_last(st.fr(_), p) : Result<&2, &2, E.DeflateError, I.DflInflated>}
      Equal.sym(Result<&2, &2, E.DeflateError, I.DflInflated>, Laws.stream_last(st.fr(st.alift(I.drv.go(l, I.DflRun{c, Nil{}, r}), a)), p), Laws.stream_last(st.fr(I.drv.go(l, I.DflRun{c, Nil{}, r})), B.Octets.append(p, B.Octets.of_list(B.rev(a)))), st.last_lift(I.drv.go(l, I.DflRun{c, Nil{}, r}), a, p))

def st.joinl(ps: List<&2, B.Octets>) -> List<&2, U32>:
  B.Octets.to_list(Laws.stream_join(ps))

def st.go_cons(+p: B.Octets, +t: List<&2, B.Octets>, +d: I.DflDrv) -> {I.drv.go(st.joinl(Con{p, t}), d) == I.drv.go(st.joinl(t), I.drv.go(B.Octets.to_list(p), d)) : I.DflDrv}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(p, Laws.stream_join(t))), B.append(B.Octets.to_list(p), B.Octets.to_list(Laws.stream_join(t))), BL.octets_append_list(p, Laws.stream_join(t))) : {I.drv.go(_, d) == I.drv.go(st.joinl(t), I.drv.go(B.Octets.to_list(p), d)) : I.DflDrv}
  st.go_append(B.Octets.to_list(p), st.joinl(t), d)

# the resumption invariant, piece by piece
def st.comp(ps: List<&2, B.Octets>, +d: I.DflDrv, +max: U32, +ignore: Bool, +o: B.Octets, +p: B.Octets) -> {Laws.inflate_pieces.go(ps, I.DflFed{I.Inflater{d, max, ignore}, o}, p) == Laws.stream_last(st.fr(I.drv.go(st.joinl(ps), d)), B.Octets.append(p, o)) : Result<&2, &2, E.DeflateError, I.DflInflated>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +e = I.drv.go(B.Octets.to_list(q), d)
      +po = B.Octets.append(p, o)
      %Equal.sym(I.DflFed, I.inf.flush(e, max, ignore), I.DflFed{I.Inflater{st.kept(e), max, ignore}, st.out(e)}, st.flush_eta(e, max, ignore)) : {Laws.inflate_pieces.go(t, _, po) == Laws.stream_last(st.fr(I.drv.go(st.joinl(Con{q, t}), d)), po) : Result<&2, &2, E.DeflateError, I.DflInflated>}
      %Equal.sym(I.DflDrv, I.drv.go(st.joinl(Con{q, t}), d), I.drv.go(st.joinl(t), e), st.go_cons(q, t, d)) : {Laws.inflate_pieces.go(t, I.DflFed{I.Inflater{st.kept(e), max, ignore}, st.out(e)}, po) == Laws.stream_last(st.fr(_), po) : Result<&2, &2, E.DeflateError, I.DflInflated>}
      Equal.trans(Result<&2, &2, E.DeflateError, I.DflInflated>, Laws.inflate_pieces.go(t, I.DflFed{I.Inflater{st.kept(e), max, ignore}, st.out(e)}, po), Laws.stream_last(st.fr(I.drv.go(st.joinl(t), st.kept(e))), B.Octets.append(po, st.out(e))), Laws.stream_last(st.fr(I.drv.go(st.joinl(t), e)), po), st.comp(t, st.kept(e), max, ignore, st.out(e), po), st.rel(e, st.joinl(t), po))

def Laws.inflate_streaming(opts, ps):
  match opts:
    case I.InflateOptions{+max, +dict, +ignore}:
      +d0 = I.drv.start(W.win.of(B.Octets.to_list(dict)), U32.to_nat(max))
      +d = I.drv.go(st.joinl(ps), d0)
      Equal.trans(Result<&2, &2, E.DeflateError, I.DflInflated>, Laws.inflate_pieces.go(ps, I.DflFed{I.Inflater{d0, max, ignore}, B.Octets.empty()}, B.Octets.empty()), Laws.stream_last(st.fr(d), B.Octets.empty()), I.inf.split.of(I.inf.out(I.drv.result(d)), max), st.comp(ps, d0, max, ignore, B.Octets.empty(), B.Octets.empty()), st.fin(d, max, st.go_inv(st.joinl(ps), d0, U32.to_nat(max), {==})))

# The zlib reader
#
# Its states: the header not yet complete (the bytes so far kept), the body
# (an inflater and the Adler-32 of the output so far), a refusal. Fed
# pieces, the body runs as the inflater above does, the Adler-32 kept piece
# by piece being the Adler-32 of the pieces joined (zs.adl); the header is
# read again from the start each time a piece arrives, and once it is
# complete (or refused other than for being short), more input changes
# nothing but the input it leaves for the body (zs.pre). The invariant
# (zs.ok): while the header is incomplete, the bytes kept are bytes (masked)
# and the header they hold is short.

# Bitwise equality of words and lists is equality (as in PROOF.bend)

def zs.and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def zs.and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, st.ft(h))

def zs.bit_sound(a: Bool, b: Bool, h: {Bool.not(Bool.xor(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, st.ft(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, st.ft(h))
    case False{} False{}:
      {==}

def zs.word_sound(+n: Nat, x: Word(n), y: Word(n), +h: {Q.eq.word(n, x, y) == True{} : Bool}) -> {x == y : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match x y:
        case WCon{+a, +s} WCon{+b, +t}:
          %zs.bit_sound(a, b, zs.and_l(Bool.not(Bool.xor(a, b)), Q.eq.word(p, s, t), h)) : {WCon{a, s} == WCon{_, t} : Word(1n+p)}
          %zs.word_sound(p, s, t, zs.and_r(Bool.not(Bool.xor(a, b)), Q.eq.word(p, s, t), h)) : {WCon{a, s} == WCon{a, _} : Word(1n+p)}
          {==}

def zs.u32_sound(a: U32, b: U32, h: {Q.eq.u32(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %zs.word_sound(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

def zs.word_refl(n: Nat, x: Word(n)) -> {Q.eq.word(n, x, x) == True{} : Bool}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n+ +p:
      match x:
        case WCon{a, s}:
          match a:
            case True{}:
              zs.word_refl(p, s)
            case False{}:
              zs.word_refl(p, s)

def zs.u32_refl(a: U32) -> {Q.eq.u32(a, a) == True{} : Bool}:
  match a:
    case U32{x}:
      zs.word_refl(32n, x)

def zs.list_live(xs: List<&2, U32>, ys: List<&2, U32>, +live: Bool, +h: {Q.eq.list.go(xs, ys, live) == True{} : Bool}) -> {live == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      h
    case Con{+a, s} Con{+b, t}:
      zs.and_l(live, Q.eq.u32(a, b), zs.list_live(s, t, Bool.and(live, Q.eq.u32(a, b)), h))
    case Nil{} Con{b, t}:
      Empty.absurd({live == True{} : Bool}, st.ft(h))
    case Con{a, s} Nil{}:
      Empty.absurd({live == True{} : Bool}, st.ft(h))

def zs.list_go_sound(xs: List<&2, U32>, ys: List<&2, U32>, +live: Bool, +h: {Q.eq.list.go(xs, ys, live) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Con{+a, +s} Con{+b, +t}:
      %zs.u32_sound(a, b, zs.and_r(live, Q.eq.u32(a, b), zs.list_live(s, t, Bool.and(live, Q.eq.u32(a, b)), h))) : {Con{a, s} == Con{_, t} : List<&2, U32>}
      %zs.list_go_sound(s, t, Bool.and(live, Q.eq.u32(a, b)), h) : {Con{a, s} == Con{a, _} : List<&2, U32>}
      {==}
    case Nil{} Con{b, t}:
      Empty.absurd({Nil{} == Con{b, t} : List<&2, U32>}, st.ft(h))
    case Con{a, s} Nil{}:
      Empty.absurd({Con{a, s} == Nil{} : List<&2, U32>}, st.ft(h))

def zs.list_sound(xs: List<&2, U32>, ys: List<&2, U32>, +h: {Q.eq.list(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  zs.list_go_sound(xs, ys, True{}, h)

def zs.list_go_refl(xs: List<&2, U32>, live: Bool) -> {Q.eq.list.go(xs, xs, live) == live : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +s}:
      match live:
        case True{}:
          %Equal.sym(Bool, Q.eq.u32(a, a), True{}, zs.u32_refl(a)) : {Q.eq.list.go(s, s, _) == True{} : Bool}
          zs.list_go_refl(s, True{})
        case False{}:
          zs.list_go_refl(s, False{})

def zs.list_refl(+xs: List<&2, U32>) -> {Q.eq.list(xs, xs) == True{} : Bool}:
  zs.list_go_refl(xs, True{})

# Adler-32 piece by piece

def zs.adl_app(xs: List<&2, U32>, +ys: List<&2, U32>, +a: A.Adler32) -> {A.adl.go(B.append(xs, ys), a) == A.adl.go(ys, A.adl.go(xs, a)) : A.Adler32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      zs.adl_app(t, ys, A.adl.step(a, h))

def zs.adl(+a: A.Adler32, +x: B.Octets, +y: B.Octets) -> {A.Adler32.update(A.Adler32.update(a, x), y) == A.Adler32.update(a, B.Octets.append(x, y)) : A.Adler32}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(x, y)), B.append(B.Octets.to_list(x), B.Octets.to_list(y)), BL.octets_append_list(x, y)) : {A.adl.go(B.Octets.to_list(y), A.adl.go(B.Octets.to_list(x), a)) == A.adl.go(_, a) : A.Adler32}
  Equal.sym(A.Adler32, A.adl.go(B.append(B.Octets.to_list(x), B.Octets.to_list(y)), a), A.adl.go(B.Octets.to_list(y), A.adl.go(B.Octets.to_list(x), a)), zs.adl_app(B.Octets.to_list(x), B.Octets.to_list(y), a))

# Octets

def zs.oj(+ay: List<&2, U32>, +ae: List<&2, U32>) -> {B.Octets.of_list(B.rev(B.append(ay, ae))) == B.Octets.append(B.Octets.of_list(B.rev(ae)), B.Octets.of_list(B.rev(ay))) : B.Octets}:
  %Equal.sym(List<&2, U32>, B.rev(B.append(ay, ae)), B.append(B.rev(ae), B.rev(ay)), st.rev_app(ay, ae)) : {B.Octets.of_list(_) == B.Octets.append(B.Octets.of_list(B.rev(ae)), B.Octets.of_list(B.rev(ay))) : B.Octets}
  st.oct_app(B.rev(ae), B.rev(ay))

def zs.last_empty(r: Result<&2, &2, E.DeflateError, B.Octets>) -> {Laws.zlib_last(r, B.Octets.empty()) == r : Result<&2, &2, E.DeflateError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+o}:
      %BL.octets_append_empty_l(o) : {Done{B.Octets.append(B.Octets.empty(), o)} == Done{_} : Result<&2, &2, E.DeflateError, B.Octets>}
      {==}

def zs.mask_tl(+q: B.Octets) -> {B.mask(B.Octets.to_list(q)) == B.Octets.to_list(q) : List<&2, U32>}:
  %BL.octets_to_of(B.Octets.to_list(q)) : {_ == B.Octets.to_list(q) : List<&2, U32>}
  %BL.octets_of_to(q) : {B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(q))) == B.Octets.to_list(_) : List<&2, U32>}
  {==}

# the bytes kept so far, then a piece: joined as the one-shot form joins them
def zs.allj(+buf: List<&2, U32>, +q: B.Octets, +t: List<&2, B.Octets>) -> {B.append(buf, st.joinl(Con{q, t})) == B.append(B.append.fast(buf, B.Octets.to_list(q)), st.joinl(t)) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(q, Laws.stream_join(t))), B.append(B.Octets.to_list(q), st.joinl(t)), BL.octets_append_list(q, Laws.stream_join(t))) : {B.append(buf, _) == B.append(B.append.fast(buf, B.Octets.to_list(q)), st.joinl(t)) : List<&2, U32>}
  %BL.append_fast(buf, B.Octets.to_list(q)) : {B.append(buf, B.append(B.Octets.to_list(q), st.joinl(t))) == B.append(_, st.joinl(t)) : List<&2, U32>}
  Equal.sym(List<&2, U32>, B.append(B.append(buf, B.Octets.to_list(q)), st.joinl(t)), B.append(buf, B.append(B.Octets.to_list(q), st.joinl(t))), st.app_assoc(buf, B.Octets.to_list(q), st.joinl(t)))

def zs.mask_all(+buf: List<&2, U32>, +q: B.Octets, +hm: {B.mask(buf) == buf : List<&2, U32>}) -> {B.mask(B.append.fast(buf, B.Octets.to_list(q))) == B.append.fast(buf, B.Octets.to_list(q)) : List<&2, U32>}:
  %BL.append_fast(buf, B.Octets.to_list(q)) : {B.mask(_) == _ : List<&2, U32>}
  %st.mask_app(buf, B.Octets.to_list(q)) : {_ == B.append(buf, B.Octets.to_list(q)) : List<&2, U32>}
  %hm : {B.append(B.mask(buf), B.mask(B.Octets.to_list(q))) == B.append(_, B.Octets.to_list(q)) : List<&2, U32>}
  %zs.mask_tl(q) : {B.append(B.mask(buf), B.mask(B.Octets.to_list(q))) == B.append(B.mask(buf), _) : List<&2, U32>}
  {==}

# The trailer check does not look at the output it answers

def zs.rest_shift(none: Bool, +x: B.Octets, +y: B.Octets, +q: B.Octets) -> {Laws.zlib_last(Z.zl.check.rest(none, B.Octets.append(x, y)), q) == Laws.zlib_last(Z.zl.check.rest(none, y), B.Octets.append(q, x)) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match none:
    case True{}:
      %BL.octets_append_assoc(q, x, y) : {Done{_} == Done{B.Octets.append(B.Octets.append(q, x), y)} : Result<&2, &2, E.DeflateError, B.Octets>}
      {==}
    case False{}:
      {==}

def zs.check_shift(ok: Bool, +x: B.Octets, +y: B.Octets, +rest: B.Octets, ign: Bool, +q: B.Octets) -> {Laws.zlib_last(Z.zl.check(ok, B.Octets.append(x, y), rest, ign), q) == Laws.zlib_last(Z.zl.check(ok, y, rest, ign), B.Octets.append(q, x)) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match ok:
    case True{}:
      match ign:
        case True{}:
          %BL.octets_append_assoc(q, x, y) : {Done{_} == Done{B.Octets.append(B.Octets.append(q, x), y)} : Result<&2, &2, E.DeflateError, B.Octets>}
          {==}
        case False{}:
          zs.rest_shift(Z.zl.none(Nat.sub(B.Octets.len(rest), 4n)), x, y, q)
    case False{}:
      {==}

def zs.trail_shift(m: Maybe<&2, U32>, +ad: U32, +x: B.Octets, +y: B.Octets, +rest: B.Octets, +ign: Bool, +q: B.Octets) -> {Laws.zlib_last(Z.zl.trail(m, ad, B.Octets.append(x, y), rest, ign), q) == Laws.zlib_last(Z.zl.trail(m, ad, y, rest, ign), B.Octets.append(q, x)) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      zs.check_shift(Q.eq.u32(v, ad), x, y, rest, ign, q)

# The body: handing the output out between feeds

def zs.end_st(+s: I.DflSt, +ay: List<&2, U32>, +ae: List<&2, U32>, +a: A.Adler32, +ign: Bool, +q: B.Octets) -> {Laws.zlib_last(Z.zl.in.end(I.inf.finish.of(I.drv.end(s, ay)), A.Adler32.update(a, B.Octets.of_list(B.rev(ae))), ign), B.Octets.append(q, B.Octets.of_list(B.rev(ae)))) == Laws.zlib_last(Z.zl.in.end(I.inf.finish.of(I.drv.end(s, B.append(ay, ae))), a, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match s:
    case I.DflEnd{+rest}:
      +oe = B.Octets.of_list(B.rev(ae))
      +oy = B.Octets.of_list(B.rev(ay))
      +rr = B.Octets.of_list(B.rev(rest))
      +m = B.Octets.be32_at(rr, 0n)
      +ad = A.Adler32.finish(A.Adler32.update(A.Adler32.update(a, oe), oy))
      %Equal.sym(B.Octets, B.Octets.of_list(B.rev(B.append(ay, ae))), B.Octets.append(oe, oy), zs.oj(ay, ae)) : {Laws.zlib_last(Z.zl.trail(m, ad, oy, rr, ign), B.Octets.append(q, oe)) == Laws.zlib_last(Z.zl.trail(m, A.Adler32.finish(A.Adler32.update(a, _)), _, rr, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}
      %zs.adl(a, oe, oy) : {Laws.zlib_last(Z.zl.trail(m, ad, oy, rr, ign), B.Octets.append(q, oe)) == Laws.zlib_last(Z.zl.trail(m, A.Adler32.finish(_), B.Octets.append(oe, oy), rr, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}
      Equal.sym(Result<&2, &2, E.DeflateError, B.Octets>, Laws.zlib_last(Z.zl.trail(m, ad, B.Octets.append(oe, oy), rr, ign), q), Laws.zlib_last(Z.zl.trail(m, ad, oy, rr, ign), B.Octets.append(q, oe)), zs.trail_shift(m, ad, oe, oy, rr, ign, q))
    case I.DflBad{e}:
      {==}
    case I.DflField{left, sh, v, k}:
      {==}
    case I.DflSym{node, k}:
      {==}
    case I.DflAlign{final}:
      {==}
    case I.DflStoredLen{n, v, final}:
      {==}
    case I.DflStored{left, final}:
      {==}

def zs.end_lift(y: I.DflDrv, +ae: List<&2, U32>, +a: A.Adler32, +ign: Bool, +q: B.Octets) -> {Laws.zlib_last(Z.zl.in.end(st.fr(y), A.Adler32.update(a, B.Octets.of_list(B.rev(ae))), ign), B.Octets.append(q, B.Octets.of_list(B.rev(ae)))) == Laws.zlib_last(Z.zl.in.end(st.fr(st.alift(y, ae)), a, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match y:
    case I.DflFull{}:
      {==}
    case I.DflRun{c, +ay, r}:
      match c:
        case I.DflCore{+s, w, em}:
          zs.end_st(s, ay, ae, a, ign, q)

def zs.rel(+e: I.DflDrv, +l: List<&2, U32>, +a: A.Adler32, +ign: Bool, +q: B.Octets) -> {Laws.zlib_last(Z.zl.in.end(st.fr(I.drv.go(l, st.kept(e))), A.Adler32.update(a, st.out(e)), ign), B.Octets.append(q, st.out(e))) == Laws.zlib_last(Z.zl.in.end(st.fr(I.drv.go(l, e)), a, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match e:
    case I.DflFull{}:
      %Equal.sym(I.DflDrv, I.drv.go(l, I.DflFull{}), I.DflFull{}, st.full(l)) : {Laws.zlib_last(Z.zl.in.end(st.fr(_), A.Adler32.update(a, B.Octets.empty()), ign), B.Octets.append(q, B.Octets.empty())) == Laws.zlib_last(Z.zl.in.end(st.fr(_), a, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}
      {==}
    case I.DflRun{+c, +ae, +r}:
      %Equal.sym(I.DflDrv, I.drv.go(l, st.alift(I.DflRun{c, Nil{}, r}, ae)), st.alift(I.drv.go(l, I.DflRun{c, Nil{}, r}), ae), st.go_lift(l, I.DflRun{c, Nil{}, r}, ae)) : {Laws.zlib_last(Z.zl.in.end(st.fr(I.drv.go(l, I.DflRun{c, Nil{}, r})), A.Adler32.update(a, B.Octets.of_list(B.rev(ae))), ign), B.Octets.append(q, B.Octets.of_list(B.rev(ae)))) == Laws.zlib_last(Z.zl.in.end(st.fr(_), a, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}
      zs.end_lift(I.drv.go(l, I.DflRun{c, Nil{}, r}), ae, a, ign, q)

# The final answers agree

def zs.guard_t(b: Bool, +out: B.Octets, +rest: B.Octets, +ign: Bool, e: {b == True{} : Bool}) -> {Z.zl.guard(b, out, rest, ign) == Z.zl.trailer(B.Octets.be32_at(rest, 0n), out, rest, ign) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Z.zl.guard(False{}, out, rest, ign) == Z.zl.trailer(B.Octets.be32_at(rest, 0n), out, rest, ign) : Result<&2, &2, E.DeflateError, B.Octets>}, st.ft(e))

def zs.fin_st(+s: I.DflSt, +a: List<&2, U32>, +max: U32, +ign: Bool, +q: B.Octets, +ok: {Nat.is_le(B.Octets.len(B.Octets.of_list(B.rev(a))), U32.to_nat(max)) == True{} : Bool}) -> {Laws.zlib_last(Z.zl.in.end(I.inf.finish.of(I.drv.end(s, a)), A.Adler32.start(), ign), q) == Laws.zlib_last(Z.zl.body(I.inf.out(I.drv.end(s, a)), max, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match s:
    case I.DflEnd{+rest}:
      +o = B.Octets.of_list(B.rev(a))
      +rr = B.Octets.of_list(B.rev(rest))
      %Equal.sym(Result<&2, &2, E.DeflateError, B.Octets>, Z.zl.guard(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o, rr, ign), Z.zl.trailer(B.Octets.be32_at(rr, 0n), o, rr, ign), zs.guard_t(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o, rr, ign, ok)) : {Laws.zlib_last(Z.zl.trail(B.Octets.be32_at(rr, 0n), A.Adler32.finish(A.Adler32.update(A.Adler32.start(), o)), o, rr, ign), q) == Laws.zlib_last(_, q) : Result<&2, &2, E.DeflateError, B.Octets>}
      {==}
    case I.DflBad{e}:
      {==}
    case I.DflField{left, sh, v, k}:
      {==}
    case I.DflSym{node, k}:
      {==}
    case I.DflAlign{final}:
      {==}
    case I.DflStoredLen{n, v, final}:
      {==}
    case I.DflStored{left, final}:
      {==}

def zs.fin(y: I.DflDrv, +max: U32, +ign: Bool, +q: B.Octets, i: st.inv(y, U32.to_nat(max))) -> {Laws.zlib_last(Z.zl.in.end(st.fr(y), A.Adler32.start(), ign), q) == Laws.zlib_last(Z.zl.body(I.inf.out(I.drv.result(y)), max, ign), q) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match y:
    case I.DflFull{}:
      {==}
    case I.DflRun{c, +a, +r}:
      match c:
        case I.DflCore{+s, w, em}:
          zs.fin_st(s, a, max, ign, q, st.within(a, r, max, i))

# The header: with more input after it

def zs.isT(e: E.DeflateError) -> Bool:
  match e:
    case E.DeflateTruncated{}:
      True{}
    case _:
      False{}

def zs.isTr(r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>) -> Bool:
  match r:
    case Fail{e}:
      zs.isT(e)
    case Done{h}:
      False{}

def zs.ntr(r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>) -> Type:
  match r:
    case Fail{e}:
      st.bt(Bool.not(zs.isT(e)))
    case Done{h}:
      Unit

def zs.hlift(r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>, +ys: List<&2, U32>) -> Result<&2, &2, E.DeflateError, Z.DflZlibHead>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Z.DflZlibHead{w, rest}}:
      Done{Z.DflZlibHead{w, B.append(rest, ys)}}

def zs.isT_true(e: E.DeflateError, h: {zs.isT(e) == True{} : Bool}) -> {e == E.DeflateTruncated{} : E.DeflateError}:
  match e:
    case E.DeflateTruncated{}:
      {==}
    case E.DeflateBadBlockType{}:
      Empty.absurd({E.DeflateBadBlockType{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateBadStoredLength{}:
      Empty.absurd({E.DeflateBadStoredLength{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateTooManyCodes{}:
      Empty.absurd({E.DeflateTooManyCodes{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateBadCodeLengthCode{}:
      Empty.absurd({E.DeflateBadCodeLengthCode{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateBadRepeat{}:
      Empty.absurd({E.DeflateBadRepeat{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateBadLitLenCode{}:
      Empty.absurd({E.DeflateBadLitLenCode{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateBadDistCode{}:
      Empty.absurd({E.DeflateBadDistCode{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateNoEndCode{}:
      Empty.absurd({E.DeflateNoEndCode{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateBadCodeLengthSymbol{}:
      Empty.absurd({E.DeflateBadCodeLengthSymbol{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateBadLitLenSymbol{}:
      Empty.absurd({E.DeflateBadLitLenSymbol{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateBadDistSymbol{}:
      Empty.absurd({E.DeflateBadDistSymbol{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateDistanceTooFar{}:
      Empty.absurd({E.DeflateDistanceTooFar{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateOutputTooLarge{}:
      Empty.absurd({E.DeflateOutputTooLarge{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateTrailingData{}:
      Empty.absurd({E.DeflateTrailingData{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateZlibBadHeader{}:
      Empty.absurd({E.DeflateZlibBadHeader{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateZlibBadMethod{}:
      Empty.absurd({E.DeflateZlibBadMethod{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateZlibBadWindow{}:
      Empty.absurd({E.DeflateZlibBadWindow{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateZlibNeedDict{}:
      Empty.absurd({E.DeflateZlibNeedDict{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateZlibBadDictId{}:
      Empty.absurd({E.DeflateZlibBadDictId{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateZlibBadChecksum{}:
      Empty.absurd({E.DeflateZlibBadChecksum{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateGzipBadMagic{}:
      Empty.absurd({E.DeflateGzipBadMagic{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateGzipBadMethod{}:
      Empty.absurd({E.DeflateGzipBadMethod{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateGzipReservedFlags{}:
      Empty.absurd({E.DeflateGzipReservedFlags{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateGzipBadHeaderCrc{}:
      Empty.absurd({E.DeflateGzipBadHeaderCrc{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateGzipBadCrc{}:
      Empty.absurd({E.DeflateGzipBadCrc{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))
    case E.DeflateGzipBadSize{}:
      Empty.absurd({E.DeflateGzipBadSize{} == E.DeflateTruncated{} : E.DeflateError}, st.ft(h))

def zs.wait_bad(e: E.DeflateError, +all: List<&2, U32>, +opts: I.InflateOptions, h: {zs.isT(e) == False{} : Bool}) -> {Z.zl.in.wait(e, all, opts) == Z.DflZlibFed{Z.ZlibInBad{e}, B.Octets.empty()} : Z.DflZlibFed}:
  match e:
    case E.DeflateTruncated{}:
      Empty.absurd({Z.zl.in.wait(E.DeflateTruncated{}, all, opts) == Z.DflZlibFed{Z.ZlibInBad{E.DeflateTruncated{}}, B.Octets.empty()} : Z.DflZlibFed}, st.ft(Equal.sym(Bool, True{}, False{}, h)))
    case E.DeflateBadBlockType{}:
      {==}
    case E.DeflateBadStoredLength{}:
      {==}
    case E.DeflateTooManyCodes{}:
      {==}
    case E.DeflateBadCodeLengthCode{}:
      {==}
    case E.DeflateBadRepeat{}:
      {==}
    case E.DeflateBadLitLenCode{}:
      {==}
    case E.DeflateBadDistCode{}:
      {==}
    case E.DeflateNoEndCode{}:
      {==}
    case E.DeflateBadCodeLengthSymbol{}:
      {==}
    case E.DeflateBadLitLenSymbol{}:
      {==}
    case E.DeflateBadDistSymbol{}:
      {==}
    case E.DeflateDistanceTooFar{}:
      {==}
    case E.DeflateOutputTooLarge{}:
      {==}
    case E.DeflateTrailingData{}:
      {==}
    case E.DeflateZlibBadHeader{}:
      {==}
    case E.DeflateZlibBadMethod{}:
      {==}
    case E.DeflateZlibBadWindow{}:
      {==}
    case E.DeflateZlibNeedDict{}:
      {==}
    case E.DeflateZlibBadDictId{}:
      {==}
    case E.DeflateZlibBadChecksum{}:
      {==}
    case E.DeflateGzipBadMagic{}:
      {==}
    case E.DeflateGzipBadMethod{}:
      {==}
    case E.DeflateGzipReservedFlags{}:
      {==}
    case E.DeflateGzipBadHeaderCrc{}:
      {==}
    case E.DeflateGzipBadCrc{}:
      {==}
    case E.DeflateGzipBadSize{}:
      {==}

def zs.tr_sound(r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>, h: {zs.isTr(r) == True{} : Bool}) -> {r == Fail{E.DeflateTruncated{}} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match r:
    case Fail{+e}:
      %zs.isT_true(e, h) : {Fail{e} == Fail{_} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}
      {==}
    case Done{x}:
      Empty.absurd({Done{x} == Fail{E.DeflateTruncated{}} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}, st.ft(h))

def zs.pmatch(ok: Bool, +dict: B.Octets, +r: List<&2, U32>, +ys: List<&2, U32>) -> {Z.zl.dict.match(ok, dict, B.append(r, ys)) == zs.hlift(Z.zl.dict.match(ok, dict, r), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def zs.phave(none: Bool, +id: U32, +dict: B.Octets, +r: List<&2, U32>, +ys: List<&2, U32>) -> {Z.zl.dict.have(none, id, dict, B.append(r, ys)) == zs.hlift(Z.zl.dict.have(none, id, dict, r), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match none:
    case True{}:
      {==}
    case False{}:
      zs.pmatch(Q.eq.u32(id, A.adler32(dict)), dict, r, ys)

def zs.pd4(m: Maybe<&2, U32>, +dict: B.Octets, +a: U32, +b: U32, +c: U32, +d: U32, +r: List<&2, U32>, +ys: List<&2, U32>) -> {Z.zl.dict(m, dict, Con{a, Con{b, Con{c, Con{d, B.append(r, ys)}}}}) == zs.hlift(Z.zl.dict(m, dict, Con{a, Con{b, Con{c, Con{d, r}}}}), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      zs.phave(Z.zl.none(B.Octets.len(dict)), v, dict, r, ys)

def zs.pdict(rest: List<&2, U32>, +dict: B.Octets, +ys: List<&2, U32>, h: zs.ntr(Z.zl.dict(B.be32_at(rest, 0n), dict, rest))) -> {Z.zl.dict(B.be32_at(B.append(rest, ys), 0n), dict, B.append(rest, ys)) == zs.hlift(Z.zl.dict(B.be32_at(rest, 0n), dict, rest), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match rest:
    case Nil{}:
      match h:
    case Con{+a, t1}:
      match t1:
        case Nil{}:
          match h:
        case Con{+b, t2}:
          match t2:
            case Nil{}:
              match h:
            case Con{+c, t3}:
              match t3:
                case Nil{}:
                  match h:
                case Con{+d, +r}:
                  zs.pd4(B.be32_at(Con{a, Con{b, Con{c, Con{d, r}}}}, 0n), dict, a, b, c, d, r, ys)

def zs.pfd(fd: Bool, +dict: B.Octets, +rest: List<&2, U32>, +ys: List<&2, U32>, h: zs.ntr(Z.zl.fdict(fd, dict, rest))) -> {Z.zl.fdict(fd, dict, B.append(rest, ys)) == zs.hlift(Z.zl.fdict(fd, dict, rest), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match fd:
    case True{}:
      zs.pdict(rest, dict, ys, h)
    case False{}:
      {==}

def zs.pci(ok: Bool, +flg: U32, +dict: B.Octets, +rest: List<&2, U32>, +ys: List<&2, U32>, h: zs.ntr(Z.zl.cinfo(ok, flg, dict, rest))) -> {Z.zl.cinfo(ok, flg, dict, B.append(rest, ys)) == zs.hlift(Z.zl.cinfo(ok, flg, dict, rest), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match ok:
    case True{}:
      zs.pfd(U32.is_eq(U32.and(flg, 32), 32), dict, rest, ys, h)
    case False{}:
      {==}

def zs.pcm(ok: Bool, +cmf: U32, +flg: U32, +dict: B.Octets, +rest: List<&2, U32>, +ys: List<&2, U32>, h: zs.ntr(Z.zl.cm(ok, cmf, flg, dict, rest))) -> {Z.zl.cm(ok, cmf, flg, dict, B.append(rest, ys)) == zs.hlift(Z.zl.cm(ok, cmf, flg, dict, rest), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match ok:
    case True{}:
      zs.pci(U32.is_le(U32.shrn(cmf, 4n), 7), flg, dict, rest, ys, h)
    case False{}:
      {==}

def zs.pfc(ok: Bool, +cmf: U32, +flg: U32, +dict: B.Octets, +rest: List<&2, U32>, +ys: List<&2, U32>, h: zs.ntr(Z.zl.fcheck(ok, cmf, flg, dict, rest))) -> {Z.zl.fcheck(ok, cmf, flg, dict, B.append(rest, ys)) == zs.hlift(Z.zl.fcheck(ok, cmf, flg, dict, rest), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match ok:
    case True{}:
      zs.pcm(U32.is_eq(U32.and(cmf, 15), 8), cmf, flg, dict, rest, ys, h)
    case False{}:
      {==}

# a header parsed, or refused other than for being short, stays so
def zs.pre(xs: List<&2, U32>, +ys: List<&2, U32>, +dict: B.Octets, h: zs.ntr(Z.zl.head(xs, dict))) -> {Z.zl.head(B.append(xs, ys), dict) == zs.hlift(Z.zl.head(xs, dict), ys) : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}:
  match xs:
    case Nil{}:
      match h:
    case Con{+cmf, t}:
      match t:
        case Nil{}:
          match h:
        case Con{+flg, +rest}:
          zs.pfc(U32.is_eq(U32.mod(U32.add(U32.shln(cmf, 8n), flg), 31), 0), cmf, flg, dict, rest, ys, h)

# the input a parsed header leaves is bytes, if its input was
def zs.zm(r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{Z.DflZlibHead{w, rest}}:
      {B.mask(rest) == rest : List<&2, U32>}

def zs.mmatch(ok: Bool, +dict: B.Octets, +r: List<&2, U32>, +hm: {B.mask(r) == r : List<&2, U32>}) -> zs.zm(Z.zl.dict.match(ok, dict, r)):
  match ok:
    case True{}:
      hm
    case False{}:
      Unit{}

def zs.mhave(none: Bool, +id: U32, +dict: B.Octets, +r: List<&2, U32>, +hm: {B.mask(r) == r : List<&2, U32>}) -> zs.zm(Z.zl.dict.have(none, id, dict, r)):
  match none:
    case True{}:
      Unit{}
    case False{}:
      zs.mmatch(Q.eq.u32(id, A.adler32(dict)), dict, r, hm)

def zs.md4(m: Maybe<&2, U32>, +dict: B.Octets, +a: U32, +b: U32, +c: U32, +d: U32, +r: List<&2, U32>, +hm: {B.mask(Con{a, Con{b, Con{c, Con{d, r}}}}) == Con{a, Con{b, Con{c, Con{d, r}}}} : List<&2, U32>}) -> zs.zm(Z.zl.dict(m, dict, Con{a, Con{b, Con{c, Con{d, r}}}})):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      zs.mhave(Z.zl.none(B.Octets.len(dict)), v, dict, r, Equal.cong(List<&2, U32>, List<&2, U32>, x => B.drop(4n, x), B.mask(Con{a, Con{b, Con{c, Con{d, r}}}}), Con{a, Con{b, Con{c, Con{d, r}}}}, hm))

def zs.mdict(rest: List<&2, U32>, +dict: B.Octets, +hm: {B.mask(rest) == rest : List<&2, U32>}) -> zs.zm(Z.zl.dict(B.be32_at(rest, 0n), dict, rest)):
  match rest:
    case Nil{}:
      Unit{}
    case Con{+a, t1}:
      match t1:
        case Nil{}:
          Unit{}
        case Con{+b, t2}:
          match t2:
            case Nil{}:
              Unit{}
            case Con{+c, t3}:
              match t3:
                case Nil{}:
                  Unit{}
                case Con{+d, +r}:
                  zs.md4(B.be32_at(Con{a, Con{b, Con{c, Con{d, r}}}}, 0n), dict, a, b, c, d, r, hm)

def zs.mfd(fd: Bool, +dict: B.Octets, +rest: List<&2, U32>, +hm: {B.mask(rest) == rest : List<&2, U32>}) -> zs.zm(Z.zl.fdict(fd, dict, rest)):
  match fd:
    case True{}:
      zs.mdict(rest, dict, hm)
    case False{}:
      hm

def zs.mci(ok: Bool, +flg: U32, +dict: B.Octets, +rest: List<&2, U32>, +hm: {B.mask(rest) == rest : List<&2, U32>}) -> zs.zm(Z.zl.cinfo(ok, flg, dict, rest)):
  match ok:
    case True{}:
      zs.mfd(U32.is_eq(U32.and(flg, 32), 32), dict, rest, hm)
    case False{}:
      Unit{}

def zs.mcm(ok: Bool, +cmf: U32, +flg: U32, +dict: B.Octets, +rest: List<&2, U32>, +hm: {B.mask(rest) == rest : List<&2, U32>}) -> zs.zm(Z.zl.cm(ok, cmf, flg, dict, rest)):
  match ok:
    case True{}:
      zs.mci(U32.is_le(U32.shrn(cmf, 4n), 7), flg, dict, rest, hm)
    case False{}:
      Unit{}

def zs.mfc(ok: Bool, +cmf: U32, +flg: U32, +dict: B.Octets, +rest: List<&2, U32>, +hm: {B.mask(rest) == rest : List<&2, U32>}) -> zs.zm(Z.zl.fcheck(ok, cmf, flg, dict, rest)):
  match ok:
    case True{}:
      zs.mcm(U32.is_eq(U32.and(cmf, 15), 8), cmf, flg, dict, rest, hm)
    case False{}:
      Unit{}

def zs.hmask(xs: List<&2, U32>, +dict: B.Octets, +hm: {B.mask(xs) == xs : List<&2, U32>}) -> zs.zm(Z.zl.head(xs, dict)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+cmf, t}:
      match t:
        case Nil{}:
          Unit{}
        case Con{+flg, +rest}:
          zs.mfc(U32.is_eq(U32.mod(U32.add(U32.shln(cmf, 8n), flg), 31), 0), cmf, flg, dict, rest, Equal.cong(List<&2, U32>, List<&2, U32>, x => B.drop(2n, x), B.mask(Con{cmf, Con{flg, rest}}), Con{cmf, Con{flg, rest}}, hm))

def zs.zm_rr(+r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>, +w: W.DflWin, +rr: List<&2, U32>, +er: {r == Done{Z.DflZlibHead{w, rr}} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}, i: zs.zm(r)) -> {B.mask(rr) == rr : List<&2, U32>}:
  %er : zs.zm(_)
  i

# The reader's states, what each leads to, and the invariant

def zs.fz(f: Z.DflZlibFed) -> Z.ZlibInflater:
  match f:
    case Z.DflZlibFed{z, o}:
      z

def zs.fo(f: Z.DflZlibFed) -> B.Octets:
  match f:
    case Z.DflZlibFed{z, o}:
      o

def zs.eta(f: Z.DflZlibFed) -> {f == Z.DflZlibFed{zs.fz(f), zs.fo(f)} : Z.DflZlibFed}:
  match f:
    case Z.DflZlibFed{z, o}:
      {==}

# what the reader in state z, having handed out p then o, answers once fed
# ps and finished
def zs.res(z: Z.ZlibInflater, +ps: List<&2, B.Octets>, +p: B.Octets, +o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match z:
    case Z.ZlibInHead{buf, opts}:
      Laws.zlib_last(Z.zl.decode(B.append(buf, st.joinl(ps)), opts), B.Octets.append(p, o))
    case Z.ZlibInBody{i, a}:
      match i:
        case I.Inflater{d, max, ign}:
          Laws.zlib_last(Z.zl.in.end(st.fr(I.drv.go(st.joinl(ps), d)), a, ign), B.Octets.append(p, o))
    case Z.ZlibInBad{e}:
      Fail{e}

def zs.ok(z: Z.ZlibInflater) -> Bool:
  match z:
    case Z.ZlibInHead{+buf, opts}:
      match opts:
        case I.InflateOptions{max, +dict, ign}:
          Bool.and(Q.eq.list(B.mask(buf), buf), zs.isTr(Z.zl.head(buf, dict)))
    case Z.ZlibInBody{i, a}:
      True{}
    case Z.ZlibInBad{e}:
      True{}

def zs.nil(z: Z.ZlibInflater, +p: B.Octets, +o: B.Octets, +inv: {zs.ok(z) == True{} : Bool}) -> {Laws.zlib_pieces.go(Nil{}, Z.DflZlibFed{z, o}, p) == zs.res(z, Nil{}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match z:
    case Z.ZlibInHead{+buf, opts}:
      match opts:
        case I.InflateOptions{+max, +dict, +ign}:
          +ht = zs.tr_sound(Z.zl.head(buf, dict), zs.and_r(Q.eq.list(B.mask(buf), buf), zs.isTr(Z.zl.head(buf, dict)), inv))
          %Equal.sym(List<&2, U32>, B.append(buf, Nil{}), buf, st.app_nil(buf)) : {Laws.zlib_last(Z.zl.in.after(Z.zl.head(buf, dict)), B.Octets.append(p, o)) == Laws.zlib_last(Z.zl.after(Z.zl.head(_, dict), max, ign), B.Octets.append(p, o)) : Result<&2, &2, E.DeflateError, B.Octets>}
          %Equal.sym(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, Z.zl.head(buf, dict), Fail{E.DeflateTruncated{}}, ht) : {Laws.zlib_last(Z.zl.in.after(_), B.Octets.append(p, o)) == Laws.zlib_last(Z.zl.after(_, max, ign), B.Octets.append(p, o)) : Result<&2, &2, E.DeflateError, B.Octets>}
          {==}
    case Z.ZlibInBody{i, a}:
      match i:
        case I.Inflater{d, max, ign}:
          {==}
    case Z.ZlibInBad{e}:
      {==}

def zs.ntr_done(+r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>, +w: W.DflWin, +rr: List<&2, U32>, +er: {r == Done{Z.DflZlibHead{w, rr}} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}) -> zs.ntr(r):
  %Equal.sym(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, r, Done{Z.DflZlibHead{w, rr}}, er) : zs.ntr(_)
  Unit{}

def zs.ntr_fail(+r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>, +e: E.DeflateError, +er: {r == Fail{e} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}, +hf: {zs.isT(e) == False{} : Bool}) -> zs.ntr(r):
  %Equal.sym(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, r, Fail{e}, er) : zs.ntr(_)
  %Equal.sym(Bool, zs.isT(e), False{}, hf) : st.bt(Bool.not(_))
  Unit{}

# a feed in the header, when the bytes so far hold a whole header (or a
# refusal): what is left goes on into the body
def zs.hdone(+buf: List<&2, U32>, +q: B.Octets, +t: List<&2, B.Octets>, +p: B.Octets, +o: B.Octets, +max: U32, +dict: B.Octets, +ign: Bool, +w: W.DflWin, +rr: List<&2, U32>, +er: {Z.zl.head(B.append.fast(buf, B.Octets.to_list(q)), dict) == Done{Z.DflZlibHead{w, rr}} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}, +hm: {B.mask(buf) == buf : List<&2, U32>}) -> {zs.res(zs.fz(Z.zl.in.head(Done{Z.DflZlibHead{w, rr}}, B.append.fast(buf, B.Octets.to_list(q)), I.InflateOptions{max, dict, ign})), t, B.Octets.append(p, o), zs.fo(Z.zl.in.head(Done{Z.DflZlibHead{w, rr}}, B.append.fast(buf, B.Octets.to_list(q)), I.InflateOptions{max, dict, ign}))) == zs.res(Z.ZlibInHead{buf, I.InflateOptions{max, dict, ign}}, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}:
  +all = B.append.fast(buf, B.Octets.to_list(q))
  +po = B.Octets.append(p, o)
  +d0 = I.drv.start(w, U32.to_nat(max))
  +e1 = I.drv.go(B.Octets.to_list(B.Octets.of_list(rr)), d0)
  +jt = st.joinl(t)
  +x = B.append(rr, jt)
  +mrr = zs.zm_rr(Z.zl.head(all, dict), w, rr, er, zs.hmask(all, dict, zs.mask_all(buf, q, hm)))
  +ee1 = Equal.trans(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(rr)), B.mask(rr), rr, BL.octets_to_of(rr), mrr)
  +ge = Equal.trans(I.DflDrv, I.drv.go(jt, e1), I.drv.go(jt, I.drv.go(rr, d0)), I.drv.go(x, d0), Equal.cong(List<&2, U32>, I.DflDrv, v => I.drv.go(jt, I.drv.go(v, d0)), B.Octets.to_list(B.Octets.of_list(rr)), rr, ee1), Equal.sym(I.DflDrv, I.drv.go(x, d0), I.drv.go(jt, I.drv.go(rr, d0)), st.go_append(rr, jt, d0)))
  +hp = Equal.trans(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, Z.zl.head(B.append(all, jt), dict), zs.hlift(Z.zl.head(all, dict), jt), Done{Z.DflZlibHead{w, x}}, zs.pre(all, jt, dict, zs.ntr_done(Z.zl.head(all, dict), w, rr, er)), Equal.cong(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, Result<&2, &2, E.DeflateError, Z.DflZlibHead>, v => zs.hlift(v, jt), Z.zl.head(all, dict), Done{Z.DflZlibHead{w, rr}}, er))
  +lhs1 = Laws.zlib_last(Z.zl.in.end(st.fr(I.drv.go(jt, st.kept(e1))), A.Adler32.update(A.Adler32.start(), st.out(e1)), ign), B.Octets.append(po, st.out(e1)))
  +lhs2 = Laws.zlib_last(Z.zl.in.end(st.fr(I.drv.go(jt, e1)), A.Adler32.start(), ign), po)
  +lhs3 = Laws.zlib_last(Z.zl.in.end(st.fr(I.drv.go(x, d0)), A.Adler32.start(), ign), po)
  +rhs1 = Laws.zlib_last(Z.zl.body(I.inf.out(I.drv.result(I.drv.go(x, d0))), max, ign), po)
  +e12 = zs.rel(e1, jt, A.Adler32.start(), ign, po)
  +e23 = Equal.cong(I.DflDrv, Result<&2, &2, E.DeflateError, B.Octets>, v => Laws.zlib_last(Z.zl.in.end(st.fr(v), A.Adler32.start(), ign), po), I.drv.go(jt, e1), I.drv.go(x, d0), ge)
  +e3r = zs.fin(I.drv.go(x, d0), max, ign, po, st.go_inv(x, d0, U32.to_nat(max), {==}))
  +rr1 = Equal.cong(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, Result<&2, &2, E.DeflateError, B.Octets>, v => Laws.zlib_last(Z.zl.after(v, max, ign), po), Z.zl.head(B.append(all, jt), dict), Done{Z.DflZlibHead{w, x}}, hp)
  %Equal.sym(I.DflFed, I.inf.flush(e1, max, ign), I.DflFed{I.Inflater{st.kept(e1), max, ign}, st.out(e1)}, st.flush_eta(e1, max, ign)) : {zs.res(zs.fz(Z.zl.in.fed(_, A.Adler32.start())), t, po, zs.fo(Z.zl.in.fed(_, A.Adler32.start()))) == zs.res(Z.ZlibInHead{buf, I.InflateOptions{max, dict, ign}}, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.append(buf, st.joinl(Con{q, t})), B.append(all, jt), zs.allj(buf, q, t)) : {lhs1 == Laws.zlib_last(Z.zl.decode(_, I.InflateOptions{max, dict, ign}), po) : Result<&2, &2, E.DeflateError, B.Octets>}
  Equal.trans(Result<&2, &2, E.DeflateError, B.Octets>, lhs1, lhs3, Laws.zlib_last(Z.zl.after(Z.zl.head(B.append(all, jt), dict), max, ign), po), Equal.trans(Result<&2, &2, E.DeflateError, B.Octets>, lhs1, lhs2, lhs3, e12, e23), Equal.trans(Result<&2, &2, E.DeflateError, B.Octets>, lhs3, rhs1, Laws.zlib_last(Z.zl.after(Z.zl.head(B.append(all, jt), dict), max, ign), po), e3r, Equal.sym(Result<&2, &2, E.DeflateError, B.Octets>, Laws.zlib_last(Z.zl.after(Z.zl.head(B.append(all, jt), dict), max, ign), po), rhs1, rr1)))

# a feed in the header that leaves it short, or refused
def zs.hfail(b: Bool, +e: E.DeflateError, +eb: {zs.isT(e) == b : Bool}, +buf: List<&2, U32>, +q: B.Octets, +t: List<&2, B.Octets>, +p: B.Octets, +o: B.Octets, +max: U32, +dict: B.Octets, +ign: Bool, +er: {Z.zl.head(B.append.fast(buf, B.Octets.to_list(q)), dict) == Fail{e} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}) -> {zs.res(zs.fz(Z.zl.in.head(Fail{e}, B.append.fast(buf, B.Octets.to_list(q)), I.InflateOptions{max, dict, ign})), t, B.Octets.append(p, o), zs.fo(Z.zl.in.head(Fail{e}, B.append.fast(buf, B.Octets.to_list(q)), I.InflateOptions{max, dict, ign}))) == zs.res(Z.ZlibInHead{buf, I.InflateOptions{max, dict, ign}}, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match b:
    case True{}:
      +all = B.append.fast(buf, B.Octets.to_list(q))
      +po = B.Octets.append(p, o)
      +o0 = {I.InflateOptions{max, dict, ign} : I.InflateOptions}
      +jt = st.joinl(t)
      %Equal.sym(E.DeflateError, e, E.DeflateTruncated{}, zs.isT_true(e, eb)) : {zs.res(zs.fz(Z.zl.in.wait(_, all, o0)), t, po, zs.fo(Z.zl.in.wait(_, all, o0))) == zs.res(Z.ZlibInHead{buf, o0}, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}
      %Equal.sym(List<&2, U32>, B.append(buf, st.joinl(Con{q, t})), B.append(all, jt), zs.allj(buf, q, t)) : {Laws.zlib_last(Z.zl.decode(B.append(all, jt), o0), B.Octets.append(po, B.Octets.empty())) == Laws.zlib_last(Z.zl.decode(_, o0), po) : Result<&2, &2, E.DeflateError, B.Octets>}
      %BL.octets_append_empty_r(po) : {Laws.zlib_last(Z.zl.decode(B.append(all, jt), o0), B.Octets.append(po, B.Octets.empty())) == Laws.zlib_last(Z.zl.decode(B.append(all, jt), o0), _) : Result<&2, &2, E.DeflateError, B.Octets>}
      {==}
    case False{}:
      +all = B.append.fast(buf, B.Octets.to_list(q))
      +po = B.Octets.append(p, o)
      +o0 = {I.InflateOptions{max, dict, ign} : I.InflateOptions}
      +jt = st.joinl(t)
      %Equal.sym(Z.DflZlibFed, Z.zl.in.wait(e, all, o0), Z.DflZlibFed{Z.ZlibInBad{e}, B.Octets.empty()}, zs.wait_bad(e, all, o0, eb)) : {zs.res(zs.fz(_), t, po, zs.fo(_)) == zs.res(Z.ZlibInHead{buf, o0}, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}
      %Equal.sym(List<&2, U32>, B.append(buf, st.joinl(Con{q, t})), B.append(all, jt), zs.allj(buf, q, t)) : {Fail{e} == Laws.zlib_last(Z.zl.decode(_, o0), po) : Result<&2, &2, E.DeflateError, B.Octets>}
      %Equal.sym(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, Z.zl.head(B.append(all, jt), dict), zs.hlift(Z.zl.head(all, dict), jt), zs.pre(all, jt, dict, zs.ntr_fail(Z.zl.head(all, dict), e, er, eb))) : {Fail{e} == Laws.zlib_last(Z.zl.after(_, max, ign), po) : Result<&2, &2, E.DeflateError, B.Octets>}
      %Equal.sym(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, Z.zl.head(all, dict), Fail{e}, er) : {Fail{e} == Laws.zlib_last(Z.zl.after(zs.hlift(_, jt), max, ign), po) : Result<&2, &2, E.DeflateError, B.Octets>}
      {==}

def zs.hstep(r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>, +buf: List<&2, U32>, +q: B.Octets, +t: List<&2, B.Octets>, +p: B.Octets, +o: B.Octets, +max: U32, +dict: B.Octets, +ign: Bool, +er: {Z.zl.head(B.append.fast(buf, B.Octets.to_list(q)), dict) == r : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}, +hm: {B.mask(buf) == buf : List<&2, U32>}) -> {zs.res(zs.fz(Z.zl.in.head(r, B.append.fast(buf, B.Octets.to_list(q)), I.InflateOptions{max, dict, ign})), t, B.Octets.append(p, o), zs.fo(Z.zl.in.head(r, B.append.fast(buf, B.Octets.to_list(q)), I.InflateOptions{max, dict, ign}))) == zs.res(Z.ZlibInHead{buf, I.InflateOptions{max, dict, ign}}, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match r:
    case Fail{+e}:
      zs.hfail(zs.isT(e), e, {==}, buf, q, t, p, o, max, dict, ign, er)
    case Done{h}:
      match h:
        case Z.DflZlibHead{+w, +rr}:
          zs.hdone(buf, q, t, p, o, max, dict, ign, w, rr, er, hm)

def zs.step(z: Z.ZlibInflater, +q: B.Octets, +t: List<&2, B.Octets>, +p: B.Octets, +o: B.Octets, +inv: {zs.ok(z) == True{} : Bool}) -> {zs.res(zs.fz(Z.zlib_inflate_feed(z, q)), t, B.Octets.append(p, o), zs.fo(Z.zlib_inflate_feed(z, q))) == zs.res(z, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match z:
    case Z.ZlibInHead{+buf, opts}:
      match opts:
        case I.InflateOptions{+max, +dict, +ign}:
          +hm = zs.list_sound(B.mask(buf), buf, zs.and_l(Q.eq.list(B.mask(buf), buf), zs.isTr(Z.zl.head(buf, dict)), inv))
          zs.hstep(Z.zl.head(B.append.fast(buf, B.Octets.to_list(q)), dict), buf, q, t, p, o, max, dict, ign, {==}, hm)
    case Z.ZlibInBody{i, +a}:
      match i:
        case I.Inflater{+d, +max, +ign}:
          +e = I.drv.go(B.Octets.to_list(q), d)
          +po = B.Octets.append(p, o)
          %Equal.sym(I.DflFed, I.inf.flush(e, max, ign), I.DflFed{I.Inflater{st.kept(e), max, ign}, st.out(e)}, st.flush_eta(e, max, ign)) : {zs.res(zs.fz(Z.zl.in.fed(_, a)), t, po, zs.fo(Z.zl.in.fed(_, a))) == zs.res(Z.ZlibInBody{I.Inflater{d, max, ign}, a}, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}
          %Equal.sym(I.DflDrv, I.drv.go(st.joinl(Con{q, t}), d), I.drv.go(st.joinl(t), e), st.go_cons(q, t, d)) : {Laws.zlib_last(Z.zl.in.end(st.fr(I.drv.go(st.joinl(t), st.kept(e))), A.Adler32.update(a, st.out(e)), ign), B.Octets.append(po, st.out(e))) == Laws.zlib_last(Z.zl.in.end(st.fr(_), a, ign), po) : Result<&2, &2, E.DeflateError, B.Octets>}
          zs.rel(e, st.joinl(t), a, ign, po)
    case Z.ZlibInBad{e}:
      {==}

def zs.hfinv(b: Bool, +e: E.DeflateError, +eb: {zs.isT(e) == b : Bool}, +buf: List<&2, U32>, +q: B.Octets, +max: U32, +dict: B.Octets, +ign: Bool, +er: {Z.zl.head(B.append.fast(buf, B.Octets.to_list(q)), dict) == Fail{e} : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}, +hm: {B.mask(buf) == buf : List<&2, U32>}) -> {zs.ok(zs.fz(Z.zl.in.head(Fail{e}, B.append.fast(buf, B.Octets.to_list(q)), I.InflateOptions{max, dict, ign}))) == True{} : Bool}:
  match b:
    case True{}:
      +all = B.append.fast(buf, B.Octets.to_list(q))
      +o0 = {I.InflateOptions{max, dict, ign} : I.InflateOptions}
      %Equal.sym(E.DeflateError, e, E.DeflateTruncated{}, zs.isT_true(e, eb)) : {zs.ok(zs.fz(Z.zl.in.wait(_, all, o0))) == True{} : Bool}
      %Equal.sym(List<&2, U32>, B.mask(all), all, zs.mask_all(buf, q, hm)) : {Bool.and(Q.eq.list(_, all), zs.isTr(Z.zl.head(all, dict))) == True{} : Bool}
      %Equal.sym(Bool, Q.eq.list(all, all), True{}, zs.list_refl(all)) : {Bool.and(_, zs.isTr(Z.zl.head(all, dict))) == True{} : Bool}
      %Equal.sym(Result<&2, &2, E.DeflateError, Z.DflZlibHead>, Z.zl.head(all, dict), Fail{e}, er) : {Bool.and(True{}, zs.isTr(_)) == True{} : Bool}
      eb
    case False{}:
      +all = B.append.fast(buf, B.Octets.to_list(q))
      +o0 = {I.InflateOptions{max, dict, ign} : I.InflateOptions}
      %Equal.sym(Z.DflZlibFed, Z.zl.in.wait(e, all, o0), Z.DflZlibFed{Z.ZlibInBad{e}, B.Octets.empty()}, zs.wait_bad(e, all, o0, eb)) : {zs.ok(zs.fz(_)) == True{} : Bool}
      {==}

def zs.hinv(r: Result<&2, &2, E.DeflateError, Z.DflZlibHead>, +buf: List<&2, U32>, +q: B.Octets, +max: U32, +dict: B.Octets, +ign: Bool, +er: {Z.zl.head(B.append.fast(buf, B.Octets.to_list(q)), dict) == r : Result<&2, &2, E.DeflateError, Z.DflZlibHead>}, +hm: {B.mask(buf) == buf : List<&2, U32>}) -> {zs.ok(zs.fz(Z.zl.in.head(r, B.append.fast(buf, B.Octets.to_list(q)), I.InflateOptions{max, dict, ign}))) == True{} : Bool}:
  match r:
    case Fail{+e}:
      zs.hfinv(zs.isT(e), e, {==}, buf, q, max, dict, ign, er, hm)
    case Done{h}:
      match h:
        case Z.DflZlibHead{+w, +rr}:
          +e1 = I.drv.go(B.Octets.to_list(B.Octets.of_list(rr)), I.drv.start(w, U32.to_nat(max)))
          %Equal.sym(I.DflFed, I.inf.flush(e1, max, ign), I.DflFed{I.Inflater{st.kept(e1), max, ign}, st.out(e1)}, st.flush_eta(e1, max, ign)) : {zs.ok(zs.fz(Z.zl.in.fed(_, A.Adler32.start()))) == True{} : Bool}
          {==}

def zs.inv_step(z: Z.ZlibInflater, +q: B.Octets, +inv: {zs.ok(z) == True{} : Bool}) -> {zs.ok(zs.fz(Z.zlib_inflate_feed(z, q))) == True{} : Bool}:
  match z:
    case Z.ZlibInHead{+buf, opts}:
      match opts:
        case I.InflateOptions{+max, +dict, +ign}:
          +hm = zs.list_sound(B.mask(buf), buf, zs.and_l(Q.eq.list(B.mask(buf), buf), zs.isTr(Z.zl.head(buf, dict)), inv))
          zs.hinv(Z.zl.head(B.append.fast(buf, B.Octets.to_list(q)), dict), buf, q, max, dict, ign, {==}, hm)
    case Z.ZlibInBody{i, +a}:
      match i:
        case I.Inflater{+d, +max, +ign}:
          +e = I.drv.go(B.Octets.to_list(q), d)
          %Equal.sym(I.DflFed, I.inf.flush(e, max, ign), I.DflFed{I.Inflater{st.kept(e), max, ign}, st.out(e)}, st.flush_eta(e, max, ign)) : {zs.ok(zs.fz(Z.zl.in.fed(_, a))) == True{} : Bool}
          {==}
    case Z.ZlibInBad{e}:
      {==}

# the resumption invariant, piece by piece
def zs.all(ps: List<&2, B.Octets>, +z: Z.ZlibInflater, +o: B.Octets, +p: B.Octets, +inv: {zs.ok(z) == True{} : Bool}) -> {Laws.zlib_pieces.go(ps, Z.DflZlibFed{z, o}, p) == zs.res(z, ps, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}:
  match ps:
    case Nil{}:
      zs.nil(z, p, o, inv)
    case Con{+q, +t}:
      +f = Z.zlib_inflate_feed(z, q)
      +po = B.Octets.append(p, o)
      %Equal.sym(Z.DflZlibFed, f, Z.DflZlibFed{zs.fz(f), zs.fo(f)}, zs.eta(f)) : {Laws.zlib_pieces.go(t, _, po) == zs.res(z, Con{q, t}, p, o) : Result<&2, &2, E.DeflateError, B.Octets>}
      Equal.trans(Result<&2, &2, E.DeflateError, B.Octets>, Laws.zlib_pieces.go(t, Z.DflZlibFed{zs.fz(f), zs.fo(f)}, po), zs.res(zs.fz(f), t, po, zs.fo(f)), zs.res(z, Con{q, t}, p, o), zs.all(t, zs.fz(f), zs.fo(f), po, zs.inv_step(z, q, inv)), zs.step(z, q, t, p, o, inv))

def Laws.zlib_streaming(opts, ps):
  match opts:
    case I.InflateOptions{+max, +dict, +ign}:
      +o0 = {I.InflateOptions{max, dict, ign} : I.InflateOptions}
      Equal.trans(Result<&2, &2, E.DeflateError, B.Octets>, Laws.zlib_pieces.go(ps, Z.DflZlibFed{Z.ZlibInHead{Nil{}, o0}, B.Octets.empty()}, B.Octets.empty()), Laws.zlib_last(Z.zl.decode(st.joinl(ps), o0), B.Octets.empty()), Z.zl.decode(st.joinl(ps), o0), zs.all(ps, Z.ZlibInHead{Nil{}, o0}, B.Octets.empty(), B.Octets.empty(), {==}), zs.last_empty(Z.zl.decode(st.joinl(ps), o0)))
