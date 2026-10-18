import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./error.bend as E
import ./window.bend as W
import ./decode.bend as D
import ./encode.bend as C
import ./lzo.bend as L
import ./adler32.bend as A
import ./lzop.bend as P
import ./LAWS.bend as Laws

# The properties follow the decoder byte by byte. Each lemma below is about
# the package's internals (decode.bend, encode.bend), never stated as a law.
# Octets enter only through bytes' interface laws (octets_append_list,
# octets_to_of, octets_of_to, octets_len_list, octets_cons_list, rev_rev),
# never through how Octets stores its bytes; only the vectors compute on
# concrete Octets.

# Logic

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def false_not_true(h: {False{} == True{} : Bool}) -> Empty:
  %h : bool_disc(_)
  Unit{}

def absurd(-P: Type, e: Empty) -> P:
  match e:

def res_disc(r: Result<&2, &2, E.LzoError, B.Octets>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def fail_not_done(-x: E.LzoError, -o: B.Octets, h: {Fail{x} == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}) -> Empty:
  %h : res_disc(_)
  Unit{}

def nat_disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def succ_not_zero(-p: Nat, h: {1n+p == 0n : Nat}) -> Empty:
  %h : nat_disc(_)
  Unit{}

# Arithmetic on Nat

def add_zero(p: Nat) -> {Nat.add(p, 0n) == p : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %add_zero(q) : {1n+Nat.add(q, 0n) == 1n+_ : Nat}
      {==}

def add_succ(p: Nat, x: Nat) -> {Nat.add(p, 1n+x) == 1n+Nat.add(p, x) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(q, x) : {1n+Nat.add(q, 1n+x) == 1n+_ : Nat}
      {==}

def add_comm(+p: Nat, +q: Nat) -> {Nat.add(p, q) == Nat.add(q, p) : Nat}:
  match p:
    case 0n:
      Equal.sym(Nat, Nat.add(q, 0n), q, add_zero(q))
    case 1n+r:
      %Equal.sym(Nat, Nat.add(q, 1n+r), 1n+Nat.add(q, r), add_succ(q, r)) : {1n+Nat.add(r, q) == _ : Nat}
      %add_comm(r, q) : {1n+Nat.add(r, q) == 1n+_ : Nat}
      {==}

def sub_zero(m: Nat) -> {Nat.sub(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_pred(n: Nat, q: Nat, h: {Nat.is_le(1n+q, n) == True{} : Bool}) -> {Nat.is_le(q, n) == True{} : Bool}:
  match n q:
    case 0n _:
      absurd({Nat.is_le(q, 0n) == True{} : Bool}, false_not_true(h))
    case 1n+m 0n:
      {==}
    case 1n+m 1n+r:
      le_pred(m, r, h)

def le_up(n: Nat, m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}) -> {Nat.is_le(n, 1n+m) == True{} : Bool}:
  match n m:
    case 0n _:
      {==}
    case 1n+a 0n:
      absurd({Nat.is_le(1n+a, 1n) == True{} : Bool}, false_not_true(h))
    case 1n+a 1n+b:
      le_up(a, b, h)

def sub_succ(n: Nat, q: Nat, h: {Nat.is_le(1n+q, n) == True{} : Bool}) -> {Nat.sub(n, q) == 1n+Nat.sub(n, 1n+q) : Nat}:
  match n q:
    case 0n _:
      absurd({Nat.sub(0n, q) == 1n+Nat.sub(0n, 1n+q) : Nat}, false_not_true(h))
    case 1n+m 0n:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, sub_zero(m)) : {1n+m == 1n+_ : Nat}
      {==}
    case 1n+m 1n+r:
      sub_succ(m, r, h)

def le_zero(c: Nat) -> {Nat.is_le(0n, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_refl(c: Nat) -> {Nat.is_le(c, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_add(a: Nat, b: Nat, c: Nat, h: {Nat.is_le(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a c:
    case 0n _:
      le_zero(c)
    case 1n+p 0n:
      absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, false_not_true(h))
    case 1n+p 1n+q:
      le_add(p, b, q, h)

# Lists

def len_mask(xs: List<&2, U32>) -> {B.len(B.mask(xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %len_mask(t) : {1n+B.len(B.mask(t)) == 1n+_ : Nat}
      {==}

def len_rev(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.len(B.rev_onto(xs, acc)) == Nat.add(B.len(xs), B.len(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %add_succ(B.len(t), B.len(acc)) : {B.len(B.rev_onto(t, Con{h, acc})) == _ : Nat}
      len_rev(t, Con{h, acc})

def len_rev_nil(+xs: List<&2, U32>) -> {B.len(B.rev(xs)) == B.len(xs) : Nat}:
  Equal.trans(Nat, B.len(B.rev(xs)), Nat.add(B.len(xs), 0n), B.len(xs), len_rev(xs, Nil{}), add_zero(B.len(xs)))

# The decoder: running over a ++ b is running over a, then over b

def go_split(a: List<&2, U32>, b: List<&2, U32>, d: D.LzoDec) -> {D.dec.go(B.append(a, b), d) == D.dec.go(b, D.dec.go(a, d)) : D.LzoDec}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      go_split(t, b, D.dec.step(d, h))

def go_app(+a: List<&2, U32>, +b: List<&2, U32>, +d: D.LzoDec, -d2: D.LzoDec, e: {D.dec.go(a, d) == d2 : D.LzoDec}) -> {D.dec.go(B.append(a, b), d) == D.dec.go(b, d2) : D.LzoDec}:
  %e : {D.dec.go(B.append(a, b), d) == D.dec.go(b, _) : D.LzoDec}
  go_split(a, b, d)

# a failure stays a failure, whatever follows
def absorb_out(zs: List<&2, U32>, +e: E.LzoError, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat) -> {D.dec.out(D.dec.end(D.dec.go(zs, D.LzoDec{D.LzoBad{e}, acc, win, room}))) == Fail{e} : Result<&2, &2, E.LzoError, B.Octets>}:
  match zs:
    case Nil{}:
      {==}
    case Con{h, t}:
      absorb_out(t, e, acc, win, room)

def absorb_fail(+zs: List<&2, U32>, +e: E.LzoError, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, -o: B.Octets, h: {D.dec.out(D.dec.end(D.dec.go(zs, D.LzoDec{D.LzoBad{e}, acc, win, room}))) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}) -> Empty:
  fail_not_done(e, o, Equal.trans(Result<&2, &2, E.LzoError, B.Octets>, Fail{e}, D.dec.out(D.dec.end(D.dec.go(zs, D.LzoDec{D.LzoBad{e}, acc, win, room}))), Done{o}, Equal.sym(Result<&2, &2, E.LzoError, B.Octets>, D.dec.out(D.dec.end(D.dec.go(zs, D.LzoDec{D.LzoBad{e}, acc, win, room}))), Fail{e}, absorb_out(zs, e, acc, win, room)), h))

# The output bound: the output so far plus the room left never grows past
# the maximum, through every step of the decoder. Only dec.apply and the
# copy write.

def Inv(d: D.LzoDec, c: Nat) -> Type:
  match d:
    case D.LzoDec{st, acc, win, room}:
      {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}

# a byte moved from the room to the output
def inv_push(+acc: List<&2, U32>, +r: Nat, +b: U32, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), 1n+r), c) == True{} : Bool}) -> {Nat.is_le(Nat.add(B.len({Con{b, acc} : List<&2, U32>}), r), c) == True{} : Bool}:
  %add_succ(B.len(acc), r) : {Nat.is_le(_, c) == True{} : Bool}
  i

def inv_copy_go(n: Nat, +room: Nat, +o: Nat, +s: Nat, +acc: List<&2, U32>, +win: W.LzoWin, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(D.dec.copy.go(n, room, o, s, acc, win), c):
  match n:
    case 0n:
      i
    case 1n+p:
      match room:
        case 0n:
          i
        case 1n+r:
          inv_copy_go(p, r, o, s, Con{W.win.get(win, o), acc}, W.win.put(win, W.win.get(win, o)), c, inv_push(acc, r, W.win.get(win, o), c, i))

def inv_copy_check(ok: Bool, +len: Nat, +o: Nat, +s: Nat, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(D.dec.copy.check(ok, len, o, s, acc, win, room), c):
  match ok:
    case True{}:
      inv_copy_go(len, room, o, s, acc, win, c, i)
    case False{}:
      i

def inv_copy_at(count: Nat, +o: Nat, +len: Nat, +s: Nat, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(D.dec.copy.at(count, o, len, s, acc, win, room), c):
  match count:
    case 0n:
      i
    case 1n+cc:
      inv_copy_check(Nat.is_lt(o, 1n+cc), len, o, s, acc, win, room, c, i)

def inv_apply(a: D.LzoAct, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(D.dec.apply(a, acc, win, room), c):
  match a:
    case D.LzoGo{st}:
      i
    case D.LzoPush{+h, st}:
      match room:
        case 0n:
          i
        case 1n+r:
          inv_push(acc, r, h, c, i)
    case D.LzoCopy{o, len, s}:
      inv_copy_at(W.win.count(win), o, len, s, acc, win, room, c, i)

def inv_step(d: D.LzoDec, +h: U32, +c: Nat, i: Inv(d, c)) -> Inv(D.dec.step(d, h), c):
  match d:
    case D.LzoDec{st, +acc, +win, +room}:
      inv_apply(D.dec.trans(st, h), acc, win, room, c, i)

def inv_go(+xs: List<&2, U32>, +d: D.LzoDec, +c: Nat, i: Inv(d, c)) -> Inv(D.dec.go(xs, d), c):
  match xs:
    case Nil{}:
      i
    case Con{h, t}:
      inv_go(t, D.dec.step(d, h), c, inv_step(d, h, c, i))

# what the decoder answers, after any input, is no longer than the maximum
def fin_end(+acc: List<&2, U32>, +room: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> {Nat.is_le(B.Octets.len(B.Octets.of_list(B.rev(acc))), c) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(B.rev(acc))), B.len(B.Octets.to_list(B.Octets.of_list(B.rev(acc)))), BL.octets_len_list(B.Octets.of_list(B.rev(acc)))) : {Nat.is_le(_, c) == True{} : Bool}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.rev(acc))), B.mask(B.rev(acc)), BL.octets_to_of(B.rev(acc))) : {Nat.is_le(B.len(_), c) == True{} : Bool}
  %Equal.sym(Nat, B.len(B.mask(B.rev(acc))), B.len(B.rev(acc)), len_mask(B.rev(acc))) : {Nat.is_le(_, c) == True{} : Bool}
  %Equal.sym(Nat, B.len(B.rev(acc)), B.len(acc), len_rev_nil(acc)) : {Nat.is_le(_, c) == True{} : Bool}
  le_add(B.len(acc), room, c, i)

def fin(d: D.LzoDec, +c: Nat, i: Inv(d, c)) -> {Nat.is_le(B.Octets.len(Result.default(&2, &2, E.LzoError, B.Octets, D.dec.out(D.dec.end(d)), B.Octets.empty())), c) == True{} : Bool}:
  match d:
    case D.LzoDec{st, +acc, +win, +room}:
      match st:
        case D.LzoEnd{}:
          fin_end(acc, room, c, i)
        case D.LzoIns{x}:
          le_zero(c)
        case D.LzoLitExt{x}:
          le_zero(c)
        case D.LzoLit{x, y}:
          le_zero(c)
        case D.LzoNear{x, y, z, u, v}:
          le_zero(c)
        case D.LzoMatExt{x, y}:
          le_zero(c)
        case D.LzoDist{x, y}:
          le_zero(c)
        case D.LzoDist2{x, y, z}:
          le_zero(c)
        case D.LzoBad{x}:
          le_zero(c)

# Literals: the literal-only stream decodes to its bytes

# the window after the bytes ys, as the decoder's literals leave it
def wpush(ys: List<&2, U32>, w: W.LzoWin) -> W.LzoWin:
  match ys:
    case Nil{}:
      w
    case Con{h, t}:
      wpush(t, W.win.put(w, h))

# literals: n of them copy n bytes
def lit_run(ys: List<&2, U32>, +c: D.LzoCls, acc: List<&2, U32>, win: W.LzoWin, +k: Nat) -> {D.dec.go(ys, D.LzoDec{D.LzoLit{B.len(ys), c}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoLit{0n, c}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match ys:
    case Nil{}:
      {==}
    case Con{+h, t}:
      lit_run(t, c, Con{h, acc}, W.win.put(win, h), k)

# the end marker, after literals of any class
def eos_lit(+c: D.LzoCls, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat) -> {D.dec.go([17, 0, 0], D.LzoDec{D.LzoLit{0n, c}, acc, win, room}) == D.LzoDec{D.LzoEnd{}, acc, win, room} : D.LzoDec}:
  {==}

# after a literal run's instruction for m = len(ys) literals: the literals,
# then the end marker
def after_hdr(+m: Nat, +c: D.LzoCls, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == m : Nat}) -> {D.dec.go(B.append(ys, [17, 0, 0]), D.LzoDec{D.LzoLit{m, c}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  %e : {D.dec.go(B.append(ys, [17, 0, 0]), D.LzoDec{D.LzoLit{_, c}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}
  Equal.trans(D.LzoDec, D.dec.go(B.append(ys, [17, 0, 0]), D.LzoDec{D.LzoLit{B.len(ys), c}, acc, win, Nat.add(B.len(ys), k)}), D.dec.go([17, 0, 0], D.LzoDec{D.LzoLit{0n, c}, B.rev_onto(ys, acc), wpush(ys, win), k}), D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k}, go_app(ys, [17, 0, 0], D.LzoDec{D.LzoLit{B.len(ys), c}, acc, win, Nat.add(B.len(ys), k)}, D.LzoDec{D.LzoLit{0n, c}, B.rev_onto(ys, acc), wpush(ys, win), k}, lit_run(ys, c, acc, win, k)), eos_lit(c, B.rev_onto(ys, acc), wpush(ys, win), k))

# The literal run's length bytes, as the decoder reads them. The last length
# byte 255 - d (d <= 254) reads as 255 - d: one lemma per d.

def cl_254(q: Nat, h: {Nat.is_le(Nat.add(254n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(254n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(254n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      absurd({D.dec.ext(B.byte(C.ext.last(Nat.add(254n, 1n+r)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(254n, 1n+r))} : D.LzoExt}, false_not_true(h))

def cl_253(q: Nat, h: {Nat.is_le(Nat.add(253n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(253n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(253n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_254(r, h)

def cl_252(q: Nat, h: {Nat.is_le(Nat.add(252n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(252n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(252n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_253(r, h)

def cl_251(q: Nat, h: {Nat.is_le(Nat.add(251n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(251n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(251n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_252(r, h)

def cl_250(q: Nat, h: {Nat.is_le(Nat.add(250n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(250n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(250n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_251(r, h)

def cl_249(q: Nat, h: {Nat.is_le(Nat.add(249n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(249n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(249n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_250(r, h)

def cl_248(q: Nat, h: {Nat.is_le(Nat.add(248n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(248n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(248n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_249(r, h)

def cl_247(q: Nat, h: {Nat.is_le(Nat.add(247n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(247n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(247n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_248(r, h)

def cl_246(q: Nat, h: {Nat.is_le(Nat.add(246n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(246n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(246n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_247(r, h)

def cl_245(q: Nat, h: {Nat.is_le(Nat.add(245n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(245n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(245n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_246(r, h)

def cl_244(q: Nat, h: {Nat.is_le(Nat.add(244n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(244n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(244n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_245(r, h)

def cl_243(q: Nat, h: {Nat.is_le(Nat.add(243n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(243n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(243n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_244(r, h)

def cl_242(q: Nat, h: {Nat.is_le(Nat.add(242n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(242n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(242n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_243(r, h)

def cl_241(q: Nat, h: {Nat.is_le(Nat.add(241n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(241n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(241n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_242(r, h)

def cl_240(q: Nat, h: {Nat.is_le(Nat.add(240n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(240n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(240n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_241(r, h)

def cl_239(q: Nat, h: {Nat.is_le(Nat.add(239n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(239n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(239n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_240(r, h)

def cl_238(q: Nat, h: {Nat.is_le(Nat.add(238n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(238n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(238n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_239(r, h)

def cl_237(q: Nat, h: {Nat.is_le(Nat.add(237n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(237n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(237n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_238(r, h)

def cl_236(q: Nat, h: {Nat.is_le(Nat.add(236n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(236n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(236n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_237(r, h)

def cl_235(q: Nat, h: {Nat.is_le(Nat.add(235n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(235n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(235n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_236(r, h)

def cl_234(q: Nat, h: {Nat.is_le(Nat.add(234n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(234n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(234n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_235(r, h)

def cl_233(q: Nat, h: {Nat.is_le(Nat.add(233n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(233n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(233n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_234(r, h)

def cl_232(q: Nat, h: {Nat.is_le(Nat.add(232n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(232n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(232n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_233(r, h)

def cl_231(q: Nat, h: {Nat.is_le(Nat.add(231n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(231n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(231n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_232(r, h)

def cl_230(q: Nat, h: {Nat.is_le(Nat.add(230n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(230n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(230n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_231(r, h)

def cl_229(q: Nat, h: {Nat.is_le(Nat.add(229n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(229n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(229n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_230(r, h)

def cl_228(q: Nat, h: {Nat.is_le(Nat.add(228n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(228n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(228n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_229(r, h)

def cl_227(q: Nat, h: {Nat.is_le(Nat.add(227n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(227n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(227n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_228(r, h)

def cl_226(q: Nat, h: {Nat.is_le(Nat.add(226n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(226n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(226n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_227(r, h)

def cl_225(q: Nat, h: {Nat.is_le(Nat.add(225n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(225n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(225n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_226(r, h)

def cl_224(q: Nat, h: {Nat.is_le(Nat.add(224n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(224n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(224n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_225(r, h)

def cl_223(q: Nat, h: {Nat.is_le(Nat.add(223n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(223n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(223n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_224(r, h)

def cl_222(q: Nat, h: {Nat.is_le(Nat.add(222n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(222n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(222n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_223(r, h)

def cl_221(q: Nat, h: {Nat.is_le(Nat.add(221n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(221n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(221n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_222(r, h)

def cl_220(q: Nat, h: {Nat.is_le(Nat.add(220n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(220n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(220n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_221(r, h)

def cl_219(q: Nat, h: {Nat.is_le(Nat.add(219n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(219n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(219n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_220(r, h)

def cl_218(q: Nat, h: {Nat.is_le(Nat.add(218n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(218n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(218n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_219(r, h)

def cl_217(q: Nat, h: {Nat.is_le(Nat.add(217n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(217n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(217n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_218(r, h)

def cl_216(q: Nat, h: {Nat.is_le(Nat.add(216n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(216n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(216n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_217(r, h)

def cl_215(q: Nat, h: {Nat.is_le(Nat.add(215n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(215n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(215n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_216(r, h)

def cl_214(q: Nat, h: {Nat.is_le(Nat.add(214n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(214n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(214n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_215(r, h)

def cl_213(q: Nat, h: {Nat.is_le(Nat.add(213n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(213n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(213n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_214(r, h)

def cl_212(q: Nat, h: {Nat.is_le(Nat.add(212n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(212n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(212n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_213(r, h)

def cl_211(q: Nat, h: {Nat.is_le(Nat.add(211n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(211n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(211n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_212(r, h)

def cl_210(q: Nat, h: {Nat.is_le(Nat.add(210n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(210n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(210n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_211(r, h)

def cl_209(q: Nat, h: {Nat.is_le(Nat.add(209n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(209n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(209n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_210(r, h)

def cl_208(q: Nat, h: {Nat.is_le(Nat.add(208n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(208n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(208n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_209(r, h)

def cl_207(q: Nat, h: {Nat.is_le(Nat.add(207n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(207n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(207n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_208(r, h)

def cl_206(q: Nat, h: {Nat.is_le(Nat.add(206n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(206n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(206n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_207(r, h)

def cl_205(q: Nat, h: {Nat.is_le(Nat.add(205n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(205n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(205n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_206(r, h)

def cl_204(q: Nat, h: {Nat.is_le(Nat.add(204n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(204n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(204n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_205(r, h)

def cl_203(q: Nat, h: {Nat.is_le(Nat.add(203n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(203n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(203n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_204(r, h)

def cl_202(q: Nat, h: {Nat.is_le(Nat.add(202n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(202n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(202n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_203(r, h)

def cl_201(q: Nat, h: {Nat.is_le(Nat.add(201n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(201n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(201n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_202(r, h)

def cl_200(q: Nat, h: {Nat.is_le(Nat.add(200n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(200n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(200n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_201(r, h)

def cl_199(q: Nat, h: {Nat.is_le(Nat.add(199n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(199n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(199n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_200(r, h)

def cl_198(q: Nat, h: {Nat.is_le(Nat.add(198n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(198n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(198n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_199(r, h)

def cl_197(q: Nat, h: {Nat.is_le(Nat.add(197n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(197n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(197n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_198(r, h)

def cl_196(q: Nat, h: {Nat.is_le(Nat.add(196n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(196n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(196n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_197(r, h)

def cl_195(q: Nat, h: {Nat.is_le(Nat.add(195n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(195n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(195n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_196(r, h)

def cl_194(q: Nat, h: {Nat.is_le(Nat.add(194n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(194n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(194n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_195(r, h)

def cl_193(q: Nat, h: {Nat.is_le(Nat.add(193n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(193n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(193n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_194(r, h)

def cl_192(q: Nat, h: {Nat.is_le(Nat.add(192n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(192n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(192n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_193(r, h)

def cl_191(q: Nat, h: {Nat.is_le(Nat.add(191n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(191n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(191n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_192(r, h)

def cl_190(q: Nat, h: {Nat.is_le(Nat.add(190n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(190n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(190n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_191(r, h)

def cl_189(q: Nat, h: {Nat.is_le(Nat.add(189n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(189n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(189n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_190(r, h)

def cl_188(q: Nat, h: {Nat.is_le(Nat.add(188n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(188n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(188n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_189(r, h)

def cl_187(q: Nat, h: {Nat.is_le(Nat.add(187n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(187n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(187n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_188(r, h)

def cl_186(q: Nat, h: {Nat.is_le(Nat.add(186n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(186n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(186n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_187(r, h)

def cl_185(q: Nat, h: {Nat.is_le(Nat.add(185n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(185n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(185n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_186(r, h)

def cl_184(q: Nat, h: {Nat.is_le(Nat.add(184n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(184n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(184n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_185(r, h)

def cl_183(q: Nat, h: {Nat.is_le(Nat.add(183n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(183n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(183n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_184(r, h)

def cl_182(q: Nat, h: {Nat.is_le(Nat.add(182n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(182n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(182n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_183(r, h)

def cl_181(q: Nat, h: {Nat.is_le(Nat.add(181n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(181n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(181n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_182(r, h)

def cl_180(q: Nat, h: {Nat.is_le(Nat.add(180n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(180n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(180n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_181(r, h)

def cl_179(q: Nat, h: {Nat.is_le(Nat.add(179n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(179n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(179n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_180(r, h)

def cl_178(q: Nat, h: {Nat.is_le(Nat.add(178n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(178n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(178n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_179(r, h)

def cl_177(q: Nat, h: {Nat.is_le(Nat.add(177n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(177n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(177n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_178(r, h)

def cl_176(q: Nat, h: {Nat.is_le(Nat.add(176n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(176n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(176n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_177(r, h)

def cl_175(q: Nat, h: {Nat.is_le(Nat.add(175n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(175n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(175n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_176(r, h)

def cl_174(q: Nat, h: {Nat.is_le(Nat.add(174n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(174n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(174n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_175(r, h)

def cl_173(q: Nat, h: {Nat.is_le(Nat.add(173n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(173n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(173n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_174(r, h)

def cl_172(q: Nat, h: {Nat.is_le(Nat.add(172n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(172n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(172n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_173(r, h)

def cl_171(q: Nat, h: {Nat.is_le(Nat.add(171n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(171n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(171n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_172(r, h)

def cl_170(q: Nat, h: {Nat.is_le(Nat.add(170n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(170n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(170n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_171(r, h)

def cl_169(q: Nat, h: {Nat.is_le(Nat.add(169n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(169n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(169n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_170(r, h)

def cl_168(q: Nat, h: {Nat.is_le(Nat.add(168n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(168n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(168n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_169(r, h)

def cl_167(q: Nat, h: {Nat.is_le(Nat.add(167n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(167n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(167n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_168(r, h)

def cl_166(q: Nat, h: {Nat.is_le(Nat.add(166n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(166n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(166n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_167(r, h)

def cl_165(q: Nat, h: {Nat.is_le(Nat.add(165n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(165n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(165n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_166(r, h)

def cl_164(q: Nat, h: {Nat.is_le(Nat.add(164n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(164n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(164n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_165(r, h)

def cl_163(q: Nat, h: {Nat.is_le(Nat.add(163n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(163n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(163n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_164(r, h)

def cl_162(q: Nat, h: {Nat.is_le(Nat.add(162n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(162n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(162n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_163(r, h)

def cl_161(q: Nat, h: {Nat.is_le(Nat.add(161n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(161n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(161n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_162(r, h)

def cl_160(q: Nat, h: {Nat.is_le(Nat.add(160n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(160n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(160n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_161(r, h)

def cl_159(q: Nat, h: {Nat.is_le(Nat.add(159n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(159n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(159n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_160(r, h)

def cl_158(q: Nat, h: {Nat.is_le(Nat.add(158n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(158n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(158n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_159(r, h)

def cl_157(q: Nat, h: {Nat.is_le(Nat.add(157n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(157n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(157n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_158(r, h)

def cl_156(q: Nat, h: {Nat.is_le(Nat.add(156n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(156n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(156n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_157(r, h)

def cl_155(q: Nat, h: {Nat.is_le(Nat.add(155n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(155n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(155n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_156(r, h)

def cl_154(q: Nat, h: {Nat.is_le(Nat.add(154n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(154n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(154n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_155(r, h)

def cl_153(q: Nat, h: {Nat.is_le(Nat.add(153n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(153n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(153n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_154(r, h)

def cl_152(q: Nat, h: {Nat.is_le(Nat.add(152n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(152n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(152n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_153(r, h)

def cl_151(q: Nat, h: {Nat.is_le(Nat.add(151n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(151n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(151n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_152(r, h)

def cl_150(q: Nat, h: {Nat.is_le(Nat.add(150n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(150n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(150n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_151(r, h)

def cl_149(q: Nat, h: {Nat.is_le(Nat.add(149n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(149n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(149n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_150(r, h)

def cl_148(q: Nat, h: {Nat.is_le(Nat.add(148n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(148n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(148n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_149(r, h)

def cl_147(q: Nat, h: {Nat.is_le(Nat.add(147n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(147n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(147n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_148(r, h)

def cl_146(q: Nat, h: {Nat.is_le(Nat.add(146n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(146n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(146n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_147(r, h)

def cl_145(q: Nat, h: {Nat.is_le(Nat.add(145n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(145n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(145n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_146(r, h)

def cl_144(q: Nat, h: {Nat.is_le(Nat.add(144n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(144n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(144n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_145(r, h)

def cl_143(q: Nat, h: {Nat.is_le(Nat.add(143n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(143n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(143n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_144(r, h)

def cl_142(q: Nat, h: {Nat.is_le(Nat.add(142n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(142n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(142n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_143(r, h)

def cl_141(q: Nat, h: {Nat.is_le(Nat.add(141n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(141n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(141n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_142(r, h)

def cl_140(q: Nat, h: {Nat.is_le(Nat.add(140n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(140n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(140n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_141(r, h)

def cl_139(q: Nat, h: {Nat.is_le(Nat.add(139n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(139n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(139n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_140(r, h)

def cl_138(q: Nat, h: {Nat.is_le(Nat.add(138n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(138n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(138n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_139(r, h)

def cl_137(q: Nat, h: {Nat.is_le(Nat.add(137n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(137n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(137n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_138(r, h)

def cl_136(q: Nat, h: {Nat.is_le(Nat.add(136n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(136n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(136n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_137(r, h)

def cl_135(q: Nat, h: {Nat.is_le(Nat.add(135n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(135n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(135n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_136(r, h)

def cl_134(q: Nat, h: {Nat.is_le(Nat.add(134n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(134n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(134n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_135(r, h)

def cl_133(q: Nat, h: {Nat.is_le(Nat.add(133n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(133n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(133n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_134(r, h)

def cl_132(q: Nat, h: {Nat.is_le(Nat.add(132n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(132n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(132n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_133(r, h)

def cl_131(q: Nat, h: {Nat.is_le(Nat.add(131n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(131n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(131n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_132(r, h)

def cl_130(q: Nat, h: {Nat.is_le(Nat.add(130n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(130n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(130n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_131(r, h)

def cl_129(q: Nat, h: {Nat.is_le(Nat.add(129n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(129n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(129n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_130(r, h)

def cl_128(q: Nat, h: {Nat.is_le(Nat.add(128n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(128n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(128n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_129(r, h)

def cl_127(q: Nat, h: {Nat.is_le(Nat.add(127n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(127n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(127n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_128(r, h)

def cl_126(q: Nat, h: {Nat.is_le(Nat.add(126n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(126n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(126n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_127(r, h)

def cl_125(q: Nat, h: {Nat.is_le(Nat.add(125n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(125n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(125n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_126(r, h)

def cl_124(q: Nat, h: {Nat.is_le(Nat.add(124n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(124n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(124n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_125(r, h)

def cl_123(q: Nat, h: {Nat.is_le(Nat.add(123n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(123n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(123n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_124(r, h)

def cl_122(q: Nat, h: {Nat.is_le(Nat.add(122n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(122n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(122n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_123(r, h)

def cl_121(q: Nat, h: {Nat.is_le(Nat.add(121n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(121n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(121n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_122(r, h)

def cl_120(q: Nat, h: {Nat.is_le(Nat.add(120n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(120n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(120n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_121(r, h)

def cl_119(q: Nat, h: {Nat.is_le(Nat.add(119n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(119n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(119n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_120(r, h)

def cl_118(q: Nat, h: {Nat.is_le(Nat.add(118n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(118n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(118n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_119(r, h)

def cl_117(q: Nat, h: {Nat.is_le(Nat.add(117n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(117n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(117n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_118(r, h)

def cl_116(q: Nat, h: {Nat.is_le(Nat.add(116n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(116n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(116n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_117(r, h)

def cl_115(q: Nat, h: {Nat.is_le(Nat.add(115n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(115n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(115n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_116(r, h)

def cl_114(q: Nat, h: {Nat.is_le(Nat.add(114n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(114n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(114n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_115(r, h)

def cl_113(q: Nat, h: {Nat.is_le(Nat.add(113n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(113n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(113n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_114(r, h)

def cl_112(q: Nat, h: {Nat.is_le(Nat.add(112n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(112n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(112n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_113(r, h)

def cl_111(q: Nat, h: {Nat.is_le(Nat.add(111n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(111n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(111n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_112(r, h)

def cl_110(q: Nat, h: {Nat.is_le(Nat.add(110n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(110n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(110n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_111(r, h)

def cl_109(q: Nat, h: {Nat.is_le(Nat.add(109n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(109n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(109n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_110(r, h)

def cl_108(q: Nat, h: {Nat.is_le(Nat.add(108n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(108n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(108n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_109(r, h)

def cl_107(q: Nat, h: {Nat.is_le(Nat.add(107n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(107n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(107n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_108(r, h)

def cl_106(q: Nat, h: {Nat.is_le(Nat.add(106n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(106n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(106n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_107(r, h)

def cl_105(q: Nat, h: {Nat.is_le(Nat.add(105n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(105n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(105n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_106(r, h)

def cl_104(q: Nat, h: {Nat.is_le(Nat.add(104n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(104n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(104n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_105(r, h)

def cl_103(q: Nat, h: {Nat.is_le(Nat.add(103n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(103n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(103n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_104(r, h)

def cl_102(q: Nat, h: {Nat.is_le(Nat.add(102n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(102n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(102n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_103(r, h)

def cl_101(q: Nat, h: {Nat.is_le(Nat.add(101n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(101n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(101n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_102(r, h)

def cl_100(q: Nat, h: {Nat.is_le(Nat.add(100n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(100n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(100n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_101(r, h)

def cl_99(q: Nat, h: {Nat.is_le(Nat.add(99n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(99n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(99n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_100(r, h)

def cl_98(q: Nat, h: {Nat.is_le(Nat.add(98n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(98n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(98n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_99(r, h)

def cl_97(q: Nat, h: {Nat.is_le(Nat.add(97n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(97n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(97n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_98(r, h)

def cl_96(q: Nat, h: {Nat.is_le(Nat.add(96n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(96n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(96n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_97(r, h)

def cl_95(q: Nat, h: {Nat.is_le(Nat.add(95n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(95n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(95n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_96(r, h)

def cl_94(q: Nat, h: {Nat.is_le(Nat.add(94n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(94n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(94n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_95(r, h)

def cl_93(q: Nat, h: {Nat.is_le(Nat.add(93n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(93n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(93n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_94(r, h)

def cl_92(q: Nat, h: {Nat.is_le(Nat.add(92n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(92n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(92n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_93(r, h)

def cl_91(q: Nat, h: {Nat.is_le(Nat.add(91n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(91n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(91n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_92(r, h)

def cl_90(q: Nat, h: {Nat.is_le(Nat.add(90n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(90n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(90n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_91(r, h)

def cl_89(q: Nat, h: {Nat.is_le(Nat.add(89n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(89n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(89n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_90(r, h)

def cl_88(q: Nat, h: {Nat.is_le(Nat.add(88n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(88n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(88n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_89(r, h)

def cl_87(q: Nat, h: {Nat.is_le(Nat.add(87n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(87n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(87n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_88(r, h)

def cl_86(q: Nat, h: {Nat.is_le(Nat.add(86n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(86n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(86n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_87(r, h)

def cl_85(q: Nat, h: {Nat.is_le(Nat.add(85n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(85n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(85n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_86(r, h)

def cl_84(q: Nat, h: {Nat.is_le(Nat.add(84n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(84n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(84n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_85(r, h)

def cl_83(q: Nat, h: {Nat.is_le(Nat.add(83n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(83n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(83n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_84(r, h)

def cl_82(q: Nat, h: {Nat.is_le(Nat.add(82n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(82n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(82n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_83(r, h)

def cl_81(q: Nat, h: {Nat.is_le(Nat.add(81n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(81n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(81n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_82(r, h)

def cl_80(q: Nat, h: {Nat.is_le(Nat.add(80n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(80n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(80n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_81(r, h)

def cl_79(q: Nat, h: {Nat.is_le(Nat.add(79n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(79n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(79n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_80(r, h)

def cl_78(q: Nat, h: {Nat.is_le(Nat.add(78n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(78n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(78n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_79(r, h)

def cl_77(q: Nat, h: {Nat.is_le(Nat.add(77n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(77n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(77n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_78(r, h)

def cl_76(q: Nat, h: {Nat.is_le(Nat.add(76n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(76n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(76n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_77(r, h)

def cl_75(q: Nat, h: {Nat.is_le(Nat.add(75n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(75n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(75n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_76(r, h)

def cl_74(q: Nat, h: {Nat.is_le(Nat.add(74n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(74n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(74n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_75(r, h)

def cl_73(q: Nat, h: {Nat.is_le(Nat.add(73n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(73n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(73n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_74(r, h)

def cl_72(q: Nat, h: {Nat.is_le(Nat.add(72n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(72n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(72n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_73(r, h)

def cl_71(q: Nat, h: {Nat.is_le(Nat.add(71n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(71n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(71n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_72(r, h)

def cl_70(q: Nat, h: {Nat.is_le(Nat.add(70n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(70n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(70n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_71(r, h)

def cl_69(q: Nat, h: {Nat.is_le(Nat.add(69n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(69n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(69n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_70(r, h)

def cl_68(q: Nat, h: {Nat.is_le(Nat.add(68n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(68n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(68n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_69(r, h)

def cl_67(q: Nat, h: {Nat.is_le(Nat.add(67n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(67n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(67n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_68(r, h)

def cl_66(q: Nat, h: {Nat.is_le(Nat.add(66n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(66n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(66n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_67(r, h)

def cl_65(q: Nat, h: {Nat.is_le(Nat.add(65n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(65n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(65n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_66(r, h)

def cl_64(q: Nat, h: {Nat.is_le(Nat.add(64n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(64n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(64n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_65(r, h)

def cl_63(q: Nat, h: {Nat.is_le(Nat.add(63n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(63n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(63n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_64(r, h)

def cl_62(q: Nat, h: {Nat.is_le(Nat.add(62n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(62n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(62n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_63(r, h)

def cl_61(q: Nat, h: {Nat.is_le(Nat.add(61n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(61n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(61n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_62(r, h)

def cl_60(q: Nat, h: {Nat.is_le(Nat.add(60n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(60n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(60n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_61(r, h)

def cl_59(q: Nat, h: {Nat.is_le(Nat.add(59n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(59n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(59n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_60(r, h)

def cl_58(q: Nat, h: {Nat.is_le(Nat.add(58n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(58n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(58n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_59(r, h)

def cl_57(q: Nat, h: {Nat.is_le(Nat.add(57n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(57n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(57n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_58(r, h)

def cl_56(q: Nat, h: {Nat.is_le(Nat.add(56n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(56n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(56n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_57(r, h)

def cl_55(q: Nat, h: {Nat.is_le(Nat.add(55n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(55n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(55n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_56(r, h)

def cl_54(q: Nat, h: {Nat.is_le(Nat.add(54n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(54n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(54n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_55(r, h)

def cl_53(q: Nat, h: {Nat.is_le(Nat.add(53n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(53n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(53n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_54(r, h)

def cl_52(q: Nat, h: {Nat.is_le(Nat.add(52n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(52n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(52n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_53(r, h)

def cl_51(q: Nat, h: {Nat.is_le(Nat.add(51n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(51n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(51n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_52(r, h)

def cl_50(q: Nat, h: {Nat.is_le(Nat.add(50n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(50n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(50n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_51(r, h)

def cl_49(q: Nat, h: {Nat.is_le(Nat.add(49n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(49n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(49n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_50(r, h)

def cl_48(q: Nat, h: {Nat.is_le(Nat.add(48n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(48n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(48n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_49(r, h)

def cl_47(q: Nat, h: {Nat.is_le(Nat.add(47n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(47n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(47n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_48(r, h)

def cl_46(q: Nat, h: {Nat.is_le(Nat.add(46n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(46n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(46n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_47(r, h)

def cl_45(q: Nat, h: {Nat.is_le(Nat.add(45n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(45n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(45n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_46(r, h)

def cl_44(q: Nat, h: {Nat.is_le(Nat.add(44n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(44n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(44n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_45(r, h)

def cl_43(q: Nat, h: {Nat.is_le(Nat.add(43n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(43n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(43n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_44(r, h)

def cl_42(q: Nat, h: {Nat.is_le(Nat.add(42n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(42n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(42n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_43(r, h)

def cl_41(q: Nat, h: {Nat.is_le(Nat.add(41n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(41n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(41n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_42(r, h)

def cl_40(q: Nat, h: {Nat.is_le(Nat.add(40n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(40n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(40n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_41(r, h)

def cl_39(q: Nat, h: {Nat.is_le(Nat.add(39n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(39n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(39n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_40(r, h)

def cl_38(q: Nat, h: {Nat.is_le(Nat.add(38n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(38n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(38n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_39(r, h)

def cl_37(q: Nat, h: {Nat.is_le(Nat.add(37n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(37n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(37n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_38(r, h)

def cl_36(q: Nat, h: {Nat.is_le(Nat.add(36n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(36n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(36n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_37(r, h)

def cl_35(q: Nat, h: {Nat.is_le(Nat.add(35n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(35n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(35n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_36(r, h)

def cl_34(q: Nat, h: {Nat.is_le(Nat.add(34n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(34n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(34n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_35(r, h)

def cl_33(q: Nat, h: {Nat.is_le(Nat.add(33n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(33n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(33n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_34(r, h)

def cl_32(q: Nat, h: {Nat.is_le(Nat.add(32n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(32n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(32n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_33(r, h)

def cl_31(q: Nat, h: {Nat.is_le(Nat.add(31n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(31n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(31n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_32(r, h)

def cl_30(q: Nat, h: {Nat.is_le(Nat.add(30n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(30n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(30n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_31(r, h)

def cl_29(q: Nat, h: {Nat.is_le(Nat.add(29n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(29n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(29n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_30(r, h)

def cl_28(q: Nat, h: {Nat.is_le(Nat.add(28n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(28n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(28n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_29(r, h)

def cl_27(q: Nat, h: {Nat.is_le(Nat.add(27n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(27n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(27n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_28(r, h)

def cl_26(q: Nat, h: {Nat.is_le(Nat.add(26n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(26n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(26n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_27(r, h)

def cl_25(q: Nat, h: {Nat.is_le(Nat.add(25n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(25n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(25n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_26(r, h)

def cl_24(q: Nat, h: {Nat.is_le(Nat.add(24n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(24n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(24n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_25(r, h)

def cl_23(q: Nat, h: {Nat.is_le(Nat.add(23n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(23n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(23n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_24(r, h)

def cl_22(q: Nat, h: {Nat.is_le(Nat.add(22n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(22n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(22n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_23(r, h)

def cl_21(q: Nat, h: {Nat.is_le(Nat.add(21n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(21n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(21n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_22(r, h)

def cl_20(q: Nat, h: {Nat.is_le(Nat.add(20n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(20n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(20n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_21(r, h)

def cl_19(q: Nat, h: {Nat.is_le(Nat.add(19n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(19n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(19n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_20(r, h)

def cl_18(q: Nat, h: {Nat.is_le(Nat.add(18n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(18n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(18n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_19(r, h)

def cl_17(q: Nat, h: {Nat.is_le(Nat.add(17n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(17n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(17n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_18(r, h)

def cl_16(q: Nat, h: {Nat.is_le(Nat.add(16n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(16n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(16n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_17(r, h)

def cl_15(q: Nat, h: {Nat.is_le(Nat.add(15n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(15n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(15n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_16(r, h)

def cl_14(q: Nat, h: {Nat.is_le(Nat.add(14n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(14n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(14n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_15(r, h)

def cl_13(q: Nat, h: {Nat.is_le(Nat.add(13n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(13n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(13n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_14(r, h)

def cl_12(q: Nat, h: {Nat.is_le(Nat.add(12n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(12n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(12n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_13(r, h)

def cl_11(q: Nat, h: {Nat.is_le(Nat.add(11n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(11n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(11n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_12(r, h)

def cl_10(q: Nat, h: {Nat.is_le(Nat.add(10n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(10n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(10n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_11(r, h)

def cl_9(q: Nat, h: {Nat.is_le(Nat.add(9n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(9n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(9n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_10(r, h)

def cl_8(q: Nat, h: {Nat.is_le(Nat.add(8n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(8n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(8n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_9(r, h)

def cl_7(q: Nat, h: {Nat.is_le(Nat.add(7n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(7n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(7n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_8(r, h)

def cl_6(q: Nat, h: {Nat.is_le(Nat.add(6n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(6n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(6n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_7(r, h)

def cl_5(q: Nat, h: {Nat.is_le(Nat.add(5n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(5n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(5n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_6(r, h)

def cl_4(q: Nat, h: {Nat.is_le(Nat.add(4n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(4n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(4n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_5(r, h)

def cl_3(q: Nat, h: {Nat.is_le(Nat.add(3n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(3n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(3n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_4(r, h)

def cl_2(q: Nat, h: {Nat.is_le(Nat.add(2n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(2n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(2n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_3(r, h)

def cl_1(q: Nat, h: {Nat.is_le(Nat.add(1n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(1n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(1n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_2(r, h)

def cl_0(q: Nat, h: {Nat.is_le(Nat.add(0n, q), 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(Nat.add(0n, q)))) == D.LzoExtLast{Nat.sub(255n, Nat.add(0n, q))} : D.LzoExt}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_1(r, h)

def classify_last(+d: Nat, h: {Nat.is_le(d, 254n) == True{} : Bool}) -> {D.dec.ext(B.byte(C.ext.last(d))) == D.LzoExtLast{Nat.sub(255n, d)} : D.LzoExt}:
  cl_0(d, h)

# the length bytes after a literal-run field of 0 add up to the literal
# count: r more, from a byte with room d (d <= 254), on top of a
def ext_run(+r: Nat, +d: Nat, +a: Nat, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, +h: {Nat.is_le(d, 254n) == True{} : Bool}) -> {D.dec.go(B.mask(C.ext.ref(r, d)), D.LzoDec{D.LzoLitExt{a}, acc, win, room}) == D.LzoDec{D.LzoLit{Nat.add(r, Nat.add(Nat.sub(255n, d), a)), D.LzoMany{}}, acc, win, room} : D.LzoDec}:
  match r:
    case 0n:
      %Equal.sym(D.LzoExt, D.dec.ext(B.byte(C.ext.last(d))), D.LzoExtLast{Nat.sub(255n, d)}, classify_last(d, h)) : {D.dec.apply(D.dec.litext(_, a), acc, win, room) == D.LzoDec{D.LzoLit{Nat.add(Nat.sub(255n, d), a), D.LzoMany{}}, acc, win, room} : D.LzoDec}
      {==}
    case 1n+p:
      match d:
        case 0n:
          %add_succ(p, Nat.add(255n, a)) : {D.dec.go(B.mask(C.ext.ref(1n+p, 0n)), D.LzoDec{D.LzoLitExt{a}, acc, win, room}) == D.LzoDec{D.LzoLit{_, D.LzoMany{}}, acc, win, room} : D.LzoDec}
          ext_run(p, 254n, Nat.add(255n, a), acc, win, room, {==})
        case 1n+q:
          %add_succ(p, Nat.add(Nat.sub(255n, 1n+q), a)) : {D.dec.go(B.mask(C.ext.ref(1n+p, 1n+q)), D.LzoDec{D.LzoLitExt{a}, acc, win, room}) == D.LzoDec{D.LzoLit{_, D.LzoMany{}}, acc, win, room} : D.LzoDec}
          %sub_succ(255n, q, le_up(1n+q, 254n, h)) : {D.dec.go(B.mask(C.ext.ref(1n+p, 1n+q)), D.LzoDec{D.LzoLitExt{a}, acc, win, room}) == D.LzoDec{D.LzoLit{Nat.add(p, Nat.add(_, a)), D.LzoMany{}}, acc, win, room} : D.LzoDec}
          ext_run(p, q, a, acc, win, room, le_pred(254n, q, h))

# the encoder runs the tail-recursive ext.go; it lays down the same bytes as
# the structural ext.ref, which ext_run follows
def ext_go(r: Nat, d: Nat, +k: Nat) -> {C.ext.zeros(k, C.ext.ref(r, d)) == C.ext.go(r, d, k) : List<&2, U32>}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      match d:
        case 0n:
          ext_go(p, 254n, 1n+k)
        case 1n+q:
          ext_go(p, q, k)

def ext_fast(r: Nat, d: Nat) -> {C.ext.ref(r, d) == C.ext.go(r, d, 0n) : List<&2, U32>}:
  ext_go(r, d, 0n)

# the instruction for K + n literals at the start of a stream, the literals,
# and the end marker: the decoder copies them and stops at the marker

def full_18(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(18n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h18(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(18n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      %ext_fast(p, 254n) : {D.dec.go(B.append(B.mask(Con{0, _}), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}
      Equal.trans(D.LzoDec, D.dec.go(B.append(B.mask(C.ext.ref(p, 254n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoLitExt{18n}, acc, win, Nat.add(B.len(ys), k)}), D.dec.go(B.append(ys, [17, 0, 0]), D.LzoDec{D.LzoLit{Nat.add(p, Nat.add(Nat.sub(255n, 254n), 18n)), D.LzoMany{}}, acc, win, Nat.add(B.len(ys), k)}), D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k}, go_app(B.mask(C.ext.ref(p, 254n)), B.append(ys, [17, 0, 0]), D.LzoDec{D.LzoLitExt{18n}, acc, win, Nat.add(B.len(ys), k)}, D.LzoDec{D.LzoLit{Nat.add(p, Nat.add(Nat.sub(255n, 254n), 18n)), D.LzoMany{}}, acc, win, Nat.add(B.len(ys), k)}, ext_run(p, 254n, 18n, acc, win, Nat.add(B.len(ys), k), {==})), after_hdr(Nat.add(p, Nat.add(Nat.sub(255n, 254n), 18n)), D.LzoMany{}, ys, k, acc, win, Equal.trans(Nat, B.len(ys), Nat.add(19n, p), Nat.add(p, 19n), e, add_comm(19n, p))))

def full_17(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(17n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h17(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(17n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_18(p, ys, k, acc, win, e)

def full_16(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(16n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h16(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(16n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_17(p, ys, k, acc, win, e)

def full_15(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(15n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h15(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(15n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_16(p, ys, k, acc, win, e)

def full_14(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(14n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h14(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(14n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_15(p, ys, k, acc, win, e)

def full_13(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(13n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h13(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(13n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_14(p, ys, k, acc, win, e)

def full_12(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(12n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h12(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(12n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_13(p, ys, k, acc, win, e)

def full_11(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(11n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h11(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(11n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_12(p, ys, k, acc, win, e)

def full_10(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(10n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h10(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(10n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_11(p, ys, k, acc, win, e)

def full_9(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(9n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h9(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(9n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_10(p, ys, k, acc, win, e)

def full_8(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(8n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h8(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(8n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_9(p, ys, k, acc, win, e)

def full_7(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(7n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h7(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(7n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_8(p, ys, k, acc, win, e)

def full_6(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(6n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h6(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(6n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_7(p, ys, k, acc, win, e)

def full_5(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(5n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h5(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(5n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_6(p, ys, k, acc, win, e)

def full_4(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(4n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h4(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(4n, D.LzoMany{}, ys, k, acc, win, e)
    case 1n+p:
      full_5(p, ys, k, acc, win, e)

def full_3(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(3n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h3(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(3n, D.LzoFew{}, ys, k, acc, win, e)
    case 1n+p:
      full_4(p, ys, k, acc, win, e)

def full_2(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(2n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h2(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(2n, D.LzoFew{}, ys, k, acc, win, e)
    case 1n+p:
      full_3(p, ys, k, acc, win, e)

def full_1(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(1n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h1(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      after_hdr(1n, D.LzoFew{}, ys, k, acc, win, e)
    case 1n+p:
      full_2(p, ys, k, acc, win, e)

def nil_of_len0(ys: List<&2, U32>) -> {B.len(ys) == 0n : Nat} -> {ys == Nil{} : List<&2, U32>}:
  match ys:
    case Nil{}:
      e => {==}
    case Con{h, t}:
      e => absurd({Con{h, t} == Nil{} : List<&2, U32>}, succ_not_zero(B.len(t), e))

def full_0(+n: Nat, +ys: List<&2, U32>, +k: Nat, +acc: List<&2, U32>, +win: W.LzoWin, e: {B.len(ys) == Nat.add(0n, n) : Nat}) -> {D.dec.go(B.append(B.mask(C.lit.h0(n)), B.append(ys, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(ys), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, acc), wpush(ys, win), k} : D.LzoDec}:
  match n:
    case 0n:
      %Equal.sym(List<&2, U32>, ys, Nil{}, nil_of_len0(ys)(e)) : {D.dec.go(B.append(B.mask(C.lit.h0(0n)), B.append(_, [17, 0, 0])), D.LzoDec{D.LzoIns{D.LzoFirst{}}, acc, win, Nat.add(B.len(_), k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(_, acc), wpush(_, win), k} : D.LzoDec}
      {==}
    case 1n+p:
      full_1(p, ys, k, acc, win, e)

# the literal-only stream for o, decoded with room len(o) + k, stops at its
# end marker with o's bytes written. The bytes come out of Octets through
# bytes' laws octets_append_list, octets_to_of and octets_len_list.
def lits_stream(+o: B.Octets, +k: Nat) -> {D.dec.go(B.Octets.to_list(C.lzo1x_literals(o)), D.dec.start(Nat.add(B.Octets.len(o), k))) == D.LzoDec{D.LzoEnd{}, B.rev_onto(B.Octets.to_list(o), Nil{}), wpush(B.Octets.to_list(o), W.win.empty()), k} : D.LzoDec}:
  +n = B.Octets.len(o)
  +h = C.lit.h0(n)
  +ys = B.Octets.to_list(o)
  +eo = B.Octets.of_list([17, 0, 0])
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(h), B.Octets.append(o, eo))), B.append(B.Octets.to_list(B.Octets.of_list(h)), B.Octets.to_list(B.Octets.append(o, eo))), BL.octets_append_list(B.Octets.of_list(h), B.Octets.append(o, eo))) : {D.dec.go(_, D.dec.start(Nat.add(n, k))) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, Nil{}), wpush(ys, W.win.empty()), k} : D.LzoDec}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(o, eo)), B.append(ys, B.Octets.to_list(eo)), BL.octets_append_list(o, eo)) : {D.dec.go(B.append(B.Octets.to_list(B.Octets.of_list(h)), _), D.dec.start(Nat.add(n, k))) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, Nil{}), wpush(ys, W.win.empty()), k} : D.LzoDec}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(h)), B.mask(h), BL.octets_to_of(h)) : {D.dec.go(B.append(_, B.append(ys, B.Octets.to_list(eo))), D.dec.start(Nat.add(n, k))) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, Nil{}), wpush(ys, W.win.empty()), k} : D.LzoDec}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(eo), B.mask([17, 0, 0]), BL.octets_to_of([17, 0, 0])) : {D.dec.go(B.append(B.mask(h), B.append(ys, _)), D.dec.start(Nat.add(n, k))) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, Nil{}), wpush(ys, W.win.empty()), k} : D.LzoDec}
  %Equal.sym(Nat, n, B.len(ys), BL.octets_len_list(o)) : {D.dec.go(B.append(B.mask(h), B.append(ys, B.mask([17, 0, 0]))), D.LzoDec{D.LzoIns{D.LzoFirst{}}, Nil{}, W.win.empty(), Nat.add(_, k)}) == D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, Nil{}), wpush(ys, W.win.empty()), k} : D.LzoDec}
  full_0(n, ys, k, Nil{}, W.win.empty(), Equal.sym(Nat, n, B.len(ys), BL.octets_len_list(o)))

def lit_round(+o: B.Octets, +k: Nat) -> {D.lzo1x_decompress(C.lzo1x_literals(o), Nat.add(B.Octets.len(o), k)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}:
  +ys = B.Octets.to_list(o)
  %Equal.sym(D.LzoDec, D.dec.go(B.Octets.to_list(C.lzo1x_literals(o)), D.dec.start(Nat.add(B.Octets.len(o), k))), D.LzoDec{D.LzoEnd{}, B.rev_onto(ys, Nil{}), wpush(ys, W.win.empty()), k}, lits_stream(o, k)) : {D.dec.out(D.dec.end(_)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.rev(B.rev(ys)), ys, BL.rev_rev(ys)) : {Done{B.Octets.of_list(_)} == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(ys), o, BL.octets_of_to(o)) : {Done{_} == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  {==}

def lit_round0(+o: B.Octets) -> {D.lzo1x_decompress(C.lzo1x_literals(o), B.Octets.len(o)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}:
  %add_zero(B.Octets.len(o)) : {D.lzo1x_decompress(C.lzo1x_literals(o), _) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  lit_round(o, 0n)

# The compressor's check: when it finds the same bytes, the stream decodes
# to its input

def and_l(p: Bool, q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {p == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, false_not_true(h))

def and_r(p: Bool, q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case True{}:
      h
    case False{}:
      absurd({q == True{} : Bool}, false_not_true(h))

def bit_sound(a: Bool, b: Bool, h: {Bool.not(Bool.xor(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      absurd({True{} == False{} : Bool}, false_not_true(h))
    case False{} True{}:
      absurd({False{} == True{} : Bool}, false_not_true(h))
    case False{} False{}:
      {==}

def weq_sound(+n: Nat, x: Word(n), y: Word(n), +h: {C.enc.weq(n, x, y) == True{} : Bool}) -> {x == y : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match x y:
        case WCon{+a, +s} WCon{+b, +t}:
          %bit_sound(a, b, and_l(Bool.not(Bool.xor(a, b)), C.enc.weq(p, s, t), h)) : {WCon{a, s} == WCon{_, t} : Word(1n+p)}
          %weq_sound(p, s, t, and_r(Bool.not(Bool.xor(a, b)), C.enc.weq(p, s, t), h)) : {WCon{a, s} == WCon{a, _} : Word(1n+p)}
          {==}

def u32_sound(a: U32, b: U32, h: {C.enc.u32_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %weq_sound(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

# the check walks both lists with a flag that the bytes so far agree: if it
# answers True, the flag was True all along
def same_live(xs: List<&2, U32>, ys: List<&2, U32>, +live: Bool, +h: {C.enc.same.go(xs, ys, live) == True{} : Bool}) -> {live == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      h
    case Con{+a, s} Con{+b, t}:
      and_l(live, C.enc.u32_eq(a, b), same_live(s, t, Bool.and(live, C.enc.u32_eq(a, b)), h))
    case Nil{} Con{b, t}:
      absurd({live == True{} : Bool}, false_not_true(h))
    case Con{a, s} Nil{}:
      absurd({live == True{} : Bool}, false_not_true(h))

def same_go_sound(xs: List<&2, U32>, ys: List<&2, U32>, +live: Bool, +h: {C.enc.same.go(xs, ys, live) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Con{+a, +s} Con{+b, +t}:
      %u32_sound(a, b, and_r(live, C.enc.u32_eq(a, b), same_live(s, t, Bool.and(live, C.enc.u32_eq(a, b)), h))) : {Con{a, s} == Con{_, t} : List<&2, U32>}
      %same_go_sound(s, t, Bool.and(live, C.enc.u32_eq(a, b)), h) : {Con{a, s} == Con{a, _} : List<&2, U32>}
      {==}
    case Nil{} Con{b, t}:
      absurd({Nil{} == Con{b, t} : List<&2, U32>}, false_not_true(h))
    case Con{a, s} Nil{}:
      absurd({Con{a, s} == Nil{} : List<&2, U32>}, false_not_true(h))

def same_sound(xs: List<&2, U32>, ys: List<&2, U32>, +h: {C.enc.same(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  same_go_sound(xs, ys, True{}, h)

# the stream c decodes, by the decoder's own answer, to an output whose bytes
# are o's: so lzo1x_decompress gives o back
def keep_ok(b: Bool, +c: B.Octets, +o: B.Octets, +acc: List<&2, U32>, +room: Nat, h: {C.enc.same(B.rev(acc), B.Octets.to_list(o)) == b : Bool}, e: {D.dec.run_list(B.Octets.to_list(c), B.Octets.len(o)) == Done{D.LzoOut{acc, room}} : Result<&2, &2, E.LzoError, D.LzoOut>}) -> {D.lzo1x_decompress(C.enc.keep(b, c, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}:
  match b:
    case True{}:
      %Equal.sym(Result<&2, &2, E.LzoError, D.LzoOut>, D.dec.run_list(B.Octets.to_list(c), B.Octets.len(o)), Done{D.LzoOut{acc, room}}, e) : {D.dec.out(_) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
      %Equal.sym(List<&2, U32>, B.rev(acc), B.Octets.to_list(o), same_sound(B.rev(acc), B.Octets.to_list(o), h)) : {Done{B.Octets.of_list(_)} == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
      %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {Done{_} == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
      {==}
    case False{}:
      lit_round0(o)

def check_ok(r: Result<&2, &2, E.LzoError, D.LzoOut>, +c: B.Octets, +o: B.Octets, e: {D.dec.run_list(B.Octets.to_list(c), B.Octets.len(o)) == r : Result<&2, &2, E.LzoError, D.LzoOut>}) -> {D.lzo1x_decompress(C.enc.check(r, c, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}:
  match r:
    case Fail{x}:
      lit_round0(o)
    case Done{D.LzoOut{+acc, +room}}:
      keep_ok(C.enc.same(B.rev(acc), B.Octets.to_list(o)), c, o, acc, room, {==}, e)

# Truncation and trailing bytes

# a decoder that, given one byte more and anything after, ends in Done, has
# not reached the end marker yet (else the byte is trailing) and has not
# failed (failures absorb): its own end is a cut-short stream
def trunc_d(d: D.LzoDec, +h: U32, +t: List<&2, U32>, -o: B.Octets, e: {D.dec.out(D.dec.end(D.dec.go(Con{h, t}, d))) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}) -> {D.dec.out(D.dec.end(d)) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}:
  match d:
    case D.LzoDec{st, +acc, +win, +room}:
      match st:
        case D.LzoEnd{}:
          absurd({D.dec.out(D.dec.end(D.LzoDec{D.LzoEnd{}, acc, win, room})) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}, absorb_fail(t, E.LzoTrailing{}, acc, win, room, o, e))
        case D.LzoBad{+x}:
          absurd({D.dec.out(D.dec.end(D.LzoDec{D.LzoBad{x}, acc, win, room})) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}, absorb_fail(t, x, acc, win, room, o, e))
        case D.LzoIns{x}:
          {==}
        case D.LzoLitExt{x}:
          {==}
        case D.LzoLit{x, y}:
          {==}
        case D.LzoNear{x, y, z, u, v}:
          {==}
        case D.LzoMatExt{x, y}:
          {==}
        case D.LzoDist{x, y}:
          {==}
        case D.LzoDist2{x, y, z}:
          {==}

# a decoder that ends in Done is at the end marker: one byte more is trailing
def trail_d(d: D.LzoDec, +h: U32, +t: List<&2, U32>, -o: B.Octets, e: {D.dec.out(D.dec.end(d)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}) -> {D.dec.out(D.dec.end(D.dec.go(Con{h, t}, d))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}:
  match d:
    case D.LzoDec{st, +acc, +win, +room}:
      match st:
        case D.LzoEnd{}:
          absorb_out(t, E.LzoTrailing{}, acc, win, room)
        case D.LzoBad{x}:
          absurd({D.dec.out(D.dec.end(D.dec.go(Con{h, t}, D.LzoDec{D.LzoBad{x}, acc, win, room}))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}, fail_not_done(x, o, e))
        case D.LzoIns{x}:
          absurd({D.dec.out(D.dec.end(D.dec.go(Con{h, t}, D.LzoDec{D.LzoIns{x}, acc, win, room}))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}, fail_not_done(E.LzoTruncated{}, o, e))
        case D.LzoLitExt{x}:
          absurd({D.dec.out(D.dec.end(D.dec.go(Con{h, t}, D.LzoDec{D.LzoLitExt{x}, acc, win, room}))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}, fail_not_done(E.LzoTruncated{}, o, e))
        case D.LzoLit{x, y}:
          absurd({D.dec.out(D.dec.end(D.dec.go(Con{h, t}, D.LzoDec{D.LzoLit{x, y}, acc, win, room}))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}, fail_not_done(E.LzoTruncated{}, o, e))
        case D.LzoNear{x, y, z, u, v}:
          absurd({D.dec.out(D.dec.end(D.dec.go(Con{h, t}, D.LzoDec{D.LzoNear{x, y, z, u, v}, acc, win, room}))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}, fail_not_done(E.LzoTruncated{}, o, e))
        case D.LzoMatExt{x, y}:
          absurd({D.dec.out(D.dec.end(D.dec.go(Con{h, t}, D.LzoDec{D.LzoMatExt{x, y}, acc, win, room}))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}, fail_not_done(E.LzoTruncated{}, o, e))
        case D.LzoDist{x, y}:
          absurd({D.dec.out(D.dec.end(D.dec.go(Con{h, t}, D.LzoDec{D.LzoDist{x, y}, acc, win, room}))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}, fail_not_done(E.LzoTruncated{}, o, e))
        case D.LzoDist2{x, y, z}:
          absurd({D.dec.out(D.dec.end(D.dec.go(Con{h, t}, D.LzoDec{D.LzoDist2{x, y, z}, acc, win, room}))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}, fail_not_done(E.LzoTruncated{}, o, e))

# the stream a ++ [h] ++ t, as lists: a's bytes, then h's, then t's
def split_hyp(+a: B.Octets, +h: U32, +t: B.Octets, +max: Nat, -o: B.Octets, e: {D.lzo1x_decompress(B.Octets.append(a, B.Octets.cons(h, t)), max) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}) -> {D.dec.out(D.dec.end(D.dec.go(Con{B.byte(h), B.Octets.to_list(t)}, D.dec.go(B.Octets.to_list(a), D.dec.start(max))))) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}:
  %go_split(B.Octets.to_list(a), Con{B.byte(h), B.Octets.to_list(t)}, D.dec.start(max)) : {D.dec.out(D.dec.end(_)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  %BL.octets_cons_list(h, t) : {D.dec.out(D.dec.end(D.dec.go(B.append(B.Octets.to_list(a), _), D.dec.start(max)))) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  %BL.octets_append_list(a, B.Octets.cons(h, t)) : {D.dec.out(D.dec.end(D.dec.go(_, D.dec.start(max)))) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  e

# The laws

def Laws.output_within_max(src, max):
  fin(D.dec.go(B.Octets.to_list(src), D.dec.start(max)), max, inv_go(B.Octets.to_list(src), D.dec.start(max), max, le_refl(max)))

def Laws.literals_round_trip(o, k):
  lit_round(o, k)

def Laws.compress_round_trip(opts, o):
  check_ok(D.dec.run_list(B.Octets.to_list(C.lzo1x_compress_unchecked(opts, o)), B.Octets.len(o)), C.lzo1x_compress_unchecked(opts, o), o, {==})

def Laws.truncation_rejected(a, h, t, max, o, e):
  trunc_d(D.dec.go(B.Octets.to_list(a), D.dec.start(max)), B.byte(h), B.Octets.to_list(t), o, split_hyp(a, h, t, max, o, e))

def Laws.truncation_rejected_witness():
  (B.Octets.of_list([97]), {==})

def Laws.trailing_rejected(a, h, t, max, o, e):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, B.Octets.cons(h, t))), B.append(B.Octets.to_list(a), B.Octets.to_list(B.Octets.cons(h, t))), BL.octets_append_list(a, B.Octets.cons(h, t))) : {D.dec.out(D.dec.end(D.dec.go(_, D.dec.start(max)))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.cons(h, t)), Con{B.byte(h), B.Octets.to_list(t)}, BL.octets_cons_list(h, t)) : {D.dec.out(D.dec.end(D.dec.go(B.append(B.Octets.to_list(a), _), D.dec.start(max)))) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(D.LzoDec, D.dec.go(B.append(B.Octets.to_list(a), Con{B.byte(h), B.Octets.to_list(t)}), D.dec.start(max)), D.dec.go(Con{B.byte(h), B.Octets.to_list(t)}, D.dec.go(B.Octets.to_list(a), D.dec.start(max))), go_split(B.Octets.to_list(a), Con{B.byte(h), B.Octets.to_list(t)}, D.dec.start(max))) : {D.dec.out(D.dec.end(_)) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}
  trail_d(D.dec.go(B.Octets.to_list(a), D.dec.start(max)), B.byte(h), B.Octets.to_list(t), o, e)

def Laws.trailing_rejected_witness():
  (B.Octets.empty(), {==})

# the first byte 17 (M4, H = 0, length 3), its two distance bytes, and the
# rest: D is not 0, so the match is not the end marker, and nothing is
# before it
def first_m4(+lo: U32, +hi: U32, +rest: List<&2, U32>, +max: Nat, e: {U32.is_lt(lo, 4) == False{} : Bool}) -> {D.dec.out(D.dec.end(D.dec.go(rest, D.dec.apply(D.dec.m4.end(Bool.and(U32.is_lt(lo, 4), U32.is_eq(hi, 0)), 3n, lo, hi), Nil{}, W.win.empty(), max)))) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}:
  %Equal.sym(Bool, U32.is_lt(lo, 4), False{}, e) : {D.dec.out(D.dec.end(D.dec.go(rest, D.dec.apply(D.dec.m4.end(Bool.and(_, U32.is_eq(hi, 0)), 3n, lo, hi), Nil{}, W.win.empty(), max)))) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}
  absorb_out(rest, E.LzoBadDistance{}, Nil{}, W.win.empty(), max)

def Laws.first_match_rejected(lo, hi, rest, max, e):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.cons(17, B.Octets.cons(lo, B.Octets.cons(hi, rest)))), Con{B.byte(17), B.Octets.to_list(B.Octets.cons(lo, B.Octets.cons(hi, rest)))}, BL.octets_cons_list(17, B.Octets.cons(lo, B.Octets.cons(hi, rest)))) : {D.dec.out(D.dec.end(D.dec.go(_, D.dec.start(max)))) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.cons(lo, B.Octets.cons(hi, rest))), Con{B.byte(lo), B.Octets.to_list(B.Octets.cons(hi, rest))}, BL.octets_cons_list(lo, B.Octets.cons(hi, rest))) : {D.dec.out(D.dec.end(D.dec.go(Con{B.byte(17), _}, D.dec.start(max)))) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.cons(hi, rest)), Con{B.byte(hi), B.Octets.to_list(rest)}, BL.octets_cons_list(hi, rest)) : {D.dec.out(D.dec.end(D.dec.go(Con{B.byte(17), Con{B.byte(lo), _}}, D.dec.start(max)))) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}
  first_m4(B.byte(lo), B.byte(hi), B.Octets.to_list(rest), max, e)

def Laws.first_match_rejected_witness():
  (4, {==})

# Streaming: the reader is the one-shot decoder with its output handed out
# piece by piece

# a decoder whose output so far has base under it
def rb(d: D.LzoDec, base: List<&2, U32>) -> D.LzoDec:
  match d:
    case D.LzoDec{st, acc, win, room}:
      D.LzoDec{st, B.append(acc, base), win, room}

def copy_go_rb(n: Nat, room: Nat, +o: Nat, +s: Nat, +acc: List<&2, U32>, +win: W.LzoWin, +base: List<&2, U32>) -> {D.dec.copy.go(n, room, o, s, B.append(acc, base), win) == rb(D.dec.copy.go(n, room, o, s, acc, win), base) : D.LzoDec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match room:
        case 0n:
          {==}
        case 1n+r:
          copy_go_rb(p, r, o, s, Con{W.win.get(win, o), acc}, W.win.put(win, W.win.get(win, o)), base)

def copy_check_rb(ok: Bool, +len: Nat, +o: Nat, +s: Nat, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, +base: List<&2, U32>) -> {D.dec.copy.check(ok, len, o, s, B.append(acc, base), win, room) == rb(D.dec.copy.check(ok, len, o, s, acc, win, room), base) : D.LzoDec}:
  match ok:
    case True{}:
      copy_go_rb(len, room, o, s, acc, win, base)
    case False{}:
      {==}

def copy_at_rb(count: Nat, +o: Nat, +len: Nat, +s: Nat, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, +base: List<&2, U32>) -> {D.dec.copy.at(count, o, len, s, B.append(acc, base), win, room) == rb(D.dec.copy.at(count, o, len, s, acc, win, room), base) : D.LzoDec}:
  match count:
    case 0n:
      {==}
    case 1n+c:
      copy_check_rb(Nat.is_lt(o, 1n+c), len, o, s, acc, win, room, base)

def apply_rb(a: D.LzoAct, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, +base: List<&2, U32>) -> {D.dec.apply(a, B.append(acc, base), win, room) == rb(D.dec.apply(a, acc, win, room), base) : D.LzoDec}:
  match a:
    case D.LzoGo{st}:
      {==}
    case D.LzoPush{h, st}:
      match room:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case D.LzoCopy{o, len, s}:
      copy_at_rb(W.win.count(win), o, len, s, acc, win, room, base)

def step_rb(d: D.LzoDec, +h: U32, +base: List<&2, U32>) -> {D.dec.step(rb(d, base), h) == rb(D.dec.step(d, h), base) : D.LzoDec}:
  match d:
    case D.LzoDec{st, +acc, +win, +room}:
      apply_rb(D.dec.trans(st, h), acc, win, room, base)

def go_rb(xs: List<&2, U32>, +d: D.LzoDec, +base: List<&2, U32>) -> {D.dec.go(xs, rb(d, base)) == rb(D.dec.go(xs, d), base) : D.LzoDec}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(D.LzoDec, D.dec.step(rb(d, base), h), rb(D.dec.step(d, h), base), step_rb(d, h, base)) : {D.dec.go(t, _) == rb(D.dec.go(t, D.dec.step(d, h)), base) : D.LzoDec}
      go_rb(t, D.dec.step(d, h), base)

def absorb_go(zs: List<&2, U32>, +e: E.LzoError, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat) -> {D.dec.go(zs, D.LzoDec{D.LzoBad{e}, acc, win, room}) == D.LzoDec{D.LzoBad{e}, acc, win, room} : D.LzoDec}:
  match zs:
    case Nil{}:
      {==}
    case Con{h, t}:
      absorb_go(t, e, acc, win, room)

# Lists and Octets

def app_assoc(a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {B.append(B.append(a, b), c) == B.append(a, B.append(b, c)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %app_assoc(t, b, c) : {Con{h, B.append(B.append(t, b), c)} == Con{h, _} : List<&2, U32>}
      {==}

def mask_app(a: List<&2, U32>, +b: List<&2, U32>) -> {B.mask(B.append(a, b)) == B.append(B.mask(a), B.mask(b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mask_app(t, b) : {Con{B.byte(h), B.mask(B.append(t, b))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def ro_gen(y: List<&2, U32>, +u: List<&2, U32>, +w: List<&2, U32>) -> {B.rev_onto(y, B.append(u, w)) == B.append(B.rev_onto(y, u), w) : List<&2, U32>}:
  match y:
    case Nil{}:
      {==}
    case Con{h, t}:
      ro_gen(t, Con{h, u}, w)

def ro_split(x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>) -> {B.rev_onto(B.append(x, y), z) == B.rev_onto(y, B.rev_onto(x, z)) : List<&2, U32>}:
  match x:
    case Nil{}:
      {==}
    case Con{h, t}:
      ro_split(t, y, Con{h, z})

def rev_app(+x: List<&2, U32>, +y: List<&2, U32>) -> {B.rev(B.append(x, y)) == B.append(B.rev(y), B.rev(x)) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.rev(B.append(x, y)), B.rev_onto(y, B.rev(x)), B.append(B.rev(y), B.rev(x)), ro_split(x, y, Nil{}), ro_gen(y, Nil{}, B.rev(x)))

# two Octets with the same bytes are the same
def oct_eq(+x: B.Octets, +y: B.Octets, e: {B.Octets.to_list(x) == B.Octets.to_list(y) : List<&2, U32>}) -> {x == y : B.Octets}:
  %BL.octets_of_to(x) : {_ == y : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(x), B.Octets.to_list(y), e) : {B.Octets.of_list(_) == y : B.Octets}
  BL.octets_of_to(y)

# what the reader answers at the end, given the decoder end
def fz(r: Result<&2, &2, E.LzoError, D.LzoOut>, out: B.Octets) -> Result<&2, &2, E.LzoError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{D.LzoOut{acc, room}}:
      Done{B.Octets.append(out, B.Octets.of_list(B.rev(acc)))}

# the bytes of both sides of oct_join
def j_eq(+outo: B.Octets, +acc: List<&2, U32>, +acc0: List<&2, U32>) -> {B.Octets.to_list(B.Octets.append(outo, B.Octets.of_list(B.rev(B.append(acc, acc0))))) == B.Octets.to_list(B.Octets.append(B.Octets.append(outo, B.Octets.of_list(B.rev(acc0))), B.Octets.of_list(B.rev(acc)))) : List<&2, U32>}:
  +lo = B.Octets.to_list(outo)
  +r0 = B.rev(acc0)
  +r1 = B.rev(acc)
  +rhs = B.Octets.to_list(B.Octets.append(B.Octets.append(outo, B.Octets.of_list(r0)), B.Octets.of_list(r1)))
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(outo, B.Octets.of_list(B.rev(B.append(acc, acc0))))), B.append(lo, B.Octets.to_list(B.Octets.of_list(B.rev(B.append(acc, acc0))))), BL.octets_append_list(outo, B.Octets.of_list(B.rev(B.append(acc, acc0))))) : {_ == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.rev(B.append(acc, acc0)))), B.mask(B.rev(B.append(acc, acc0))), BL.octets_to_of(B.rev(B.append(acc, acc0)))) : {B.append(lo, _) == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.rev(B.append(acc, acc0)), B.append(r0, r1), rev_app(acc, acc0)) : {B.append(lo, B.mask(_)) == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(B.append(r0, r1)), B.append(B.mask(r0), B.mask(r1)), mask_app(r0, r1)) : {B.append(lo, _) == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, rhs, B.append(B.Octets.to_list(B.Octets.append(outo, B.Octets.of_list(r0))), B.Octets.to_list(B.Octets.of_list(r1))), BL.octets_append_list(B.Octets.append(outo, B.Octets.of_list(r0)), B.Octets.of_list(r1))) : {B.append(lo, B.append(B.mask(r0), B.mask(r1))) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(outo, B.Octets.of_list(r0))), B.append(lo, B.Octets.to_list(B.Octets.of_list(r0))), BL.octets_append_list(outo, B.Octets.of_list(r0))) : {B.append(lo, B.append(B.mask(r0), B.mask(r1))) == B.append(_, B.Octets.to_list(B.Octets.of_list(r1))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(r0)), B.mask(r0), BL.octets_to_of(r0)) : {B.append(lo, B.append(B.mask(r0), B.mask(r1))) == B.append(B.append(lo, _), B.Octets.to_list(B.Octets.of_list(r1))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(r1)), B.mask(r1), BL.octets_to_of(r1)) : {B.append(lo, B.append(B.mask(r0), B.mask(r1))) == B.append(B.append(lo, B.mask(r0)), _) : List<&2, U32>}
  Equal.sym(List<&2, U32>, B.append(B.append(lo, B.mask(r0)), B.mask(r1)), B.append(lo, B.append(B.mask(r0), B.mask(r1))), app_assoc(lo, B.mask(r0), B.mask(r1)))

def oct_join(+outo: B.Octets, +acc: List<&2, U32>, +acc0: List<&2, U32>) -> {B.Octets.append(outo, B.Octets.of_list(B.rev(B.append(acc, acc0)))) == B.Octets.append(B.Octets.append(outo, B.Octets.of_list(B.rev(acc0))), B.Octets.of_list(B.rev(acc))) : B.Octets}:
  oct_eq(B.Octets.append(outo, B.Octets.of_list(B.rev(B.append(acc, acc0)))), B.Octets.append(B.Octets.append(outo, B.Octets.of_list(B.rev(acc0))), B.Octets.of_list(B.rev(acc))), j_eq(outo, acc, acc0))

def fz_rb(d: D.LzoDec, +acc0: List<&2, U32>, +outo: B.Octets) -> {fz(D.dec.end(rb(d, acc0)), outo) == fz(D.dec.end(d), B.Octets.append(outo, B.Octets.of_list(B.rev(acc0)))) : Result<&2, &2, E.LzoError, B.Octets>}:
  match d:
    case D.LzoDec{st, +acc, +win, +room}:
      match st:
        case D.LzoEnd{}:
          %Equal.sym(B.Octets, B.Octets.append(outo, B.Octets.of_list(B.rev(B.append(acc, acc0)))), B.Octets.append(B.Octets.append(outo, B.Octets.of_list(B.rev(acc0))), B.Octets.of_list(B.rev(acc))), oct_join(outo, acc, acc0)) : {Done{_} == Done{B.Octets.append(B.Octets.append(outo, B.Octets.of_list(B.rev(acc0))), B.Octets.of_list(B.rev(acc)))} : Result<&2, &2, E.LzoError, B.Octets>}
          {==}
        case D.LzoBad{x}:
          {==}
        case D.LzoIns{x}:
          {==}
        case D.LzoLitExt{x}:
          {==}
        case D.LzoLit{x, y}:
          {==}
        case D.LzoNear{x, y, z, u, v}:
          {==}
        case D.LzoMatExt{x, y}:
          {==}
        case D.LzoDist{x, y}:
          {==}
        case D.LzoDist2{x, y, z}:
          {==}

def jl(ps: List<&2, B.Octets>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      B.append(B.Octets.to_list(p), jl(t))

# the last piece: the reader finish is the decoder end
def nil_case(d: D.LzoDec, +outo: B.Octets) -> {D.rd.all(Nil{}, D.rd.fed(d), outo) == fz(D.dec.end(d), outo) : Result<&2, &2, E.LzoError, B.Octets>}:
  match d:
    case D.LzoDec{st, +acc, +win, +room}:
      match st:
        case D.LzoEnd{}:
          {==}
        case D.LzoBad{x}:
          {==}
        case D.LzoIns{x}:
          {==}
        case D.LzoLitExt{x}:
          {==}
        case D.LzoLit{x, y}:
          {==}
        case D.LzoNear{x, y, z, u, v}:
          {==}
        case D.LzoMatExt{x, y}:
          {==}
        case D.LzoDist{x, y}:
          {==}
        case D.LzoDist2{x, y, z}:
          {==}

def reset(d: D.LzoDec) -> D.LzoDec:
  match d:
    case D.LzoDec{st, acc, win, room}:
      D.LzoDec{st, Nil{}, win, room}

def accof(d: D.LzoDec) -> List<&2, U32>:
  match d:
    case D.LzoDec{st, acc, win, room}:
      acc

# a piece, for a decoder that has not failed: what it hands out, then the
# rest of the pieces (ih)
def con_nb(+p: B.Octets, +t: List<&2, B.Octets>, +st: D.LzoSt, +acc: List<&2, U32>, +win: W.LzoWin, +room: Nat, +outo: B.Octets, nb: {D.rd.err(st) == None{} : Maybe<&2, E.LzoError>}, ih: {D.rd.all(t, D.rd.fed(D.dec.go(B.Octets.to_list(p), D.LzoDec{st, Nil{}, win, room})), B.Octets.append(outo, B.Octets.of_list(B.rev(acc)))) == fz(D.dec.end(D.dec.go(jl(t), D.dec.go(B.Octets.to_list(p), D.LzoDec{st, Nil{}, win, room}))), B.Octets.append(outo, B.Octets.of_list(B.rev(acc)))) : Result<&2, &2, E.LzoError, B.Octets>}) -> {D.rd.all(Con{p, t}, D.rd.fed(D.LzoDec{st, acc, win, room}), outo) == fz(D.dec.end(D.dec.go(B.append(B.Octets.to_list(p), jl(t)), D.LzoDec{st, acc, win, room})), outo) : Result<&2, &2, E.LzoError, B.Octets>}:
  +lp = B.Octets.to_list(p)
  +d0 = {D.LzoDec{st, Nil{}, win, room} : D.LzoDec}
  +x = D.dec.go(jl(t), D.dec.go(lp, d0))
  +o2 = B.Octets.append(outo, B.Octets.of_list(B.rev(acc)))
  %Equal.sym(Maybe<&2, E.LzoError>, D.rd.err(st), None{}, nb) : {D.rd.all(Con{p, t}, D.rd.fed.pick(_, st, acc, win, room), outo) == fz(D.dec.end(D.dec.go(B.append(lp, jl(t)), D.LzoDec{st, acc, win, room})), outo) : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(D.LzoDec, D.dec.go(B.append(lp, jl(t)), rb(d0, acc)), rb(D.dec.go(B.append(lp, jl(t)), d0), acc), go_rb(B.append(lp, jl(t)), d0, acc)) : {D.rd.all(t, D.rd.fed(D.dec.go(lp, d0)), o2) == fz(D.dec.end(_), outo) : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(D.LzoDec, D.dec.go(B.append(lp, jl(t)), d0), x, go_split(lp, jl(t), d0)) : {D.rd.all(t, D.rd.fed(D.dec.go(lp, d0)), o2) == fz(D.dec.end(rb(_, acc)), outo) : Result<&2, &2, E.LzoError, B.Octets>}
  %Equal.sym(Result<&2, &2, E.LzoError, B.Octets>, fz(D.dec.end(rb(x, acc)), outo), fz(D.dec.end(x), o2), fz_rb(x, acc, outo)) : {D.rd.all(t, D.rd.fed(D.dec.go(lp, d0)), o2) == _ : Result<&2, &2, E.LzoError, B.Octets>}
  ih

def con_case(+p: B.Octets, +t: List<&2, B.Octets>, d: D.LzoDec, +outo: B.Octets, ih: {D.rd.all(t, D.rd.fed(D.dec.go(B.Octets.to_list(p), reset(d))), B.Octets.append(outo, B.Octets.of_list(B.rev(accof(d))))) == fz(D.dec.end(D.dec.go(jl(t), D.dec.go(B.Octets.to_list(p), reset(d)))), B.Octets.append(outo, B.Octets.of_list(B.rev(accof(d))))) : Result<&2, &2, E.LzoError, B.Octets>}) -> {D.rd.all(Con{p, t}, D.rd.fed(d), outo) == fz(D.dec.end(D.dec.go(B.append(B.Octets.to_list(p), jl(t)), d)), outo) : Result<&2, &2, E.LzoError, B.Octets>}:
  match d:
    case D.LzoDec{st, +acc, +win, +room}:
      match st:
        case D.LzoBad{+x}:
          %Equal.sym(D.LzoDec, D.dec.go(B.append(B.Octets.to_list(p), jl(t)), D.LzoDec{D.LzoBad{x}, acc, win, room}), D.LzoDec{D.LzoBad{x}, acc, win, room}, absorb_go(B.append(B.Octets.to_list(p), jl(t)), x, acc, win, room)) : {D.rd.all(Con{p, t}, D.rd.fed(D.LzoDec{D.LzoBad{x}, acc, win, room}), outo) == fz(D.dec.end(_), outo) : Result<&2, &2, E.LzoError, B.Octets>}
          {==}
        case D.LzoEnd{}:
          con_nb(p, t, D.LzoEnd{}, acc, win, room, outo, {==}, ih)
        case D.LzoIns{+x}:
          con_nb(p, t, D.LzoIns{x}, acc, win, room, outo, {==}, ih)
        case D.LzoLitExt{+x}:
          con_nb(p, t, D.LzoLitExt{x}, acc, win, room, outo, {==}, ih)
        case D.LzoLit{+x, +y}:
          con_nb(p, t, D.LzoLit{x, y}, acc, win, room, outo, {==}, ih)
        case D.LzoNear{+x, +y, +z, +u, +v}:
          con_nb(p, t, D.LzoNear{x, y, z, u, v}, acc, win, room, outo, {==}, ih)
        case D.LzoMatExt{+x, +y}:
          con_nb(p, t, D.LzoMatExt{x, y}, acc, win, room, outo, {==}, ih)
        case D.LzoDist{+x, +y}:
          con_nb(p, t, D.LzoDist{x, y}, acc, win, room, outo, {==}, ih)
        case D.LzoDist2{+x, +y, +z}:
          con_nb(p, t, D.LzoDist2{x, y, z}, acc, win, room, outo, {==}, ih)

def stream_b(+ps: List<&2, B.Octets>, +d: D.LzoDec, +outo: B.Octets) -> {D.rd.all(ps, D.rd.fed(d), outo) == fz(D.dec.end(D.dec.go(jl(ps), d)), outo) : Result<&2, &2, E.LzoError, B.Octets>}:
  match ps:
    case Nil{}:
      nil_case(d, outo)
    case Con{+p, t}:
      con_case(p, t, d, outo, stream_b(t, D.dec.go(B.Octets.to_list(p), reset(d)), B.Octets.append(outo, B.Octets.of_list(B.rev(accof(d))))))

def join_list(+ps: List<&2, B.Octets>) -> {B.Octets.to_list(Laws.LzoLaws.join(ps)) == jl(ps) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, t}:
      %join_list(t) : {B.Octets.to_list(B.Octets.append(p, Laws.LzoLaws.join(t))) == B.append(B.Octets.to_list(p), _) : List<&2, U32>}
      BL.octets_append_list(p, Laws.LzoLaws.join(t))

def fz_empty(r: Result<&2, &2, E.LzoError, D.LzoOut>) -> {fz(r, B.Octets.empty()) == D.dec.out(r) : Result<&2, &2, E.LzoError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{D.LzoOut{+acc, room}}:
      %Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), B.Octets.of_list(B.rev(acc))), B.Octets.of_list(B.rev(acc)), oct_eq(B.Octets.append(B.Octets.empty(), B.Octets.of_list(B.rev(acc))), B.Octets.of_list(B.rev(acc)), BL.octets_append_list(B.Octets.empty(), B.Octets.of_list(B.rev(acc))))) : {Done{_} == Done{B.Octets.of_list(B.rev(acc))} : Result<&2, &2, E.LzoError, B.Octets>}
      {==}

def Laws.reader_pieces(max, ps):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(Laws.LzoLaws.join(ps)), jl(ps), join_list(ps)) : {D.reader_decompress(max, ps) == D.dec.out(D.dec.end(D.dec.go(_, D.dec.start(max)))) : Result<&2, &2, E.LzoError, B.Octets>}
  Equal.trans(Result<&2, &2, E.LzoError, B.Octets>, D.reader_decompress(max, ps), fz(D.dec.end(D.dec.go(jl(ps), D.dec.start(max))), B.Octets.empty()), D.dec.out(D.dec.end(D.dec.go(jl(ps), D.dec.start(max)))), stream_b(ps, D.dec.start(max), B.Octets.empty()), fz_empty(D.dec.end(D.dec.go(jl(ps), D.dec.start(max)))))

# Adler-32: running over a ++ b is running over a, then over b

def adl_split(xs: List<&2, U32>, +ys: List<&2, U32>, s: A.Adler32) -> {A.adl.go(B.append(xs, ys), s) == A.adl.go(ys, A.adl.go(xs, s)) : A.Adler32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      match s:
        case A.Adler32{+a, +b}:
          adl_split(t, ys, A.Adler32{A.adl.mod(U32.add(a, h)), A.adl.mod(U32.add(b, A.adl.mod(U32.add(a, h))))})

def Laws.adler32_pieces(s, a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {A.adl.go(_, s) == A.adl.go(B.Octets.to_list(b), A.adl.go(B.Octets.to_list(a), s)) : A.Adler32}
  adl_split(B.Octets.to_list(a), B.Octets.to_list(b), s)

# Vectors: proved by computation

def Laws.end_marker_only():
  {==}

def Laws.first_byte_one_literal():
  {==}

def Laws.first_byte_four_literals():
  {==}

def Laws.first_byte_238_literals():
  {==}

def Laws.long_literal_run():
  {==}

def Laws.literal_length_bytes():
  {==}

def Laws.m1_after_few_literals():
  {==}

def Laws.m1_overlap():
  {==}

def Laws.m1_after_many_literals():
  {==}

def Laws.m2_three_bytes():
  {==}

def Laws.m2_six_bytes():
  {==}

def Laws.m3_with_trailing_literals():
  {==}

def Laws.literal_run_after_match():
  {==}

def Laws.m3_overlap():
  {==}

def Laws.m3_length_bytes():
  {==}

def Laws.end_marker_with_length():
  {==}

def Laws.empty_input():
  {==}

def Laws.missing_end_marker():
  {==}

def Laws.cut_in_literals():
  {==}

def Laws.cut_in_distance():
  {==}

def Laws.cut_in_length_bytes():
  {==}

def Laws.distance_past_start():
  {==}

def Laws.first_m4():
  {==}

def Laws.output_limit_match():
  {==}

def Laws.output_limit_literals():
  {==}

def Laws.trailing_byte():
  {==}

def Laws.reader_three_pieces():
  {==}

def Laws.reader_cut_short():
  {==}

def Laws.entry_round_trip():
  {==}

def Laws.entry_limit():
  {==}

def Laws.literals_short():
  {==}

def Laws.literals_length_bytes():
  {==}

def Laws.compress_empty():
  {==}

def Laws.compress_run():
  {==}

def Laws.compress_text():
  {==}

def Laws.adler32_empty():
  {==}

def Laws.adler32_wikipedia():
  {==}

def Laws.lzop_two_blocks():
  {==}

def Laws.lzop_header_fields():
  {==}

def Laws.lzop_every_checksum():
  {==}

def Laws.lzop_bad_header_checksum():
  {==}

def Laws.lzop_bad_block_checksum():
  {==}

def Laws.lzop_unverified():
  {==}

def Laws.lzop_bad_magic():
  {==}

def Laws.lzop_filter_unsupported():
  {==}

def Laws.lzop_bad_method():
  {==}

def Laws.lzop_old_version():
  {==}

def Laws.lzop_block_larger():
  {==}

def Laws.lzop_trailing():
  {==}

def Laws.lzop_cut_short():
  {==}

def Laws.lzop_write_empty():
  {==}

def Laws.lzop_write_every_checksum():
  {==}

def Laws.lzop_stream_round_trip():
  {==}
