import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./block.bend as K
import ./frame.bend as F
import ./lz4.bend as L
import ./compress.bend as C
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

# The properties follow the block decoder byte by byte. Each lemma below is
# about the decoder's internals (block.bend), never stated as a law. Octets
# enter only through bytes' interface laws (octets_append_list, octets_to_of,
# octets_of_to, octets_len_list), never through how Octets stores its bytes;
# only the vectors compute on concrete Octets.

# Arithmetic on Nat

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

def sub_succ(n: Nat, q: Nat, h: {Nat.is_le(1n+q, n) == True{} : Bool}) -> {Nat.sub(n, q) == 1n+Nat.sub(n, 1n+q) : Nat}:
  match n q:
    case 0n _:
      absurd({Nat.sub(0n, q) == 1n+Nat.sub(0n, 1n+q) : Nat}, false_not_true(h))
    case 1n+m 0n:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, sub_zero(m)) : {1n+m == 1n+_ : Nat}
      {==}
    case 1n+m 1n+r:
      sub_succ(m, r, h)

# Lists

def append_nil(xs: List<&2, U32>) -> {B.append(xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %append_nil(t) : {Con{h, B.append(t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def drop_nil(o: Nat) -> {B.drop(o, Nil{}) == Nil{} : List<&2, U32>}:
  match o:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the decoder pushes its bytes onto a reversed list: reversing it again gives
# them in order, masked
def rev_push(ys: List<&2, U32>, acc: List<&2, U32>, zs: List<&2, U32>) -> {List.reverse.go(&2, U32, K.blk.push(ys, acc), zs) == List.reverse.go(&2, U32, acc, B.append(B.mask(ys), zs)) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_push(t, Con{B.byte(h), acc}, zs)

def rev_push_nil(+ys: List<&2, U32>) -> {K.blk.rev(K.blk.push(ys, Nil{})) == B.mask(ys) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, K.blk.rev(K.blk.push(ys, Nil{})), B.append(B.mask(ys), Nil{}), B.mask(ys), rev_push(ys, Nil{}, Nil{}), append_nil(B.mask(ys)))

# The decoder: running over a ++ b is running over a, then over b

def go_split(a: List<&2, U32>, b: List<&2, U32>, d: K.Lz4Dec) -> {K.blk.go(B.append(a, b), d) == K.blk.go(b, K.blk.go(a, d)) : K.Lz4Dec}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      go_split(t, b, K.blk.step(d, h))

def go_app(+a: List<&2, U32>, +b: List<&2, U32>, +d: K.Lz4Dec, -d2: K.Lz4Dec, e: {K.blk.go(a, d) == d2 : K.Lz4Dec}) -> {K.blk.go(B.append(a, b), d) == K.blk.go(b, d2) : K.Lz4Dec}:
  %e : {K.blk.go(B.append(a, b), d) == K.blk.go(b, _) : K.Lz4Dec}
  go_split(a, b, d)

# a failure stays a failure, whatever follows
def bad_absorbs(zs: List<&2, U32>, +e: K.Lz4Error) -> {K.blk.go(zs, K.blk.bad(e)) == K.blk.bad(e) : K.Lz4Dec}:
  match zs:
    case Nil{}:
      {==}
    case Con{h, t}:
      bad_absorbs(t, e)

# a first match finds no byte to copy, at every offset
def copy_nil(off: Nat, +len: Nat, +room: Nat) -> {K.blk.copy(off, len, Nil{}, room) == K.blk.bad(K.Lz4BadOffset{}) : K.Lz4Dec}:
  match off:
    case 0n:
      {==}
    case 1n+o:
      %Equal.sym(List<&2, U32>, B.drop(o, Nil{}), Nil{}, drop_nil(o)) : {K.blk.copy.check(Maybe.is_some(&2, U32, B.at.head(_)), len, o, Nil{}, room) == K.blk.bad(K.Lz4BadOffset{}) : K.Lz4Dec}
      {==}

# literals: n of them copy n bytes
def lit_run(ys: List<&2, U32>, +total: Nat, acc: List<&2, U32>, k: Nat, +last: Nat) -> {K.blk.go(ys, K.Lz4Dec{K.Lz4Lit{B.len(ys), total, 0}, acc, Nat.add(B.len(ys), k), last}) == K.Lz4Dec{K.Lz4Lit{0n, total, 0}, K.blk.push(ys, acc), k, last} : K.Lz4Dec}:
  match ys:
    case Nil{}:
      {==}
    case Con{h, t}:
      lit_run(t, total, Con{B.byte(h), acc}, k, last)

# The literal-only encoder's length bytes, as the decoder reads them. The
# last length byte 254 - d reads as 254 - d (and not 255): one lemma per d,
# down to the d past 254 where the byte is 0.

def cl_255(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(255n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(255n, q))} : K.Lz4Ext}:
  {==}

def cl_254(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(254n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(254n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_255(r)

def cl_253(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(253n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(253n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_254(r)

def cl_252(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(252n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(252n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_253(r)

def cl_251(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(251n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(251n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_252(r)

def cl_250(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(250n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(250n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_251(r)

def cl_249(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(249n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(249n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_250(r)

def cl_248(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(248n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(248n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_249(r)

def cl_247(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(247n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(247n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_248(r)

def cl_246(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(246n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(246n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_247(r)

def cl_245(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(245n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(245n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_246(r)

def cl_244(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(244n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(244n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_245(r)

def cl_243(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(243n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(243n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_244(r)

def cl_242(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(242n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(242n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_243(r)

def cl_241(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(241n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(241n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_242(r)

def cl_240(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(240n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(240n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_241(r)

def cl_239(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(239n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(239n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_240(r)

def cl_238(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(238n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(238n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_239(r)

def cl_237(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(237n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(237n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_238(r)

def cl_236(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(236n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(236n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_237(r)

def cl_235(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(235n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(235n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_236(r)

def cl_234(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(234n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(234n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_235(r)

def cl_233(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(233n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(233n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_234(r)

def cl_232(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(232n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(232n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_233(r)

def cl_231(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(231n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(231n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_232(r)

def cl_230(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(230n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(230n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_231(r)

def cl_229(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(229n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(229n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_230(r)

def cl_228(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(228n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(228n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_229(r)

def cl_227(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(227n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(227n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_228(r)

def cl_226(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(226n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(226n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_227(r)

def cl_225(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(225n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(225n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_226(r)

def cl_224(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(224n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(224n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_225(r)

def cl_223(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(223n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(223n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_224(r)

def cl_222(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(222n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(222n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_223(r)

def cl_221(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(221n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(221n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_222(r)

def cl_220(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(220n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(220n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_221(r)

def cl_219(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(219n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(219n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_220(r)

def cl_218(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(218n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(218n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_219(r)

def cl_217(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(217n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(217n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_218(r)

def cl_216(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(216n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(216n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_217(r)

def cl_215(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(215n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(215n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_216(r)

def cl_214(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(214n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(214n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_215(r)

def cl_213(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(213n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(213n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_214(r)

def cl_212(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(212n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(212n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_213(r)

def cl_211(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(211n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(211n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_212(r)

def cl_210(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(210n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(210n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_211(r)

def cl_209(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(209n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(209n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_210(r)

def cl_208(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(208n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(208n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_209(r)

def cl_207(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(207n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(207n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_208(r)

def cl_206(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(206n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(206n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_207(r)

def cl_205(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(205n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(205n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_206(r)

def cl_204(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(204n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(204n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_205(r)

def cl_203(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(203n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(203n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_204(r)

def cl_202(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(202n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(202n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_203(r)

def cl_201(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(201n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(201n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_202(r)

def cl_200(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(200n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(200n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_201(r)

def cl_199(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(199n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(199n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_200(r)

def cl_198(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(198n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(198n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_199(r)

def cl_197(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(197n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(197n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_198(r)

def cl_196(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(196n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(196n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_197(r)

def cl_195(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(195n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(195n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_196(r)

def cl_194(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(194n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(194n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_195(r)

def cl_193(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(193n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(193n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_194(r)

def cl_192(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(192n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(192n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_193(r)

def cl_191(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(191n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(191n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_192(r)

def cl_190(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(190n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(190n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_191(r)

def cl_189(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(189n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(189n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_190(r)

def cl_188(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(188n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(188n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_189(r)

def cl_187(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(187n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(187n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_188(r)

def cl_186(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(186n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(186n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_187(r)

def cl_185(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(185n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(185n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_186(r)

def cl_184(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(184n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(184n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_185(r)

def cl_183(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(183n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(183n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_184(r)

def cl_182(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(182n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(182n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_183(r)

def cl_181(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(181n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(181n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_182(r)

def cl_180(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(180n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(180n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_181(r)

def cl_179(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(179n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(179n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_180(r)

def cl_178(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(178n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(178n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_179(r)

def cl_177(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(177n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(177n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_178(r)

def cl_176(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(176n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(176n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_177(r)

def cl_175(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(175n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(175n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_176(r)

def cl_174(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(174n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(174n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_175(r)

def cl_173(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(173n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(173n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_174(r)

def cl_172(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(172n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(172n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_173(r)

def cl_171(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(171n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(171n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_172(r)

def cl_170(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(170n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(170n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_171(r)

def cl_169(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(169n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(169n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_170(r)

def cl_168(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(168n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(168n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_169(r)

def cl_167(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(167n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(167n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_168(r)

def cl_166(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(166n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(166n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_167(r)

def cl_165(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(165n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(165n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_166(r)

def cl_164(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(164n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(164n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_165(r)

def cl_163(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(163n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(163n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_164(r)

def cl_162(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(162n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(162n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_163(r)

def cl_161(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(161n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(161n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_162(r)

def cl_160(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(160n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(160n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_161(r)

def cl_159(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(159n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(159n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_160(r)

def cl_158(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(158n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(158n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_159(r)

def cl_157(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(157n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(157n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_158(r)

def cl_156(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(156n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(156n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_157(r)

def cl_155(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(155n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(155n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_156(r)

def cl_154(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(154n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(154n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_155(r)

def cl_153(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(153n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(153n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_154(r)

def cl_152(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(152n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(152n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_153(r)

def cl_151(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(151n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(151n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_152(r)

def cl_150(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(150n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(150n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_151(r)

def cl_149(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(149n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(149n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_150(r)

def cl_148(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(148n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(148n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_149(r)

def cl_147(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(147n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(147n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_148(r)

def cl_146(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(146n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(146n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_147(r)

def cl_145(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(145n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(145n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_146(r)

def cl_144(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(144n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(144n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_145(r)

def cl_143(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(143n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(143n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_144(r)

def cl_142(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(142n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(142n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_143(r)

def cl_141(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(141n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(141n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_142(r)

def cl_140(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(140n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(140n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_141(r)

def cl_139(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(139n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(139n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_140(r)

def cl_138(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(138n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(138n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_139(r)

def cl_137(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(137n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(137n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_138(r)

def cl_136(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(136n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(136n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_137(r)

def cl_135(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(135n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(135n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_136(r)

def cl_134(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(134n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(134n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_135(r)

def cl_133(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(133n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(133n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_134(r)

def cl_132(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(132n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(132n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_133(r)

def cl_131(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(131n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(131n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_132(r)

def cl_130(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(130n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(130n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_131(r)

def cl_129(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(129n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(129n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_130(r)

def cl_128(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(128n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(128n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_129(r)

def cl_127(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(127n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(127n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_128(r)

def cl_126(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(126n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(126n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_127(r)

def cl_125(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(125n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(125n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_126(r)

def cl_124(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(124n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(124n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_125(r)

def cl_123(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(123n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(123n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_124(r)

def cl_122(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(122n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(122n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_123(r)

def cl_121(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(121n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(121n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_122(r)

def cl_120(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(120n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(120n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_121(r)

def cl_119(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(119n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(119n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_120(r)

def cl_118(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(118n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(118n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_119(r)

def cl_117(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(117n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(117n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_118(r)

def cl_116(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(116n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(116n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_117(r)

def cl_115(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(115n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(115n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_116(r)

def cl_114(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(114n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(114n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_115(r)

def cl_113(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(113n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(113n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_114(r)

def cl_112(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(112n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(112n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_113(r)

def cl_111(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(111n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(111n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_112(r)

def cl_110(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(110n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(110n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_111(r)

def cl_109(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(109n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(109n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_110(r)

def cl_108(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(108n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(108n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_109(r)

def cl_107(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(107n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(107n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_108(r)

def cl_106(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(106n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(106n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_107(r)

def cl_105(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(105n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(105n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_106(r)

def cl_104(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(104n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(104n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_105(r)

def cl_103(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(103n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(103n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_104(r)

def cl_102(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(102n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(102n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_103(r)

def cl_101(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(101n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(101n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_102(r)

def cl_100(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(100n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(100n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_101(r)

def cl_99(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(99n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(99n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_100(r)

def cl_98(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(98n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(98n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_99(r)

def cl_97(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(97n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(97n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_98(r)

def cl_96(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(96n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(96n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_97(r)

def cl_95(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(95n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(95n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_96(r)

def cl_94(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(94n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(94n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_95(r)

def cl_93(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(93n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(93n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_94(r)

def cl_92(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(92n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(92n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_93(r)

def cl_91(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(91n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(91n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_92(r)

def cl_90(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(90n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(90n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_91(r)

def cl_89(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(89n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(89n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_90(r)

def cl_88(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(88n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(88n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_89(r)

def cl_87(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(87n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(87n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_88(r)

def cl_86(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(86n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(86n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_87(r)

def cl_85(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(85n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(85n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_86(r)

def cl_84(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(84n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(84n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_85(r)

def cl_83(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(83n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(83n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_84(r)

def cl_82(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(82n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(82n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_83(r)

def cl_81(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(81n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(81n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_82(r)

def cl_80(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(80n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(80n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_81(r)

def cl_79(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(79n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(79n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_80(r)

def cl_78(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(78n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(78n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_79(r)

def cl_77(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(77n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(77n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_78(r)

def cl_76(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(76n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(76n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_77(r)

def cl_75(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(75n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(75n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_76(r)

def cl_74(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(74n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(74n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_75(r)

def cl_73(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(73n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(73n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_74(r)

def cl_72(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(72n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(72n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_73(r)

def cl_71(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(71n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(71n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_72(r)

def cl_70(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(70n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(70n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_71(r)

def cl_69(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(69n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(69n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_70(r)

def cl_68(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(68n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(68n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_69(r)

def cl_67(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(67n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(67n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_68(r)

def cl_66(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(66n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(66n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_67(r)

def cl_65(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(65n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(65n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_66(r)

def cl_64(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(64n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(64n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_65(r)

def cl_63(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(63n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(63n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_64(r)

def cl_62(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(62n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(62n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_63(r)

def cl_61(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(61n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(61n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_62(r)

def cl_60(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(60n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(60n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_61(r)

def cl_59(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(59n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(59n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_60(r)

def cl_58(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(58n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(58n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_59(r)

def cl_57(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(57n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(57n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_58(r)

def cl_56(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(56n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(56n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_57(r)

def cl_55(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(55n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(55n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_56(r)

def cl_54(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(54n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(54n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_55(r)

def cl_53(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(53n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(53n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_54(r)

def cl_52(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(52n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(52n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_53(r)

def cl_51(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(51n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(51n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_52(r)

def cl_50(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(50n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(50n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_51(r)

def cl_49(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(49n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(49n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_50(r)

def cl_48(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(48n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(48n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_49(r)

def cl_47(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(47n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(47n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_48(r)

def cl_46(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(46n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(46n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_47(r)

def cl_45(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(45n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(45n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_46(r)

def cl_44(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(44n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(44n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_45(r)

def cl_43(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(43n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(43n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_44(r)

def cl_42(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(42n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(42n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_43(r)

def cl_41(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(41n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(41n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_42(r)

def cl_40(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(40n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(40n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_41(r)

def cl_39(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(39n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(39n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_40(r)

def cl_38(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(38n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(38n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_39(r)

def cl_37(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(37n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(37n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_38(r)

def cl_36(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(36n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(36n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_37(r)

def cl_35(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(35n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(35n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_36(r)

def cl_34(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(34n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(34n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_35(r)

def cl_33(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(33n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(33n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_34(r)

def cl_32(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(32n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(32n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_33(r)

def cl_31(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(31n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(31n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_32(r)

def cl_30(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(30n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(30n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_31(r)

def cl_29(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(29n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(29n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_30(r)

def cl_28(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(28n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(28n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_29(r)

def cl_27(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(27n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(27n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_28(r)

def cl_26(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(26n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(26n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_27(r)

def cl_25(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(25n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(25n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_26(r)

def cl_24(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(24n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(24n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_25(r)

def cl_23(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(23n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(23n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_24(r)

def cl_22(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(22n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(22n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_23(r)

def cl_21(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(21n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(21n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_22(r)

def cl_20(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(20n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(20n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_21(r)

def cl_19(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(19n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(19n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_20(r)

def cl_18(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(18n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(18n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_19(r)

def cl_17(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(17n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(17n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_18(r)

def cl_16(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(16n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(16n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_17(r)

def cl_15(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(15n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(15n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_16(r)

def cl_14(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(14n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(14n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_15(r)

def cl_13(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(13n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(13n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_14(r)

def cl_12(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(12n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(12n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_13(r)

def cl_11(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(11n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(11n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_12(r)

def cl_10(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(10n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(10n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_11(r)

def cl_9(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(9n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(9n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_10(r)

def cl_8(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(8n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(8n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_9(r)

def cl_7(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(7n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(7n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_8(r)

def cl_6(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(6n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(6n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_7(r)

def cl_5(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(5n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(5n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_6(r)

def cl_4(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(4n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(4n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_5(r)

def cl_3(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(3n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(3n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_4(r)

def cl_2(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(2n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(2n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_3(r)

def cl_1(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(1n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(1n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_2(r)

def cl_0(q: Nat) -> {K.blk.ext(B.byte(K.lit.last(Nat.add(0n, q)))) == K.Lz4Last{Nat.sub(254n, Nat.add(0n, q))} : K.Lz4Ext}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      cl_1(r)

def classify_last(+d: Nat) -> {K.blk.ext(B.byte(K.lit.last(d))) == K.Lz4Last{Nat.sub(254n, d)} : K.Lz4Ext}:
  cl_0(d)

# the length bytes after a nibble of 15 add up to the literal count: r more,
# from a byte with room d (d <= 254), on top of a
def ext_run(+r: Nat, +d: Nat, +a: Nat, +m: U32, +acc: List<&2, U32>, +room: Nat, +last: Nat, +h: {Nat.is_le(d, 254n) == True{} : Bool}) -> {K.blk.go(B.mask(K.lit.ext(r, d)), K.Lz4Dec{K.Lz4LitExt{a, m}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(r, Nat.add(Nat.sub(254n, d), a)), Nat.add(r, Nat.add(Nat.sub(254n, d), a)), m}, acc, room, last} : K.Lz4Dec}:
  match r:
    case 0n:
      %Equal.sym(K.Lz4Ext, K.blk.ext(B.byte(K.lit.last(d))), K.Lz4Last{Nat.sub(254n, d)}, classify_last(d)) : {K.blk.litext(_, a, m, acc, room, last) == K.Lz4Dec{K.Lz4Lit{Nat.add(Nat.sub(254n, d), a), Nat.add(Nat.sub(254n, d), a), m}, acc, room, last} : K.Lz4Dec}
      {==}
    case 1n+p:
      match d:
        case 0n:
          %add_succ(p, Nat.add(254n, a)) : {K.blk.go(B.mask(K.lit.ext(1n+p, 0n)), K.Lz4Dec{K.Lz4LitExt{a, m}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{_, _, m}, acc, room, last} : K.Lz4Dec}
          ext_run(p, 254n, Nat.add(255n, a), m, acc, room, last, {==})
        case 1n+q:
          %add_succ(p, Nat.add(Nat.sub(254n, 1n+q), a)) : {K.blk.go(B.mask(K.lit.ext(1n+p, 1n+q)), K.Lz4Dec{K.Lz4LitExt{a, m}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{_, _, m}, acc, room, last} : K.Lz4Dec}
          %sub_succ(254n, q, h) : {K.blk.go(B.mask(K.lit.ext(1n+p, 1n+q)), K.Lz4Dec{K.Lz4LitExt{a, m}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(p, Nat.add(_, a)), Nat.add(p, Nat.add(_, a)), m}, acc, room, last} : K.Lz4Dec}
          ext_run(p, q, a, m, acc, room, last, le_pred(254n, q, h))

# the token and length bytes for K + n literals leave the decoder copying
# K + n literals

def hd_14(+n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h14(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(14n, n), Nat.add(14n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_comm(p, 15n) : {K.blk.go(B.mask(K.lit.h14(1n+p)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{_, _, 0}, acc, room, last} : K.Lz4Dec}
      ext_run(p, 254n, 15n, 0, acc, room, last, {==})

def hd_13(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h13(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(13n, n), Nat.add(13n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_14(p, acc, room, last)

def hd_12(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h12(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(12n, n), Nat.add(12n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_13(p, acc, room, last)

def hd_11(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h11(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(11n, n), Nat.add(11n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_12(p, acc, room, last)

def hd_10(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h10(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(10n, n), Nat.add(10n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_11(p, acc, room, last)

def hd_9(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h9(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(9n, n), Nat.add(9n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_10(p, acc, room, last)

def hd_8(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h8(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(8n, n), Nat.add(8n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_9(p, acc, room, last)

def hd_7(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h7(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(7n, n), Nat.add(7n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_8(p, acc, room, last)

def hd_6(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h6(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(6n, n), Nat.add(6n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_7(p, acc, room, last)

def hd_5(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h5(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(5n, n), Nat.add(5n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_6(p, acc, room, last)

def hd_4(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h4(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(4n, n), Nat.add(4n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_5(p, acc, room, last)

def hd_3(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h3(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(3n, n), Nat.add(3n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_4(p, acc, room, last)

def hd_2(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h2(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(2n, n), Nat.add(2n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_3(p, acc, room, last)

def hd_1(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h1(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(1n, n), Nat.add(1n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_2(p, acc, room, last)

def hd_0(n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat) -> {K.blk.go(B.mask(K.lit.h0(n)), K.Lz4Dec{K.Lz4Tok{}, acc, room, last}) == K.Lz4Dec{K.Lz4Lit{Nat.add(0n, n), Nat.add(0n, n), 0}, acc, room, last} : K.Lz4Dec}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hd_1(p, acc, room, last)

# lit_run, with the literal count given as any n equal to the list's length
def lit_run_n(+ys: List<&2, U32>, +n: Nat, +total: Nat, +acc: List<&2, U32>, +k: Nat, +last: Nat, e: {B.len(ys) == n : Nat}) -> {K.blk.go(ys, K.Lz4Dec{K.Lz4Lit{n, total, 0}, acc, Nat.add(n, k), last}) == K.Lz4Dec{K.Lz4Lit{0n, total, 0}, K.blk.push(ys, acc), k, last} : K.Lz4Dec}:
  %e : {K.blk.go(ys, K.Lz4Dec{K.Lz4Lit{_, total, 0}, acc, Nat.add(_, k), last}) == K.Lz4Dec{K.Lz4Lit{0n, total, 0}, K.blk.push(ys, acc), k, last} : K.Lz4Dec}
  lit_run(ys, total, acc, k, last)

# block_literals(o), decoded with room len(o) + k, stops after its literals
# with them all copied. The bytes come out of Octets through bytes' laws
# octets_append_list, octets_to_of and octets_len_list.
def lits_run_h(+o: B.Octets, +k: Nat, +hs: List<&2, U32>) -> {K.blk.go(B.Octets.to_list(K.block_literals(o)), K.Lz4Dec{K.Lz4Tok{}, hs, Nat.add(B.Octets.len(o), k), 0n}) == K.Lz4Dec{K.Lz4Lit{0n, B.Octets.len(o), 0}, K.blk.push(B.Octets.to_list(o), hs), k, 0n} : K.Lz4Dec}:
  +n = B.Octets.len(o)
  +h = K.lit.h0(n)
  +ys = B.Octets.to_list(o)
  +room = Nat.add(n, k)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(h), o)), B.append(B.Octets.to_list(B.Octets.of_list(h)), ys), BL.octets_append_list(B.Octets.of_list(h), o)) : {K.blk.go(_, K.Lz4Dec{K.Lz4Tok{}, hs, room, 0n}) == K.Lz4Dec{K.Lz4Lit{0n, n, 0}, K.blk.push(ys, hs), k, 0n} : K.Lz4Dec}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(h)), B.mask(h), BL.octets_to_of(h)) : {K.blk.go(B.append(_, ys), K.Lz4Dec{K.Lz4Tok{}, hs, room, 0n}) == K.Lz4Dec{K.Lz4Lit{0n, n, 0}, K.blk.push(ys, hs), k, 0n} : K.Lz4Dec}
  Equal.trans(K.Lz4Dec, K.blk.go(B.append(B.mask(h), ys), K.Lz4Dec{K.Lz4Tok{}, hs, room, 0n}), K.blk.go(ys, K.Lz4Dec{K.Lz4Lit{n, n, 0}, hs, room, 0n}), K.Lz4Dec{K.Lz4Lit{0n, n, 0}, K.blk.push(ys, hs), k, 0n}, go_app(B.mask(h), ys, K.Lz4Dec{K.Lz4Tok{}, hs, room, 0n}, K.Lz4Dec{K.Lz4Lit{n, n, 0}, hs, room, 0n}, hd_0(n, hs, room, 0n)), lit_run_n(ys, n, n, hs, k, 0n, Equal.sym(Nat, n, B.len(ys), BL.octets_len_list(o))))

def lits_run(+o: B.Octets, +k: Nat) -> {K.blk.go(B.Octets.to_list(K.block_literals(o)), K.Lz4Dec{K.Lz4Tok{}, Nil{}, Nat.add(B.Octets.len(o), k), 0n}) == K.Lz4Dec{K.Lz4Lit{0n, B.Octets.len(o), 0}, K.blk.push(B.Octets.to_list(o), Nil{}), k, 0n} : K.Lz4Dec}:
  lits_run_h(o, k, Nil{})

# The output bound: the output so far plus the room left never grows past
# the maximum, through every step of the decoder

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

def len_mask(xs: List<&2, U32>) -> {B.len(B.mask(xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %len_mask(t) : {1n+B.len(B.mask(t)) == 1n+_ : Nat}
      {==}

def len_rev(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.len(List.reverse.go(&2, U32, xs, acc)) == Nat.add(B.len(xs), B.len(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %add_succ(B.len(t), B.len(acc)) : {B.len(List.reverse.go(&2, U32, t, Con{h, acc})) == _ : Nat}
      len_rev(t, Con{h, acc})

def len_rev_nil(+xs: List<&2, U32>) -> {B.len(K.blk.rev(xs)) == B.len(xs) : Nat}:
  Equal.trans(Nat, B.len(K.blk.rev(xs)), Nat.add(B.len(xs), 0n), B.len(xs), len_rev(xs, Nil{}), add_zero(B.len(xs)))

def Inv(d: K.Lz4Dec, c: Nat) -> Type:
  match d:
    case K.Lz4Dec{st, acc, room, last}:
      {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}

def inv_bad(+e: K.Lz4Error, +c: Nat) -> Inv(K.blk.bad(e), c):
  le_zero(c)

# a byte moved from the room to the output
def inv_push(+acc: List<&2, U32>, +r: Nat, +b: U32, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), 1n+r), c) == True{} : Bool}) -> {Nat.is_le(Nat.add(B.len({Con{b, acc} : List<&2, U32>}), r), c) == True{} : Bool}:
  %add_succ(B.len(acc), r) : {Nat.is_le(_, c) == True{} : Bool}
  i

def inv_copy_go(n: Nat, +room: Nat, +o: Nat, +acc: List<&2, U32>, +last: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(K.blk.copy.go(n, room, o, acc, last), c):
  match n:
    case 0n:
      i
    case 1n+p:
      match room:
        case 0n:
          inv_bad(K.Lz4OutputTooLarge{}, c)
        case 1n+r:
          inv_copy_go(p, r, o, Con{Maybe.default(&2, U32, B.at(acc, o), 0), acc}, last, c, inv_push(acc, r, Maybe.default(&2, U32, B.at(acc, o), 0), c, i))

def inv_copy_check(ok: Bool, +len: Nat, +o: Nat, +acc: List<&2, U32>, +room: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(K.blk.copy.check(ok, len, o, acc, room), c):
  match ok:
    case True{}:
      inv_copy_go(len, room, o, acc, len, c, i)
    case False{}:
      inv_bad(K.Lz4BadOffset{}, c)

def inv_copy(+off: Nat, +len: Nat, +acc: List<&2, U32>, +room: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(K.blk.copy(off, len, acc, room), c):
  match off:
    case 0n:
      inv_bad(K.Lz4BadOffset{}, c)
    case 1n+o:
      inv_copy_check(Maybe.is_some(&2, U32, B.at(acc, o)), len, o, acc, room, c, i)

def inv_tok_pick(more: Bool, +l: U32, +m: U32, +acc: List<&2, U32>, +room: Nat, +last: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(K.blk.tok.pick(more, l, m, acc, room, last), c):
  match more:
    case True{}:
      i
    case False{}:
      i

def inv_litext(e: K.Lz4Ext, +n: Nat, +m: U32, +acc: List<&2, U32>, +room: Nat, +last: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(K.blk.litext(e, n, m, acc, room, last), c):
  match e:
    case K.Lz4Full{}:
      i
    case K.Lz4Last{v}:
      i

def inv_lit(n: Nat, +room: Nat, +total: Nat, +m: U32, +h: U32, +acc: List<&2, U32>, +last: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(K.blk.lit(n, room, total, m, h, acc, last), c):
  match n:
    case 0n:
      i
    case 1n+p:
      match room:
        case 0n:
          inv_bad(K.Lz4OutputTooLarge{}, c)
        case 1n+r:
          inv_push(acc, r, B.byte(h), c, i)

def inv_off_pick(more: Bool, +off: Nat, +m: U32, +acc: List<&2, U32>, +room: Nat, +last: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(K.blk.off.pick(more, off, m, acc, room, last), c):
  match more:
    case True{}:
      i
    case False{}:
      inv_copy(off, Nat.add(U32.to_nat(m), 4n), acc, room, c, i)

def inv_matext(e: K.Lz4Ext, +off: Nat, +n: Nat, +acc: List<&2, U32>, +room: Nat, +last: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> Inv(K.blk.matext(e, off, n, acc, room, last), c):
  match e:
    case K.Lz4Full{}:
      i
    case K.Lz4Last{v}:
      inv_copy(off, Nat.add(v, n), acc, room, c, i)

def inv_step(d: K.Lz4Dec, +h: U32, +c: Nat, i: Inv(d, c)) -> Inv(K.blk.step(d, h), c):
  match d:
    case K.Lz4Dec{st, +acc, +room, +last}:
      match st:
        case K.Lz4Tok{}:
          inv_tok_pick(U32.is_eq(U32.shrn(B.byte(h), 4n), 15), U32.shrn(B.byte(h), 4n), U32.and(B.byte(h), 15), acc, room, last, c, i)
        case K.Lz4LitExt{n, m}:
          inv_litext(K.blk.ext(h), n, m, acc, room, last, c, i)
        case K.Lz4Lit{n, total, m}:
          inv_lit(n, room, total, m, h, acc, last, c, i)
        case K.Lz4Off{lo, +m}:
          inv_off_pick(U32.is_eq(m, 15), U32.to_nat(U32.or(lo, U32.shln(B.byte(h), 8n))), m, acc, room, last, c, i)
        case K.Lz4MatExt{off, n}:
          inv_matext(K.blk.ext(h), off, n, acc, room, last, c, i)
        case K.Lz4Bad{e}:
          inv_bad(e, c)

def inv_go(+xs: List<&2, U32>, +d: K.Lz4Dec, +c: Nat, i: Inv(d, c)) -> Inv(K.blk.go(xs, d), c):
  match xs:
    case Nil{}:
      i
    case Con{h, t}:
      inv_go(t, K.blk.step(d, h), c, inv_step(d, h, c, i))

def fin_pick(ok: Bool, +acc: List<&2, U32>, +room: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> {Nat.is_le(B.Octets.len(Result.default(&2, &2, K.Lz4Error, B.Octets, K.blk.out(0n, K.blk.end.pick(ok, acc, room)), B.Octets.empty())), c) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(K.blk.rev(acc))), B.len(B.Octets.to_list(B.Octets.of_list(K.blk.rev(acc)))), BL.octets_len_list(B.Octets.of_list(K.blk.rev(acc)))) : {Nat.is_le(_, c) == True{} : Bool}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(K.blk.rev(acc))), B.mask(K.blk.rev(acc)), BL.octets_to_of(K.blk.rev(acc))) : {Nat.is_le(B.len(_), c) == True{} : Bool}
      %Equal.sym(Nat, B.len(B.mask(K.blk.rev(acc))), B.len(K.blk.rev(acc)), len_mask(K.blk.rev(acc))) : {Nat.is_le(_, c) == True{} : Bool}
      %Equal.sym(Nat, B.len(K.blk.rev(acc)), B.len(acc), len_rev_nil(acc)) : {Nat.is_le(_, c) == True{} : Bool}
      le_add(B.len(acc), room, c, i)
    case False{}:
      le_zero(c)

def fin_lit(n: Nat, +total: Nat, +m: U32, +acc: List<&2, U32>, +room: Nat, +last: Nat, +c: Nat, i: {Nat.is_le(Nat.add(B.len(acc), room), c) == True{} : Bool}) -> {Nat.is_le(B.Octets.len(Result.default(&2, &2, K.Lz4Error, B.Octets, K.blk.out(0n, K.blk.end.lit(n, total, m, acc, room, last)), B.Octets.empty())), c) == True{} : Bool}:
  match n:
    case 0n:
      fin_pick(Bool.and(U32.is_eq(m, 0), K.blk.end.ok(last, total)), acc, room, c, i)
    case 1n+p:
      le_zero(c)

# what the decoder answers, after any input, is no longer than the maximum
def fin(d: K.Lz4Dec, +c: Nat, i: Inv(d, c)) -> {Nat.is_le(B.Octets.len(Result.default(&2, &2, K.Lz4Error, B.Octets, K.blk.out(0n, K.blk.end(d)), B.Octets.empty())), c) == True{} : Bool}:
  match d:
    case K.Lz4Dec{st, +acc, +room, +last}:
      match st:
        case K.Lz4Tok{}:
          le_zero(c)
        case K.Lz4LitExt{n, m}:
          le_zero(c)
        case K.Lz4Lit{n, total, m}:
          fin_lit(n, total, m, acc, room, last, c, i)
        case K.Lz4Off{lo, m}:
          le_zero(c)
        case K.Lz4MatExt{off, n}:
          le_zero(c)
        case K.Lz4Bad{e}:
          le_zero(c)

# The laws

def Laws.output_within_max(src, max):
  fin(K.blk.go(B.Octets.to_list(src), K.Lz4Dec{K.Lz4Tok{}, Nil{}, max, 0n}), max, inv_go(B.Octets.to_list(src), K.Lz4Dec{K.Lz4Tok{}, Nil{}, max, 0n}, max, le_refl(max)))

def lit_round(+o: B.Octets, +k: Nat) -> {K.block_decompress(K.block_literals(o), Nat.add(B.Octets.len(o), k)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}:
  +ys = B.Octets.to_list(o)
  %Equal.sym(K.Lz4Dec, K.blk.go(B.Octets.to_list(K.block_literals(o)), K.Lz4Dec{K.Lz4Tok{}, Nil{}, Nat.add(B.Octets.len(o), k), 0n}), K.Lz4Dec{K.Lz4Lit{0n, B.Octets.len(o), 0}, K.blk.push(ys, Nil{}), k, 0n}, lits_run(o, k)) : {K.blk.out(0n, K.blk.end(_)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(List<&2, U32>, K.blk.rev(K.blk.push(ys, Nil{})), B.mask(ys), rev_push_nil(ys)) : {Done{B.Octets.of_list(_)} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %BL.octets_to_of(ys) : {Done{B.Octets.of_list(_)} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(ys))), B.Octets.of_list(ys), BL.octets_of_to(B.Octets.of_list(ys))) : {Done{_} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(ys), o, BL.octets_of_to(o)) : {Done{_} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  {==}

def lit_round0(+o: B.Octets) -> {K.block_decompress(K.block_literals(o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}:
  %add_zero(B.Octets.len(o)) : {K.block_decompress(K.block_literals(o), _) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  lit_round(o, 0n)

# After a dictionary: the literals land on top of it, and the block's own
# bytes are what follows it

def rev_rev(dl: List<&2, U32>, acc: List<&2, U32>, z: List<&2, U32>) -> {List.reverse.go(&2, U32, List.reverse.go(&2, U32, dl, acc), z) == List.reverse.go(&2, U32, acc, B.append(dl, z)) : List<&2, U32>}:
  match dl:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_rev(t, Con{h, acc}, z)

def drop_app(dl: List<&2, U32>, +m: List<&2, U32>) -> {B.drop(B.len(dl), B.append(dl, m)) == m : List<&2, U32>}:
  match dl:
    case Nil{}:
      {==}
    case Con{h, t}:
      drop_app(t, m)

def rev_push_dict(+ys: List<&2, U32>, +dl: List<&2, U32>) -> {K.blk.rev(K.blk.push(ys, K.blk.rev(dl))) == B.append(dl, B.mask(ys)) : List<&2, U32>}:
  %append_nil(B.mask(ys)) : {K.blk.rev(K.blk.push(ys, K.blk.rev(dl))) == B.append(dl, _) : List<&2, U32>}
  Equal.trans(List<&2, U32>, K.blk.rev(K.blk.push(ys, K.blk.rev(dl))), List.reverse.go(&2, U32, K.blk.rev(dl), B.append(B.mask(ys), Nil{})), B.append(dl, B.append(B.mask(ys), Nil{})), rev_push(ys, K.blk.rev(dl), Nil{}), rev_rev(dl, Nil{}, B.append(B.mask(ys), Nil{})))

def lit_round_dict(+dict: B.Octets, +o: B.Octets, +k: Nat) -> {K.block_decompress_dict(dict, K.block_literals(o), Nat.add(B.Octets.len(o), k)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}:
  +dl = B.Octets.to_list(dict)
  +ys = B.Octets.to_list(o)
  %Equal.sym(K.Lz4Dec, K.blk.go(B.Octets.to_list(K.block_literals(o)), K.Lz4Dec{K.Lz4Tok{}, K.blk.rev(dl), Nat.add(B.Octets.len(o), k), 0n}), K.Lz4Dec{K.Lz4Lit{0n, B.Octets.len(o), 0}, K.blk.push(ys, K.blk.rev(dl)), k, 0n}, lits_run_h(o, k, K.blk.rev(dl))) : {K.blk.out(B.Octets.len(dict), K.blk.end(_)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(List<&2, U32>, K.blk.rev(K.blk.push(ys, K.blk.rev(dl))), B.append(dl, B.mask(ys)), rev_push_dict(ys, dl)) : {Done{B.Octets.of_list(B.drop(B.Octets.len(dict), _))} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(Nat, B.Octets.len(dict), B.len(dl), BL.octets_len_list(dict)) : {Done{B.Octets.of_list(B.drop(_, B.append(dl, B.mask(ys))))} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.drop(B.len(dl), B.append(dl, B.mask(ys))), B.mask(ys), drop_app(dl, B.mask(ys))) : {Done{B.Octets.of_list(_)} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %BL.octets_to_of(ys) : {Done{B.Octets.of_list(_)} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(ys))), B.Octets.of_list(ys), BL.octets_of_to(B.Octets.of_list(ys))) : {Done{_} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(ys), o, BL.octets_of_to(o)) : {Done{_} == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  {==}

def lit_round_dict0(+dict: B.Octets, +o: B.Octets) -> {K.block_decompress_dict(dict, K.block_literals(o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}:
  %add_zero(B.Octets.len(o)) : {K.block_decompress_dict(dict, K.block_literals(o), _) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}
  lit_round_dict(dict, o, 0n)

# The compressor's check: equal bytes mean equal Octets

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

def weq_sound(+n: Nat, x: Word(n), y: Word(n), +h: {C.cmp.weq(n, x, y) == True{} : Bool}) -> {x == y : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match x y:
        case WCon{+a, +s} WCon{+b, +t}:
          %bit_sound(a, b, and_l(Bool.not(Bool.xor(a, b)), C.cmp.weq(p, s, t), h)) : {WCon{a, s} == WCon{_, t} : Word(1n+p)}
          %weq_sound(p, s, t, and_r(Bool.not(Bool.xor(a, b)), C.cmp.weq(p, s, t), h)) : {WCon{a, s} == WCon{a, _} : Word(1n+p)}
          {==}

def u32_sound(a: U32, b: U32, h: {C.cmp.u32_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %weq_sound(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

def same_sound(xs: List<&2, U32>, ys: List<&2, U32>, +h: {C.cmp.same(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Con{+a, +s} Con{+b, +t}:
      %u32_sound(a, b, and_l(C.cmp.u32_eq(a, b), C.cmp.same(s, t), h)) : {Con{a, s} == Con{_, t} : List<&2, U32>}
      %same_sound(s, t, and_r(C.cmp.u32_eq(a, b), C.cmp.same(s, t), h)) : {Con{a, s} == Con{a, _} : List<&2, U32>}
      {==}
    case Nil{} Con{b, t}:
      absurd({Nil{} == Con{b, t} : List<&2, U32>}, false_not_true(h))
    case Con{a, s} Nil{}:
      absurd({Con{a, s} == Nil{} : List<&2, U32>}, false_not_true(h))

def eq_of_lists(+d: B.Octets, +o: B.Octets, h: {B.Octets.to_list(d) == B.Octets.to_list(o) : List<&2, U32>}) -> {d == o : B.Octets}:
  %BL.octets_of_to(d) : {_ == o : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(d), B.Octets.to_list(o), h) : {B.Octets.of_list(_) == o : B.Octets}
  BL.octets_of_to(o)

def keep_ok(b: Bool, +c: B.Octets, +o: B.Octets, +d: B.Octets, h: {C.cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)) == b : Bool}, e: {K.block_decompress(c, B.Octets.len(o)) == Done{d} : Result<&2, &2, K.Lz4Error, B.Octets>}) -> {K.block_decompress(C.cmp.keep(b, c, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}:
  match b:
    case True{}:
      %eq_of_lists(d, o, same_sound(B.Octets.to_list(d), B.Octets.to_list(o), h)) : {K.block_decompress(c, B.Octets.len(o)) == Done{_} : Result<&2, &2, K.Lz4Error, B.Octets>}
      e
    case False{}:
      lit_round0(o)

def check_ok(r: Result<&2, &2, K.Lz4Error, B.Octets>, +c: B.Octets, +o: B.Octets, e: {K.block_decompress(c, B.Octets.len(o)) == r : Result<&2, &2, K.Lz4Error, B.Octets>}) -> {K.block_decompress(C.cmp.check(r, c, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}:
  match r:
    case Fail{x}:
      lit_round0(o)
    case Done{+d}:
      keep_ok(C.cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)), c, o, d, {==}, e)

def keep_ok_dict(b: Bool, +dict: B.Octets, +c: B.Octets, +o: B.Octets, +d: B.Octets, h: {C.cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)) == b : Bool}, e: {K.block_decompress_dict(dict, c, B.Octets.len(o)) == Done{d} : Result<&2, &2, K.Lz4Error, B.Octets>}) -> {K.block_decompress_dict(dict, C.cmp.keep(b, c, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}:
  match b:
    case True{}:
      %eq_of_lists(d, o, same_sound(B.Octets.to_list(d), B.Octets.to_list(o), h)) : {K.block_decompress_dict(dict, c, B.Octets.len(o)) == Done{_} : Result<&2, &2, K.Lz4Error, B.Octets>}
      e
    case False{}:
      lit_round_dict0(dict, o)

def check_ok_dict(r: Result<&2, &2, K.Lz4Error, B.Octets>, +dict: B.Octets, +c: B.Octets, +o: B.Octets, e: {K.block_decompress_dict(dict, c, B.Octets.len(o)) == r : Result<&2, &2, K.Lz4Error, B.Octets>}) -> {K.block_decompress_dict(dict, C.cmp.check_dict(r, c, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}:
  match r:
    case Fail{x}:
      lit_round_dict0(dict, o)
    case Done{+d}:
      keep_ok_dict(C.cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)), dict, c, o, d, {==}, e)

def Laws.literals_round_trip(xs, k):
  lit_round(B.Octets.of_list(xs), k)

def Laws.literals_round_trip_dict(dict, o, k):
  lit_round_dict(dict, o, k)

def Laws.block_compress_round_trip(o):
  check_ok(K.block_decompress(C.block_compress_unchecked(o), B.Octets.len(o)), C.block_compress_unchecked(o), o, {==})

def Laws.block_compress_dict_round_trip(dict, o):
  check_ok_dict(K.block_decompress_dict(dict, B.Octets.of_list(C.cmp.block(B.Octets.to_list(dict), B.Octets.to_list(o))), B.Octets.len(o)), dict, B.Octets.of_list(C.cmp.block(B.Octets.to_list(dict), B.Octets.to_list(o))), o, {==})

def Laws.offset_zero_rejected(xs, k, rest):
  +o = B.Octets.of_list(xs)
  +bl = K.block_literals(o)
  +z = B.Octets.of_list([0, 0])
  +d0 = {K.Lz4Dec{K.Lz4Tok{}, Nil{}, Nat.add(B.Octets.len(o), k), 0n} : K.Lz4Dec}
  +dl = {K.Lz4Dec{K.Lz4Lit{0n, B.Octets.len(o), 0}, K.blk.push(B.Octets.to_list(o), Nil{}), k, 0n} : K.Lz4Dec}
  +tail = B.append(B.Octets.to_list(z), B.Octets.to_list(rest))
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(bl, B.Octets.append(z, rest))), B.append(B.Octets.to_list(bl), B.Octets.to_list(B.Octets.append(z, rest))), BL.octets_append_list(bl, B.Octets.append(z, rest))) : {K.blk.out(0n, K.blk.end(K.blk.go(_, d0))) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(z, rest)), tail, BL.octets_append_list(z, rest)) : {K.blk.out(0n, K.blk.end(K.blk.go(B.append(B.Octets.to_list(bl), _), d0))) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(K.Lz4Dec, K.blk.go(B.append(B.Octets.to_list(bl), tail), d0), K.blk.go(tail, dl), go_app(B.Octets.to_list(bl), tail, d0, dl, lits_run(o, k))) : {K.blk.out(0n, K.blk.end(_)) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(z), B.mask([0, 0]), BL.octets_to_of([0, 0])) : {K.blk.out(0n, K.blk.end(K.blk.go(B.append(_, B.Octets.to_list(rest)), dl))) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(K.Lz4Dec, K.blk.go(B.Octets.to_list(rest), K.blk.bad(K.Lz4BadOffset{})), K.blk.bad(K.Lz4BadOffset{}), bad_absorbs(B.Octets.to_list(rest), K.Lz4BadOffset{})) : {K.blk.out(0n, K.blk.end(_)) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  {==}

def Laws.offset_before_start_rejected(lo, hi, rest, max):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list([0, lo, hi]), rest)), B.append(B.Octets.to_list(B.Octets.of_list([0, lo, hi])), B.Octets.to_list(rest)), BL.octets_append_list(B.Octets.of_list([0, lo, hi]), rest)) : {K.blk.out(0n, K.blk.end(K.blk.go(_, K.Lz4Dec{K.Lz4Tok{}, Nil{}, max, 0n}))) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([0, lo, hi])), B.mask([0, lo, hi]), BL.octets_to_of([0, lo, hi])) : {K.blk.out(0n, K.blk.end(K.blk.go(B.append(_, B.Octets.to_list(rest)), K.Lz4Dec{K.Lz4Tok{}, Nil{}, max, 0n}))) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(K.Lz4Dec, K.blk.copy(U32.to_nat(U32.or(B.byte(B.byte(lo)), U32.shln(B.byte(B.byte(hi)), 8n))), 4n, Nil{}, max), K.blk.bad(K.Lz4BadOffset{}), copy_nil(U32.to_nat(U32.or(B.byte(B.byte(lo)), U32.shln(B.byte(B.byte(hi)), 8n))), 4n, max)) : {K.blk.out(0n, K.blk.end(K.blk.go(B.Octets.to_list(rest), _))) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  %Equal.sym(K.Lz4Dec, K.blk.go(B.Octets.to_list(rest), K.blk.bad(K.Lz4BadOffset{})), K.blk.bad(K.Lz4BadOffset{}), bad_absorbs(B.Octets.to_list(rest), K.Lz4BadOffset{})) : {K.blk.out(0n, K.blk.end(_)) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}
  {==}

# Vectors: proved by computation

def Laws.spec_length_48():
  {==}

def Laws.spec_length_280():
  {==}

def Laws.spec_length_15():
  {==}

def Laws.empty_block():
  {==}

def Laws.no_token():
  {==}

def Laws.overlapping_match():
  {==}

def Laws.long_match():
  {==}

def Laws.output_limit():
  {==}

def Laws.offset_zero():
  {==}

def Laws.offset_past_start():
  {==}

def Laws.cut_in_literals():
  {==}

def Laws.cut_in_offset():
  {==}

def Laws.cut_in_length():
  {==}

def Laws.length_past_input():
  {==}

def Laws.last_literals_short():
  {==}

def Laws.last_token_has_match():
  {==}

def Laws.last_match_too_close():
  {==}

def Laws.dict_match():
  {==}

def Laws.empty_frame():
  {==}

def Laws.frame_with_checksums():
  {==}

def Laws.frame_uncompressed():
  {==}

def Laws.skippable_then_frame():
  {==}

def Laws.two_frames():
  {==}

def Laws.empty_stream():
  {==}

def Laws.bad_magic():
  {==}

def Laws.bad_version():
  {==}

def Laws.reserved_bd():
  {==}

def Laws.bad_header_checksum():
  {==}

def Laws.bad_content_checksum():
  {==}

def Laws.bad_block_checksum():
  {==}

def Laws.bad_content_size():
  {==}

def Laws.block_too_large():
  {==}

def Laws.frame_cut_short():
  {==}

def Laws.header_info():
  {==}

def Laws.frame_then_rest():
  {==}

def Laws.unverified():
  {==}

def Laws.stream_limit():
  {==}

def Laws.compress_empty():
  {==}

def Laws.compress_like_the_tool():
  {==}

def Laws.compress_run():
  {==}

def Laws.frame_round_trip_linked():
  {==}

def Laws.frame_round_trip_stream():
  {==}

def Laws.frame_round_trip_text():
  {==}
