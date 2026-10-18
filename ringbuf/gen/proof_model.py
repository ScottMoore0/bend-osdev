#!/usr/bin/env python3
"""Generates the part of ringbuf/PROOF.bend that proves the model laws and
the relation between the Array ring and the model: everything from the line
"# Lists and Nat, for the model" up to the line "# The Array ring's
elements, through bend-osdev-array" (or the end), whose lemma signatures
repeat long hypotheses. The part of PROOF.bend above the first line is
written by hand, and the part from the second on is gen/proof_elems.py's;
both are kept as they are.

Run from anywhere: python3 gen/proof_model.py rewrites ../PROOF.bend; with
--check it only reports whether the file is up to date (exit 1 if not).
"""
import os, sys
RU = "Result<&2, &2, R.RingError, Unit>"
R32 = "Result<&2, &2, R.RingError, U32>"
L = "List<&2, U32>"
LEN = "List.length(&2, U32, %s)"
HV = "+h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}"
HC = "ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}"
HL = "el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}"
HLp = "+" + HL
MATCH = "  match r m:\n    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:\n"
li = LEN % "items"
P = []
def d(s):
    P.append(s.strip("\n") + "\n")

d("""
# Lists and Nat, for the model

def nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def nat.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => nat.pred(n), 1n+a, 1n+b, e)

def nat.min_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({0n == 1n+ap : Nat}, absurd.ft(e))
    case 1n+ +ap 1n+ +bp:
      %nat.min_le(ap, bp, e) : {1n+Nat.min(ap, bp) == 1n+_ : Nat}
      {==}

def nat.min_le_l(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nat.min_le_l(ap, bp)

def nat.min_le_r(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n +bb:
      nat.le_zero(bb)
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nat.min_le_r(ap, bp)

# l <= c and k <= c - l: l + k <= c
def nat.add_le_sub(l: Nat, -k: Nat, c: Nat, e: {Nat.is_le(l, c) == True{} : Bool}, f: {Nat.is_le(k, Nat.sub(c, l)) == True{} : Bool}) -> {Nat.is_le(Nat.add(l, k), c) == True{} : Bool}:
  match l c:
    case 0n +cc:
      %nat.sub_zero(cc) : {Nat.is_le(k, _) == True{} : Bool}
      f
    case 1n+lp 0n:
      Empty.absurd({Nat.is_le(1n+Nat.add(lp, k), 0n) == True{} : Bool}, absurd.ft(e))
    case 1n+lp 1n+cp:
      nat.add_le_sub(lp, k, cp, e, f)

def list.take_all(xs: List<&2, U32>) -> {List.take(&2, U32, xs, List.length(&2, U32, xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %list.take_all(t) : {Con{h, List.take(&2, U32, t, List.length(&2, U32, t))} == Con{h, _} : List<&2, U32>}
      {==}

def list.length_take(xs: List<&2, U32>, n: Nat) -> {List.length(&2, U32, List.take(&2, U32, xs, n)) == Nat.min(n, List.length(&2, U32, xs)) : Nat}:
  match xs n:
    case Nil{} +nn:
      Equal.sym(Nat, Nat.min(nn, 0n), 0n, nat.min_zero_r(nn))
    case Con{h, t} 0n:
      {==}
    case Con{h, +t} 1n+ +p:
      %list.length_take(t, p) : {1n+List.length(&2, U32, List.take(&2, U32, t, p)) == 1n+_ : Nat}
      {==}

def list.length_drop_le(xs: List<&2, U32>, n: Nat) -> {Nat.is_le(List.length(&2, U32, List.drop(&2, U32, xs, n)), List.length(&2, U32, xs)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{h, +t} 0n:
      nat.le_refl(List.length(&2, U32, t))
    case Con{h, +t} 1n+ +p:
      +lt = List.length(&2, U32, t)
      nat.le_trans(List.length(&2, U32, List.drop(&2, U32, t, p)), lt, 1n+lt, list.length_drop_le(t, p), nat.le_succ(lt, lt, nat.le_refl(lt)))

def list.length_append(a: List<&2, U32>, +b: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, a, b)) == Nat.add(List.length(&2, U32, a), List.length(&2, U32, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %list.length_append(t, b) : {1n+List.length(&2, U32, List.append(&2, U32, t, b)) == 1n+_ : Nat}
      {==}

# The model
""")

ISF = "Nat.is_eq(%s, cap)" % li
for name, concl, tbody, fbody, extra in [
    ("mo.push_items", "{M.model.items(Pair.fst(M.RingModel, %s, M.model.push.go(c, cap, items, x))) == List.append(&2, U32, items, Con{x, Nil{}}) : %s}" % (RU, L), None, "{==}", "e: {%s == False{} : Bool}" % ISF),
    ("mo.push_done", "{Pair.snd(M.RingModel, %s, M.model.push.go(c, cap, items, x)) == Done{Unit{}} : %s}" % (RU, RU), None, "{==}", "e: {%s == False{} : Bool}" % ISF),
]:
    d("""
def %s(c: Bool, -cap: Nat, -items: %s, -x: U32, ec: {%s == c : Bool}, %s) -> %s:
  match c:
    case True{}:
      bool.contra(%s, %s, ec, e)
    case False{}:
      %s
""" % (name, L, ISF, extra, concl, ISF, concl.replace("(c,", "(True{},"), fbody))

FULLC = "{M.model.push.go(c, cap, items, x) == (M.RingModel{cap, items}, Fail{R.RingFull{}}) : M.RingModel & %s}" % RU
d("""
def mo.push_full(c: Bool, -cap: Nat, -items: %s, -x: U32, ec: {%s == c : Bool}, e: {%s == True{} : Bool}) -> %s:
  match c:
    case True{}:
      {==}
    case False{}:
      bool.contra(%s, %s, e, ec)
""" % (L, ISF, ISF, FULLC, ISF, FULLC.replace("(c,", "(False{},")))

d("""
def mo.push_valid(c: Bool, +cap: Nat, +items: %s, -x: U32, +h: {Nat.is_le(%s, cap) == True{} : Bool}, ec: {%s == c : Bool}) -> {M.model.valid(Pair.fst(M.RingModel, %s, M.model.push.go(c, cap, items, x))) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      %%Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, items, Con{x, Nil{}})), 1n+%s, list.len_snoc(items, x)) : {Nat.is_le(_, cap) == True{} : Bool}
      nat.le_ne_succ(%s, cap, h, ec)
""" % (L, li, ISF, RU, li, li))

MH = "m: M.RingModel"
LXS = LEN % "xs"
AVM = "Nat.sub(cap, %s)" % li
d("""
def mo.push_list(%s, +xs: %s, h: {M.model.valid(m) == True{} : Bool}, l: {Nat.is_le(%s, M.model.avail(m)) == True{} : Bool}) -> {M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs))) == List.append(&2, U32, M.model.items(m), xs) : %s}:
  match m:
    case M.RingModel{+cap, +items}:
      %%Equal.sym(Nat, Nat.min(%s, %s), %s, nat.min_le(%s, %s, l)) : {List.append(&2, U32, items, List.take(&2, U32, xs, _)) == List.append(&2, U32, items, xs) : %s}
      %%Equal.sym(%s, List.take(&2, U32, xs, %s), xs, list.take_all(xs)) : {List.append(&2, U32, items, _) == List.append(&2, U32, items, xs) : %s}
      {==}
""" % (MH, L, LXS, L, LXS, AVM, LXS, LXS, AVM, L, L, LXS, L))

K = "Nat.min(%s, %s)" % (LXS, AVM)
d("""
def mo.push_list_valid(%s, +xs: %s, h: {M.model.valid(m) == True{} : Bool}) -> {M.model.valid(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs))) == True{} : Bool}:
  match m:
    case M.RingModel{+cap, +items}:
      %%Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, items, List.take(&2, U32, xs, %s))), Nat.add(%s, List.length(&2, U32, List.take(&2, U32, xs, %s))), list.length_append(items, List.take(&2, U32, xs, %s))) : {Nat.is_le(_, cap) == True{} : Bool}
      %%Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, xs, %s)), Nat.min(%s, %s), list.length_take(xs, %s)) : {Nat.is_le(Nat.add(%s, _), cap) == True{} : Bool}
      nat.add_le_sub(%s, Nat.min(%s, %s), cap, h, nat.le_trans(Nat.min(%s, %s), %s, %s, nat.min_le_l(%s, %s), nat.min_le_r(%s, %s)))
""" % (MH, L, K, li, K, K, K, K, LXS, K, li, li, K, LXS, K, LXS, K, AVM, K, LXS, LXS, AVM))

d("""
def mo.pop_list_valid(%s, +n: Nat, h: {M.model.valid(m) == True{} : Bool}) -> {M.model.valid(Pair.fst(M.RingModel, %s, M.model.pop_list(m, n))) == True{} : Bool}:
  match m:
    case M.RingModel{+cap, +items}:
      nat.le_trans(List.length(&2, U32, List.drop(&2, U32, items, n)), %s, cap, list.length_drop_le(items, n), h)
""" % (MH, L, li))

d("""
def mo.fifo(%s, +xs: %s, h: {M.model.valid(m) == True{} : Bool}, l: {Nat.is_le(%s, M.model.avail(m)) == True{} : Bool}) -> {Pair.snd(M.RingModel, %s, M.model.pop_list(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs)), Nat.add(M.model.len(m), %s))) == List.append(&2, U32, M.model.items(m), xs) : %s}:
  match m:
    case M.RingModel{+cap, +items}:
      %%Equal.sym(Nat, Nat.min(%s, %s), %s, nat.min_le(%s, %s, l)) : {List.take(&2, U32, List.append(&2, U32, items, List.take(&2, U32, xs, _)), Nat.add(%s, %s)) == List.append(&2, U32, items, xs) : %s}
      %%Equal.sym(%s, List.take(&2, U32, xs, %s), xs, list.take_all(xs)) : {List.take(&2, U32, List.append(&2, U32, items, _), Nat.add(%s, %s)) == List.append(&2, U32, items, xs) : %s}
      %%list.length_append(items, xs) : {List.take(&2, U32, List.append(&2, U32, items, xs), _) == List.append(&2, U32, items, xs) : %s}
      list.take_all(List.append(&2, U32, items, xs))
""" % (MH, L, LXS, L, LXS, L, LXS, AVM, LXS, LXS, AVM, li, LXS, L, L, LXS, li, LXS, L, L))

# Relation lemmas
d("""
# The Array ring against the model

def rl.push(c: Bool, -o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, -x: U32, -cap: Nat, -items: %s) -> {Pair.snd(R.RingBuf, %s, R.ring.push.go(c, o, i, u, a, x)) == Pair.snd(M.RingModel, %s, M.model.push.go(c, cap, items, x)) : %s}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def rl.push_cap(c: Bool, -o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, -x: U32, -items: %s) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, %s, R.ring.push.go(c, o, i, u, a, x)))) == M.model.capacity(Pair.fst(M.RingModel, %s, M.model.push.go(c, R.ring.size(o), items, x))) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def rl.push_len(c: Bool, +o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, -x: U32, +items: %s, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +el: {Nat.sub(i, u) == %s : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, %s, R.ring.push.go(c, o, i, u, a, x)))) == M.model.len(Pair.fst(M.RingModel, %s, M.model.push.go(c, R.ring.size(o), items, x))) : Nat}:
  match c:
    case True{}:
      el
    case False{}:
      %%Equal.sym(Nat, Nat.sub(1n+i, u), 1n+Nat.sub(i, u), nat.sub_succ(i, u, inv.p2(o, i, u, h))) : {_ == List.length(&2, U32, List.append(&2, U32, items, Con{x, Nil{}})) : Nat}
      %%Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, items, Con{x, Nil{}})), 1n+%s, list.len_snoc(items, x)) : {1n+Nat.sub(i, u) == _ : Nat}
      %%el : {1n+Nat.sub(i, u) == 1n+_ : Nat}
      {==}

def rl.pop_done(items: %s, +o: Nat, -i: Nat, +u: Nat, a: Array<U32>, -cap: Nat) -> {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, %s, R.ring.pop.go(Nat.is_eq(%s, 0n), o, i, u, a))) == Result.is_done(&2, &2, R.RingError, U32, Pair.snd(M.RingModel, %s, M.model.pop(M.RingModel{cap, items}))) : Bool}:
  match items:
    case Nil{}:
      {==}
    case Con{y, t}:
      po.done.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))

def rl.ne(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, -y: U32, -t: %s, el: {Nat.sub(i, u) == List.length(&2, U32, Con{y, t}) : Nat}) -> {R.ring.empty.test(i, u) == False{} : Bool}:
  %%Equal.sym(Bool, Nat.is_eq(i, u), Nat.is_eq(Nat.sub(i, u), 0n), nat.eq_sub(i, u, inv.p2(o, i, u, h))) : {_ == False{} : Bool}
  %%Equal.sym(Nat, Nat.sub(i, u), List.length(&2, U32, Con{y, t}), el) : {Nat.is_eq(_, 0n) == False{} : Bool}
  {==}

def rl.pop_len(items: %s, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, -cap: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +el: {Nat.sub(i, u) == %s : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, %s, R.ring.pop.go(Nat.is_eq(%s, 0n), o, i, u, a)))) == M.model.len(Pair.fst(M.RingModel, %s, M.model.pop(M.RingModel{cap, items}))) : Nat}:
  match items:
    case Nil{}:
      el
    case Con{y, +t}:
      nat.succ_inj(Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, %s, R.ring.pop.read(o, i, u, Array.get(U32, a, U32.from_nat(u)))))), List.length(&2, U32, t), Equal.trans(Nat, 1n+Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, %s, R.ring.pop.read(o, i, u, Array.get(U32, a, U32.from_nat(u)))))), Nat.sub(i, u), 1n+List.length(&2, U32, t), po.len.r(o, i, u, Array.get(U32, a, U32.from_nat(u)), h, rl.ne(o, i, u, h, y, t, el)), el))

def rl.pop_cap.w(w: Bool, -o: Nat, -i: Nat, -u1: Nat, -a: Array<U32>, -x: U32) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, %s, R.ring.pop.wrap(w, o, i, u1, a, x)))) == R.ring.size(o) : Nat}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def rl.pop_cap.r(+o: Nat, -i: Nat, +u: Nat, ax: Array<U32> & U32) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, %s, R.ring.pop.read(o, i, u, ax)))) == R.ring.size(o) : Nat}:
  match ax:
    case (a, x):
      rl.pop_cap.w(Nat.is_eq(1n+u, R.ring.size(o)), o, i, 1n+u, a, x)

def rl.pop_cap(c: Bool, +o: Nat, -i: Nat, +u: Nat, a: Array<U32>, items: %s) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, %s, R.ring.pop.go(c, o, i, u, a)))) == M.model.capacity(Pair.fst(M.RingModel, %s, M.model.pop(M.RingModel{R.ring.size(o), items}))) : Nat}:
  match c items:
    case True{} Nil{}:
      {==}
    case True{} Con{y, t}:
      {==}
    case False{} Nil{}:
      rl.pop_cap.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))
    case False{} Con{y, t}:
      rl.pop_cap.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))
""" % (L, RU, RU, RU, L, RU, RU, L, li, RU, RU, li, L, R32, li, R32, L, L, li, R32, li, R32, R32, R32, R32, R32, L, R32, R32))

def relsig(name, extra, concl, hl=HL):
    return "def %s(r: R.RingBuf, m: M.RingModel, %s%s, %s, %s) -> %s:\n" % (name, extra, HV, HC, hl, concl)

PUSHG = "R.ring.push.go(R.ring.full.test(o, i, u), o, i, u, a, x)"
def mpush(b, c): return "M.model.push.go(Nat.is_eq(%s, %s), %s, items, x)" % (b, c, c)

d(relsig("rel.is_full", "", "{Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == M.model.is_full(m) : Bool}") + MATCH + """      %%ec : {Nat.is_eq(Nat.sub(i, u), R.ring.size(o)) == Nat.is_eq(%s, _) : Bool}
      %%el : {Nat.is_eq(Nat.sub(i, u), R.ring.size(o)) == Nat.is_eq(_, R.ring.size(o)) : Bool}
      {==}
""" % li)
d(relsig("rel.is_empty", "", "{Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == M.model.is_empty(m) : Bool}") + MATCH + """      %el : {Nat.is_eq(i, u) == Nat.is_eq(_, 0n) : Bool}
      nat.eq_sub(i, u, inv.p2(o, i, u, h))
""")
d(relsig("rel.avail", "", "{Pair.snd(R.RingBuf, Nat, R.ring.avail(r)) == M.model.avail(m) : Nat}") + MATCH + """      %%ec : {Nat.sub(R.ring.size(o), Nat.sub(i, u)) == Nat.sub(_, %s) : Nat}
      %%el : {Nat.sub(R.ring.size(o), Nat.sub(i, u)) == Nat.sub(R.ring.size(o), _) : Nat}
      {==}
""" % li)
LHSP = "Pair.snd(R.RingBuf, %s, %s)" % (RU, PUSHG)
d(relsig("rel.push", "-x: U32, ", "{Pair.snd(R.RingBuf, %s, R.ring.push(r, x)) == Pair.snd(M.RingModel, %s, M.model.push(m, x)) : %s}" % (RU, RU, RU)) + MATCH + """      %%ec : {%s == Pair.snd(M.RingModel, %s, %s) : %s}
      %%el : {%s == Pair.snd(M.RingModel, %s, %s) : %s}
      rl.push(R.ring.full.test(o, i, u), o, i, u, a, x, R.ring.size(o), items)
""" % (LHSP, RU, mpush(li, "_"), RU, LHSP, RU, mpush("_", "R.ring.size(o)").replace("Nat.is_eq(_, R.ring.size(o)), R.ring.size(o)", "Nat.is_eq(_, R.ring.size(o)), R.ring.size(o)"), RU))
LHSL = "Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, %s, %s)))" % (RU, PUSHG)
d(relsig("rel.push_len", "-x: U32, ", "{Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, %s, R.ring.push(r, x)))) == M.model.len(Pair.fst(M.RingModel, %s, M.model.push(m, x))) : Nat}" % (RU, RU), HLp) + MATCH + """      %%ec : {%s == M.model.len(Pair.fst(M.RingModel, %s, %s)) : Nat}
      %%el : {%s == M.model.len(Pair.fst(M.RingModel, %s, %s)) : Nat}
      rl.push_len(R.ring.full.test(o, i, u), o, i, u, a, x, items, h, el)
""" % (LHSL, RU, mpush(li, "_"), LHSL, RU, mpush("_", "R.ring.size(o)"), ))
LHSC = "Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, %s, %s)))" % (RU, PUSHG)
d(relsig("rel.push_capacity", "-x: U32, ", "{Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, %s, R.ring.push(r, x)))) == M.model.capacity(Pair.fst(M.RingModel, %s, M.model.push(m, x))) : Nat}" % (RU, RU)) + MATCH + """      %%ec : {%s == M.model.capacity(Pair.fst(M.RingModel, %s, %s)) : Nat}
      %%el : {%s == M.model.capacity(Pair.fst(M.RingModel, %s, %s)) : Nat}
      rl.push_cap(R.ring.full.test(o, i, u), o, i, u, a, x, items)
""" % (LHSC, RU, mpush(li, "_"), LHSC, RU, mpush("_", "R.ring.size(o)")))
POPG = "R.ring.pop.go(%s, o, i, u, a)"
def done(x): return "Result.is_done(&2, &2, R.RingError, U32, %s)" % x
RHSD = done("Pair.snd(M.RingModel, %s, M.model.pop(M.RingModel{cap, items}))" % R32)
d(relsig("rel.pop_done", "", "{%s == %s : Bool}" % (done("Pair.snd(R.RingBuf, %s, R.ring.pop(r))" % R32), done("Pair.snd(M.RingModel, %s, M.model.pop(m))" % R32))) + MATCH + """      %%Equal.sym(Bool, Nat.is_eq(i, u), Nat.is_eq(Nat.sub(i, u), 0n), nat.eq_sub(i, u, inv.p2(o, i, u, h))) : {%s == %s : Bool}
      %%Equal.sym(Nat, Nat.sub(i, u), %s, el) : {%s == %s : Bool}
      rl.pop_done(items, o, i, u, a, cap)
""" % (done("Pair.snd(R.RingBuf, %s, %s)" % (R32, POPG % "_")), RHSD, li, done("Pair.snd(R.RingBuf, %s, %s)" % (R32, POPG % "Nat.is_eq(_, 0n)")), RHSD))
RHSPL = "M.model.len(Pair.fst(M.RingModel, %s, M.model.pop(M.RingModel{cap, items})))" % R32
def lenpop(b): return "Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, %s, %s)))" % (R32, POPG % b)
d(relsig("rel.pop_len", "", "{Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, %s, R.ring.pop(r)))) == M.model.len(Pair.fst(M.RingModel, %s, M.model.pop(m))) : Nat}" % (R32, R32), HLp) + MATCH + """      %%Equal.sym(Bool, Nat.is_eq(i, u), Nat.is_eq(Nat.sub(i, u), 0n), nat.eq_sub(i, u, inv.p2(o, i, u, h))) : {%s == %s : Nat}
      %%Equal.sym(Nat, Nat.sub(i, u), %s, el) : {%s == %s : Nat}
      rl.pop_len(items, o, i, u, a, cap, h, el)
""" % (lenpop("_"), RHSPL, li, lenpop("Nat.is_eq(_, 0n)"), RHSPL))
d(relsig("rel.pop_capacity", "", "{Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, %s, R.ring.pop(r)))) == M.model.capacity(Pair.fst(M.RingModel, %s, M.model.pop(m))) : Nat}" % (R32, R32)) + MATCH + """      %%ec : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, %s, %s))) == M.model.capacity(Pair.fst(M.RingModel, %s, M.model.pop(M.RingModel{_, items}))) : Nat}
      rl.pop_cap(R.ring.empty.test(i, u), o, i, u, a, items)
""" % (R32, POPG % "R.ring.empty.test(i, u)", R32))
MINR = "Nat.min(%s, Nat.sub(R.ring.size(o), Nat.sub(i, u)))" % LXS
d(relsig("rel.push_list", "+xs: %s, " % L, "{Pair.snd(R.RingBuf, Nat, R.ring.push_list(r, xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(m, xs)) : Nat}") + MATCH + """      %%Equal.sym(Nat, Pair.snd(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs)), %s, bp.count(xs, o, i, u, a, 0n, h)) : {_ == Pair.snd(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs)) : Nat}
      %%ec : {%s == Nat.min(%s, Nat.sub(_, %s)) : Nat}
      %%el : {%s == Nat.min(%s, Nat.sub(R.ring.size(o), _)) : Nat}
      {==}
""" % (MINR, MINR, LXS, li, MINR, LXS))
d(relsig("rel.pop_list", "+k: Nat, ", "{List.length(&2, U32, Pair.snd(R.RingBuf, %s, R.ring.pop_list(r, k))) == List.length(&2, U32, Pair.snd(M.RingModel, %s, M.model.pop_list(m, k))) : Nat}" % (L, L)) + MATCH + """      %%Equal.sym(Nat, List.length(&2, U32, Pair.snd(R.RingBuf, %s, R.ring.pop_list(R.RingBuf{o, i, u, a}, k))), Nat.min(k, Nat.sub(i, u)), bo.count(k, o, i, u, a, Nil{}, h)) : {_ == List.length(&2, U32, List.take(&2, U32, items, k)) : Nat}
      %%Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, items, k)), Nat.min(k, %s), list.length_take(items, k)) : {Nat.min(k, Nat.sub(i, u)) == _ : Nat}
      %%el : {Nat.min(k, Nat.sub(i, u)) == Nat.min(k, _) : Nat}
      {==}
""" % (L, li))

d("""
# The laws: the model

def Laws.model_new_valid(o):
  nat.le_zero(R.ring.size(o))

def Laws.model_new_empty(o):
  {==}

def Laws.model_new_capacity(o):
  {==}

def Laws.model_push_items(m, x, e):
  match m:
    case M.RingModel{+cap, +items}:
      mo.push_items(%s, cap, items, x, {==}, e)

def Laws.model_push_done(m, x, e):
  match m:
    case M.RingModel{+cap, +items}:
      mo.push_done(%s, cap, items, x, {==}, e)

def Laws.model_push_full(m, x, e):
  match m:
    case M.RingModel{+cap, +items}:
      mo.push_full(%s, cap, items, x, {==}, e)

def Laws.model_push_valid(m, x, h):
  match m:
    case M.RingModel{+cap, +items}:
      mo.push_valid(%s, cap, items, x, h, {==})

def Laws.model_pop(m, y, t, e):
  match m:
    case M.RingModel{cap, items}:
      %%Equal.sym(%s, items, Con{y, t}, e) : {Pair.snd(M.RingModel, %s, M.model.pop(M.RingModel{cap, _})) == Done{y} : %s}
      {==}

def Laws.model_pop_items(m, y, t, e):
  match m:
    case M.RingModel{cap, items}:
      %%Equal.sym(%s, items, Con{y, t}, e) : {M.model.items(Pair.fst(M.RingModel, %s, M.model.pop(M.RingModel{cap, _}))) == t : %s}
      {==}

def Laws.model_pop_empty(m, e):
  match m:
    case M.RingModel{cap, items}:
      match items:
        case Nil{}:
          {==}
        case Con{y, t}:
          Empty.absurd({M.model.pop(M.RingModel{cap, Con{y, t}}) == (M.RingModel{cap, Con{y, t}}, Fail{R.RingEmpty{}}) : M.RingModel & %s}, absurd.ft(e))

def Laws.model_pop_valid(m, h):
  match m:
    case M.RingModel{+cap, items}:
      match items:
        case Nil{}:
          h
        case Con{y, +t}:
          nat.le_trans(List.length(&2, U32, t), 1n+List.length(&2, U32, t), cap, nat.le_succ(List.length(&2, U32, t), List.length(&2, U32, t), nat.le_refl(List.length(&2, U32, t))), h)

def Laws.model_peek_is_pop(m):
  match m:
    case M.RingModel{cap, items}:
      match items:
        case Nil{}:
          {==}
        case Con{y, t}:
          {==}

def Laws.model_peek_keeps(m):
  match m:
    case M.RingModel{cap, items}:
      match items:
        case Nil{}:
          {==}
        case Con{y, t}:
          {==}

def Laws.model_push_list(m, xs, h, l):
  mo.push_list(m, xs, h, l)

def Laws.model_push_list_count(m, xs):
  match m:
    case M.RingModel{cap, items}:
      {==}

def Laws.model_push_list_valid(m, xs, h):
  mo.push_list_valid(m, xs, h)

def Laws.model_pop_list(m, n):
  match m:
    case M.RingModel{cap, items}:
      {==}

def Laws.model_pop_list_items(m, n):
  match m:
    case M.RingModel{cap, items}:
      {==}

def Laws.model_pop_list_valid(m, n, h):
  mo.pop_list_valid(m, n, h)

def Laws.model_fifo(m, xs, h, l):
  mo.fifo(m, xs, h, l)

# The laws: the Array ring against the model

def Laws.rel_is_full(r, m, h, c, n):
  rel.is_full(r, m, h, c, n)

def Laws.rel_is_empty(r, m, h, c, n):
  rel.is_empty(r, m, h, c, n)

def Laws.rel_avail(r, m, h, c, n):
  rel.avail(r, m, h, c, n)

def Laws.rel_push(r, m, x, h, c, n):
  rel.push(r, m, x, h, c, n)

def Laws.rel_push_len(r, m, x, h, c, n):
  rel.push_len(r, m, x, h, c, n)

def Laws.rel_push_capacity(r, m, x, h, c, n):
  rel.push_capacity(r, m, x, h, c, n)

def Laws.rel_pop_done(r, m, h, c, n):
  rel.pop_done(r, m, h, c, n)

def Laws.rel_pop_len(r, m, h, c, n):
  rel.pop_len(r, m, h, c, n)

def Laws.rel_pop_capacity(r, m, h, c, n):
  rel.pop_capacity(r, m, h, c, n)

def Laws.rel_push_list(r, m, xs, h, c, n):
  rel.push_list(r, m, xs, h, c, n)

def Laws.rel_pop_list(r, m, k, h, c, n):
  rel.pop_list(r, m, k, h, c, n)

# Witnesses

def Laws.wit_full():
  {==}

def Laws.wit_not_full():
  {==}

def Laws.wit_not_empty():
  {==}

def Laws.wit_related():
  {==}

def Laws.wit_model():
  {==}
""" % (ISF, ISF, ISF, ISF, L, R32, R32, L, R32, L, R32))

MARK = "# Lists and Nat, for the model\n"
# the part from this line on is gen/proof_elems.py's, and is kept as it is
MARK2 = "# The Array ring's elements, through bend-osdev-array\n"
path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "PROOF.bend")
old = open(path, newline="").read()
tail = "\n" + old[old.index(MARK2):] if MARK2 in old else ""
new = old[:old.index(MARK)] + "\n".join(P) + tail
if "--check" in sys.argv[1:]:
    print("up to date" if new == old else "differs")
    sys.exit(0 if new == old else 1)
open(path, "w", newline="\n").write(new)
