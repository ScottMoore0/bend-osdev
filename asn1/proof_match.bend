# Proofs for bend-osdev-asn1: what a schema match holds are slices of the
# input. pm.gl(d, ms, c) says every match of ms has its octets in c and, to
# depth d, every match inside each has its octets in the element holding
# it (a SEQUENCE's fields in its octets, an EXPLICIT tag's inner match in
# its octets). The matcher, by induction on its fuel, answers for an element
# e matches whose element is e (pm.ones) and, for a sequence's fields,
# matches within the element's octets (pm.ls), as each field's element is
# one of the elements Asn1.items read from the contents octets
# (proof_split.bend: those join to the contents, a slice of the element's
# octets). Following steps (Asn1Match.follow) keeps within the octets
# (pm.follow), which gives laws match_tlv_within and match_within; the
# element matched is the element read (match_tlv_tlv), so laws
# match_split, match_whole and match_der follow from read_split and
# read_der; a SET OF or SEQUENCE OF match is of a constructed element of
# its tag (match_of_node).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./asn1.bend as A
import ./schema.bend as Sc
import ./proof_nat.bend as AN
import ./proof_oct.bend as OA
import ./proof_split.bend as PS
import ./proof_der.bend as PD

# Matches within octets, to a depth

def pm.gl(+d: Nat, ms: List<&2, Sc.Asn1Match>, +c: B.Octets) -> Type:
  match d ms:
    case 0n Nil{}:
      Unit
    case 0n Con{m, t}:
      OA.oa.sl(Sc.Asn1Match.raw(m), c) & pm.gl(d, t, c)
    case 1n+k Nil{}:
      Unit
    case 1n+k Con{Sc.Asn1MElem{e}, t}:
      OA.oa.sl(A.Asn1Tlv.raw(e), c) & pm.gl(d, t, c)
    case 1n+k Con{Sc.Asn1MSeq{e, xs}, t}:
      OA.oa.sl(A.Asn1Tlv.raw(e), c) & (pm.gl(k, xs, A.Asn1Tlv.raw(e)) & pm.gl(d, t, c))
    case 1n+k Con{Sc.Asn1MChoice{i, x}, t}:
      OA.oa.sl(Sc.Asn1Match.raw(x), c) & (pm.gl(k, [x], Sc.Asn1Match.raw(x)) & pm.gl(d, t, c))
    case 1n+k Con{Sc.Asn1MExplicit{e, x}, t}:
      OA.oa.sl(A.Asn1Tlv.raw(e), c) & (pm.gl(k, [x], A.Asn1Tlv.raw(e)) & pm.gl(d, t, c))
    case 1n+k Con{Sc.Asn1MAbsent{}, t}:
      OA.oa.sl(B.Octets.empty(), c) & pm.gl(d, t, c)
    case 1n+k Con{Sc.Asn1MDefault{v}, t}:
      OA.oa.sl(B.Octets.empty(), c) & pm.gl(d, t, c)

def pm.gnil(+d: Nat, +c: B.Octets) -> pm.gl(d, Nil{}, c):
  match d:
    case 0n:
      Unit{}
    case 1n+k:
      Unit{}

# the first of matches within c: its octets in c, its own fields within
# its octets
def pm.head2(+d: Nat, m: Sc.Asn1Match, +t: List<&2, Sc.Asn1Match>, +c: B.Octets, g: pm.gl(d, Con{m, t}, c)) -> OA.oa.sl(Sc.Asn1Match.raw(m), c) & pm.gl(d, [m], Sc.Asn1Match.raw(m)):
  match d m:
    case 0n +m0:
      (a, b) = g
      (a, (OA.oa.sl_refl(Sc.Asn1Match.raw(m0)), Unit{}))
    case 1n+k Sc.Asn1MElem{+e}:
      (a, b) = g
      (a, (OA.oa.sl_refl(A.Asn1Tlv.raw(e)), Unit{}))
    case 1n+k Sc.Asn1MSeq{+e, xs}:
      (a, (b, u)) = g
      (a, (OA.oa.sl_refl(A.Asn1Tlv.raw(e)), (b, Unit{})))
    case 1n+k Sc.Asn1MChoice{i, +x}:
      (a, (b, u)) = g
      (a, (OA.oa.sl_refl(Sc.Asn1Match.raw(x)), (b, Unit{})))
    case 1n+k Sc.Asn1MExplicit{+e, x}:
      (a, (b, u)) = g
      (a, (OA.oa.sl_refl(A.Asn1Tlv.raw(e)), (b, Unit{})))
    case 1n+k Sc.Asn1MAbsent{}:
      (a, b) = g
      (a, (OA.oa.sl_refl(B.Octets.empty()), Unit{}))
    case 1n+k Sc.Asn1MDefault{v}:
      (a, b) = g
      (a, (OA.oa.sl_refl(B.Octets.empty()), Unit{}))

# the others
def pm.tail(+d: Nat, m: Sc.Asn1Match, +t: List<&2, Sc.Asn1Match>, +c: B.Octets, g: pm.gl(d, Con{m, t}, c)) -> pm.gl(d, t, c):
  match d m:
    case 0n m0:
      (a, b) = g
      b
    case 1n+k Sc.Asn1MElem{e}:
      (a, b) = g
      b
    case 1n+k Sc.Asn1MSeq{e, xs}:
      (a, (b, u)) = g
      u
    case 1n+k Sc.Asn1MChoice{i, x}:
      (a, (b, u)) = g
      u
    case 1n+k Sc.Asn1MExplicit{e, x}:
      (a, (b, u)) = g
      u
    case 1n+k Sc.Asn1MAbsent{}:
      (a, b) = g
      b
    case 1n+k Sc.Asn1MDefault{v}:
      (a, b) = g
      b

# and back: a match within c, with its fields within it, in front of others
def pm.mk(+d: Nat, m: Sc.Asn1Match, +t: List<&2, Sc.Asn1Match>, +c: B.Octets, hs: OA.oa.sl(Sc.Asn1Match.raw(m), c), h: pm.gl(d, [m], Sc.Asn1Match.raw(m)), ht: pm.gl(d, t, c)) -> pm.gl(d, Con{m, t}, c):
  match d m:
    case 0n m0:
      (hs, ht)
    case 1n+k Sc.Asn1MElem{e}:
      (hs, ht)
    case 1n+k Sc.Asn1MSeq{e, xs}:
      (a, (b, u)) = h
      (hs, (b, ht))
    case 1n+k Sc.Asn1MChoice{i, x}:
      (a, (b, u)) = h
      (hs, (b, ht))
    case 1n+k Sc.Asn1MExplicit{e, x}:
      (a, (b, u)) = h
      (hs, (b, ht))
    case 1n+k Sc.Asn1MAbsent{}:
      (hs, ht)
    case 1n+k Sc.Asn1MDefault{v}:
      (hs, ht)

# a match whose octets are in c, with its fields within it, is within c
def pm.rebase(+m: Sc.Asn1Match, +c: B.Octets, +d: Nat, hs: OA.oa.sl(Sc.Asn1Match.raw(m), c), h: pm.gl(d, [m], Sc.Asn1Match.raw(m))) -> pm.gl(d, [m], c):
  pm.mk(d, m, Nil{}, c, hs, h, pm.gnil(d, c))

# less depth asks less
def pm.mono(+k: Nat, ms: List<&2, Sc.Asn1Match>, +c: B.Octets, g: pm.gl(1n+k, ms, c)) -> pm.gl(k, ms, c):
  match k ms:
    case 0n Nil{}:
      Unit{}
    case 1n+j Nil{}:
      Unit{}
    case 0n Con{Sc.Asn1MElem{e}, +t}:
      (a, b) = g
      (a, pm.mono(k, t, c, b))
    case 0n Con{Sc.Asn1MSeq{e, xs}, +t}:
      (a, (b, u)) = g
      (a, pm.mono(k, t, c, u))
    case 0n Con{Sc.Asn1MChoice{i, x}, +t}:
      (a, (b, u)) = g
      (a, pm.mono(k, t, c, u))
    case 0n Con{Sc.Asn1MExplicit{e, x}, +t}:
      (a, (b, u)) = g
      (a, pm.mono(k, t, c, u))
    case 0n Con{Sc.Asn1MAbsent{}, +t}:
      (a, b) = g
      (a, pm.mono(k, t, c, b))
    case 0n Con{Sc.Asn1MDefault{v}, +t}:
      (a, b) = g
      (a, pm.mono(k, t, c, b))
    case 1n+j Con{Sc.Asn1MElem{e}, +t}:
      (a, b) = g
      (a, pm.mono(k, t, c, b))
    case 1n+j Con{Sc.Asn1MSeq{+e, +xs}, +t}:
      (a, (b, u)) = g
      (a, (pm.mono(j, xs, A.Asn1Tlv.raw(e), b), pm.mono(k, t, c, u)))
    case 1n+j Con{Sc.Asn1MChoice{i, +x}, +t}:
      (a, (b, u)) = g
      (a, (pm.mono(j, [x], Sc.Asn1Match.raw(x), b), pm.mono(k, t, c, u)))
    case 1n+j Con{Sc.Asn1MExplicit{+e, +x}, +t}:
      (a, (b, u)) = g
      (a, (pm.mono(j, [x], A.Asn1Tlv.raw(e), b), pm.mono(k, t, c, u)))
    case 1n+j Con{Sc.Asn1MAbsent{}, +t}:
      (a, b) = g
      (a, pm.mono(k, t, c, b))
    case 1n+j Con{Sc.Asn1MDefault{v}, +t}:
      (a, b) = g
      (a, pm.mono(k, t, c, b))

# matches with nothing inside them

def pm.g_absent(+d: Nat) -> pm.gl(d, [Sc.Asn1MAbsent{}], Sc.Asn1Match.raw(Sc.Asn1MAbsent{})):
  match d:
    case 0n:
      (OA.oa.sl_refl(B.Octets.empty()), Unit{})
    case 1n+k:
      (OA.oa.sl_refl(B.Octets.empty()), Unit{})

def pm.g_default(+v: N.Asn1Node, +d: Nat) -> pm.gl(d, [Sc.Asn1MDefault{v}], Sc.Asn1Match.raw(Sc.Asn1MDefault{v})):
  match d:
    case 0n:
      (OA.oa.sl_refl(B.Octets.empty()), Unit{})
    case 1n+k:
      (OA.oa.sl_refl(B.Octets.empty()), Unit{})

def pm.g_elem(+e: A.Asn1Tlv, +d: Nat) -> pm.gl(d, [Sc.Asn1MElem{e}], A.Asn1Tlv.raw(e)):
  match d:
    case 0n:
      (OA.oa.sl_refl(A.Asn1Tlv.raw(e)), Unit{})
    case 1n+k:
      (OA.oa.sl_refl(A.Asn1Tlv.raw(e)), Unit{})

# Steps, each keeping within the octets top of the match followed from

# a match within c, and c within top: the match within top
def pm.lift(+k: Nat, +m: Sc.Asn1Match, +c: B.Octets, +top: B.Octets, acc: OA.oa.sl(c, top), p: OA.oa.sl(Sc.Asn1Match.raw(m), c) & pm.gl(k, [m], Sc.Asn1Match.raw(m))) -> OA.oa.sl(Sc.Asn1Match.raw(m), top) & pm.gl(k, [m], Sc.Asn1Match.raw(m)):
  (s, g) = p
  (OA.oa.sl_trans(Sc.Asn1Match.raw(m), c, top, s, acc), g)

# the i-th of matches within c
def pm.nth(xs: List<&2, Sc.Asn1Match>, i: Nat, +c: B.Octets, +top: B.Octets, acc: OA.oa.sl(c, top), +k: Nat, g: pm.gl(k, xs, c)) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.a1.s.nth(xs, i)), top) & pm.gl(k, [Sc.a1.s.nth(xs, i)], Sc.Asn1Match.raw(Sc.a1.s.nth(xs, i))):
  match xs i:
    case Nil{} _:
      (OA.oa.sl_empty(top), pm.g_absent(k))
    case Con{+m, +t} 0n:
      pm.lift(k, m, c, top, acc, pm.head2(k, m, t, c, g))
    case Con{+m, +t} 1n+j:
      pm.nth(t, j, c, top, acc, k, pm.tail(k, m, t, c, g))

def pm.at_step(m: Sc.Asn1Match, +i: Nat, +k: Nat, +top: B.Octets, hp: OA.oa.sl(Sc.Asn1Match.raw(m), top) & pm.gl(1n+k, [m], Sc.Asn1Match.raw(m))) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.Asn1Match.at(m, i)), top) & pm.gl(k, [Sc.Asn1Match.at(m, i)], Sc.Asn1Match.raw(Sc.Asn1Match.at(m, i))):
  match m:
    case Sc.Asn1MSeq{+e, +xs}:
      (acc, h) = hp
      (a, (b, u)) = h
      pm.nth(xs, i, A.Asn1Tlv.raw(e), top, acc, k, b)
    case Sc.Asn1MElem{e}:
      (OA.oa.sl_empty(top), pm.g_absent(k))
    case Sc.Asn1MChoice{j, x}:
      (OA.oa.sl_empty(top), pm.g_absent(k))
    case Sc.Asn1MExplicit{e, x}:
      (OA.oa.sl_empty(top), pm.g_absent(k))
    case Sc.Asn1MAbsent{}:
      (OA.oa.sl_empty(top), pm.g_absent(k))
    case Sc.Asn1MDefault{v}:
      (OA.oa.sl_empty(top), pm.g_absent(k))

def pm.in_step(m: Sc.Asn1Match, +k: Nat, +top: B.Octets, hp: OA.oa.sl(Sc.Asn1Match.raw(m), top) & pm.gl(1n+k, [m], Sc.Asn1Match.raw(m))) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.Asn1Match.inner(m)), top) & pm.gl(k, [Sc.Asn1Match.inner(m)], Sc.Asn1Match.raw(Sc.Asn1Match.inner(m))):
  match m:
    case Sc.Asn1MExplicit{+e, +x}:
      (acc, h) = hp
      (a, (b, u)) = h
      pm.lift(k, x, A.Asn1Tlv.raw(e), top, acc, pm.head2(k, x, Nil{}, A.Asn1Tlv.raw(e), b))
    case Sc.Asn1MChoice{i, +x}:
      (acc, h) = hp
      (a, (b, u)) = h
      (acc, b)
    case Sc.Asn1MSeq{+e, +xs}:
      (acc, h) = hp
      (acc, pm.mono(k, [Sc.Asn1MSeq{e, xs}], A.Asn1Tlv.raw(e), h))
    case Sc.Asn1MElem{+e}:
      (acc, h) = hp
      (acc, pm.mono(k, [Sc.Asn1MElem{e}], A.Asn1Tlv.raw(e), h))
    case Sc.Asn1MAbsent{}:
      (acc, h) = hp
      (acc, pm.g_absent(k))
    case Sc.Asn1MDefault{+v}:
      (acc, h) = hp
      (acc, pm.g_default(v, k))

def pm.len(p: List<&2, Sc.Asn1Step>) -> Nat:
  List.length(&2, Sc.Asn1Step, p)

# following steps keeps within the octets
def pm.follow(p: List<&2, Sc.Asn1Step>, +m: Sc.Asn1Match, +top: B.Octets, +d: Nat, hp: OA.oa.sl(Sc.Asn1Match.raw(m), top) & pm.gl(Nat.add(pm.len(p), d), [m], Sc.Asn1Match.raw(m))) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.a1.s.follow(p, m)), top) & pm.gl(d, [Sc.a1.s.follow(p, m)], Sc.Asn1Match.raw(Sc.a1.s.follow(p, m))):
  match p:
    case Nil{}:
      hp
    case Con{Sc.Asn1StepAt{+i}, +t}:
      pm.follow(t, Sc.Asn1Match.at(m, i), top, d, pm.at_step(m, i, Nat.add(pm.len(t), d), top, hp))
    case Con{Sc.Asn1StepInner{}, +t}:
      pm.follow(t, Sc.Asn1Match.inner(m), top, d, pm.in_step(m, Nat.add(pm.len(t), d), top, hp))

def pm.fapp(p: List<&2, Sc.Asn1Step>, +q: List<&2, Sc.Asn1Step>, +m: Sc.Asn1Match) -> {Sc.a1.s.follow(List.append(&2, Sc.Asn1Step, p, q), m) == Sc.a1.s.follow(q, Sc.a1.s.follow(p, m)) : Sc.Asn1Match}:
  match p:
    case Nil{}:
      {==}
    case Con{Sc.Asn1StepAt{+i}, +t}:
      pm.fapp(t, q, Sc.Asn1Match.at(m, i))
    case Con{Sc.Asn1StepInner{}, +t}:
      pm.fapp(t, q, Sc.Asn1Match.inner(m))

# The matcher

# elements matched within c
def pm.all(es: List<&2, A.Asn1Tlv>, +c: B.Octets) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{e, t}:
      OA.oa.sl(A.Asn1Tlv.raw(e), c) & pm.all(t, c)

def pm.slots(sl: List<&2, Sc.A1Slot>, +c: B.Octets) -> Type:
  match sl:
    case Nil{}:
      Unit
    case Con{Sc.A1Slot{s, None{}}, t}:
      pm.slots(t, c)
    case Con{Sc.A1Slot{s, Some{e}}, t}:
      OA.oa.sl(A.Asn1Tlv.raw(e), c) & pm.slots(t, c)

def pm.pre(w: Sc.A1Work, +c: B.Octets) -> Type:
  match w:
    case Sc.A1WSlots{sl, ex}:
      pm.slots(sl, c)
    case Sc.A1WOne{s, e}:
      Unit
    case Sc.A1WNone{}:
      Unit

def pm.one_l(ms: List<&2, Sc.Asn1Match>, +e: A.Asn1Tlv, +d: Nat) -> Type:
  match ms:
    case Nil{}:
      Unit
    case Con{m, t}:
      {Sc.Asn1Match.tlv(m) == Some{e} : Maybe<&2, A.Asn1Tlv>} & (pm.gl(d, [m], Sc.Asn1Match.raw(m)) & pm.one_l(t, e, d))

def pm.ones(res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +e: A.Asn1Tlv, +d: Nat) -> Type:
  match res:
    case Fail{x}:
      Unit
    case Done{ms}:
      pm.one_l(ms, e, d)

def pm.ls(res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +c: B.Octets, +d: Nat) -> Type:
  match res:
    case Fail{x}:
      Unit
    case Done{ms}:
      pm.gl(d, ms, c)

def pm.sm(res: Result<&2, &2, E.Asn1Error, Sc.Asn1Match>, +c: B.Octets, +d: Nat) -> Type:
  match res:
    case Fail{x}:
      Unit
    case Done{m}:
      OA.oa.sl(Sc.Asn1Match.raw(m), c) & pm.gl(d, [m], Sc.Asn1Match.raw(m))

def pm.post(w: Sc.A1Work, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +c: B.Octets, +d: Nat) -> Type:
  match w:
    case Sc.A1WOne{s, e}:
      pm.ones(res, e, d)
    case Sc.A1WSlots{sl, ex}:
      pm.ls(res, c, d)
    case Sc.A1WNone{}:
      Unit

def pm.dm1(d: Nat) -> Nat:
  match d:
    case 0n:
      0n
    case 1n+k:
      k

# the elements a constructed element holds are within its octets

def pm.all_concat(xs: List<&2, A.Asn1Tlv>, +c: B.Octets, h: OA.oa.sl(B.Octets.concat(A.Asn1.raws(xs)), c)) -> pm.all(xs, c):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (+u, (+v, +eq)) = h
      +rx = A.Asn1Tlv.raw(x)
      +rt = B.Octets.concat(A.Asn1.raws(t))
      +eq2 = Equal.trans(B.Octets, c, B.Octets.append(u, B.Octets.append(B.Octets.concat(Con{rx, A.Asn1.raws(t)}), v)), B.Octets.append(u, B.Octets.append(B.Octets.append(rx, rt), v)), eq, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(u, B.Octets.append(z, v)), B.Octets.concat(Con{rx, A.Asn1.raws(t)}), B.Octets.append(rx, rt), BL.octets_concat_cons(rx, A.Asn1.raws(t))))
      (OA.oa.sl_trans(rx, B.Octets.append(rx, rt), c, OA.oa.sl_front(rx, rt), (u, (v, eq2))), pm.all_concat(t, c, OA.oa.sl_trans(rt, B.Octets.append(rx, rt), c, OA.oa.sl_back(rx, rt), (u, (v, eq2)))))

def pm.ion(items: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, +r: R.Asn1Rules, +e: A.Asn1Tlv, +eq: {A.Asn1.items(r, e) == items : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>}) -> pm.all(Sc.a1.s.items_or_nil(items), A.Asn1Tlv.raw(e)):
  match items:
    case Fail{x}:
      Unit{}
    case Done{+xs}:
      +ct = A.Asn1.contents(r, e)
      pm.all_concat(xs, A.Asn1Tlv.raw(e), OA.oa.sl_eq(ct, B.Octets.concat(A.Asn1.raws(xs)), A.Asn1Tlv.raw(e), Equal.sym(B.Octets, B.Octets.concat(A.Asn1.raws(xs)), ct, PS.ps.items(r, e, xs, eq)), PS.ps.contents(r, e)))

def pm.aslots(a: Sc.A1Aligned) -> List<&2, Sc.A1Slot>:
  match a:
    case Sc.A1Aligned{sl, ex}:
      sl

def pm.slot_some(+s: Sc.Asn1Schema, +e: A.Asn1Tlv, a: Sc.A1Aligned, +c: B.Octets, he: OA.oa.sl(A.Asn1Tlv.raw(e), c), ha: pm.slots(pm.aslots(a), c)) -> pm.slots(pm.aslots(Sc.a1.s.slot(Sc.A1Slot{s, Some{e}}, a)), c):
  match a:
    case Sc.A1Aligned{xs, ex}:
      (he, ha)

def pm.slot_none(+s: Sc.Asn1Schema, a: Sc.A1Aligned, +c: B.Octets, ha: pm.slots(pm.aslots(a), c)) -> pm.slots(pm.aslots(Sc.a1.s.slot(Sc.A1Slot{s, None{}}, a)), c):
  match a:
    case Sc.A1Aligned{xs, ex}:
      ha

def pm.align(fs: List<&2, Sc.Asn1Schema>, hit: Bool, es: List<&2, A.Asn1Tlv>, +c: B.Octets, h: pm.all(es, c)) -> pm.slots(pm.aslots(Sc.a1.s.align(fs, hit, es)), c):
  match fs hit es:
    case Nil{} _ Nil{}:
      Unit{}
    case Nil{} _ Con{e, t}:
      Unit{}
    case Con{+s, +rest} True{} Con{+e, +t}:
      (he, ht) = h
      pm.slot_some(s, e, Sc.a1.s.align(rest, Sc.a1.s.hit_head(rest, t), t), c, he, pm.align(rest, Sc.a1.s.hit_head(rest, t), t, c, ht))
    case Con{+s, +rest} True{} Nil{}:
      pm.slot_none(s, Sc.a1.s.align(rest, Sc.a1.s.hit_head(rest, Nil{}), Nil{}), c, pm.align(rest, Sc.a1.s.hit_head(rest, Nil{}), Nil{}, c, Unit{}))
    case Con{+s, +rest} False{} +es2:
      pm.slot_none(s, Sc.a1.s.align(rest, Sc.a1.s.hit_head(rest, es2), es2), c, pm.align(rest, Sc.a1.s.hit_head(rest, es2), es2, c, h))

def pm.pre_al(a: Sc.A1Aligned, +c: B.Octets, h: pm.slots(pm.aslots(a), c)) -> pm.pre(Sc.a1.s.work_of(a), c):
  match a:
    case Sc.A1Aligned{sl, ex}:
      h

def pm.post_al(a: Sc.A1Aligned, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +c: B.Octets, +d: Nat, h: pm.post(Sc.a1.s.work_of(a), res, c, d)) -> pm.ls(res, c, d):
  match a:
    case Sc.A1Aligned{sl, ex}:
      h

def pm.ofs(xs: List<&2, A.Asn1Tlv>, +item: Sc.Asn1Schema, +c: B.Octets, h: pm.all(xs, c)) -> pm.slots(Sc.a1.s.of_slots(xs, item), c):
  match xs:
    case Nil{}:
      Unit{}
    case Con{x, +t}:
      (hx, ht) = h
      (hx, pm.ofs(t, item, c, ht))

def pm.pre_cw(p: Maybe<&2, Sc.A1Pick>, +e: A.Asn1Tlv, +c: B.Octets) -> pm.pre(Sc.a1.s.choice_work(p, e), c):
  match p:
    case None{}:
      Unit{}
    case Some{Sc.A1Pick{i, s}}:
      Unit{}

def pm.pre_ow(items: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, +inner: Sc.Asn1Schema, +c: B.Octets) -> pm.pre(Sc.a1.s.one_work(items, inner), c):
  match items:
    case Fail{x}:
      Unit{}
    case Done{Nil{}}:
      Unit{}
    case Done{Con{x, Nil{}}}:
      Unit{}
    case Done{Con{x, Con{y, t}}}:
      Unit{}

# results

def pm.raw_tlv(+m: Sc.Asn1Match, +e: A.Asn1Tlv, +c: B.Octets, +h: {Sc.Asn1Match.tlv(m) == Some{e} : Maybe<&2, A.Asn1Tlv>}, hs: OA.oa.sl(A.Asn1Tlv.raw(e), c)) -> OA.oa.sl(Sc.Asn1Match.raw(m), c):
  %Equal.sym(Maybe<&2, A.Asn1Tlv>, Sc.Asn1Match.tlv(m), Some{e}, h) : OA.oa.sl(Sc.a1.s.raw_of(_), c)
  hs

def pm.cons(a: Result<&2, &2, E.Asn1Error, Sc.Asn1Match>, b: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +c: B.Octets, +d: Nat, ha: pm.sm(a, c, d), hb: pm.ls(b, c, d)) -> pm.ls(Sc.a1.s.cons(a, b), c, d):
  match a b:
    case Fail{x} _:
      Unit{}
    case Done{x} Fail{y}:
      Unit{}
    case Done{+x} Done{+ms}:
      (s1, g1) = ha
      pm.mk(d, x, ms, c, s1, g1, hb)

def pm.snone(+der: Bool, s: Sc.Asn1Schema, res0: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +c: B.Octets, +d: Nat) -> pm.sm(Sc.a1.s.slot_res(der, None{}, s, res0), c, d):
  match s:
    case Sc.Asn1SOpt{i}:
      (OA.oa.sl_empty(c), pm.g_absent(d))
    case Sc.Asn1SDefault{i, +v}:
      (OA.oa.sl_empty(c), pm.g_default(v, d))
    case Sc.Asn1SAny{}:
      Unit{}
    case Sc.Asn1SElem{t}:
      Unit{}
    case Sc.Asn1SSeq{t, fs}:
      Unit{}
    case Sc.Asn1SOf{t, i, st}:
      Unit{}
    case Sc.Asn1SChoice{alts}:
      Unit{}
    case Sc.Asn1SExplicit{n, i}:
      Unit{}

def pm.ok1(res0: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +e: A.Asn1Tlv, +c: B.Octets, +d: Nat, hs: OA.oa.sl(A.Asn1Tlv.raw(e), c), h0: pm.ones(res0, e, d)) -> pm.sm(Sc.a1.s.ok1(res0), c, d):
  match res0:
    case Fail{x}:
      Unit{}
    case Done{Nil{}}:
      Unit{}
    case Done{Con{+m, Nil{}}}:
      (+ht, (g, u)) = h0
      (pm.raw_tlv(m, e, c, ht, hs), g)
    case Done{Con{m, Con{y, t}}}:
      Unit{}

def pm.present(ok: Bool, res0: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +e: A.Asn1Tlv, +c: B.Octets, +d: Nat, hs: OA.oa.sl(A.Asn1Tlv.raw(e), c), h0: pm.ones(res0, e, d)) -> pm.sm(Sc.a1.s.present(ok, res0), c, d):
  match ok:
    case True{}:
      pm.ok1(res0, e, c, d, hs, h0)
    case False{}:
      Unit{}

def pm.gate(ok: Bool, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +e: A.Asn1Tlv, +d: Nat, h: pm.ones(res, e, d)) -> pm.ones(Sc.a1.s.gate(ok, res), e, d):
  match ok:
    case True{}:
      h
    case False{}:
      Unit{}

def pm.ierr(items: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +e: A.Asn1Tlv, +d: Nat, h: pm.ones(res, e, d)) -> pm.ones(Sc.a1.s.items_err(items, res), e, d):
  match items:
    case Fail{x}:
      Unit{}
    case Done{xs}:
      h

def pm.elem_one(+e: A.Asn1Tlv, +d: Nat) -> pm.ones(Done{[Sc.Asn1MElem{e}]}, e, d):
  ({==}, (pm.g_elem(e, d), Unit{}))

def pm.wseq(+e: A.Asn1Tlv, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +d: Nat, h: pm.ls(res, A.Asn1Tlv.raw(e), pm.dm1(d))) -> pm.ones(Sc.a1.s.wrap_seq(e, res), e, d):
  match res:
    case Fail{x}:
      Unit{}
    case Done{+ms}:
      match d:
        case 0n:
          ({==}, ((OA.oa.sl_refl(A.Asn1Tlv.raw(e)), Unit{}), Unit{}))
        case 1n+k:
          ({==}, ((OA.oa.sl_refl(A.Asn1Tlv.raw(e)), (h, Unit{})), Unit{}))

def pm.choice2(+i: Nat, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +e: A.Asn1Tlv, +d: Nat, h: pm.ones(res, e, pm.dm1(d))) -> pm.ones(Sc.a1.s.wrap_choice(i, res), e, d):
  match res:
    case Fail{x}:
      Unit{}
    case Done{Nil{}}:
      Unit{}
    case Done{Con{+m, Nil{}}}:
      match d:
        case 0n:
          (ht, (g, u)) = h
          (ht, ((OA.oa.sl_refl(Sc.Asn1Match.raw(m)), Unit{}), Unit{}))
        case 1n+k:
          (ht, (g, u)) = h
          (ht, ((OA.oa.sl_refl(Sc.Asn1Match.raw(m)), (g, Unit{})), Unit{}))
    case Done{Con{m, Con{y, t}}}:
      Unit{}

def pm.choice(p: Maybe<&2, Sc.A1Pick>, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +e: A.Asn1Tlv, +c: B.Octets, +d: Nat, h: pm.post(Sc.a1.s.choice_work(p, e), res, c, pm.dm1(d))) -> pm.ones(Sc.a1.s.choice_res(p, res), e, d):
  match p:
    case None{}:
      Unit{}
    case Some{Sc.A1Pick{+i, s}}:
      pm.choice2(i, res, e, d, h)

def pm.expl2(+e: A.Asn1Tlv, +x: A.Asn1Tlv, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +d: Nat, hx: OA.oa.sl(A.Asn1Tlv.raw(x), A.Asn1Tlv.raw(e)), h: pm.ones(res, x, pm.dm1(d))) -> pm.ones(Sc.a1.s.wrap_explicit(e, res), e, d):
  match res:
    case Fail{y}:
      Unit{}
    case Done{Nil{}}:
      Unit{}
    case Done{Con{+m, Nil{}}}:
      match d:
        case 0n:
          ({==}, ((OA.oa.sl_refl(A.Asn1Tlv.raw(e)), Unit{}), Unit{}))
        case 1n+ +k:
          (+ht, (g, u)) = h
          ({==}, ((OA.oa.sl_refl(A.Asn1Tlv.raw(e)), (pm.rebase(m, A.Asn1Tlv.raw(e), k, pm.raw_tlv(m, x, A.Asn1Tlv.raw(e), ht, hx), g), Unit{})), Unit{}))
    case Done{Con{m, Con{y, t}}}:
      Unit{}

def pm.expl(items: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, +inner: Sc.Asn1Schema, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +e: A.Asn1Tlv, +c: B.Octets, +d: Nat, hall: pm.all(Sc.a1.s.items_or_nil(items), A.Asn1Tlv.raw(e)), h: pm.post(Sc.a1.s.one_work(items, inner), res, c, pm.dm1(d))) -> pm.ones(Sc.a1.s.one_res(items, e, res), e, d):
  match items:
    case Fail{y}:
      Unit{}
    case Done{Nil{}}:
      Unit{}
    case Done{Con{+x, Nil{}}}:
      (hx, u) = hall
      pm.expl2(e, x, res, d, hx, h)
    case Done{Con{x, Con{y, t}}}:
      Unit{}

def pm.m(f: Nat, +r: R.Asn1Rules, w: Sc.A1Work, +c: B.Octets, +d: Nat, hp: pm.pre(w, c)) -> pm.post(w, Sc.a1.s.m(f, r, w), c, d):
  match f:
    case 0n:
      match w:
        case Sc.A1WOne{s, e}:
          Unit{}
        case Sc.A1WSlots{sl, ex}:
          Unit{}
        case Sc.A1WNone{}:
          Unit{}
    case 1n+ +g:
      match w:
        case Sc.A1WNone{}:
          Unit{}
        case Sc.A1WSlots{Nil{}, True{}}:
          Unit{}
        case Sc.A1WSlots{Nil{}, False{}}:
          pm.gnil(d, c)
        case Sc.A1WSlots{Con{Sc.A1Slot{+s, me}, +rest}, +ex}:
          match me:
            case None{}:
              +der = R.Asn1Rules.values(r)
              +res0 = Sc.a1.s.m(g, r, Sc.a1.s.slot_work(s, None{}))
              pm.cons(Sc.a1.s.slot_res(der, None{}, s, res0), Sc.a1.s.m(g, r, Sc.A1WSlots{rest, ex}), c, d, pm.snone(der, s, res0, c, d), pm.m(g, r, Sc.A1WSlots{rest, ex}, c, d, hp))
            case Some{+e}:
              (hs, hr) = hp
              +der = R.Asn1Rules.values(r)
              +res0 = Sc.a1.s.m(g, r, Sc.A1WOne{Sc.a1.s.inner(s), e})
              pm.cons(Sc.a1.s.slot_res(der, Some{e}, s, res0), Sc.a1.s.m(g, r, Sc.A1WSlots{rest, ex}), c, d, pm.present(Sc.a1.s.default_ok(der, s, e), res0, e, c, d, hs, pm.m(g, r, Sc.A1WOne{Sc.a1.s.inner(s), e}, c, d, Unit{})), pm.m(g, r, Sc.A1WSlots{rest, ex}, c, d, hr))
        case Sc.A1WOne{Sc.Asn1SAny{}, +e}:
          pm.elem_one(e, d)
        case Sc.A1WOne{Sc.Asn1SElem{+t}, +e}:
          pm.gate(Sc.a1.s.tag_ok(t, False{}, e), Done{[Sc.Asn1MElem{e}]}, e, d, pm.elem_one(e, d))
        case Sc.A1WOne{Sc.Asn1SSeq{+t, +fs}, +e}:
          +items = A.Asn1.items(r, e)
          +xs = Sc.a1.s.items_or_nil(items)
          +a = Sc.a1.s.align(fs, Sc.a1.s.hit_head(fs, xs), xs)
          +res = Sc.a1.s.m(g, r, Sc.a1.s.work_of(a))
          ih = pm.m(g, r, Sc.a1.s.work_of(a), A.Asn1Tlv.raw(e), pm.dm1(d), pm.pre_al(a, A.Asn1Tlv.raw(e), pm.align(fs, Sc.a1.s.hit_head(fs, xs), xs, A.Asn1Tlv.raw(e), pm.ion(items, r, e, {==}))))
          pm.gate(Sc.a1.s.tag_ok(t, True{}, e), Sc.a1.s.items_err(items, Sc.a1.s.wrap_seq(e, res)), e, d, pm.ierr(items, Sc.a1.s.wrap_seq(e, res), e, d, pm.wseq(e, res, d, pm.post_al(a, res, A.Asn1Tlv.raw(e), pm.dm1(d), ih))))
        case Sc.A1WOne{Sc.Asn1SOf{+t, +item, +set}, +e}:
          +items = A.Asn1.items(r, e)
          +xs = Sc.a1.s.items_or_nil(items)
          +w2 : Sc.A1Work = Sc.A1WSlots{Sc.a1.s.of_slots(xs, item), False{}}
          +res = Sc.a1.s.m(g, r, w2)
          ih = pm.m(g, r, w2, A.Asn1Tlv.raw(e), pm.dm1(d), pm.ofs(xs, item, A.Asn1Tlv.raw(e), pm.ion(items, r, e, {==})))
          pm.gate(Bool.and(Sc.a1.s.tag_ok(t, True{}, e), Sc.a1.s.set_ok(set, r, xs)), Sc.a1.s.items_err(items, Sc.a1.s.wrap_seq(e, res)), e, d, pm.ierr(items, Sc.a1.s.wrap_seq(e, res), e, d, pm.wseq(e, res, d, ih)))
        case Sc.A1WOne{Sc.Asn1SChoice{+alts}, +e}:
          +p = Sc.a1.s.pick(alts, Sc.a1.s.tlv_tag(e), 0n)
          pm.choice(p, Sc.a1.s.m(g, r, Sc.a1.s.choice_work(p, e)), e, c, d, pm.m(g, r, Sc.a1.s.choice_work(p, e), c, pm.dm1(d), pm.pre_cw(p, e, c)))
        case Sc.A1WOne{Sc.Asn1SExplicit{+n, +inner}, +e}:
          +items = A.Asn1.items(r, e)
          +w2 = Sc.a1.s.one_work(items, inner)
          +res = Sc.a1.s.m(g, r, w2)
          pm.gate(Sc.a1.s.tag_ok(T.Asn1Tag.context(n), True{}, e), Sc.a1.s.one_res(items, e, res), e, d, pm.expl(items, inner, res, e, c, d, pm.ion(items, r, e, {==}), pm.m(g, r, w2, c, pm.dm1(d), pm.pre_ow(items, inner, c))))
        case Sc.A1WOne{Sc.Asn1SOpt{+inner}, +e}:
          pm.m(g, r, Sc.A1WOne{inner, e}, c, d, Unit{})
        case Sc.A1WOne{Sc.Asn1SDefault{+inner, v}, +e}:
          pm.m(g, r, Sc.A1WOne{inner, e}, c, d, Unit{})

# From the matcher to the public matchers

def pm.mdisc(z: Result<&2, &2, E.Asn1Error, Sc.Asn1Match>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pm.mfd(-x: E.Asn1Error, -y: Sc.Asn1Match, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> Empty:
  %e : pm.mdisc(_)
  Unit{}

def pm.mval(z: Result<&2, &2, E.Asn1Error, Sc.Asn1Match>) -> Sc.Asn1Match:
  match z:
    case Fail{x}:
      Sc.Asn1MAbsent{}
    case Done{v}:
      v

def pm.top(res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +x: A.Asn1Tlv, +m: Sc.Asn1Match, +d: Nat, +e: {Sc.a1.s.ok1(res) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}, h: pm.ones(res, x, d)) -> {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>} & pm.gl(d, [m], Sc.Asn1Match.raw(m)):
  match res:
    case Fail{er}:
      Empty.absurd({Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>} & pm.gl(d, [m], Sc.Asn1Match.raw(m)), pm.mfd(er, m, e))
    case Done{Nil{}}:
      Empty.absurd({Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>} & pm.gl(d, [m], Sc.Asn1Match.raw(m)), pm.mfd(E.Asn1SchemaMismatch{}, m, e))
    case Done{Con{+m0, Nil{}}}:
      (ht, (g, u)) = h
      +em = Equal.cong(Result<&2, &2, E.Asn1Error, Sc.Asn1Match>, Sc.Asn1Match, z => pm.mval(z), Done{m0}, Done{m}, e)
      %em : {Sc.Asn1Match.tlv(_) == Some{x} : Maybe<&2, A.Asn1Tlv>} & pm.gl(d, [_], Sc.Asn1Match.raw(_))
      (ht, g)
    case Done{Con{m0, Con{y, t}}}:
      Empty.absurd({Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>} & pm.gl(d, [m], Sc.Asn1Match.raw(m)), pm.mfd(E.Asn1SchemaMismatch{}, m, e))

# a match of an element: its element, and what it holds within its octets
def pm.tlv_top(+r: R.Asn1Rules, +s: Sc.Asn1Schema, x: A.Asn1Tlv, +m: Sc.Asn1Match, +d: Nat, +e: {Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>} & pm.gl(d, [m], Sc.Asn1Match.raw(m)):
  match x:
    case A.Asn1Tlv{+n, +raw}:
      +w : Sc.A1Work = Sc.A1WOne{s, A.Asn1Tlv{n, raw}}
      +f = Nat.mul(Nat.add(B.Octets.len(raw), 1n), 64n)
      pm.top(Sc.a1.s.m(f, r, w), A.Asn1Tlv{n, raw}, m, d, e, pm.m(f, r, w, raw, d, Unit{}))

def pm.fst_t(+m: Sc.Asn1Match, +x: A.Asn1Tlv, +d: Nat, p: {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>} & pm.gl(d, [m], Sc.Asn1Match.raw(m))) -> {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>}:
  (a, b) = p
  a

# law match_tlv_tlv
def pm.tlvtlv(+r: R.Asn1Rules, +s: Sc.Asn1Schema, +x: A.Asn1Tlv, +m: Sc.Asn1Match, +e: {Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>}:
  pm.fst_t(m, x, 0n, pm.tlv_top(r, s, x, m, 0n, e))

def pm.raw_eq(+m: Sc.Asn1Match, +x: A.Asn1Tlv, +h: {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>}) -> {Sc.Asn1Match.raw(m) == A.Asn1Tlv.raw(x) : B.Octets}:
  Equal.cong(Maybe<&2, A.Asn1Tlv>, B.Octets, z => Sc.a1.s.raw_of(z), Sc.Asn1Match.tlv(m), Some{x}, h)

# following p, then q, from a match

def pm.w3(+q: List<&2, Sc.Asn1Step>, +m1: Sc.Asn1Match, fq: OA.oa.sl(Sc.Asn1Match.raw(Sc.a1.s.follow(q, m1)), Sc.Asn1Match.raw(m1)) & pm.gl(0n, [Sc.a1.s.follow(q, m1)], Sc.Asn1Match.raw(Sc.a1.s.follow(q, m1)))) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.a1.s.follow(q, m1)), Sc.Asn1Match.raw(m1)):
  (s, g) = fq
  s

def pm.w2(+q: List<&2, Sc.Asn1Step>, +m1: Sc.Asn1Match, +top: B.Octets, fp: OA.oa.sl(Sc.Asn1Match.raw(m1), top) & pm.gl(Nat.add(pm.len(q), 0n), [m1], Sc.Asn1Match.raw(m1))) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.a1.s.follow(q, m1)), Sc.Asn1Match.raw(m1)):
  (s, g) = fp
  pm.w3(q, m1, pm.follow(q, m1, Sc.Asn1Match.raw(m1), 0n, (OA.oa.sl_refl(Sc.Asn1Match.raw(m1)), g)))

def pm.w1(+m: Sc.Asn1Match, +p: List<&2, Sc.Asn1Step>, +q: List<&2, Sc.Asn1Step>, +x: A.Asn1Tlv, hp: {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>} & pm.gl(Nat.add(pm.len(p), Nat.add(pm.len(q), 0n)), [m], Sc.Asn1Match.raw(m))) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.a1.s.follow(q, Sc.a1.s.follow(p, m))), Sc.Asn1Match.raw(Sc.a1.s.follow(p, m))):
  (ht, g) = hp
  pm.w2(q, Sc.a1.s.follow(p, m), Sc.Asn1Match.raw(m), pm.follow(p, m, Sc.Asn1Match.raw(m), Nat.add(pm.len(q), 0n), (OA.oa.sl_refl(Sc.Asn1Match.raw(m)), g)))

# law match_tlv_within
def pm.tlv_within(+r: R.Asn1Rules, +s: Sc.Asn1Schema, +x: A.Asn1Tlv, +m: Sc.Asn1Match, +p: List<&2, Sc.Asn1Step>, +q: List<&2, Sc.Asn1Step>, +e: {Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, List.append(&2, Sc.Asn1Step, p, q))), Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p))):
  %Equal.sym(Sc.Asn1Match, Sc.a1.s.follow(List.append(&2, Sc.Asn1Step, p, q), m), Sc.a1.s.follow(q, Sc.a1.s.follow(p, m)), pm.fapp(p, q, m)) : OA.oa.sl(Sc.Asn1Match.raw(_), Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)))
  pm.w1(m, p, q, x, pm.tlv_top(r, s, x, m, Nat.add(pm.len(p), Nat.add(pm.len(q), 0n)), e))

# A match of octets: the element read, matched

def pm.top2(ok: Bool, +r: R.Asn1Rules, +s: Sc.Asn1Schema, +x: A.Asn1Tlv, +m: Sc.Asn1Match, +e: {Sc.a1.s.top2(ok, r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> {Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>} & {ok == True{} : Bool}:
  match ok:
    case True{}:
      (e, {==})
    case False{}:
      Empty.absurd({Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>} & {False{} == True{} : Bool}, pm.mfd(E.Asn1Trailing{}, m, e))

def pm.mt(+r: R.Asn1Rules, +s: Sc.Asn1Schema, +b: B.Octets, +m: Sc.Asn1Match) -> Type:
  Sigma<&1, &1, A.Asn1Tlv, x => Sigma<&1, &1, B.Octets, rest => {A.Asn1.read(r, b) == Done{A.Asn1TlvRead{x, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>} & ({Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>} & {Bool.or(R.Asn1Rules.trailing(r), Nat.is_eq(B.Octets.len(rest), 0n)) == True{} : Bool})>>

def pm.mtop(res: Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>, +r: R.Asn1Rules, +s: Sc.Asn1Schema, +b: B.Octets, +m: Sc.Asn1Match, +eq: {A.Asn1.read(r, b) == res : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}, +e: {Sc.a1.s.top(r, s, res) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> pm.mt(r, s, b, m):
  match res:
    case Fail{er}:
      Empty.absurd(pm.mt(r, s, b, m), pm.mfd(er, m, e))
    case Done{A.Asn1TlvRead{+x, +rest}}:
      (x, (rest, (eq, pm.top2(Bool.or(R.Asn1Rules.trailing(r), Nat.is_eq(B.Octets.len(rest), 0n)), r, s, x, m, e))))

def pm.mread(+r: R.Asn1Rules, +s: Sc.Asn1Schema, +b: B.Octets, +m: Sc.Asn1Match, +e: {Sc.Asn1.match(r, s, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> pm.mt(r, s, b, m):
  pm.mtop(A.Asn1.read(r, b), r, s, b, m, {==}, e)

# law match_split
def pm.msplit(+r: R.Asn1Rules, +s: Sc.Asn1Schema, +b: B.Octets, +m: Sc.Asn1Match, mt: pm.mt(r, s, b, m)) -> Sigma<&1, &1, B.Octets, rest => {B.Octets.append(Sc.Asn1Match.raw(m), rest) == b : B.Octets}>:
  (+x, (+rest, (+er, (+em, ok)))) = mt
  +hr = pm.raw_eq(m, x, pm.tlvtlv(r, s, x, m, em))
  (rest, Equal.trans(B.Octets, B.Octets.append(Sc.Asn1Match.raw(m), rest), B.Octets.append(A.Asn1Tlv.raw(x), rest), b, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(z, rest), Sc.Asn1Match.raw(m), A.Asn1Tlv.raw(x), hr), PS.ps.read(r, b, x, rest, er)))

def pm.ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+k:
      Unit

def pm.nfd(-k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  %e : pm.ndisc(_)
  Unit{}

def pm.nil_len(xs: List<&2, U32>, +h: {List.length(&2, U32, xs) == 0n : Nat}) -> {xs == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, t}:
      Empty.absurd({Con{y, t} == Nil{} : List<&2, U32>}, pm.nfd(List.length(&2, U32, t), h))

def pm.or_f(a: Bool, -b: Bool, +ha: {a == False{} : Bool}, +h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, AN.an.tf(ha))
    case False{}:
      h

# octets of length 0 are empty
def pm.len0(+o: B.Octets, +h: {Nat.is_eq(B.Octets.len(o), 0n) == True{} : Bool}) -> {o == B.Octets.empty() : B.Octets}:
  +hl = Equal.trans(Nat, List.length(&2, U32, B.Octets.to_list(o)), B.Octets.len(o), 0n, Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o)), AN.an.eq_sound(B.Octets.len(o), 0n, h))
  OA.oa.ext(o, B.Octets.empty(), Equal.trans(List<&2, U32>, B.Octets.to_list(o), Nil{}, B.Octets.to_list(B.Octets.empty()), pm.nil_len(B.Octets.to_list(o), hl), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.empty()), Nil{}, OA.oa.empty_list())))

# law match_whole
def pm.mwhole(+r: R.Asn1Rules, +ht: {R.Asn1Rules.trailing(r) == False{} : Bool}, +s: Sc.Asn1Schema, +b: B.Octets, +m: Sc.Asn1Match, mt: pm.mt(r, s, b, m)) -> {Sc.Asn1Match.raw(m) == b : B.Octets}:
  (+x, (+rest, (+er, (+em, ok)))) = mt
  +hr = pm.raw_eq(m, x, pm.tlvtlv(r, s, x, m, em))
  +he = pm.len0(rest, pm.or_f(R.Asn1Rules.trailing(r), Nat.is_eq(B.Octets.len(rest), 0n), ht, ok))
  +hs = PS.ps.read(r, b, x, rest, er)
  %OA.oa.app_empty_r(Sc.Asn1Match.raw(m)) : {_ == b : B.Octets}
  %he : {B.Octets.append(Sc.Asn1Match.raw(m), _) == b : B.Octets}
  %Equal.sym(B.Octets, Sc.Asn1Match.raw(m), A.Asn1Tlv.raw(x), hr) : {B.Octets.append(_, rest) == b : B.Octets}
  hs

# law match_within
def pm.mwithin(+r: R.Asn1Rules, +s: Sc.Asn1Schema, +b: B.Octets, +m: Sc.Asn1Match, +p: List<&2, Sc.Asn1Step>, +q: List<&2, Sc.Asn1Step>, mt: pm.mt(r, s, b, m)) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, List.append(&2, Sc.Asn1Step, p, q))), Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p))):
  (+x, (+rest, (+er, (+em, ok)))) = mt
  pm.tlv_within(r, s, x, m, p, q, em)

# law match_input
def pm.minput2(+m: Sc.Asn1Match, +p: List<&2, Sc.Asn1Step>, +b: B.Octets, hw: OA.oa.sl(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)), Sc.Asn1Match.raw(m)), sp: Sigma<&1, &1, B.Octets, rest => {B.Octets.append(Sc.Asn1Match.raw(m), rest) == b : B.Octets}>) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)), b):
  (+rest, +e) = sp
  %e : OA.oa.sl(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)), _)
  OA.oa.sl_trans(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)), Sc.Asn1Match.raw(m), B.Octets.append(Sc.Asn1Match.raw(m), rest), hw, OA.oa.sl_front(Sc.Asn1Match.raw(m), rest))

def pm.minput(+r: R.Asn1Rules, +s: Sc.Asn1Schema, +b: B.Octets, +m: Sc.Asn1Match, +p: List<&2, Sc.Asn1Step>, +e: {Sc.Asn1.match(r, s, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> OA.oa.sl(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)), b):
  pm.minput2(m, p, b, pm.mwithin(r, s, b, m, Nil{}, p, pm.mread(r, s, b, m, e)), pm.msplit(r, s, b, m, pm.mread(r, s, b, m, e)))

def pm.tdisc(z: Maybe<&2, A.Asn1Tlv>) -> Type:
  match z:
    case None{}:
      Unit
    case Some{y}:
      Empty

def pm.tfd(-x: A.Asn1Tlv, e: {None{} == Some{x} : Maybe<&2, A.Asn1Tlv>}) -> Empty:
  %e : pm.tdisc(_)
  Unit{}

# the element a match holds
def pm.node_of(m: Sc.Asn1Match, +x: A.Asn1Tlv, +h: {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>}) -> {Sc.Asn1Match.node(m) == Some{A.Asn1Tlv.node(x)} : Maybe<&2, N.Asn1Node>}:
  match m:
    case Sc.Asn1MElem{+e}:
      %Equal.sym(Maybe<&2, A.Asn1Tlv>, Some{e}, Some{x}, h) : {Maybe.map(&2, A.Asn1Tlv, N.Asn1Node, z => A.Asn1Tlv.node(z), _) == Some{A.Asn1Tlv.node(x)} : Maybe<&2, N.Asn1Node>}
      {==}
    case Sc.Asn1MSeq{+e, ms}:
      %Equal.sym(Maybe<&2, A.Asn1Tlv>, Some{e}, Some{x}, h) : {Maybe.map(&2, A.Asn1Tlv, N.Asn1Node, z => A.Asn1Tlv.node(z), _) == Some{A.Asn1Tlv.node(x)} : Maybe<&2, N.Asn1Node>}
      {==}
    case Sc.Asn1MExplicit{+e, y}:
      %Equal.sym(Maybe<&2, A.Asn1Tlv>, Some{e}, Some{x}, h) : {Maybe.map(&2, A.Asn1Tlv, N.Asn1Node, z => A.Asn1Tlv.node(z), _) == Some{A.Asn1Tlv.node(x)} : Maybe<&2, N.Asn1Node>}
      {==}
    case Sc.Asn1MChoice{i, +y}:
      %Equal.sym(Maybe<&2, A.Asn1Tlv>, Sc.Asn1Match.tlv(y), Some{x}, h) : {Maybe.map(&2, A.Asn1Tlv, N.Asn1Node, z => A.Asn1Tlv.node(z), _) == Some{A.Asn1Tlv.node(x)} : Maybe<&2, N.Asn1Node>}
      {==}
    case Sc.Asn1MAbsent{}:
      Empty.absurd({Sc.Asn1Match.node(Sc.Asn1MAbsent{}) == Some{A.Asn1Tlv.node(x)} : Maybe<&2, N.Asn1Node>}, pm.tfd(x, h))
    case Sc.Asn1MDefault{v}:
      Empty.absurd({Sc.Asn1Match.node(Sc.Asn1MDefault{v}) == Some{A.Asn1Tlv.node(x)} : Maybe<&2, N.Asn1Node>}, pm.tfd(x, h))

# law match_der
def pm.mder(+r: R.Asn1Rules, +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}, +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}, +s: Sc.Asn1Schema, +b: B.Octets, +m: Sc.Asn1Match, mt: pm.mt(r, s, b, m)) -> Sigma<&1, &1, N.Asn1Node, n => {Sc.Asn1Match.node(m) == Some{n} : Maybe<&2, N.Asn1Node>} & {En.Asn1.encode(n) == Done{Sc.Asn1Match.raw(m)} : Result<&2, &2, E.Asn1Error, B.Octets>}>:
  (+x, (+rest, (+er, (+em, ok)))) = mt
  +ht = pm.tlvtlv(r, s, x, m, em)
  +hr = pm.raw_eq(m, x, ht)
  +hd = PD.pd.read_der(r, hm, hi, b, x, rest, er)
  (A.Asn1Tlv.node(x), (pm.node_of(m, x, ht), Equal.trans(Result<&2, &2, E.Asn1Error, B.Octets>, En.Asn1.encode(A.Asn1Tlv.node(x)), Done{A.Asn1Tlv.raw(x)}, Done{Sc.Asn1Match.raw(m)}, hd, Equal.cong(B.Octets, Result<&2, &2, E.Asn1Error, B.Octets>, z => Done{z}, A.Asn1Tlv.raw(x), Sc.Asn1Match.raw(m), Equal.sym(B.Octets, Sc.Asn1Match.raw(m), A.Asn1Tlv.raw(x), hr)))))

# SET OF and SEQUENCE OF matches are of constructed elements of their tag

def pm.cls_eq(c: T.Asn1Class, d: T.Asn1Class, +h: {T.Asn1Class.is_eq(c, d) == True{} : Bool}) -> {c == d : T.Asn1Class}:
  match c d:
    case T.Asn1Universal{} T.Asn1Universal{}:
      {==}
    case T.Asn1Universal{} T.Asn1Application{}:
      Empty.absurd({T.Asn1Universal{} == T.Asn1Application{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Universal{} T.Asn1Context{}:
      Empty.absurd({T.Asn1Universal{} == T.Asn1Context{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Universal{} T.Asn1Private{}:
      Empty.absurd({T.Asn1Universal{} == T.Asn1Private{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Application{} T.Asn1Universal{}:
      Empty.absurd({T.Asn1Application{} == T.Asn1Universal{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Application{} T.Asn1Application{}:
      {==}
    case T.Asn1Application{} T.Asn1Context{}:
      Empty.absurd({T.Asn1Application{} == T.Asn1Context{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Application{} T.Asn1Private{}:
      Empty.absurd({T.Asn1Application{} == T.Asn1Private{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Context{} T.Asn1Universal{}:
      Empty.absurd({T.Asn1Context{} == T.Asn1Universal{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Context{} T.Asn1Application{}:
      Empty.absurd({T.Asn1Context{} == T.Asn1Application{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Context{} T.Asn1Context{}:
      {==}
    case T.Asn1Context{} T.Asn1Private{}:
      Empty.absurd({T.Asn1Context{} == T.Asn1Private{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Private{} T.Asn1Universal{}:
      Empty.absurd({T.Asn1Private{} == T.Asn1Universal{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Private{} T.Asn1Application{}:
      Empty.absurd({T.Asn1Private{} == T.Asn1Application{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Private{} T.Asn1Context{}:
      Empty.absurd({T.Asn1Private{} == T.Asn1Context{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Private{} T.Asn1Private{}:
      {==}

def pm.tag_eq(t: T.Asn1Tag, u: T.Asn1Tag, +h: {T.Asn1Tag.is_eq(t, u) == True{} : Bool}) -> {t == u : T.Asn1Tag}:
  match t u:
    case T.Asn1Tag{+c, +n} T.Asn1Tag{+d, +k}:
      +hc = pm.cls_eq(c, d, AN.an.and_l(T.Asn1Class.is_eq(c, d), Nat.is_eq(n, k), h))
      +hn = AN.an.eq_sound(n, k, AN.an.and_r(T.Asn1Class.is_eq(c, d), Nat.is_eq(n, k), h))
      %hc : {T.Asn1Tag{c, n} == T.Asn1Tag{_, k} : T.Asn1Tag}
      %hn : {T.Asn1Tag{c, n} == T.Asn1Tag{c, _} : T.Asn1Tag}
      {==}

def pm.tag_cons(+t: T.Asn1Tag, n: N.Asn1Node, +raw: B.Octets, +h: {Sc.a1.s.tag_ok(t, True{}, A.Asn1Tlv{n, raw}) == True{} : Bool}) -> Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {n == N.Asn1Cons{t, ns} : N.Asn1Node}>:
  match n:
    case N.Asn1Prim{+tg, o}:
      Empty.absurd(Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {N.Asn1Prim{tg, o} == N.Asn1Cons{t, ns} : N.Asn1Node}>, AN.an.ft(AN.an.and_r(T.Asn1Tag.is_eq(t, tg), False{}, h)))
    case N.Asn1Cons{+tg, +ns}:
      +he = pm.tag_eq(t, tg, AN.an.and_l(T.Asn1Tag.is_eq(t, tg), True{}, h))
      (ns, Equal.cong(T.Asn1Tag, N.Asn1Node, z => N.Asn1Cons{z, ns}, tg, t, Equal.sym(T.Asn1Tag, t, tg, he)))

def pm.gate_ok(ok: Bool, res: Result<&2, &2, E.Asn1Error, List<&2, Sc.Asn1Match>>, +m: Sc.Asn1Match, +e: {Sc.a1.s.ok1(Sc.a1.s.gate(ok, res)) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, pm.mfd(E.Asn1SchemaMismatch{}, m, e))

def pm.of_f(f: Nat, +r: R.Asn1Rules, +t: T.Asn1Tag, +item: Sc.Asn1Schema, +set: Bool, +n: N.Asn1Node, +raw: B.Octets, +m: Sc.Asn1Match, +e: {Sc.a1.s.ok1(Sc.a1.s.m(f, r, Sc.A1WOne{Sc.Asn1SOf{t, item, set}, A.Asn1Tlv{n, raw}})) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {n == N.Asn1Cons{t, ns} : N.Asn1Node}>:
  match f:
    case 0n:
      Empty.absurd(Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {n == N.Asn1Cons{t, ns} : N.Asn1Node}>, pm.mfd(E.Asn1Exhausted{}, m, e))
    case 1n+ +g:
      +x : A.Asn1Tlv = A.Asn1Tlv{n, raw}
      +items = A.Asn1.items(r, x)
      +xs = Sc.a1.s.items_or_nil(items)
      +w2 : Sc.A1Work = Sc.A1WSlots{Sc.a1.s.of_slots(xs, item), False{}}
      +ok = Bool.and(Sc.a1.s.tag_ok(t, True{}, x), Sc.a1.s.set_ok(set, r, xs))
      +hok = pm.gate_ok(ok, Sc.a1.s.items_err(items, Sc.a1.s.wrap_seq(x, Sc.a1.s.m(g, r, w2))), m, e)
      pm.tag_cons(t, n, raw, AN.an.and_l(Sc.a1.s.tag_ok(t, True{}, x), Sc.a1.s.set_ok(set, r, xs), hok))

def pm.of_x(+r: R.Asn1Rules, +t: T.Asn1Tag, +item: Sc.Asn1Schema, +set: Bool, x: A.Asn1Tlv, +m: Sc.Asn1Match, +e: {Sc.Asn1.match_tlv(r, Sc.Asn1SOf{t, item, set}, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}) -> Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {A.Asn1Tlv.node(x) == N.Asn1Cons{t, ns} : N.Asn1Node}>:
  match x:
    case A.Asn1Tlv{+n, +raw}:
      pm.of_f(Nat.mul(Nat.add(B.Octets.len(raw), 1n), 64n), r, t, item, set, n, raw, m, e)

def pm.mof2(+m: Sc.Asn1Match, +x: A.Asn1Tlv, +t: T.Asn1Tag, +hn: {Sc.Asn1Match.node(m) == Some{A.Asn1Tlv.node(x)} : Maybe<&2, N.Asn1Node>}, hx: Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {A.Asn1Tlv.node(x) == N.Asn1Cons{t, ns} : N.Asn1Node}>) -> Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {Sc.Asn1Match.node(m) == Some{N.Asn1Cons{t, ns}} : Maybe<&2, N.Asn1Node>}>:
  (+ns, +e) = hx
  (ns, Equal.trans(Maybe<&2, N.Asn1Node>, Sc.Asn1Match.node(m), Some{A.Asn1Tlv.node(x)}, Some{N.Asn1Cons{t, ns}}, hn, Equal.cong(N.Asn1Node, Maybe<&2, N.Asn1Node>, z => Some{z}, A.Asn1Tlv.node(x), N.Asn1Cons{t, ns}, e)))

# law match_of_node
def pm.mof(+r: R.Asn1Rules, +t: T.Asn1Tag, +item: Sc.Asn1Schema, +set: Bool, +b: B.Octets, +m: Sc.Asn1Match, mt: pm.mt(r, Sc.Asn1SOf{t, item, set}, b, m)) -> Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {Sc.Asn1Match.node(m) == Some{N.Asn1Cons{t, ns}} : Maybe<&2, N.Asn1Node>}>:
  (+x, (+rest, (+er, (+em, ok)))) = mt
  pm.mof2(m, x, t, pm.node_of(m, x, pm.tlvtlv(r, Sc.Asn1SOf{t, item, set}, x, m, em)), pm.of_x(r, t, item, set, x, m, em))

# law at_items
def pm.nth_app(pre: List<&2, Sc.Asn1Match>, +x: Sc.Asn1Match, +post: List<&2, Sc.Asn1Match>) -> {Sc.a1.s.nth(List.append(&2, Sc.Asn1Match, pre, Con{x, post}), List.length(&2, Sc.Asn1Match, pre)) == x : Sc.Asn1Match}:
  match pre:
    case Nil{}:
      {==}
    case Con{h, +t}:
      pm.nth_app(t, x, post)
