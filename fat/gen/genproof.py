#!/usr/bin/env python3
"""Writes fat/PROOF.bend.

The properties about bit packing (directory entry fields, FAT12 and FAT32
entries) are proved by splitting each U32 into its 32 bits and computing;
those patterns are long, so this script writes them. Run it from anywhere:
python3 fat/gen/genproof.py
"""
import os

def bits(v, n=32):
    s = "WNil{}"
    for i in reversed(range(n)):
        s = "WCon{%s_%d, %s}" % (v, i, s)
    return "U32{" + s + "}"

HEADER = """\
# Proofs of LAWS.bend. Written by gen/genproof.py: edit that, not this.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T
import ./dirent.bend as R
import ./map.bend as A
import ./alias.bend as L
import ./format.bend as K
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# Equality of words is reflexive (U32.is_eq(a, a) is True for every a)
def word_refl(n: Nat, w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          %word_refl(p, t) : {EQ{} == Word.cmp.fin(True{}, True{}, _) : Cmp}
          {==}
        case WCon{False{}, t}:
          %word_refl(p, t) : {EQ{} == Word.cmp.fin(False{}, False{}, _) : Cmp}
          {==}

def u32_refl(a: U32) -> {True{} == U32.is_eq(a, a) : Bool}:
  match a:
    case U32{+x}:
      %word_refl(32n, x) : {True{} == Cmp.is_eq(_) : Bool}
      {==}

def zero_le(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Directory entries. The encoder writes the 11 name bytes (cut or padded),
# then the fields; the decoder takes 11 bytes, then reads the fields. Going
# through Octets masks every byte (bytes' interface law octets_to_of); the
# name comes back through octets_of_to, and the fields by computing on their
# bits.

def mask_append(a: List<&2, U32>, +b: List<&2, U32>) -> {B.append(B.mask(a), B.mask(b)) == B.mask(B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %mask_append(t, b) : {Con{B.byte(h), B.append(B.mask(t), B.mask(b))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def take_fit(n: Nat, +pad: U32, ys: List<&2, U32>, +r: List<&2, U32>) -> {B.mask(P.Fat.fit(n, pad, ys)) == B.take(n, B.append(B.mask(P.Fat.fit(n, pad, ys)), r)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match ys:
        case Nil{}:
          %take_fit(p, pad, Nil{}, r) : {Con{B.byte(pad), B.mask(P.Fat.fit(p, pad, Nil{}))} == Con{B.byte(pad), _} : List<&2, U32>}
          {==}
        case Con{+h, t}:
          %take_fit(p, pad, t, r) : {Con{B.byte(h), B.mask(P.Fat.fit(p, pad, t))} == Con{B.byte(h), _} : List<&2, U32>}
          {==}

def drop_fit(n: Nat, +pad: U32, ys: List<&2, U32>, +r: List<&2, U32>) -> {r == B.drop(n, B.append(B.mask(P.Fat.fit(n, pad, ys)), r)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match ys:
        case Nil{}:
          drop_fit(p, pad, Nil{}, r)
        case Con{h, t}:
          drop_fit(p, pad, t, r)

def of_list_mask(+zs: List<&2, U32>) -> {B.Octets.of_list(zs) == B.Octets.of_list(B.mask(zs)) : B.Octets}:
  %BL.octets_to_of(zs) : {B.Octets.of_list(zs) == B.Octets.of_list(_) : B.Octets}
  Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(zs))), B.Octets.of_list(zs), BL.octets_of_to(B.Octets.of_list(zs)))

"""

def dirent_tail():
    fields = ["attr", "nt", "tenth", "ctime", "cdate", "adate", "hi", "wtime", "wdate", "lo", "size"]
    params = ", ".join("%s: U32" % f for f in fields)
    norm = "R.FatDirent{nm, B.byte(attr), B.byte(nt), B.byte(tenth), B.low16(ctime), B.low16(cdate), B.low16(adate), B.low16(hi), B.low16(wtime), B.low16(wdate), B.low16(lo), size}"
    out = ["# the fields after the name, for every value: split into bits, computed"]
    out.append("def dirent_tail(name: B.Octets, nm: B.Octets, %s) -> {R.FatDirent.decode.rest(nm, B.mask(R.FatDirent.encode.tail(R.FatDirent{name, %s}))) == Done{%s} : Result<&2, &2, E.FatError, R.FatDirent>}:" % (params, ", ".join(fields), norm))
    out.append("  match %s:" % " ".join(fields))
    out.append("    case %s:" % " ".join(bits(f) for f in fields))
    out.append("      {==}")
    return "\n".join(out) + "\n\n"

ROUND_TRIP = """\
def Laws.dirent_round_trip(d):
  match d:
    case R.FatDirent{+name, +attr, +nt, +tenth, +ctime, +cdate, +adate, +hi, +wtime, +wdate, +lo, +size}:
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.append(P.Fat.fit(11n, 32, B.Octets.to_list(name)), R.FatDirent.encode.tail(D0)))), B.mask(B.append(P.Fat.fit(11n, 32, B.Octets.to_list(name)), R.FatDirent.encode.tail(D0))), BL.octets_to_of(B.append(P.Fat.fit(11n, 32, B.Octets.to_list(name)), R.FatDirent.encode.tail(D0)))) : {R.FatDirent.decode.list(_) == Done{R.FatDirent.norm(D0)} : RES}
      %mask_append(P.Fat.fit(11n, 32, B.Octets.to_list(name)), R.FatDirent.encode.tail(D0)) : {R.FatDirent.decode.list(_) == Done{R.FatDirent.norm(D0)} : RES}
      %take_fit(11n, 32, B.Octets.to_list(name), B.mask(R.FatDirent.encode.tail(D0))) : {R.FatDirent.decode.rest(B.Octets.of_list(_), B.drop(11n, B.append(B.mask(P.Fat.fit(11n, 32, B.Octets.to_list(name))), B.mask(R.FatDirent.encode.tail(D0))))) == Done{R.FatDirent.norm(D0)} : RES}
      %drop_fit(11n, 32, B.Octets.to_list(name), B.mask(R.FatDirent.encode.tail(D0))) : {R.FatDirent.decode.rest(B.Octets.of_list(B.mask(P.Fat.fit(11n, 32, B.Octets.to_list(name)))), _) == Done{R.FatDirent.norm(D0)} : RES}
      %of_list_mask(P.Fat.fit(11n, 32, B.Octets.to_list(name))) : {R.FatDirent.decode.rest(_, B.mask(R.FatDirent.encode.tail(D0))) == Done{R.FatDirent.norm(D0)} : RES}
      dirent_tail(name, B.Octets.of_list(P.Fat.fit(11n, 32, B.Octets.to_list(name))), attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size)

""".replace("D0", "R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}").replace("RES", "Result<&2, &2, E.FatError, R.FatDirent>")

LFN = """\
# Long names: every entry build.go makes carries the checksum it was given

def build_carries(+i: Nat, +k: Nat, +name: List<&2, U32>, +c: U32) -> {R.FatLfn.carries(R.FatLfn.build.go(i, k, name, c), c) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      %u32_refl(c) : {Bool.and(_, R.FatLfn.carries(R.FatLfn.build.go(p, k, name, c), c)) == True{} : Bool}
      build_carries(p, k, name, c)

def Laws.lfn_carries_checksum(short, name):
  build_carries(R.FatLfn.count(B.len(name)), R.FatLfn.count(B.len(name)), name, R.FatLfn.checksum(short))

"""

def fat12():
    a, b, c, v = bits("a"), bits("b"), bits("c"), bits("v")
    out = ["# FAT12 and FAT32 packing, for every value: split into bits, computed"]
    out.append("def Laws.fat12_set_get(odd, w, v):")
    out.append("  match odd w v:")
    for o in ("True{}", "False{}"):
        out.append("    case %s T.Fat12Window{%s, %s} %s:" % (o, a, b, v))
        out.append("      {==}")
    out.append("")
    for law in ("fat12_even_keeps_odd", "fat12_odd_keeps_even"):
        out.append("def Laws.%s(a, b, c, v):" % law)
        out.append("  match a b c v:")
        out.append("    case %s %s %s %s:" % (a, b, c, v))
        out.append("      {==}")
        out.append("")
    for law in ("fat32_set_get", "fat32_keeps_reserved"):
        out.append("def Laws.%s(old, v):" % law)
        out.append("  match old v:")
        out.append("    case %s %s:" % (bits("o"), v))
        out.append("      {==}")
        out.append("")
    return "\n".join(out) + "\n"

ENTRIES = """\
# Entry values: per FAT type, computed; a next-cluster value through its
# three hypotheses

def Laws.entry_end(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def Laws.entry_bad(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def Laws.entry_free(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def Laws.entry_next(t, c, nonzero, not_bad, below):
  %Equal.sym(Bool, U32.is_eq(c, 0), False{}, nonzero) : {T.FatEntry.of.pick(_, U32.is_eq(c, T.FatEntry.bad(t)), U32.is_gt(c, T.FatEntry.bad(t)), c) == T.FatNext{c} : T.FatEntry}
  %Equal.sym(Bool, U32.is_eq(c, T.FatEntry.bad(t)), False{}, not_bad) : {T.FatEntry.of.pick(False{}, _, U32.is_gt(c, T.FatEntry.bad(t)), c) == T.FatNext{c} : T.FatEntry}
  %Equal.sym(Bool, U32.is_gt(c, T.FatEntry.bad(t)), False{}, below) : {T.FatEntry.of.pick(False{}, False{}, _, c) == T.FatNext{c} : T.FatEntry}
  {==}

def Laws.entry_next_witness_nonzero():
  {==}

def Laws.entry_next_witness_not_bad(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def Laws.entry_next_witness_below(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

"""

CHAIN = """\
# The chain bound. Each step of the walk spends one unit of fuel and adds
# one cluster, so a walk with fuel n returns at most n clusters, whatever the
# device answers: induction on the fuel, a case on each answer.

def cons_le(+c: U32, r: Result<&2, &2, E.FatError, List<&2, U32>>, +p: Nat, ih: {Nat.is_le(Laws.chain_count(r), p) == True{} : Bool}) -> {Nat.is_le(Laws.chain_count(T.FatChain.cons(c, r)), 1n+p) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{cs}:
      ih

def go_bound(+d: D.MemDev, +vol: P.FatVolume, +fuel: Nat, +c: U32, l: Result<&2, &2, E.FatError, T.FatLink>) -> {Nat.is_le(Laws.chain_count(T.FatChain.go.ref(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, fuel, c, l)), fuel) == True{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      match l:
        case Fail{e}:
          {==}
        case Done{T.FatLinkEnd{}}:
          zero_le(p)
        case Done{T.FatLinkNext{+n}}:
          cons_le(c, T.FatChain.go.ref(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, p, n, T.FatChain.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, n)), p, go_bound(d, vol, p, n, T.FatChain.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, n)))

# The walk runs the loop FatChain.go; it equals the reference FatChain.go.ref
# (on which the bound is proved) for every device, fuel, cluster and link:
# with acc the clusters before, the loop gives the reference's chain with
# acc reversed in front of it.

def chain_lift(acc: List<&2, U32>, r: Result<&2, &2, E.FatError, List<&2, U32>>) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      Done{T.FatChain.rev(acc, cs)}

def chain_lift_cons(+c: U32, +acc: List<&2, U32>, r: Result<&2, &2, E.FatError, List<&2, U32>>) -> {chain_lift(Con{c, acc}, r) == chain_lift(acc, T.FatChain.cons(c, r)) : Result<&2, &2, E.FatError, List<&2, U32>>}:
  match r:
    case Fail{e}:
      {==}
    case Done{cs}:
      {==}

def chain_lift_nil(r: Result<&2, &2, E.FatError, List<&2, U32>>) -> {r == chain_lift(Nil{}, r) : Result<&2, &2, E.FatError, List<&2, U32>>}:
  match r:
    case Fail{e}:
      {==}
    case Done{cs}:
      {==}

def chain_go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, +fuel: Nat, +c: U32, l: Result<&2, &2, E.FatError, T.FatLink>, +acc: List<&2, U32>) -> {T.FatChain.go(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l, acc) == chain_lift(acc, T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l)) : Result<&2, &2, E.FatError, List<&2, U32>>}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      match l:
        case Fail{e}:
          {==}
        case Done{T.FatLinkEnd{}}:
          {==}
        case Done{T.FatLinkNext{+n}}:
          Equal.trans(Result<&2, &2, E.FatError, List<&2, U32>>, T.FatChain.go(~Dv, ~block_size, ~read_block, d, vol, p, n, T.FatChain.next(~Dv, ~block_size, ~read_block, d, vol, n), Con{c, acc}), chain_lift(Con{c, acc}, T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, p, n, T.FatChain.next(~Dv, ~block_size, ~read_block, d, vol, n))), chain_lift(acc, T.FatChain.cons(c, T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, p, n, T.FatChain.next(~Dv, ~block_size, ~read_block, d, vol, n)))),
            chain_go(~Dv, ~block_size, ~read_block, d, vol, p, n, T.FatChain.next(~Dv, ~block_size, ~read_block, d, vol, n), Con{c, acc}),
            chain_lift_cons(c, acc, T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, p, n, T.FatChain.next(~Dv, ~block_size, ~read_block, d, vol, n))))

# reference == loop, the direction a rewrite uses
def chain_eq(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, +fuel: Nat, +c: U32, +l: Result<&2, &2, E.FatError, T.FatLink>) -> {T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l) == T.FatChain.go(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l, Nil{}) : Result<&2, &2, E.FatError, List<&2, U32>>}:
  Equal.trans(Result<&2, &2, E.FatError, List<&2, U32>>, T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l), chain_lift(Nil{}, T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l)), T.FatChain.go(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l, Nil{}),
    chain_lift_nil(T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l)),
    Equal.sym(Result<&2, &2, E.FatError, List<&2, U32>>, T.FatChain.go(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l, Nil{}), chain_lift(Nil{}, T.FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l)), chain_go(~Dv, ~block_size, ~read_block, d, vol, fuel, c, l, Nil{})))

def walk_bound(empty: Bool, ok: Bool, +d: D.MemDev, +vol: P.FatVolume, +start: U32) -> {Nat.is_le(Laws.chain_count(T.FatChain.walk.from(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, empty, ok, d, vol, start)), U32.to_nat(P.FatVolume.clusters(vol))) == True{} : Bool}:
  match empty ok:
    case True{} _:
      zero_le(U32.to_nat(P.FatVolume.clusters(vol)))
    case False{} False{}:
      zero_le(U32.to_nat(P.FatVolume.clusters(vol)))
    case False{} True{}:
      %chain_eq(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, U32.to_nat(P.FatVolume.clusters(vol)), start, T.FatChain.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, start)) : {Nat.is_le(Laws.chain_count(_), U32.to_nat(P.FatVolume.clusters(vol))) == True{} : Bool}
      go_bound(d, vol, U32.to_nat(P.FatVolume.clusters(vol)), start, T.FatChain.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, start))

def Laws.chain_bound(d, vol, start):
  walk_bound(U32.is_eq(start, 0), P.FatVolume.valid_cluster(vol, start), d, vol, start)

"""

# The writer's laws: the allocation table in memory (MP: the tree; MQ to
# MW: the two phases of an allocation, and its laws; MX: extending,
# freeing, cutting), short names (MY) and format (MY), and their vectors
WRITE = r"""
def MP.bool_t(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def MP.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : MP.bool_t(_)
  Unit{}

def MP.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : MP.bool_t(_)
  Unit{}

def MP.lt_irrefl(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      MP.lt_irrefl(p)

def MP.sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      MP.sub_self(p)

def MP.sub_nz(m: Nat, n: Nat, h1: {Nat.is_lt(m, n) == False{} : Bool}, h2: {Nat.is_eq(n, m) == False{} : Bool}) -> {Nat.is_eq(Nat.sub(m, n), 0n) == False{} : Bool}:
  match m n:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(Nat.sub(0n, 0n), 0n) == False{} : Bool}, MP.tf(h2))
    case 0n 1n+q:
      Empty.absurd({Nat.is_eq(Nat.sub(0n, 1n+q), 0n) == False{} : Bool}, MP.tf(h1))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      MP.sub_nz(p, q, h1, h2)

def MP.sub_ne(n: Nat, m: Nat, k: Nat, hn: {Nat.is_lt(n, k) == False{} : Bool}, hm: {Nat.is_lt(m, k) == False{} : Bool}, h: {Nat.is_eq(n, m) == False{} : Bool}) -> {Nat.is_eq(Nat.sub(n, k), Nat.sub(m, k)) == False{} : Bool}:
  match n m k:
    case 0n 0n 0n:
      h
    case 0n 1n+q 0n:
      h
    case 1n+p 0n 0n:
      h
    case 1n+p 1n+q 0n:
      h
    case 0n _ 1n+r:
      Empty.absurd({Nat.is_eq(Nat.sub(0n, 1n+r), Nat.sub(m, 1n+r)) == False{} : Bool}, MP.tf(hn))
    case 1n+p 0n 1n+r:
      Empty.absurd({Nat.is_eq(Nat.sub(1n+p, 1n+r), Nat.sub(0n, 1n+r)) == False{} : Bool}, MP.tf(hm))
    case 1n+p 1n+q 1n+r:
      MP.sub_ne(p, q, r, hn, hm, h)

def MP.get_set_same(t: A.FatTree, +n: Nat, +v: U32, z: Bool, ez: {z == Nat.is_lt(n, A.FatTree.left_count(t)) : Bool}) -> {A.FatTree.get(A.FatTree.set.at(t, n, v, z), n) == v : U32}:
  match t z:
    case A.FatTEmpty{} _:
      %Equal.sym(Bool, Nat.is_lt(n, n), False{}, MP.lt_irrefl(n)) : {A.FatTree.get.at(A.FatTNode{n, A.FatTEmpty{}, A.FatTLeaf{v}}, n, _) == v : U32}
      %Equal.sym(Nat, Nat.sub(n, n), 0n, MP.sub_self(n)) : {A.FatTree.get.at(A.FatTLeaf{v}, _, Nat.is_lt(_, 0n)) == v : U32}
      {==}
    case A.FatTLeaf{b} _:
      match n:
        case 0n:
          {==}
        case 1n+p:
          %Equal.sym(Bool, Nat.is_lt(p, p), False{}, MP.lt_irrefl(p)) : {A.FatTree.get.at(A.FatTNode{1n+p, A.FatTLeaf{b}, A.FatTLeaf{v}}, 1n+p, _) == v : U32}
          %Equal.sym(Nat, Nat.sub(p, p), 0n, MP.sub_self(p)) : {A.FatTree.get.at(A.FatTLeaf{v}, _, Nat.is_lt(_, 0n)) == v : U32}
          {==}
    case A.FatTNode{+k, +l, r} True{}:
      +zl = Nat.is_lt(n, A.FatTree.left_count(l))
      %ez : {A.FatTree.get.at(A.FatTNode{k, A.FatTree.set.at(l, n, v, zl), r}, n, _) == v : U32}
      MP.get_set_same(l, n, v, zl, {==})
    case A.FatTNode{+k, l, +r} False{}:
      +m = Nat.sub(n, k)
      +zr = Nat.is_lt(m, A.FatTree.left_count(r))
      %ez : {A.FatTree.get.at(A.FatTNode{k, l, A.FatTree.set.at(r, m, v, zr)}, n, _) == v : U32}
      MP.get_set_same(r, m, v, zr, {==})

def MP.node_other(+k: Nat, +l: A.FatTree, +r: A.FatTree, +l2: A.FatTree, +m: Nat, b: Bool, +eb: {Nat.is_lt(m, k) == b : Bool}, e: {A.FatTree.get(l2, m) == A.FatTree.get(l, m) : U32}) -> {A.FatTree.get(A.FatTNode{k, l2, r}, m) == A.FatTree.get(A.FatTNode{k, l, r}, m) : U32}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, k), True{}, eb) : {A.FatTree.get.at(A.FatTNode{k, l2, r}, m, _) == A.FatTree.get.at(A.FatTNode{k, l, r}, m, _) : U32}
      e
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, k), False{}, eb) : {A.FatTree.get.at(A.FatTNode{k, l2, r}, m, _) == A.FatTree.get.at(A.FatTNode{k, l, r}, m, _) : U32}
      {==}

def MP.node_other_r(+k: Nat, +l: A.FatTree, +r: A.FatTree, +r2: A.FatTree, +m: Nat, b: Bool, +eb: {Nat.is_lt(m, k) == b : Bool}, e: {Nat.is_lt(m, k) == False{} : Bool} -> {A.FatTree.get(r2, Nat.sub(m, k)) == A.FatTree.get(r, Nat.sub(m, k)) : U32}) -> {A.FatTree.get(A.FatTNode{k, l, r2}, m) == A.FatTree.get(A.FatTNode{k, l, r}, m) : U32}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, k), True{}, eb) : {A.FatTree.get.at(A.FatTNode{k, l, r2}, m, _) == A.FatTree.get.at(A.FatTNode{k, l, r}, m, _) : U32}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, k), False{}, eb) : {A.FatTree.get.at(A.FatTNode{k, l, r2}, m, _) == A.FatTree.get.at(A.FatTNode{k, l, r}, m, _) : U32}
      e(eb)

def MP.empty_other(+n: Nat, +v: U32, +m: Nat, b: Bool, +eb: {Nat.is_lt(m, n) == b : Bool}, h: {Nat.is_eq(n, m) == False{} : Bool}) -> {A.FatTree.get(A.FatTNode{n, A.FatTEmpty{}, A.FatTLeaf{v}}, m) == 0 : U32}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, n), True{}, eb) : {A.FatTree.get.at(A.FatTNode{n, A.FatTEmpty{}, A.FatTLeaf{v}}, m, _) == 0 : U32}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, n), False{}, eb) : {A.FatTree.get.at(A.FatTNode{n, A.FatTEmpty{}, A.FatTLeaf{v}}, m, _) == 0 : U32}
      %Equal.sym(Bool, Nat.is_eq(Nat.sub(m, n), 0n), False{}, MP.sub_nz(m, n, eb, h)) : {A.FatTree.get.leaf(_, v) == 0 : U32}
      {==}

def MP.leaf_other_f(m: Nat, +p: Nat, +bl: U32, +v: U32, +eb: {Nat.is_lt(m, 1n+p) == False{} : Bool}, h: {Nat.is_eq(1n+p, m) == False{} : Bool}) -> {A.FatTree.get(A.FatTNode{1n+p, A.FatTLeaf{bl}, A.FatTLeaf{v}}, m) == A.FatTree.get(A.FatTLeaf{bl}, m) : U32}:
  match m:
    case 0n:
      Empty.absurd({A.FatTree.get(A.FatTNode{1n+p, A.FatTLeaf{bl}, A.FatTLeaf{v}}, 0n) == A.FatTree.get(A.FatTLeaf{bl}, 0n) : U32}, MP.tf(eb))
    case 1n+ +q:
      %Equal.sym(Bool, Nat.is_lt(1n+q, 1n+p), False{}, eb) : {A.FatTree.get.at(A.FatTNode{1n+p, A.FatTLeaf{bl}, A.FatTLeaf{v}}, 1n+q, _) == 0 : U32}
      %Equal.sym(Bool, Nat.is_eq(Nat.sub(1n+q, 1n+p), 0n), False{}, MP.sub_nz(1n+q, 1n+p, eb, h)) : {A.FatTree.get.leaf(_, v) == 0 : U32}
      {==}

def MP.leaf_other(+p: Nat, +bl: U32, +v: U32, +m: Nat, b: Bool, +eb: {Nat.is_lt(m, 1n+p) == b : Bool}, h: {Nat.is_eq(1n+p, m) == False{} : Bool}) -> {A.FatTree.get(A.FatTNode{1n+p, A.FatTLeaf{bl}, A.FatTLeaf{v}}, m) == A.FatTree.get(A.FatTLeaf{bl}, m) : U32}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, 1n+p), True{}, eb) : {A.FatTree.get.at(A.FatTNode{1n+p, A.FatTLeaf{bl}, A.FatTLeaf{v}}, m, _) == A.FatTree.get(A.FatTLeaf{bl}, m) : U32}
      {==}
    case False{}:
      MP.leaf_other_f(m, p, bl, v, eb, h)

def MP.get_set_other(t: A.FatTree, +n: Nat, +v: U32, z: Bool, ez: {z == Nat.is_lt(n, A.FatTree.left_count(t)) : Bool}, +m: Nat, h: {Nat.is_eq(n, m) == False{} : Bool}) -> {A.FatTree.get(A.FatTree.set.at(t, n, v, z), m) == A.FatTree.get(t, m) : U32}:
  match t z:
    case A.FatTEmpty{} _:
      MP.empty_other(n, v, m, Nat.is_lt(m, n), {==}, h)
    case A.FatTLeaf{+b} _:
      match n:
        case 0n:
          match m:
            case 0n:
              Empty.absurd({A.FatTree.get(A.FatTLeaf{v}, 0n) == A.FatTree.get(A.FatTLeaf{b}, 0n) : U32}, MP.tf(h))
            case 1n+q:
              {==}
        case 1n+ +p:
          MP.leaf_other(p, b, v, m, Nat.is_lt(m, 1n+p), {==}, h)
    case A.FatTNode{+k, +l, +r} True{}:
      +zl = Nat.is_lt(n, A.FatTree.left_count(l))
      MP.node_other(k, l, r, A.FatTree.set.at(l, n, v, zl), m, Nat.is_lt(m, k), {==}, MP.get_set_other(l, n, v, zl, {==}, m, h))
    case A.FatTNode{+k, +l, +r} False{}:
      +nk = Nat.sub(n, k)
      +zr = Nat.is_lt(nk, A.FatTree.left_count(r))
      MP.node_other_r(k, l, r, A.FatTree.set.at(r, nk, v, zr), m, Nat.is_lt(m, k), {==}, hm => MP.get_set_other(r, nk, v, zr, {==}, Nat.sub(m, k), MP.sub_ne(n, m, k, Equal.sym(Bool, False{}, Nat.is_lt(n, k), ez), hm, h)))

def Laws.map_get_set(m, n, v):
  match m:
    case A.FatMap{+t, c, +tr}:
      MP.get_set_same(tr, n, A.FatMap.mask(t, v), Nat.is_lt(n, A.FatTree.left_count(tr)), {==})

def Laws.map_get_set_other(m, n, k, v, ne):
  match m:
    case A.FatMap{+t, c, +tr}:
      MP.get_set_other(tr, n, A.FatMap.mask(t, v), Nat.is_lt(n, A.FatTree.left_count(tr)), {==}, k, ne)

def MQ.or_false_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MP.tf(e))

def MQ.or_false_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, MP.tf(e))

def MQ.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MP.ft(e))

def MQ.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, MP.ft(e))

def MQ.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      MQ.eq_refl(p)

def MQ.eq_sym(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      MQ.eq_sym(p, q)

def MQ.ne_sym(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(b, a), Nat.is_eq(a, b), False{}, MQ.eq_sym(b, a), e)

def MQ.eq_true(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, MP.ft(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, MP.ft(e))
    case 1n+p 1n+q:
      %MQ.eq_true(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def MQ.word_refl(n: Nat, w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          %MQ.word_refl(p, t) : {EQ{} == Word.cmp.fin(True{}, True{}, _) : Cmp}
          {==}
        case WCon{False{}, t}:
          %MQ.word_refl(p, t) : {EQ{} == Word.cmp.fin(False{}, False{}, _) : Cmp}
          {==}

def MQ.u32_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+x}:
      %MQ.word_refl(32n, x) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def MQ.end_nz(t: P.FatType) -> {U32.is_eq(A.FatMap.mask(t, T.FatEntry.end_value(t)), 0) == False{} : Bool}:
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def MQ.mask_end(t: P.FatType) -> {A.FatMap.mask(t, A.FatMap.mask(t, T.FatEntry.end_value(t))) == A.FatMap.mask(t, T.FatEntry.end_value(t)) : U32}:
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def MQ.mask_zero(t: P.FatType) -> {A.FatMap.mask(t, 0) == 0 : U32}:
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def MQ.set_kind(m: A.FatMap, +n: Nat, +v: U32) -> {A.FatMap.kind(A.FatMap.set(m, n, v)) == A.FatMap.kind(m) : P.FatType}:
  match m:
    case A.FatMap{t, c, tr}:
      {==}

def MQ.set_count(m: A.FatMap, +n: Nat, +v: U32) -> {A.FatMap.count(A.FatMap.set(m, n, v)) == A.FatMap.count(m) : Nat}:
  match m:
    case A.FatMap{t, c, tr}:
      {==}

def MQ.found_free(+m: A.FatMap, f: Maybe<&2, Nat>) -> Bool:
  match f:
    case None{}:
      True{}
    case Some{c}:
      A.FatMap.is_free(m, c)

def MQ.find_go(fuel: Nat, +m: A.FatMap, +c: Nat, b: Bool, eb: {A.FatMap.is_free(m, c) == b : Bool}) -> {MQ.found_free(m, A.FatMap.find.go(fuel, m, c, b)) == True{} : Bool}:
  match fuel b:
    case _ True{}:
      eb
    case 0n False{}:
      {==}
    case 1n+f False{}:
      +c2 = A.FatMap.wrap(m, Nat.add(c, 1n))
      MQ.find_go(f, m, c2, A.FatMap.is_free(m, c2), {==})

def MQ.find(+m: A.FatMap, +hint: Nat) -> {MQ.found_free(m, A.FatMap.find(m, hint)) == True{} : Bool}:
  +c = A.FatMap.wrap(m, hint)
  MQ.find_go(Nat.sub(A.FatMap.count(m), 3n), m, c, A.FatMap.is_free(m, c), {==})

def MR.or_swap(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(b, a), c) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def MR.and_swap(a: Bool, b: Bool, c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(b, a), c) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def MR.or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def MR.and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def MR.not_true(a: Bool, +e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MP.ft(e))

def MR.member_rev(+n: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {A.FatMap.member(n, A.FatMap.rev_nat(xs, ys)) == Bool.or(A.FatMap.member(n, xs), A.FatMap.member(n, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Bool, A.FatMap.member(n, A.FatMap.rev_nat(t, Con{h, ys})), Bool.or(A.FatMap.member(n, t), Bool.or(Nat.is_eq(n, h), A.FatMap.member(n, ys))), Bool.or(Bool.or(Nat.is_eq(n, h), A.FatMap.member(n, t)), A.FatMap.member(n, ys)), MR.member_rev(n, t, Con{h, ys}), MR.or_swap(A.FatMap.member(n, t), Nat.is_eq(n, h), A.FatMap.member(n, ys)))

def MR.free_rev(+m: A.FatMap, xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {A.FatMap.all_free(m, A.FatMap.rev_nat(xs, ys)) == Bool.and(A.FatMap.all_free(m, xs), A.FatMap.all_free(m, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Bool, A.FatMap.all_free(m, A.FatMap.rev_nat(t, Con{h, ys})), Bool.and(A.FatMap.all_free(m, t), Bool.and(A.FatMap.is_free(m, h), A.FatMap.all_free(m, ys))), Bool.and(Bool.and(A.FatMap.is_free(m, h), A.FatMap.all_free(m, t)), A.FatMap.all_free(m, ys)), MR.free_rev(m, t, Con{h, ys}), MR.and_swap(A.FatMap.all_free(m, t), A.FatMap.is_free(m, h), A.FatMap.all_free(m, ys)))

def MR.len_rev(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {List.length(&2, Nat, A.FatMap.rev_nat(xs, ys)) == Nat.add(List.length(&2, Nat, xs), List.length(&2, Nat, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, Nat, A.FatMap.rev_nat(t, Con{h, ys})), Nat.add(List.length(&2, Nat, t), 1n+List.length(&2, Nat, ys)), 1n+Nat.add(List.length(&2, Nat, t), List.length(&2, Nat, ys)), MR.len_rev(t, Con{h, ys}), UL.nat_add_succ(List.length(&2, Nat, t), List.length(&2, Nat, ys)))

# every element of xs is missing from ys
def MR.disjoint(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(A.FatMap.member(h, ys)), MR.disjoint(t, ys))

def MR.disjoint_nil(xs: List<&2, Nat>) -> {MR.disjoint(xs, Nil{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      MR.disjoint_nil(t)

def MR.disjoint_cons(xs: List<&2, Nat>, +h: Nat, +ys: List<&2, Nat>, +nh: {A.FatMap.member(h, xs) == False{} : Bool}, +dj: {MR.disjoint(xs, ys) == True{} : Bool}) -> {MR.disjoint(xs, Con{h, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +nx = MQ.ne_sym(h, x, MQ.or_false_l(Nat.is_eq(h, x), A.FatMap.member(h, r), nh))
      +my = MR.not_true(A.FatMap.member(x, ys), MQ.and_l(Bool.not(A.FatMap.member(x, ys)), MR.disjoint(r, ys), dj))
      %Equal.sym(Bool, Nat.is_eq(x, h), False{}, nx) : {Bool.and(Bool.not(Bool.or(_, A.FatMap.member(x, ys))), MR.disjoint(r, Con{h, ys})) == True{} : Bool}
      %Equal.sym(Bool, A.FatMap.member(x, ys), False{}, my) : {Bool.and(Bool.not(Bool.or(False{}, _)), MR.disjoint(r, Con{h, ys})) == True{} : Bool}
      MR.disjoint_cons(r, h, ys, MQ.or_false_r(Nat.is_eq(h, x), A.FatMap.member(h, r), nh), MQ.and_r(Bool.not(A.FatMap.member(x, ys)), MR.disjoint(r, ys), dj))

def MR.distinct_cons(+h: Nat, +ys: List<&2, Nat>, +ny: {A.FatMap.member(h, ys) == False{} : Bool}, +d: {A.FatMap.distinct(ys) == True{} : Bool}) -> {A.FatMap.distinct(Con{h, ys}) == True{} : Bool}:
  %Equal.sym(Bool, A.FatMap.member(h, ys), False{}, ny) : {Bool.and(Bool.not(_), A.FatMap.distinct(ys)) == True{} : Bool}
  d

def MR.distinct_rev(xs: List<&2, Nat>, +ys: List<&2, Nat>, +d1: {A.FatMap.distinct(xs) == True{} : Bool}, +d2: {A.FatMap.distinct(ys) == True{} : Bool}, +dj: {MR.disjoint(xs, ys) == True{} : Bool}) -> {A.FatMap.distinct(A.FatMap.rev_nat(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      d2
    case Con{+h, +t}:
      +nh = MR.not_true(A.FatMap.member(h, t), MQ.and_l(Bool.not(A.FatMap.member(h, t)), A.FatMap.distinct(t), d1))
      +ny = MR.not_true(A.FatMap.member(h, ys), MQ.and_l(Bool.not(A.FatMap.member(h, ys)), MR.disjoint(t, ys), dj))
      +dh = MQ.and_r(Bool.not(A.FatMap.member(h, t)), A.FatMap.distinct(t), d1)
      +dt = MQ.and_r(Bool.not(A.FatMap.member(h, ys)), MR.disjoint(t, ys), dj)
      MR.distinct_rev(t, Con{h, ys}, dh, MR.distinct_cons(h, ys, ny, d2), MR.disjoint_cons(t, h, ys, nh, dt))

def MS.overlay(+m0: A.FatMap, acc: List<&2, Nat>) -> A.FatMap:
  match acc:
    case Nil{}:
      m0
    case Con{+a, t}:
      A.FatMap.set(MS.overlay(m0, t), a, A.FatMap.end(m0))

def MS.pick(hit: Bool, a: U32, b: U32) -> U32:
  match hit:
    case True{}:
      a
    case False{}:
      b

def MS.expect(+m0: A.FatMap, acc: List<&2, Nat>, +n: Nat) -> U32:
  MS.pick(A.FatMap.member(n, acc), A.FatMap.end(m0), A.FatMap.get(m0, n))

def MS.ov_kind(+m0: A.FatMap, acc: List<&2, Nat>) -> {A.FatMap.kind(MS.overlay(m0, acc)) == A.FatMap.kind(m0) : P.FatType}:
  match acc:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      Equal.trans(P.FatType, A.FatMap.kind(A.FatMap.set(MS.overlay(m0, t), a, A.FatMap.end(m0))), A.FatMap.kind(MS.overlay(m0, t)), A.FatMap.kind(m0), MQ.set_kind(MS.overlay(m0, t), a, A.FatMap.end(m0)), MS.ov_kind(m0, t))

def MS.ov_count(+m0: A.FatMap, acc: List<&2, Nat>) -> {A.FatMap.count(MS.overlay(m0, acc)) == A.FatMap.count(m0) : Nat}:
  match acc:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      Equal.trans(Nat, A.FatMap.count(A.FatMap.set(MS.overlay(m0, t), a, A.FatMap.end(m0))), A.FatMap.count(MS.overlay(m0, t)), A.FatMap.count(m0), MQ.set_count(MS.overlay(m0, t), a, A.FatMap.end(m0)), MS.ov_count(m0, t))

# the end value is the same for maps of one type
def MS.end_eq(+m: A.FatMap, +m0: A.FatMap, +hk: {A.FatMap.kind(m) == A.FatMap.kind(m0) : P.FatType}) -> {A.FatMap.end(m) == A.FatMap.end(m0) : U32}:
  %hk : {A.FatMap.mask(A.FatMap.kind(m), T.FatEntry.end_value(A.FatMap.kind(m))) == A.FatMap.mask(_, T.FatEntry.end_value(_)) : U32}
  {==}

# one more cluster a over the overlay of t, read at n (b: whether n is a;
# ih: the read of the overlay of t)
def MS.ov_get_step(+m0: A.FatMap, +a: Nat, +t: List<&2, Nat>, +n: Nat, b: Bool, +eb: {Nat.is_eq(n, a) == b : Bool}, +ih: {A.FatMap.get(MS.overlay(m0, t), n) == MS.expect(m0, t, n) : U32}) -> {A.FatMap.get(MS.overlay(m0, Con{a, t}), n) == MS.expect(m0, Con{a, t}, n) : U32}:
  match b:
    case True{}:
      +m = MS.overlay(m0, t)
      +na = MQ.eq_true(n, a, eb)
      %Equal.sym(Bool, Nat.is_eq(n, a), True{}, eb) : {A.FatMap.get(A.FatMap.set(m, a, A.FatMap.end(m0)), n) == MS.pick(Bool.or(_, A.FatMap.member(n, t)), A.FatMap.end(m0), A.FatMap.get(m0, n)) : U32}
      %Equal.sym(Nat, n, a, na) : {A.FatMap.get(A.FatMap.set(m, a, A.FatMap.end(m0)), _) == A.FatMap.end(m0) : U32}
      %Equal.sym(U32, A.FatMap.get(A.FatMap.set(m, a, A.FatMap.end(m0)), a), A.FatMap.mask(A.FatMap.kind(m), A.FatMap.end(m0)), Laws.map_get_set(m, a, A.FatMap.end(m0))) : {_ == A.FatMap.end(m0) : U32}
      %Equal.sym(P.FatType, A.FatMap.kind(m), A.FatMap.kind(m0), MS.ov_kind(m0, t)) : {A.FatMap.mask(_, A.FatMap.end(m0)) == A.FatMap.end(m0) : U32}
      MQ.mask_end(A.FatMap.kind(m0))
    case False{}:
      +m = MS.overlay(m0, t)
      %Equal.sym(Bool, Nat.is_eq(n, a), False{}, eb) : {A.FatMap.get(A.FatMap.set(m, a, A.FatMap.end(m0)), n) == MS.pick(Bool.or(_, A.FatMap.member(n, t)), A.FatMap.end(m0), A.FatMap.get(m0, n)) : U32}
      %Equal.sym(U32, A.FatMap.get(A.FatMap.set(m, a, A.FatMap.end(m0)), n), A.FatMap.get(m, n), Laws.map_get_set_other(m, a, n, A.FatMap.end(m0), MQ.ne_sym(n, a, eb))) : {_ == MS.pick(A.FatMap.member(n, t), A.FatMap.end(m0), A.FatMap.get(m0, n)) : U32}
      ih

# every entry of the overlay: the end of a chain for a cluster taken, the
# entry before for every other
def MS.ov_get(+m0: A.FatMap, acc: List<&2, Nat>, +n: Nat) -> {A.FatMap.get(MS.overlay(m0, acc), n) == MS.expect(m0, acc, n) : U32}:
  match acc:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      MS.ov_get_step(m0, a, t, n, Nat.is_eq(n, a), {==}, MS.ov_get(m0, t, n))

# What the first phase answers: its map is the overlay of the clusters it
# took (latest first), which it answers in the order taken, all free before,
# none twice, k0 of them
def MT.cfacts(+m0: A.FatMap, +k0: Nat, +m2: A.FatMap, +cs: List<&2, Nat>) -> Type:
  &acc: List<&2, Nat> -> ({m2 == MS.overlay(m0, acc) : A.FatMap} & ({cs == A.FatMap.rev_nat(acc, Nil{}) : List<&2, Nat>} & ({A.FatMap.all_free(m0, acc) == True{} : Bool} & ({A.FatMap.distinct(acc) == True{} : Bool} & {List.length(&2, Nat, acc) == k0 : Nat}))))

def MT.cspec(+m0: A.FatMap, +k0: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{A.FatAlloc{m2, cs}}:
      MT.cfacts(m0, k0, m2, cs)

def MT.mem_found(f: Maybe<&2, Nat>, +acc: List<&2, Nat>) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{c}:
      A.FatMap.member(c, acc)

def MT.kind_of(+m0: A.FatMap, +m: A.FatMap, +acc: List<&2, Nat>, +hm: {m == MS.overlay(m0, acc) : A.FatMap}) -> {A.FatMap.kind(m) == A.FatMap.kind(m0) : P.FatType}:
  %Equal.sym(A.FatMap, m, MS.overlay(m0, acc), hm) : {A.FatMap.kind(_) == A.FatMap.kind(m0) : P.FatType}
  MS.ov_kind(m0, acc)

def MT.get_eq(+m0: A.FatMap, +m: A.FatMap, +acc: List<&2, Nat>, +c: Nat, +hm: {m == MS.overlay(m0, acc) : A.FatMap}) -> {A.FatMap.get(m, c) == MS.expect(m0, acc, c) : U32}:
  %Equal.sym(A.FatMap, m, MS.overlay(m0, acc), hm) : {A.FatMap.get(_, c) == MS.expect(m0, acc, c) : U32}
  MS.ov_get(m0, acc, c)

# a cluster not yet taken is as free in the map as it was before
def MT.free_eq(+m0: A.FatMap, +m: A.FatMap, +acc: List<&2, Nat>, +c: Nat, +eb: {A.FatMap.member(c, acc) == False{} : Bool}, +hm: {m == MS.overlay(m0, acc) : A.FatMap}) -> {A.FatMap.is_free(m, c) == A.FatMap.is_free(m0, c) : Bool}:
  +ov = MS.overlay(m0, acc)
  %Equal.sym(A.FatMap, m, ov, hm) : {A.FatMap.is_free(_, c) == A.FatMap.is_free(m0, c) : Bool}
  %Equal.sym(Nat, A.FatMap.count(ov), A.FatMap.count(m0), MS.ov_count(m0, acc)) : {Bool.and(Bool.and(Nat.is_le(2n, c), Nat.is_lt(c, _)), U32.is_eq(A.FatMap.get(ov, c), 0)) == A.FatMap.is_free(m0, c) : Bool}
  %Equal.sym(U32, A.FatMap.get(ov, c), MS.expect(m0, acc, c), MS.ov_get(m0, acc, c)) : {Bool.and(Bool.and(Nat.is_le(2n, c), Nat.is_lt(c, A.FatMap.count(m0))), U32.is_eq(_, 0)) == A.FatMap.is_free(m0, c) : Bool}
  %Equal.sym(Bool, A.FatMap.member(c, acc), False{}, eb) : {Bool.and(Bool.and(Nat.is_le(2n, c), Nat.is_lt(c, A.FatMap.count(m0))), U32.is_eq(MS.pick(_, A.FatMap.end(m0), A.FatMap.get(m0, c)), 0)) == A.FatMap.is_free(m0, c) : Bool}
  {==}

def MT.pick_true(b: Bool, +eb: {b == True{} : Bool}, +x: U32, +y: U32) -> {MS.pick(b, x, y) == x : U32}:
  %Equal.sym(Bool, b, True{}, eb) : {MS.pick(_, x, y) == x : U32}
  {==}

def MT.subst_zero(+a: U32, +b: U32, +e: {a == b : U32}, +z: {U32.is_eq(a, 0) == True{} : Bool}) -> {U32.is_eq(b, 0) == True{} : Bool}:
  %e : {U32.is_eq(_, 0) == True{} : Bool}
  z

# a cluster taken is not free in the map
def MT.absurd(+m0: A.FatMap, +m: A.FatMap, +acc: List<&2, Nat>, +c: Nat, +eb: {A.FatMap.member(c, acc) == True{} : Bool}, +hf: {A.FatMap.is_free(m, c) == True{} : Bool}, +hm: {m == MS.overlay(m0, acc) : A.FatMap}) -> Empty:
  +z = MQ.and_r(Bool.and(Nat.is_le(2n, c), Nat.is_lt(c, A.FatMap.count(m))), U32.is_eq(A.FatMap.get(m, c), 0), hf)
  +g = MT.get_eq(m0, m, acc, c, hm)
  +g2 = Equal.trans(U32, A.FatMap.get(m, c), MS.expect(m0, acc, c), A.FatMap.end(m0), g, MT.pick_true(A.FatMap.member(c, acc), eb, A.FatMap.end(m0), A.FatMap.get(m0, c)))
  +z2 = MT.subst_zero(A.FatMap.get(m, c), A.FatMap.end(m0), g2, z)
  MP.tf(Equal.trans(Bool, True{}, U32.is_eq(A.FatMap.end(m0), 0), False{}, Equal.sym(Bool, U32.is_eq(A.FatMap.end(m0), 0), True{}, z2), MQ.end_nz(A.FatMap.kind(m0))))

def MT.hm2(+m0: A.FatMap, +m: A.FatMap, +acc: List<&2, Nat>, +c: Nat, +hm: {m == MS.overlay(m0, acc) : A.FatMap}) -> {A.FatMap.set(m, c, A.FatMap.end(m)) == MS.overlay(m0, Con{c, acc}) : A.FatMap}:
  %hm : {A.FatMap.set(m, c, A.FatMap.end(m)) == A.FatMap.set(_, c, A.FatMap.end(m0)) : A.FatMap}
  %MS.end_eq(m, m0, MT.kind_of(m0, m, acc, hm)) : {A.FatMap.set(m, c, A.FatMap.end(m)) == A.FatMap.set(m, c, _) : A.FatMap}
  {==}

def MT.fr2(+m0: A.FatMap, +m: A.FatMap, +acc: List<&2, Nat>, +c: Nat, +eb: {A.FatMap.member(c, acc) == False{} : Bool}, +hf: {A.FatMap.is_free(m, c) == True{} : Bool}, +hm: {m == MS.overlay(m0, acc) : A.FatMap}, +hfr: {A.FatMap.all_free(m0, acc) == True{} : Bool}) -> {A.FatMap.all_free(m0, Con{c, acc}) == True{} : Bool}:
  +ec = Equal.trans(Bool, A.FatMap.is_free(m0, c), A.FatMap.is_free(m, c), True{}, Equal.sym(Bool, A.FatMap.is_free(m, c), A.FatMap.is_free(m0, c), MT.free_eq(m0, m, acc, c, eb, hm)), hf)
  %Equal.sym(Bool, A.FatMap.is_free(m0, c), True{}, ec) : {Bool.and(_, A.FatMap.all_free(m0, acc)) == True{} : Bool}
  hfr

def MT.d2(+acc: List<&2, Nat>, +c: Nat, +eb: {A.FatMap.member(c, acc) == False{} : Bool}, +hd: {A.FatMap.distinct(acc) == True{} : Bool}) -> {A.FatMap.distinct(Con{c, acc}) == True{} : Bool}:
  %Equal.sym(Bool, A.FatMap.member(c, acc), False{}, eb) : {Bool.and(Bool.not(_), A.FatMap.distinct(acc)) == True{} : Bool}
  hd

def MT.l2(+acc: List<&2, Nat>, +c: Nat, +p: Nat, +k0: Nat, +hl: {Nat.add(List.length(&2, Nat, acc), 1n+p) == k0 : Nat}) -> {Nat.add(List.length(&2, Nat, Con{c, acc}), p) == k0 : Nat}:
  Equal.trans(Nat, 1n+Nat.add(List.length(&2, Nat, acc), p), Nat.add(List.length(&2, Nat, acc), 1n+p), k0, Equal.sym(Nat, Nat.add(List.length(&2, Nat, acc), 1n+p), 1n+Nat.add(List.length(&2, Nat, acc), p), UL.nat_add_succ(List.length(&2, Nat, acc), p)), hl)

# the first phase, from any state its invariants hold in
def MT.claim(k: Nat, +m0: A.FatMap, +k0: Nat, +m: A.FatMap, found: Maybe<&2, Nat>, +acc: List<&2, Nat>, b: Bool, +eb: {MT.mem_found(found, acc) == b : Bool}, +hf: {MQ.found_free(m, found) == True{} : Bool}, +hm: {m == MS.overlay(m0, acc) : A.FatMap}, +hfr: {A.FatMap.all_free(m0, acc) == True{} : Bool}, +hd: {A.FatMap.distinct(acc) == True{} : Bool}, +hl: {Nat.add(List.length(&2, Nat, acc), k) == k0 : Nat}) -> MT.cspec(m0, k0, A.FatMap.claim(k, m, found, acc)):
  match k found b:
    case 0n _ _:
      (acc, (hm, ({==}, (hfr, (hd, Equal.trans(Nat, List.length(&2, Nat, acc), Nat.add(List.length(&2, Nat, acc), 0n), k0, Equal.sym(Nat, Nat.add(List.length(&2, Nat, acc), 0n), List.length(&2, Nat, acc), UL.nat_add_zero(List.length(&2, Nat, acc))), hl))))))
    case 1n+ +p None{} _:
      Unit{}
    case 1n+ +p Some{+c} True{}:
      Empty.absurd(MT.cspec(m0, k0, A.FatMap.claim(1n+p, m, Some{c}, acc)), MT.absurd(m0, m, acc, c, eb, hf, hm))
    case 1n+ +p Some{+c} False{}:
      +m2 = A.FatMap.set(m, c, A.FatMap.end(m))
      +f2 = A.FatMap.find(m2, Nat.add(c, 1n))
      MT.claim(p, m0, k0, m2, f2, Con{c, acc}, MT.mem_found(f2, Con{c, acc}), {==}, MQ.find(m2, Nat.add(c, 1n)), MT.hm2(m0, m, acc, c, hm), MT.fr2(m0, m, acc, c, eb, hf, hm, hfr), MT.d2(acc, c, eb, hd), MT.l2(acc, c, p, k0, hl))

def MU.last(xs: List<&2, Nat>, +p: Nat) -> Nat:
  match xs:
    case Nil{}:
      p
    case Con{+c, t}:
      MU.last(t, c)

def MU.or_true_l(a: Bool, -b: Bool, +e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

def MU.or_true_r(a: Bool, b: Bool, +e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def MU.link_kind(xs: List<&2, Nat>, +m: A.FatMap, +p: Nat) -> {A.FatMap.kind(A.FatMap.link(xs, m, p)) == A.FatMap.kind(m) : P.FatType}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Equal.trans(P.FatType, A.FatMap.kind(A.FatMap.link(t, A.FatMap.set(m, p, U32.from_nat(c)), c)), A.FatMap.kind(A.FatMap.set(m, p, U32.from_nat(c))), A.FatMap.kind(m), MU.link_kind(t, A.FatMap.set(m, p, U32.from_nat(c)), c), MQ.set_kind(m, p, U32.from_nat(c)))

def MU.link_frame(xs: List<&2, Nat>, +m: A.FatMap, +p: Nat, +n: Nat, +np: {Nat.is_eq(n, p) == False{} : Bool}, +nx: {A.FatMap.member(n, xs) == False{} : Bool}) -> {A.FatMap.get(A.FatMap.link(xs, m, p), n) == A.FatMap.get(m, n) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      +m1 = A.FatMap.set(m, p, U32.from_nat(c))
      +nc = MQ.or_false_l(Nat.is_eq(n, c), A.FatMap.member(n, t), nx)
      +nt = MQ.or_false_r(Nat.is_eq(n, c), A.FatMap.member(n, t), nx)
      Equal.trans(U32, A.FatMap.get(A.FatMap.link(t, m1, c), n), A.FatMap.get(m1, n), A.FatMap.get(m, n), MU.link_frame(t, m1, c, n, nc, nt), Laws.map_get_set_other(m, p, n, U32.from_nat(c), MQ.ne_sym(n, p, np)))

# the last of a list is in it
def MU.last_mem(xs: List<&2, Nat>, +c: Nat) -> {A.FatMap.member(MU.last(xs, c), Con{c, xs}) == True{} : Bool}:
  match xs:
    case Nil{}:
      MU.or_true_l(Nat.is_eq(c, c), False{}, MQ.eq_refl(c))
    case Con{+d, +t}:
      MU.or_true_r(Nat.is_eq(MU.last(t, d), c), A.FatMap.member(MU.last(t, d), Con{d, t}), MU.last_mem(t, d))

def MU.or_rest(a: Bool, b: Bool, +ea: {a == False{} : Bool}, +e: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == True{} : Bool}, MP.tf(ea))

def MU.ne_step(+x: Nat, +p: Nat, +y: Nat, +t: List<&2, Nat>, b: Bool, +eb: {Nat.is_eq(x, y) == b : Bool}, +hx: {A.FatMap.member(x, Con{y, t}) == True{} : Bool}, +hp: {A.FatMap.member(p, Con{y, t}) == False{} : Bool}, ih: {A.FatMap.member(x, t) == True{} : Bool} -> {Nat.is_eq(x, p) == False{} : Bool}) -> {Nat.is_eq(x, p) == False{} : Bool}:
  match b:
    case True{}:
      +xy = MQ.eq_true(x, y, eb)
      +py = MQ.or_false_l(Nat.is_eq(p, y), A.FatMap.member(p, t), hp)
      %Equal.sym(Nat, x, y, xy) : {Nat.is_eq(_, p) == False{} : Bool}
      MQ.ne_sym(p, y, py)
    case False{}:
      ih(MU.or_rest(Nat.is_eq(x, y), A.FatMap.member(x, t), eb, hx))

# x in ys and p not: x is not p
def MU.ne_of_mem(+x: Nat, +p: Nat, ys: List<&2, Nat>, +hx: {A.FatMap.member(x, ys) == True{} : Bool}, +hp: {A.FatMap.member(p, ys) == False{} : Bool}) -> {Nat.is_eq(x, p) == False{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Nat.is_eq(x, p) == False{} : Bool}, MP.ft(hx))
    case Con{+y, +t}:
      MU.ne_step(x, p, y, t, Nat.is_eq(x, y), {==}, hx, hp, h => MU.ne_of_mem(x, p, t, h, MQ.or_false_r(Nat.is_eq(p, y), A.FatMap.member(p, t), hp)))

def MU.links_first(+m: A.FatMap, +p: Nat, +c: Nat, +t: List<&2, Nat>, +np: {Nat.is_eq(p, c) == False{} : Bool}, +nt: {A.FatMap.member(p, t) == False{} : Bool}) -> {U32.is_eq(A.FatMap.get(A.FatMap.link(t, A.FatMap.set(m, p, U32.from_nat(c)), c), p), A.FatMap.mask(A.FatMap.kind(A.FatMap.link(t, A.FatMap.set(m, p, U32.from_nat(c)), c)), U32.from_nat(c))) == True{} : Bool}:
  +m1 = A.FatMap.set(m, p, U32.from_nat(c))
  +l = A.FatMap.link(t, m1, c)
  %Equal.sym(U32, A.FatMap.get(l, p), A.FatMap.get(m1, p), MU.link_frame(t, m1, c, p, np, nt)) : {U32.is_eq(_, A.FatMap.mask(A.FatMap.kind(l), U32.from_nat(c))) == True{} : Bool}
  %Equal.sym(U32, A.FatMap.get(m1, p), A.FatMap.mask(A.FatMap.kind(m), U32.from_nat(c)), Laws.map_get_set(m, p, U32.from_nat(c))) : {U32.is_eq(_, A.FatMap.mask(A.FatMap.kind(l), U32.from_nat(c))) == True{} : Bool}
  %Equal.sym(P.FatType, A.FatMap.kind(l), A.FatMap.kind(m), Equal.trans(P.FatType, A.FatMap.kind(l), A.FatMap.kind(m1), A.FatMap.kind(m), MU.link_kind(t, m1, c), MQ.set_kind(m, p, U32.from_nat(c)))) : {U32.is_eq(A.FatMap.mask(A.FatMap.kind(m), U32.from_nat(c)), A.FatMap.mask(_, U32.from_nat(c))) == True{} : Bool}
  MQ.u32_refl(A.FatMap.mask(A.FatMap.kind(m), U32.from_nat(c)))

# the last entry, past a write elsewhere
def MU.last_end(+m: A.FatMap, +p: Nat, +c: Nat, +t: List<&2, Nat>, +hp: {A.FatMap.member(p, Con{c, t}) == False{} : Bool}, +he: {A.FatMap.get(m, MU.last(t, c)) == A.FatMap.end(m) : U32}) -> {A.FatMap.get(A.FatMap.set(m, p, U32.from_nat(c)), MU.last(t, c)) == A.FatMap.end(A.FatMap.set(m, p, U32.from_nat(c))) : U32}:
  +m1 = A.FatMap.set(m, p, U32.from_nat(c))
  +x = MU.last(t, c)
  +ne = MQ.ne_sym(x, p, MU.ne_of_mem(x, p, Con{c, t}, MU.last_mem(t, c), hp))
  Equal.trans(U32, A.FatMap.get(m1, x), A.FatMap.get(m, x), A.FatMap.end(m1), Laws.map_get_set_other(m, p, x, U32.from_nat(c), ne), Equal.trans(U32, A.FatMap.get(m, x), A.FatMap.end(m), A.FatMap.end(m1), he, Equal.sym(U32, A.FatMap.end(m1), A.FatMap.end(m), MS.end_eq(m1, m, MQ.set_kind(m, p, U32.from_nat(c))))))

# linking distinct clusters, the last one's entry the end of a chain, makes
# them a chain
def MU.link_links(xs: List<&2, Nat>, +m: A.FatMap, +p: Nat, +hd: {A.FatMap.distinct(Con{p, xs}) == True{} : Bool}, +he: {A.FatMap.get(m, MU.last(xs, p)) == A.FatMap.end(m) : U32}) -> {A.FatMap.links.go(xs, A.FatMap.link(xs, m, p), p) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(U32, A.FatMap.get(m, p), A.FatMap.end(m), he) : {U32.is_eq(_, A.FatMap.end(m)) == True{} : Bool}
      MQ.u32_refl(A.FatMap.end(m))
    case Con{+c, +t}:
      +hp = MR.not_true(A.FatMap.member(p, Con{c, t}), MQ.and_l(Bool.not(A.FatMap.member(p, Con{c, t})), A.FatMap.distinct(Con{c, t}), hd))
      +np = MQ.or_false_l(Nat.is_eq(p, c), A.FatMap.member(p, t), hp)
      +nt = MQ.or_false_r(Nat.is_eq(p, c), A.FatMap.member(p, t), hp)
      +m1 = A.FatMap.set(m, p, U32.from_nat(c))
      +l = A.FatMap.link(t, m1, c)
      +e1 = MU.links_first(m, p, c, t, np, nt)
      %Equal.sym(Bool, U32.is_eq(A.FatMap.get(l, p), A.FatMap.mask(A.FatMap.kind(l), U32.from_nat(c))), True{}, e1) : {Bool.and(_, A.FatMap.links.go(t, l, c)) == True{} : Bool}
      MU.link_links(t, m1, c, MQ.and_r(Bool.not(A.FatMap.member(p, Con{c, t})), A.FatMap.distinct(Con{c, t}), hd), MU.last_end(m, p, c, t, hp, he))

def MV.mem_rev(+n: Nat, +acc: List<&2, Nat>) -> {A.FatMap.member(n, A.FatMap.rev_nat(acc, Nil{})) == A.FatMap.member(n, acc) : Bool}:
  Equal.trans(Bool, A.FatMap.member(n, A.FatMap.rev_nat(acc, Nil{})), Bool.or(A.FatMap.member(n, acc), False{}), A.FatMap.member(n, acc), MR.member_rev(n, acc, Nil{}), MR.or_false(A.FatMap.member(n, acc)))

def MV.first_clusters(a: A.FatAlloc) -> {A.FatAlloc.clusters(A.FatMap.link.first(a)) == A.FatAlloc.clusters(a) : List<&2, Nat>}:
  match a:
    case A.FatAlloc{m2, cs}:
      match cs:
        case Nil{}:
          {==}
        case Con{c, t}:
          {==}

def MV.after_clusters(+last: Nat, a: A.FatAlloc) -> {A.FatAlloc.clusters(A.FatMap.link.after(last, a)) == A.FatAlloc.clusters(a) : List<&2, Nat>}:
  match a:
    case A.FatAlloc{m2, cs}:
      {==}

def MV.fresh_c(+m: A.FatMap, +cs: List<&2, Nat>, +acc: List<&2, Nat>, +e2: {cs == A.FatMap.rev_nat(acc, Nil{}) : List<&2, Nat>}, +e3: {A.FatMap.all_free(m, acc) == True{} : Bool}) -> {A.FatMap.all_free(m, cs) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, cs, A.FatMap.rev_nat(acc, Nil{}), e2) : {A.FatMap.all_free(m, _) == True{} : Bool}
  %Equal.sym(Bool, A.FatMap.all_free(m, A.FatMap.rev_nat(acc, Nil{})), Bool.and(A.FatMap.all_free(m, acc), A.FatMap.all_free(m, Nil{})), MR.free_rev(m, acc, Nil{})) : {_ == True{} : Bool}
  %Equal.sym(Bool, A.FatMap.all_free(m, acc), True{}, e3) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def MV.distinct_c(+cs: List<&2, Nat>, +acc: List<&2, Nat>, +e2: {cs == A.FatMap.rev_nat(acc, Nil{}) : List<&2, Nat>}, +e4: {A.FatMap.distinct(acc) == True{} : Bool}) -> {A.FatMap.distinct(cs) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, cs, A.FatMap.rev_nat(acc, Nil{}), e2) : {A.FatMap.distinct(_) == True{} : Bool}
  MR.distinct_rev(acc, Nil{}, e4, {==}, MR.disjoint_nil(acc))

def MV.size_c(+k: Nat, +cs: List<&2, Nat>, +acc: List<&2, Nat>, +e2: {cs == A.FatMap.rev_nat(acc, Nil{}) : List<&2, Nat>}, +e5: {List.length(&2, Nat, acc) == k : Nat}) -> {List.length(&2, Nat, cs) == k : Nat}:
  %Equal.sym(List<&2, Nat>, cs, A.FatMap.rev_nat(acc, Nil{}), e2) : {List.length(&2, Nat, _) == k : Nat}
  Equal.trans(Nat, List.length(&2, Nat, A.FatMap.rev_nat(acc, Nil{})), Nat.add(List.length(&2, Nat, acc), 0n), k, MR.len_rev(acc, Nil{}), Equal.trans(Nat, Nat.add(List.length(&2, Nat, acc), 0n), List.length(&2, Nat, acc), k, UL.nat_add_zero(List.length(&2, Nat, acc)), e5))

def MV.fresh_d(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, s: MT.cfacts(m, k, m2, cs)) -> {A.FatMap.all_free(m, cs) == True{} : Bool}:
  (+acc, es) = s
  (+e1, es2) = es
  (+e2, es3) = es2
  (+e3, es4) = es3
  MV.fresh_c(m, cs, acc, e2, e3)

def MV.distinct_d(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, s: MT.cfacts(m, k, m2, cs)) -> {A.FatMap.distinct(cs) == True{} : Bool}:
  (+acc, es) = s
  (+e1, es2) = es
  (+e2, es3) = es2
  (+e3, es4) = es3
  (+e4, e5) = es4
  MV.distinct_c(cs, acc, e2, e4)

def MV.size_d(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, s: MT.cfacts(m, k, m2, cs)) -> {List.length(&2, Nat, cs) == k : Nat}:
  (+acc, es) = s
  (+e1, es2) = es
  (+e2, es3) = es2
  (+e3, es4) = es3
  (+e4, e5) = es4
  MV.size_c(k, cs, acc, e2, e5)

def MV.spec(+m: A.FatMap, +hint: Nat, +k: Nat) -> MT.cspec(m, k, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{})):
  MT.claim(k, m, k, m, A.FatMap.find(m, hint), Nil{}, MT.mem_found(A.FatMap.find(m, hint), Nil{}), {==}, MQ.find(m, hint), {==}, {==}, {==}, {==})

def MV.fresh_l(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, s: MT.cfacts(m, k, m2, cs)) -> {A.FatMap.all_free(m, A.FatAlloc.clusters(A.FatMap.link.first(A.FatAlloc{m2, cs}))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, A.FatAlloc.clusters(A.FatMap.link.first(A.FatAlloc{m2, cs})), cs, MV.first_clusters(A.FatAlloc{m2, cs})) : {A.FatMap.all_free(m, _) == True{} : Bool}
  MV.fresh_d(m, k, m2, cs, s)

def MV.fresh_r(+m: A.FatMap, +k: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.all_free(m, Laws.alloc_clusters(Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, A.FatMap.link.first, r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MV.fresh_l(m, k, m2, cs, s)

def Laws.alloc_fresh(m, hint, k):
  MV.fresh_r(m, k, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def MV.distinct_l(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, s: MT.cfacts(m, k, m2, cs)) -> {A.FatMap.distinct(A.FatAlloc.clusters(A.FatMap.link.first(A.FatAlloc{m2, cs}))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, A.FatAlloc.clusters(A.FatMap.link.first(A.FatAlloc{m2, cs})), cs, MV.first_clusters(A.FatAlloc{m2, cs})) : {A.FatMap.distinct(_) == True{} : Bool}
  MV.distinct_d(m, k, m2, cs, s)

def MV.distinct_r(+m: A.FatMap, +k: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.distinct(Laws.alloc_clusters(Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, A.FatMap.link.first, r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MV.distinct_l(m, k, m2, cs, s)

def Laws.alloc_distinct(m, hint, k):
  MV.distinct_r(m, k, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def MV.size_l(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, s: MT.cfacts(m, k, m2, cs)) -> {List.length(&2, Nat, A.FatAlloc.clusters(A.FatMap.link.first(A.FatAlloc{m2, cs}))) == k : Nat}:
  %Equal.sym(List<&2, Nat>, A.FatAlloc.clusters(A.FatMap.link.first(A.FatAlloc{m2, cs})), cs, MV.first_clusters(A.FatAlloc{m2, cs})) : {List.length(&2, Nat, _) == k : Nat}
  MV.size_d(m, k, m2, cs, s)

def MV.size_r(+m: A.FatMap, +k: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {Laws.alloc_size(k, Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, A.FatMap.link.first, r)) == k : Nat}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MV.size_l(m, k, m2, cs, s)

def Laws.alloc_count(m, hint, k):
  MV.size_r(m, k, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def MW.subst_list(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +e: {a == b : List<&2, Nat>}, +h: {A.FatMap.member(n, a) == True{} : Bool}) -> {A.FatMap.member(n, b) == True{} : Bool}:
  %e : {A.FatMap.member(n, _) == True{} : Bool}
  h

def MW.subst_list_f(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +e: {a == b : List<&2, Nat>}, +h: {A.FatMap.member(n, a) == False{} : Bool}) -> {A.FatMap.member(n, b) == False{} : Bool}:
  %e : {A.FatMap.member(n, _) == False{} : Bool}
  h

def MW.pick_false(b: Bool, +eb: {b == False{} : Bool}, +x: U32, +y: U32) -> {MS.pick(b, x, y) == y : U32}:
  %Equal.sym(Bool, b, False{}, eb) : {MS.pick(_, x, y) == y : U32}
  {==}

def MW.hit(+m: A.FatMap, +m2: A.FatMap, +cs: List<&2, Nat>, +n: Nat, +hit: {A.FatMap.member(n, cs) == True{} : Bool}, +acc: List<&2, Nat>, +e1: {m2 == MS.overlay(m, acc) : A.FatMap}, +e2: {cs == A.FatMap.rev_nat(acc, Nil{}) : List<&2, Nat>}) -> {A.FatMap.get(m2, n) == A.FatMap.end(m2) : U32}:
  +ha = Equal.trans(Bool, A.FatMap.member(n, acc), A.FatMap.member(n, A.FatMap.rev_nat(acc, Nil{})), True{}, Equal.sym(Bool, A.FatMap.member(n, A.FatMap.rev_nat(acc, Nil{})), A.FatMap.member(n, acc), MV.mem_rev(n, acc)), MW.subst_list(cs, A.FatMap.rev_nat(acc, Nil{}), n, e2, hit))
  +g = Equal.trans(U32, A.FatMap.get(m2, n), MS.expect(m, acc, n), A.FatMap.end(m), MT.get_eq(m, m2, acc, n, e1), MT.pick_true(A.FatMap.member(n, acc), ha, A.FatMap.end(m), A.FatMap.get(m, n)))
  Equal.trans(U32, A.FatMap.get(m2, n), A.FatMap.end(m), A.FatMap.end(m2), g, Equal.sym(U32, A.FatMap.end(m2), A.FatMap.end(m), MS.end_eq(m2, m, MT.kind_of(m, m2, acc, e1))))

def MW.miss(+m: A.FatMap, +m2: A.FatMap, +cs: List<&2, Nat>, +n: Nat, +miss: {A.FatMap.member(n, cs) == False{} : Bool}, +acc: List<&2, Nat>, +e1: {m2 == MS.overlay(m, acc) : A.FatMap}, +e2: {cs == A.FatMap.rev_nat(acc, Nil{}) : List<&2, Nat>}) -> {A.FatMap.get(m2, n) == A.FatMap.get(m, n) : U32}:
  +ha = Equal.trans(Bool, A.FatMap.member(n, acc), A.FatMap.member(n, A.FatMap.rev_nat(acc, Nil{})), False{}, Equal.sym(Bool, A.FatMap.member(n, A.FatMap.rev_nat(acc, Nil{})), A.FatMap.member(n, acc), MV.mem_rev(n, acc)), MW.subst_list_f(cs, A.FatMap.rev_nat(acc, Nil{}), n, e2, miss))
  Equal.trans(U32, A.FatMap.get(m2, n), MS.expect(m, acc, n), A.FatMap.get(m, n), MT.get_eq(m, m2, acc, n, e1), MW.pick_false(A.FatMap.member(n, acc), ha, A.FatMap.end(m), A.FatMap.get(m, n)))

def MW.links_c(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +c: Nat, +t: List<&2, Nat>, s: MT.cfacts(m, k, m2, Con{c, t})) -> {A.FatMap.links.go(t, A.FatMap.link(t, m2, c), c) == True{} : Bool}:
  (+acc, es) = s
  (+e1, es2) = es
  (+e2, es3) = es2
  (+e3, es4) = es3
  (+e4, e5) = es4
  MU.link_links(t, m2, c, MV.distinct_c(Con{c, t}, acc, e2, e4), MW.hit(m, m2, Con{c, t}, MU.last(t, c), MU.last_mem(t, c), acc, e1, e2))

def MW.links_l(+m: A.FatMap, +k: Nat, +m2: A.FatMap, cs: List<&2, Nat>) -> MT.cfacts(m, k, m2, cs) -> {A.FatMap.links(A.FatAlloc.map(A.FatMap.link.first(A.FatAlloc{m2, cs})), A.FatAlloc.clusters(A.FatMap.link.first(A.FatAlloc{m2, cs}))) == True{} : Bool}:
  match cs:
    case Nil{}:
      s => {==}
    case Con{+c, +t}:
      s => MW.links_c(m, k, m2, c, t, s)

def MW.links_r(+m: A.FatMap, +k: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.links(Laws.alloc_map(m, Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, A.FatMap.link.first, r)), Laws.alloc_clusters(Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, A.FatMap.link.first, r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MW.links_l(m, k, m2, cs)(s)

def Laws.alloc_links(m, hint, k):
  MW.links_r(m, k, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def MW.miss_s(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, +n: Nat, +miss: {A.FatMap.member(n, cs) == False{} : Bool}, s: MT.cfacts(m, k, m2, cs)) -> {A.FatMap.get(m2, n) == A.FatMap.get(m, n) : U32}:
  (+acc, es) = s
  (+e1, es2) = es
  (+e2, es3) = es2
  MW.miss(m, m2, cs, n, miss, acc, e1, e2)

def MW.frame_l(+m: A.FatMap, +k: Nat, +m2: A.FatMap, cs: List<&2, Nat>, +n: Nat) -> MT.cfacts(m, k, m2, cs) -> {A.FatMap.member(n, A.FatAlloc.clusters(A.FatMap.link.first(A.FatAlloc{m2, cs}))) == False{} : Bool} -> {A.FatMap.get(A.FatAlloc.map(A.FatMap.link.first(A.FatAlloc{m2, cs})), n) == A.FatMap.get(m, n) : U32}:
  match cs:
    case Nil{}:
      s => miss => MW.miss_s(m, k, m2, Nil{}, n, miss, s)
    case Con{+c, +t}:
      s => +miss => Equal.trans(U32, A.FatMap.get(A.FatMap.link(t, m2, c), n), A.FatMap.get(m2, n), A.FatMap.get(m, n), MU.link_frame(t, m2, c, n, MQ.or_false_l(Nat.is_eq(n, c), A.FatMap.member(n, t), miss), MQ.or_false_r(Nat.is_eq(n, c), A.FatMap.member(n, t), miss)), MW.miss_s(m, k, m2, Con{c, t}, n, miss, s))

def MW.frame_r(+m: A.FatMap, +k: Nat, +n: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.member(n, Laws.alloc_clusters(Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, A.FatMap.link.first, r))) == False{} : Bool} -> {A.FatMap.get(Laws.alloc_map(m, Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, A.FatMap.link.first, r)), n) == A.FatMap.get(m, n) : U32}:
  match r:
    case Fail{e}:
      s => miss => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => miss => MW.frame_l(m, k, m2, cs, n)(s)(miss)

def Laws.alloc_frame(m, hint, k, n, miss):
  MW.frame_r(m, k, n, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))(miss)

def MW.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def MW.used_not_free(+m: A.FatMap, +n: Nat, +used: {U32.is_eq(A.FatMap.get(m, n), 0) == False{} : Bool}) -> {A.FatMap.is_free(m, n) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(A.FatMap.get(m, n), 0), False{}, used) : {Bool.and(Bool.and(Nat.is_le(2n, n), Nat.is_lt(n, A.FatMap.count(m))), _) == False{} : Bool}
  MW.and_false(Bool.and(Nat.is_le(2n, n), Nat.is_lt(n, A.FatMap.count(m))))

def MW.free_subst(+m: A.FatMap, +x: Nat, +c: Nat, +e: {x == c : Nat}, +h: {A.FatMap.is_free(m, c) == True{} : Bool}) -> {A.FatMap.is_free(m, x) == True{} : Bool}:
  %Equal.sym(Nat, x, c, e) : {A.FatMap.is_free(m, _) == True{} : Bool}
  h

def MW.not_in_step(+m: A.FatMap, +x: Nat, +c: Nat, +t: List<&2, Nat>, b: Bool, +eb: {Nat.is_eq(x, c) == b : Bool}, +all: {A.FatMap.all_free(m, Con{c, t}) == True{} : Bool}, +nf: {A.FatMap.is_free(m, x) == False{} : Bool}, ih: {A.FatMap.all_free(m, t) == True{} : Bool} -> {A.FatMap.member(x, t) == False{} : Bool}) -> {A.FatMap.member(x, Con{c, t}) == False{} : Bool}:
  match b:
    case True{}:
      +xc = MQ.eq_true(x, c, eb)
      +fc = MQ.and_l(A.FatMap.is_free(m, c), A.FatMap.all_free(m, t), all)
      +fx = MW.free_subst(m, x, c, xc, fc)
      Empty.absurd({A.FatMap.member(x, Con{c, t}) == False{} : Bool}, MP.tf(Equal.trans(Bool, True{}, A.FatMap.is_free(m, x), False{}, Equal.sym(Bool, A.FatMap.is_free(m, x), True{}, fx), nf)))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(x, c), False{}, eb) : {Bool.or(_, A.FatMap.member(x, t)) == False{} : Bool}
      ih(MQ.and_r(A.FatMap.is_free(m, c), A.FatMap.all_free(m, t), all))

# a cluster that is not free is not among clusters that all are
def MW.not_in(+m: A.FatMap, cs: List<&2, Nat>, +x: Nat, +all: {A.FatMap.all_free(m, cs) == True{} : Bool}, +nf: {A.FatMap.is_free(m, x) == False{} : Bool}) -> {A.FatMap.member(x, cs) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      MW.not_in_step(m, x, c, t, Nat.is_eq(x, c), {==}, all, nf, a => MW.not_in(m, t, x, a, nf))

def MW.used_l(+m: A.FatMap, +m2: A.FatMap, cs: List<&2, Nat>, +n: Nat, +nin: {A.FatMap.member(n, cs) == False{} : Bool}, +acc: List<&2, Nat>, +e1: {m2 == MS.overlay(m, acc) : A.FatMap}, +e2: {cs == A.FatMap.rev_nat(acc, Nil{}) : List<&2, Nat>}) -> {A.FatMap.get(A.FatAlloc.map(A.FatMap.link.first(A.FatAlloc{m2, cs})), n) == A.FatMap.get(m, n) : U32}:
  match cs:
    case Nil{}:
      MW.miss(m, m2, Nil{}, n, nin, acc, e1, e2)
    case Con{+c, +t}:
      Equal.trans(U32, A.FatMap.get(A.FatMap.link(t, m2, c), n), A.FatMap.get(m2, n), A.FatMap.get(m, n), MU.link_frame(t, m2, c, n, MQ.or_false_l(Nat.is_eq(n, c), A.FatMap.member(n, t), nin), MQ.or_false_r(Nat.is_eq(n, c), A.FatMap.member(n, t), nin)), MW.miss(m, m2, Con{c, t}, n, nin, acc, e1, e2))

def MW.used_d(+m: A.FatMap, +k: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, +n: Nat, +used: {U32.is_eq(A.FatMap.get(m, n), 0) == False{} : Bool}, s: MT.cfacts(m, k, m2, cs)) -> {A.FatMap.get(A.FatAlloc.map(A.FatMap.link.first(A.FatAlloc{m2, cs})), n) == A.FatMap.get(m, n) : U32}:
  (+acc, es) = s
  (+e1, es2) = es
  (+e2, es3) = es2
  (+e3, es4) = es3
  +nin = MW.not_in(m, cs, n, MV.fresh_c(m, cs, acc, e2, e3), MW.used_not_free(m, n, used))
  MW.used_l(m, m2, cs, n, nin, acc, e1, e2)

def MW.used_r(+m: A.FatMap, +k: Nat, +n: Nat, +used: {U32.is_eq(A.FatMap.get(m, n), 0) == False{} : Bool}, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.get(Laws.alloc_map(m, Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, A.FatMap.link.first, r)), n) == A.FatMap.get(m, n) : U32}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MW.used_d(m, k, m2, cs, n, used, s)

def Laws.alloc_keeps_used(m, hint, k, n, used):
  MW.used_r(m, k, n, used, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def MX.fresh_r(+m: A.FatMap, +k: Nat, +last: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.all_free(m, Laws.alloc_clusters(Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, a => A.FatMap.link.after(last, a), r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MV.fresh_d(m, k, m2, cs, s)

def MX.distinct_r(+m: A.FatMap, +k: Nat, +last: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.distinct(Laws.alloc_clusters(Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, a => A.FatMap.link.after(last, a), r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MV.distinct_d(m, k, m2, cs, s)

def MX.size_r(+m: A.FatMap, +k: Nat, +last: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {Laws.alloc_size(k, Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, a => A.FatMap.link.after(last, a), r)) == k : Nat}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MV.size_d(m, k, m2, cs, s)

def Laws.extend_fresh(m, last, hint, k):
  MX.fresh_r(m, k, last, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def Laws.extend_distinct(m, last, hint, k):
  MX.distinct_r(m, k, last, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def Laws.extend_count(m, last, hint, k):
  MX.size_r(m, k, last, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def MX.k0(+k: Nat, +e: {0n == k : Nat}, +pos: {Nat.is_eq(k, 0n) == False{} : Bool}) -> {Nat.is_eq(0n, 0n) == False{} : Bool}:
  %Equal.sym(Nat, 0n, k, e) : {Nat.is_eq(_, 0n) == False{} : Bool}
  pos

def MX.links_d(+m: A.FatMap, +k: Nat, +last: Nat, +m2: A.FatMap, +c: Nat, +t: List<&2, Nat>, +used_last: {A.FatMap.is_free(m, last) == False{} : Bool}, s: MT.cfacts(m, k, m2, Con{c, t})) -> {A.FatMap.links.go(Con{c, t}, A.FatMap.link(Con{c, t}, m2, last), last) == True{} : Bool}:
  (+acc, es) = s
  (+e1, es2) = es
  (+e2, es3) = es2
  (+e3, es4) = es3
  (+e4, e5) = es4
  +cs = {Con{c, t} : List<&2, Nat>}
  +hd = MR.distinct_cons(last, cs, MW.not_in(m, cs, last, MV.fresh_c(m, cs, acc, e2, e3), used_last), MV.distinct_c(cs, acc, e2, e4))
  MU.link_links(cs, m2, last, hd, MW.hit(m, m2, cs, MU.last(t, c), MU.last_mem(t, c), acc, e1, e2))

def MX.links_c(+m: A.FatMap, +k: Nat, +last: Nat, +m2: A.FatMap, cs: List<&2, Nat>, +used_last: {A.FatMap.is_free(m, last) == False{} : Bool}, +pos: {Nat.is_eq(k, 0n) == False{} : Bool}) -> MT.cfacts(m, k, m2, cs) -> {A.FatMap.links.go(cs, A.FatMap.link(cs, m2, last), last) == True{} : Bool}:
  match cs:
    case Nil{}:
      s => Empty.absurd({A.FatMap.links.go(Nil{}, A.FatMap.link(Nil{}, m2, last), last) == True{} : Bool}, MP.tf(MX.k0(k, MV.size_d(m, k, m2, Nil{}, s), pos)))
    case Con{+c, +t}:
      s => MX.links_d(m, k, last, m2, c, t, used_last, s)

def MX.links_r(+m: A.FatMap, +k: Nat, +last: Nat, +used_last: {A.FatMap.is_free(m, last) == False{} : Bool}, +pos: {Nat.is_eq(k, 0n) == False{} : Bool}, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {Laws.chain_after(last, Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, a => A.FatMap.link.after(last, a), r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MX.links_c(m, k, last, m2, cs, used_last, pos)(s)

def Laws.extend_links(m, last, hint, k, used_last, pos):
  MX.links_r(m, k, last, used_last, pos, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def MX.frame_c(+m: A.FatMap, +k: Nat, +last: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, +n: Nat, +miss: {A.FatMap.member(n, cs) == False{} : Bool}, +other: {Nat.is_eq(n, last) == False{} : Bool}, s: MT.cfacts(m, k, m2, cs)) -> {A.FatMap.get(A.FatMap.link(cs, m2, last), n) == A.FatMap.get(m, n) : U32}:
  Equal.trans(U32, A.FatMap.get(A.FatMap.link(cs, m2, last), n), A.FatMap.get(m2, n), A.FatMap.get(m, n), MU.link_frame(cs, m2, last, n, other, miss), MW.miss_s(m, k, m2, cs, n, miss, s))

def MX.frame_r(+m: A.FatMap, +k: Nat, +last: Nat, +n: Nat, +other: {Nat.is_eq(n, last) == False{} : Bool}, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.member(n, Laws.alloc_clusters(Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, a => A.FatMap.link.after(last, a), r))) == False{} : Bool} -> {A.FatMap.get(Laws.alloc_map(m, Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, a => A.FatMap.link.after(last, a), r)), n) == A.FatMap.get(m, n) : U32}:
  match r:
    case Fail{e}:
      s => miss => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => miss => MX.frame_c(m, k, last, m2, cs, n, miss, other, s)

def Laws.extend_frame(m, last, hint, k, n, miss, other):
  MX.frame_r(m, k, last, n, other, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))(miss)

def MX.used_c(+m: A.FatMap, +k: Nat, +last: Nat, +m2: A.FatMap, +cs: List<&2, Nat>, +n: Nat, +used: {U32.is_eq(A.FatMap.get(m, n), 0) == False{} : Bool}, +other: {Nat.is_eq(n, last) == False{} : Bool}, s: MT.cfacts(m, k, m2, cs)) -> {A.FatMap.get(A.FatMap.link(cs, m2, last), n) == A.FatMap.get(m, n) : U32}:
  (+acc, es) = s
  (+e1, es2) = es
  (+e2, es3) = es2
  (+e3, es4) = es3
  +nin = MW.not_in(m, cs, n, MV.fresh_c(m, cs, acc, e2, e3), MW.used_not_free(m, n, used))
  Equal.trans(U32, A.FatMap.get(A.FatMap.link(cs, m2, last), n), A.FatMap.get(m2, n), A.FatMap.get(m, n), MU.link_frame(cs, m2, last, n, other, nin), MW.miss(m, m2, cs, n, nin, acc, e1, e2))

def MX.used_r(+m: A.FatMap, +k: Nat, +last: Nat, +n: Nat, +used: {U32.is_eq(A.FatMap.get(m, n), 0) == False{} : Bool}, +other: {Nat.is_eq(n, last) == False{} : Bool}, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> MT.cspec(m, k, r) -> {A.FatMap.get(Laws.alloc_map(m, Result.map(&2, &2, E.FatError, A.FatAlloc, A.FatAlloc, a => A.FatMap.link.after(last, a), r)), n) == A.FatMap.get(m, n) : U32}:
  match r:
    case Fail{e}:
      s => {==}
    case Done{A.FatAlloc{+m2, +cs}}:
      s => MX.used_c(m, k, last, m2, cs, n, used, other, s)

def Laws.extend_keeps_used(m, last, hint, k, n, used, other):
  MX.used_r(m, k, last, n, used, other, A.FatMap.claim(k, m, A.FatMap.find(m, hint), Nil{}))(MV.spec(m, hint, k))

def MX.free_frame(cs: List<&2, Nat>, +m: A.FatMap, +c: Nat, +miss: {A.FatMap.member(c, cs) == False{} : Bool}) -> {A.FatMap.get(A.FatMap.free(cs, m), c) == A.FatMap.get(m, c) : U32}:
  match cs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +m1 = A.FatMap.set(m, h, 0)
      Equal.trans(U32, A.FatMap.get(A.FatMap.free(t, m1), c), A.FatMap.get(m1, c), A.FatMap.get(m, c), MX.free_frame(t, m1, c, MQ.or_false_r(Nat.is_eq(c, h), A.FatMap.member(c, t), miss)), Laws.map_get_set_other(m, h, c, 0, MQ.ne_sym(c, h, MQ.or_false_l(Nat.is_eq(c, h), A.FatMap.member(c, t), miss))))

def Laws.free_frame(m, cs, c, miss):
  MX.free_frame(cs, m, c, miss)

def MX.or_rest_l(a: Bool, b: Bool, +eb: {b == False{} : Bool}, +e: {Bool.or(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MP.tf(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, e), eb)))

def MX.set_zero(+m: A.FatMap, +h: Nat, +c: Nat, +ch: {c == h : Nat}) -> {A.FatMap.get(A.FatMap.set(m, h, 0), c) == 0 : U32}:
  %Equal.sym(Nat, c, h, ch) : {A.FatMap.get(A.FatMap.set(m, h, 0), _) == 0 : U32}
  Equal.trans(U32, A.FatMap.get(A.FatMap.set(m, h, 0), h), A.FatMap.mask(A.FatMap.kind(m), 0), 0, Laws.map_get_set(m, h, 0), MQ.mask_zero(A.FatMap.kind(m)))

def MX.frees_step(+h: Nat, +t: List<&2, Nat>, +m: A.FatMap, +c: Nat, b: Bool, +eb: {A.FatMap.member(c, t) == b : Bool}, +hit: {A.FatMap.member(c, Con{h, t}) == True{} : Bool}, ih: {A.FatMap.member(c, t) == True{} : Bool} -> {A.FatMap.get(A.FatMap.free(t, A.FatMap.set(m, h, 0)), c) == 0 : U32}) -> {A.FatMap.get(A.FatMap.free(Con{h, t}, m), c) == 0 : U32}:
  match b:
    case True{}:
      ih(eb)
    case False{}:
      +m1 = A.FatMap.set(m, h, 0)
      +ch = MQ.eq_true(c, h, MX.or_rest_l(Nat.is_eq(c, h), A.FatMap.member(c, t), eb, hit))
      Equal.trans(U32, A.FatMap.get(A.FatMap.free(t, m1), c), A.FatMap.get(m1, c), 0, MX.free_frame(t, m1, c, eb), MX.set_zero(m, h, c, ch))

def MX.frees(cs: List<&2, Nat>, +m: A.FatMap, +c: Nat, +hit: {A.FatMap.member(c, cs) == True{} : Bool}) -> {A.FatMap.get(A.FatMap.free(cs, m), c) == 0 : U32}:
  match cs:
    case Nil{}:
      Empty.absurd({A.FatMap.get(A.FatMap.free(Nil{}, m), c) == 0 : U32}, MP.ft(hit))
    case Con{+h, +t}:
      MX.frees_step(h, t, m, c, A.FatMap.member(c, t), {==}, hit, e => MX.frees(t, A.FatMap.set(m, h, 0), c, e))

def Laws.free_frees(m, cs, c, hit):
  MX.frees(cs, m, c, hit)

def Laws.cut_ends(m, c):
  Equal.trans(U32, A.FatMap.get(A.FatMap.set(m, c, A.FatMap.end(m)), c), A.FatMap.mask(A.FatMap.kind(m), A.FatMap.end(m)), A.FatMap.end(m), Laws.map_get_set(m, c, A.FatMap.end(m)), MQ.mask_end(A.FatMap.kind(m)))

def MY.tail_free(+taken: List<&2, B.Octets>, r: Result<&2, &2, E.FatError, B.Octets>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{s}:
      Bool.not(L.FatAlias.taken(s, taken))

def MY.tail_go(fuel: Nat, +base: List<&2, U32>, +ext: List<&2, U32>, +taken: List<&2, B.Octets>, +n: Nat, +cand: B.Octets, u: Bool, +eu: {L.FatAlias.taken(cand, taken) == u : Bool}) -> {MY.tail_free(taken, L.FatAlias.tail.go(fuel, base, ext, taken, n, cand, u)) == True{} : Bool}:
  match fuel u:
    case _ False{}:
      %Equal.sym(Bool, L.FatAlias.taken(cand, taken), False{}, eu) : {Bool.not(_) == True{} : Bool}
      {==}
    case 0n True{}:
      {==}
    case 1n+f True{}:
      +n2 = Nat.add(n, 1n)
      +c2 = L.FatAlias.with_tail(base, ext, n2)
      MY.tail_go(f, base, ext, taken, n2, c2, L.FatAlias.taken(c2, taken), {==})

def MY.tail(+base: List<&2, U32>, +ext: List<&2, U32>, +taken: List<&2, B.Octets>) -> {MY.tail_free(taken, L.FatAlias.tail(base, ext, taken)) == True{} : Bool}:
  +n = L.FatAlias.first_tail(base, ext, taken)
  +c = L.FatAlias.with_tail(base, ext, n)
  MY.tail_go(999998n, base, ext, taken, n, c, L.FatAlias.taken(c, taken), {==})

def MY.bind(+taken: List<&2, B.Octets>, +long: List<&2, U32>, r: Result<&2, &2, E.FatError, B.Octets>, +h: {MY.tail_free(taken, r) == True{} : Bool}) -> {Laws.alias_free(taken, Result.bind(&2, &2, E.FatError, B.Octets, L.FatAlias, r, s => Result.pure(&2, &2, E.FatError, L.FatAlias, L.FatAlias{s, 0, long}))) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{s}:
      h

def MY.tailed(p: L.FatBasis, +taken: List<&2, B.Octets>, +long: List<&2, U32>) -> {Laws.alias_free(taken, L.FatAlias.tailed.go(p, taken, long)) == True{} : Bool}:
  match p:
    case L.FatBasis{+b, +e, l}:
      MY.bind(taken, long, L.FatAlias.tail(b, e, taken), MY.tail(b, e, taken))

def MY.fits_case(m: Maybe<&2, U32>, +s: B.Octets, +long: List<&2, U32>) -> {L.FatAlias.short(L.FatAlias.fits.case(m, s, long)) == s : B.Octets}:
  match m:
    case None{}:
      {==}
    case Some{f}:
      {==}

def MY.fits.done.go(+s2: B.Octets, +s: B.Octets, +taken: List<&2, B.Octets>, +es: {s2 == s : B.Octets}, +eu: {L.FatAlias.taken(s, taken) == False{} : Bool}) -> {Bool.not(L.FatAlias.taken(s2, taken)) == True{} : Bool}:
  %Equal.sym(B.Octets, s2, s, es) : {Bool.not(L.FatAlias.taken(_, taken)) == True{} : Bool}
  %Equal.sym(Bool, L.FatAlias.taken(s, taken), False{}, eu) : {Bool.not(_) == True{} : Bool}
  {==}

def MY.fits.done(a: L.FatAlias, +s: B.Octets, +taken: List<&2, B.Octets>) -> {L.FatAlias.short(a) == s : B.Octets} -> {L.FatAlias.taken(s, taken) == False{} : Bool} -> {Laws.alias_free(taken, Done{a}) == True{} : Bool}:
  match a:
    case L.FatAlias{+s2, nt, long}:
      +es => +eu => MY.fits.done.go(s2, s, taken, es, eu)

def MY.fits(+s: B.Octets, +taken: List<&2, B.Octets>, +nt: Bool, +xs: List<&2, U32>, used: Bool, +eu: {L.FatAlias.taken(s, taken) == used : Bool}) -> {Laws.alias_free(taken, L.FatAlias.fits(used, nt, xs, s, taken)) == True{} : Bool}:
  match used:
    case True{}:
      MY.tailed(L.FatAlias.basis(xs), taken, R.FatName.units(L.FatAlias.text(xs)))
    case False{}:
      +m = L.FatAlias.case(nt, L.FatAlias.split83(xs))
      +long = R.FatName.units(L.FatAlias.text(xs))
      MY.fits.done(L.FatAlias.fits.case(m, s, long), s, taken)(MY.fits_case(m, s, long))(eu)

def MY.make_go(m: Maybe<&2, B.Octets>, +nt: Bool, +xs: List<&2, U32>, +taken: List<&2, B.Octets>) -> {Laws.alias_free(taken, L.FatAlias.make.go(m, nt, xs, taken)) == True{} : Bool}:
  match m:
    case None{}:
      MY.tailed(L.FatAlias.basis(xs), taken, R.FatName.units(L.FatAlias.text(xs)))
    case Some{+s}:
      MY.fits(s, taken, nt, xs, L.FatAlias.taken(s, taken), {==})

def Laws.alias_fresh(nt_case, name, taken):
  MY.make_go(R.FatName.short_of(name), nt_case, L.FatAlias.codes(name), taken)

def MY.same(a: P.FatType, b: P.FatType) -> {Laws.fat_same_type(a, b) == K.FatFormat.same_type(a, b) : Bool}:
  match a b:
    case P.Fat12{} P.Fat12{}:
      {==}
    case P.Fat12{} P.Fat16{}:
      {==}
    case P.Fat12{} P.Fat32{}:
      {==}
    case P.Fat16{} P.Fat12{}:
      {==}
    case P.Fat16{} P.Fat16{}:
      {==}
    case P.Fat16{} P.Fat32{}:
      {==}
    case P.Fat32{} P.Fat12{}:
      {==}
    case P.Fat32{} P.Fat16{}:
      {==}
    case P.Fat32{} P.Fat32{}:
      {==}

def MY.vk.done(+t: P.FatType, +l: K.FatLayout, +v: P.FatVolume, +eb: {Bool.and(K.FatFormat.same_type(P.FatVolume.kind(v), t), Nat.is_eq(U32.to_nat(P.FatVolume.clusters(v)), K.FatLayout.clusters(l))) == True{} : Bool}, +e: {P.FatVolume.of_bpb(P.FatOptions.default(), K.FatLayout.bpb(l)) == Done{v} : Result<&2, &2, E.FatError, P.FatVolume>}) -> {Laws.mounts_as(t, l, P.FatVolume.of_bpb(P.FatOptions.default(), K.FatLayout.bpb(l))) == True{} : Bool}:
  %Equal.sym(Result<&2, &2, E.FatError, P.FatVolume>, P.FatVolume.of_bpb(P.FatOptions.default(), K.FatLayout.bpb(l)), Done{v}, e) : {Laws.mounts_as(t, l, _) == True{} : Bool}
  %Equal.sym(Bool, Laws.fat_same_type(P.FatVolume.kind(v), t), K.FatFormat.same_type(P.FatVolume.kind(v), t), MY.same(P.FatVolume.kind(v), t)) : {Bool.and(_, Nat.is_eq(U32.to_nat(P.FatVolume.clusters(v)), K.FatLayout.clusters(l))) == True{} : Bool}
  eb

def MY.vk(+t: P.FatType, +l: K.FatLayout, +v: P.FatVolume, b: Bool, +eb: {Bool.and(K.FatFormat.same_type(P.FatVolume.kind(v), t), Nat.is_eq(U32.to_nat(P.FatVolume.clusters(v)), K.FatLayout.clusters(l))) == b : Bool}) -> {P.FatVolume.of_bpb(P.FatOptions.default(), K.FatLayout.bpb(l)) == Done{v} : Result<&2, &2, E.FatError, P.FatVolume>} -> {Laws.mounts_ok(t, K.FatFormat.verify.kind(b, l)) == True{} : Bool}:
  match b:
    case True{}:
      +e => MY.vk.done(t, l, v, eb, e)
    case False{}:
      e => {==}

def MY.vv(+t: P.FatType, +l: K.FatLayout, r: Result<&2, &2, E.FatError, P.FatVolume>) -> {P.FatVolume.of_bpb(P.FatOptions.default(), K.FatLayout.bpb(l)) == r : Result<&2, &2, E.FatError, P.FatVolume>} -> {Laws.mounts_ok(t, K.FatFormat.verify.vol(r, t, l)) == True{} : Bool}:
  match r:
    case Fail{x}:
      e => {==}
    case Done{+v}:
      e => MY.vk(t, l, v, Bool.and(K.FatFormat.same_type(P.FatVolume.kind(v), t), Nat.is_eq(U32.to_nat(P.FatVolume.clusters(v)), K.FatLayout.clusters(l))), {==})(e)

def MY.vr(+t: P.FatType, r: Result<&2, &2, E.FatError, K.FatLayout>) -> {Laws.mounts_ok(t, K.FatFormat.verify.r(t, r)) == True{} : Bool}:
  match r:
    case Fail{x}:
      {==}
    case Done{+l}:
      MY.vv(t, l, P.FatVolume.of_bpb(P.FatOptions.default(), K.FatLayout.bpb(l)))({==})

def Laws.format_mounts(t, tot, o):
  MY.vr(t, K.FatFormat.layout.raw(t, tot, o))

def Laws.w_ne():
  {==}

def Laws.v_alloc():
  {==}

def Laws.v_alloc_map():
  {==}

def Laws.v_alloc_hint():
  {==}

def Laws.v_alloc_full():
  {==}

def Laws.w_alloc_miss():
  {==}

def Laws.w_used():
  {==}

def Laws.v_extend_map():
  {==}

def Laws.w_extend_used():
  {==}

def Laws.w_extend_pos():
  {==}

def Laws.w_extend_miss():
  {==}

def Laws.w_extend_other():
  {==}

def Laws.w_free_hit():
  {==}

def Laws.w_free_miss():
  {==}

def Laws.v_free():
  {==}

def Laws.v_alias_tail():
  {==}

def Laws.v_alias_tail2():
  {==}

def Laws.v_alias_83():
  {==}

def Laws.v_alias_lower():
  {==}

def Laws.v_alias_nt():
  {==}

def Laws.v_alias_lossy():
  {==}

def Laws.v_format12():
  {==}
"""

VECTORS = ["type_fat12_max", "type_fat16_min", "type_fat16_max", "type_fat32_min", "checksum_bootx64",
           "readme_cluster", "readme_size", "readme_date", "readme_time", "readme_short_entry", "lfn_build_two",
           "lfn_entry_round_trip", "lfn_not_long", "short_of_efi", "short_of_dir", "short_of_long",
           "short_of_two_dots", "short_of_space", "fat12_even_vector", "fat12_odd_vector", "fat12_set_vector",
           "short_text_lower"]

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out = HEADER + dirent_tail() + ROUND_TRIP + LFN + fat12() + ENTRIES + CHAIN + WRITE + "\n"
    out += "# Vectors, computed\n\n" + "".join("def Laws.%s():\n  {==}\n\n" % v for v in VECTORS)
    with open(os.path.join(here, "..", "PROOF.bend"), "w", newline="\n") as f:
        f.write(out.rstrip() + "\n")

main()
