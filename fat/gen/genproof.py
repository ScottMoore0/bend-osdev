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
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

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

VECTORS = ["type_fat12_max", "type_fat16_min", "type_fat16_max", "type_fat32_min", "checksum_bootx64",
           "readme_cluster", "readme_size", "readme_date", "readme_time", "readme_short_entry", "lfn_build_two",
           "lfn_entry_round_trip", "lfn_not_long", "short_of_efi", "short_of_dir", "short_of_long",
           "short_of_two_dots", "short_of_space", "fat12_even_vector", "fat12_odd_vector", "fat12_set_vector",
           "short_text_lower"]

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out = HEADER + dirent_tail() + ROUND_TRIP + LFN + fat12() + ENTRIES + CHAIN
    out += "# Vectors, computed\n\n" + "".join("def Laws.%s():\n  {==}\n\n" % v for v in VECTORS)
    with open(os.path.join(here, "..", "PROOF.bend"), "w", newline="\n") as f:
        f.write(out.rstrip() + "\n")

main()
