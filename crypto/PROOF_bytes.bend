# Proofs of LAWS_bytes.bend, from bytes' laws and cipher-core's
# block64_octets_round_trip (and proof_bits.bend's 128-bit format lemma).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-core/cipher-core.bend as L
import ../cipher-core/LAWS.bend as CoreL
import ../cipher-core/PROOF.bend as CoreP
import ../gf/gf128.bend as G
import ./crypto.bend as Cr
import ./stream.bend as St
import ./modes.bend as Md
import ./pcbc.bend as Pc
import ./lrw.bend as Lw
import ./inst_cm.bend as CM
import ./inst_lc.bend as LC
import ./proof_bits.bend as Bits
import ./LAWS_bytes.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# How the proofs go. CrModes.octets_of writes the blocks' bytes one block
# after another (pb.tlo: the list of them is pb.J, each block's bytes
# appended); CrModes.blocks_of cuts a byte list into pieces of bsize bytes
# (cr.chunks, which keeps the piece being filled reversed), reads each
# piece through the format and checks that the length is a multiple of
# bsize. A piece of exactly bsize bytes followed by anything is cut off
# whole (pb.piece, by induction on the piece, its i bytes so far counted
# against bsize), so the bytes of blocks of bsize bytes each are cut into
# exactly the blocks' bytes (pb.chJ), which read back as the blocks
# (pb.gp, pb.frs); their length is a multiple of bsize (pb.modJ, as Base's
# Nat.divmod.go takes a whole divisor off). The modes on bytes then reduce
# to the modes on blocks.

# Naturals

def pb.ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def pb.nd(+p: Nat, h: {1n+p == 0n : Nat}) -> Empty:
  %h : pb.ndisc(_)
  Unit{}

def pb.bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def pb.bd(h: {False{} == True{} : Bool}) -> Empty:
  %h : pb.bdisc(_)
  Unit{}

def pb.add1(+i: Nat) -> {Nat.add(i, 1n) == 1n+i : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      %pb.add1(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

def pb.eq_refl(+x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      pb.eq_refl(p)

# i + 1 bytes of n: the piece is full
def pb.full(+i: Nat, +n: Nat) -> {Nat.add(i, 1n) == n : Nat} -> {Nat.is_eq(1n+i, n) == True{} : Bool}:
  h => %h : {Nat.is_eq(1n+i, _) == True{} : Bool}
    %Equal.sym(Nat, Nat.add(i, 1n), 1n+i, pb.add1(i)) : {Nat.is_eq(1n+i, _) == True{} : Bool}
    pb.eq_refl(1n+i)

def pb.nf(+i: Nat, +k: Nat) -> {Nat.is_eq(1n+i, Nat.add(i, 2n+k)) == False{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      pb.nf(p, k)

# i + 1 bytes of i + 2 + k: not yet
def pb.notfull(+i: Nat, +k: Nat, +n: Nat) -> {Nat.add(i, 2n+k) == n : Nat} -> {Nat.is_eq(1n+i, n) == False{} : Bool}:
  h => %h : {Nat.is_eq(1n+i, _) == False{} : Bool}
    pb.nf(i, k)

# Base's division: (1 + q) + x and x leave the same remainder mod 1 + q

def pb.snd_go(+n: Nat, +m: Nat, +d1: Nat, +d2: Nat, +r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d1, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d2, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          pb.snd_go(np, r, 1n+d1, 1n+d2, 0n)
        case 1n+mp:
          pb.snd_go(np, mp, d1, d2, 1n+r)

def pb.go_skip(+m: Nat, +x: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(1n+Nat.add(m, x), m, d, r) == Nat.divmod.go(x, Nat.add(m, r), 1n+d, 0n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      Equal.trans(Nat & Nat, Nat.divmod.go(1n+Nat.add(mp, x), mp, d, 1n+r), Nat.divmod.go(x, Nat.add(mp, 1n+r), 1n+d, 0n), Nat.divmod.go(x, 1n+Nat.add(mp, r), 1n+d, 0n), pb.go_skip(mp, x, d, 1n+r), Equal.cong(Nat, Nat & Nat, z => Nat.divmod.go(x, z, 1n+d, 0n), Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), UL.nat_add_succ(mp, r)))

def pb.mod_add(+q: Nat, +x: Nat) -> {Nat.mod(Nat.add(1n+q, x), 1n+q) == Nat.mod(x, 1n+q) : Nat}:
  Equal.trans(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(1n+Nat.add(q, x), q, 0n, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(x, Nat.add(q, 0n), 1n, 0n)), Nat.mod(x, 1n+q), Equal.cong(Nat & Nat, Nat, p => Pair.snd(Nat, Nat, p), Nat.divmod.go(1n+Nat.add(q, x), q, 0n, 0n), Nat.divmod.go(x, Nat.add(q, 0n), 1n, 0n), pb.go_skip(q, x, 0n, 0n)), Equal.trans(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(x, Nat.add(q, 0n), 1n, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(x, q, 1n, 0n)), Nat.mod(x, 1n+q), Equal.cong(Nat, Nat, z => Pair.snd(Nat, Nat, Nat.divmod.go(x, z, 1n, 0n)), Nat.add(q, 0n), q, UL.nat_add_zero(q)), pb.snd_go(x, q, 1n, 0n, 0n)))

# Lists of bytes

def pb.len_append(a: List<&2, U32>, +b: List<&2, U32>) -> {B.len(B.append(a, b)) == Nat.add(B.len(a), B.len(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %pb.len_append(t, b) : {1n+B.len(B.append(t, b)) == 1n+_ : Nat}
      {==}

def pb.app_nil(p: List<&2, U32>) -> {B.append(p, Nil{}) == p : List<&2, U32>}:
  match p:
    case Nil{}:
      {==}
    case Con{h, t}:
      %pb.app_nil(t) : {Con{h, B.append(t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def pb.rro(p: List<&2, U32>, c: List<&2, U32>, +z: List<&2, U32>) -> {St.cr.rev_onto(St.cr.rev_onto(p, c), z) == St.cr.rev_onto(c, B.append(p, z)) : List<&2, U32>}:
  match p:
    case Nil{}:
      {==}
    case Con{x, t}:
      pb.rro(t, Con{x, c}, z)

def pb.rr(+p: List<&2, U32>) -> {St.cr.rev_onto(St.cr.rev_onto(p, Nil{}), Nil{}) == p : List<&2, U32>}:
  Equal.trans(List<&2, U32>, St.cr.rev_onto(St.cr.rev_onto(p, Nil{}), Nil{}), B.append(p, Nil{}), p, pb.rro(p, Nil{}, Nil{}), pb.app_nil(p))

# Cutting into pieces

# cr.chunks with its step's values as arguments
def pb.ch(xs: List<&2, U32>, +n: Nat, +full: Bool, +c: List<&2, U32>, +i: Nat, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  Md.cr.chunks(xs, n, Md.cr.pick_n(full, 1n+i), Md.cr.pick_cur(full, c), Md.cr.pick_acc(full, c, acc))

# a piece Con{x, t} of the i bytes so far and 1 + len(t) more fills n, and
# is cut off whole
def pb.piece(t: List<&2, U32>, +x: U32, +r: List<&2, U32>, +n: Nat, +i: Nat, +cur: List<&2, U32>, +acc: List<&2, List<&2, U32>>) -> {Nat.add(i, 1n+B.len(t)) == n : Nat} -> {Md.cr.chunks(Con{x, B.append(t, r)}, n, i, cur, acc) == Md.cr.chunks(r, n, 0n, Nil{}, Con{St.cr.rev_onto(St.cr.rev_onto(t, Con{x, cur}), Nil{}), acc}) : List<&2, List<&2, U32>>}:
  match t:
    case Nil{}:
      h => %Equal.sym(Bool, Nat.is_eq(1n+i, n), True{}, pb.full(i, n)(h)) : {pb.ch(r, n, _, Con{x, cur}, i, acc) == Md.cr.chunks(r, n, 0n, Nil{}, Con{St.cr.rev_onto(Con{x, cur}, Nil{}), acc}) : List<&2, List<&2, U32>>}
        {==}
    case Con{+y, +t2}:
      +h => %Equal.sym(Bool, Nat.is_eq(1n+i, n), False{}, pb.notfull(i, B.len(t2), n)(h)) : {pb.ch(Con{y, B.append(t2, r)}, n, _, Con{x, cur}, i, acc) == Md.cr.chunks(r, n, 0n, Nil{}, Con{St.cr.rev_onto(St.cr.rev_onto(t2, Con{y, Con{x, cur}}), Nil{}), acc}) : List<&2, List<&2, U32>>}
        pb.piece(t2, y, r, n, 1n+i, Con{x, cur}, acc)(Equal.trans(Nat, 1n+Nat.add(i, 1n+B.len(t2)), Nat.add(i, 2n+B.len(t2)), n, Equal.sym(Nat, Nat.add(i, 2n+B.len(t2)), 1n+Nat.add(i, 1n+B.len(t2)), UL.nat_add_succ(i, 1n+B.len(t2))), h))

# a piece p of 1 + q bytes, from the start of a piece
def pb.piece0(p: List<&2, U32>, +r: List<&2, U32>, +q: Nat, +acc: List<&2, List<&2, U32>>) -> {B.len(p) == 1n+q : Nat} -> {Md.cr.chunks(B.append(p, r), 1n+q, 0n, Nil{}, acc) == Md.cr.chunks(r, 1n+q, 0n, Nil{}, Con{p, acc}) : List<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      h => Empty.absurd({Md.cr.chunks(r, 1n+q, 0n, Nil{}, acc) == Md.cr.chunks(r, 1n+q, 0n, Nil{}, Con{Nil{}, acc}) : List<&2, List<&2, U32>>}, pb.nd(q, Equal.sym(Nat, 0n, 1n+q, h)))
    case Con{+x, +t}:
      h => Equal.trans(List<&2, List<&2, U32>>, Md.cr.chunks(Con{x, B.append(t, r)}, 1n+q, 0n, Nil{}, acc), Md.cr.chunks(r, 1n+q, 0n, Nil{}, Con{St.cr.rev_onto(St.cr.rev_onto(t, Con{x, Nil{}}), Nil{}), acc}), Md.cr.chunks(r, 1n+q, 0n, Nil{}, Con{Con{x, t}, acc}), pb.piece(t, x, r, 1n+q, 0n, Nil{}, acc)(h), Equal.cong(List<&2, U32>, List<&2, List<&2, U32>>, z => Md.cr.chunks(r, 1n+q, 0n, Nil{}, Con{z, acc}), St.cr.rev_onto(St.cr.rev_onto(Con{x, t}, Nil{}), Nil{}), Con{x, t}, pb.rr(Con{x, t})))

# Lists of blocks: their bytes, their pieces, their pieces read back

def pb.J(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      B.append(B.Octets.to_list(blk_to(b)), pb.J(~Blk, ~blk_to, t))

def pb.pr(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      pb.pr(~Blk, ~blk_to, t, Con{B.Octets.to_list(blk_to(b)), acc})

def pb.fr(~Blk: Data, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>, a: Maybe<&2, List<&2, Blk>>) -> Maybe<&2, List<&2, Blk>>:
  match bs:
    case Nil{}:
      a
    case Con{b, t}:
      Md.cr.cons_m(~Blk, blk_of(B.Octets.of_list(B.Octets.to_list(blk_to(b)))), pb.fr(~Blk, ~blk_of, ~blk_to, t, a))

def pb.tos(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>, z: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match bs:
    case Nil{}:
      z
    case Con{b, t}:
      Con{blk_to(b), pb.tos(~Blk, ~blk_to, t, z)}

# heads and tails of the hypotheses' lists

def pb.nhd(l: List<&2, Nat>) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{x, t}:
      x

def pb.ntl(l: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def pb.mhd(-Blk: Data, l: List<&2, Maybe<&2, Blk>>) -> Maybe<&2, Blk>:
  match l:
    case Nil{}:
      None{}
    case Con{x, t}:
      x

def pb.mtl(-Blk: Data, l: List<&2, Maybe<&2, Blk>>) -> List<&2, Maybe<&2, Blk>>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

# a block's bytes have 1 + q bytes, and so do the rest's
def pb.lhd(~Blk: Data, ~blk_to: Blk -> B.Octets, +b: Blk, +t: List<&2, Blk>, +q: Nat, h: {Laws.crbl.lens(~Blk, ~blk_to, Con{b, t}) == Laws.crbl.reps(~Blk, 1n+q, Con{b, t}) : List<&2, Nat>}) -> {B.len(B.Octets.to_list(blk_to(b))) == 1n+q : Nat}:
  Equal.trans(Nat, B.len(B.Octets.to_list(blk_to(b))), B.Octets.len(blk_to(b)), 1n+q, Equal.sym(Nat, B.Octets.len(blk_to(b)), B.len(B.Octets.to_list(blk_to(b))), BL.octets_len_list(blk_to(b))), Equal.cong(List<&2, Nat>, Nat, l => pb.nhd(l), Laws.crbl.lens(~Blk, ~blk_to, Con{b, t}), Laws.crbl.reps(~Blk, 1n+q, Con{b, t}), h))

def pb.ltl(~Blk: Data, ~blk_to: Blk -> B.Octets, +b: Blk, +t: List<&2, Blk>, +q: Nat, h: {Laws.crbl.lens(~Blk, ~blk_to, Con{b, t}) == Laws.crbl.reps(~Blk, 1n+q, Con{b, t}) : List<&2, Nat>}) -> {Laws.crbl.lens(~Blk, ~blk_to, t) == Laws.crbl.reps(~Blk, 1n+q, t) : List<&2, Nat>}:
  Equal.cong(List<&2, Nat>, List<&2, Nat>, l => pb.ntl(l), Laws.crbl.lens(~Blk, ~blk_to, Con{b, t}), Laws.crbl.reps(~Blk, 1n+q, Con{b, t}), h)

# the bytes of blocks of 1 + q bytes each are cut into the blocks' bytes
def pb.chJ(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>, +q: Nat, +acc: List<&2, List<&2, U32>>) -> {Laws.crbl.lens(~Blk, ~blk_to, bs) == Laws.crbl.reps(~Blk, 1n+q, bs) : List<&2, Nat>} -> {Md.cr.chunks(pb.J(~Blk, ~blk_to, bs), 1n+q, 0n, Nil{}, acc) == pb.pr(~Blk, ~blk_to, bs, acc) : List<&2, List<&2, U32>>}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+b, +t}:
      +h => Equal.trans(List<&2, List<&2, U32>>, Md.cr.chunks(B.append(B.Octets.to_list(blk_to(b)), pb.J(~Blk, ~blk_to, t)), 1n+q, 0n, Nil{}, acc), Md.cr.chunks(pb.J(~Blk, ~blk_to, t), 1n+q, 0n, Nil{}, Con{B.Octets.to_list(blk_to(b)), acc}), pb.pr(~Blk, ~blk_to, t, Con{B.Octets.to_list(blk_to(b)), acc}), pb.piece0(B.Octets.to_list(blk_to(b)), pb.J(~Blk, ~blk_to, t), q, acc)(pb.lhd(~Blk, ~blk_to, b, t, q, h)), pb.chJ(~Blk, ~blk_to, t, q, Con{B.Octets.to_list(blk_to(b)), acc})(pb.ltl(~Blk, ~blk_to, b, t, q, h)))

# reading the pieces (last first) is reading the blocks' bytes in order
def pb.gp(~Blk: Data, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>, acc: List<&2, List<&2, U32>>, +a: Maybe<&2, List<&2, Blk>>) -> {Md.cr.blocks_of.go(~Blk, ~blk_of, pb.pr(~Blk, ~blk_to, bs, acc), a) == Md.cr.blocks_of.go(~Blk, ~blk_of, acc, pb.fr(~Blk, ~blk_of, ~blk_to, bs, a)) : Maybe<&2, List<&2, Blk>>}:
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      pb.gp(~Blk, ~blk_of, ~blk_to, t, Con{B.Octets.to_list(blk_to(b)), acc}, a)

# which gives the blocks, when each block's bytes read back as it
def pb.frs(~Blk: Data, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>) -> {Laws.crbl.reads(~Blk, ~blk_of, ~blk_to, bs) == Laws.crbl.somes(~Blk, bs) : List<&2, Maybe<&2, Blk>>} -> {pb.fr(~Blk, ~blk_of, ~blk_to, bs, Some{Nil{}}) == Some{bs} : Maybe<&2, List<&2, Blk>>}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+b, +t}:
      +h => %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(blk_to(b))), blk_to(b), BL.octets_of_to(blk_to(b))) : {Md.cr.cons_m(~Blk, blk_of(_), pb.fr(~Blk, ~blk_of, ~blk_to, t, Some{Nil{}})) == Some{Con{b, t}} : Maybe<&2, List<&2, Blk>>}
        %Equal.sym(Maybe<&2, Blk>, blk_of(blk_to(b)), Some{b}, Equal.cong(List<&2, Maybe<&2, Blk>>, Maybe<&2, Blk>, l => pb.mhd(Blk, l), Laws.crbl.reads(~Blk, ~blk_of, ~blk_to, Con{b, t}), Laws.crbl.somes(~Blk, Con{b, t}), h)) : {Md.cr.cons_m(~Blk, _, pb.fr(~Blk, ~blk_of, ~blk_to, t, Some{Nil{}})) == Some{Con{b, t}} : Maybe<&2, List<&2, Blk>>}
        %Equal.sym(Maybe<&2, List<&2, Blk>>, pb.fr(~Blk, ~blk_of, ~blk_to, t, Some{Nil{}}), Some{t}, pb.frs(~Blk, ~blk_of, ~blk_to, t)(Equal.cong(List<&2, Maybe<&2, Blk>>, List<&2, Maybe<&2, Blk>>, l => pb.mtl(Blk, l), Laws.crbl.reads(~Blk, ~blk_of, ~blk_to, Con{b, t}), Laws.crbl.somes(~Blk, Con{b, t}), h))) : {Md.cr.cons_m(~Blk, Some{b}, _) == Some{Con{b, t}} : Maybe<&2, List<&2, Blk>>}
        {==}

# the blocks' bytes
def pb.oo(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>, acc: List<&2, B.Octets>, +z: List<&2, B.Octets>) -> {Md.cr.blks.rev_onto(~B.Octets, Md.cr.octets_of.go(~Blk, ~blk_to, bs, acc), z) == Md.cr.blks.rev_onto(~B.Octets, acc, pb.tos(~Blk, ~blk_to, bs, z)) : List<&2, B.Octets>}:
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      pb.oo(~Blk, ~blk_to, t, Con{blk_to(b), acc}, z)

def pb.cj(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>) -> {B.Octets.to_list(B.Octets.concat(pb.tos(~Blk, ~blk_to, bs, Nil{}))) == pb.J(~Blk, ~blk_to, bs) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(B.Octets, B.Octets.concat(Con{blk_to(b), pb.tos(~Blk, ~blk_to, t, Nil{})}), B.Octets.append(blk_to(b), B.Octets.concat(pb.tos(~Blk, ~blk_to, t, Nil{}))), BL.octets_concat_cons(blk_to(b), pb.tos(~Blk, ~blk_to, t, Nil{}))) : {B.Octets.to_list(_) == pb.J(~Blk, ~blk_to, Con{b, t}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(blk_to(b), B.Octets.concat(pb.tos(~Blk, ~blk_to, t, Nil{})))), B.append(B.Octets.to_list(blk_to(b)), B.Octets.to_list(B.Octets.concat(pb.tos(~Blk, ~blk_to, t, Nil{})))), BL.octets_append_list(blk_to(b), B.Octets.concat(pb.tos(~Blk, ~blk_to, t, Nil{})))) : {_ == pb.J(~Blk, ~blk_to, Con{b, t}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.concat(pb.tos(~Blk, ~blk_to, t, Nil{}))), pb.J(~Blk, ~blk_to, t), pb.cj(~Blk, ~blk_to, t)) : {B.append(B.Octets.to_list(blk_to(b)), _) == pb.J(~Blk, ~blk_to, Con{b, t}) : List<&2, U32>}
      {==}

def pb.tlo(~Blk: Data, ~blk_to: Blk -> B.Octets, +bs: List<&2, Blk>) -> {B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs)) == pb.J(~Blk, ~blk_to, bs) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs)), B.Octets.to_list(B.Octets.concat(pb.tos(~Blk, ~blk_to, bs, Nil{}))), pb.J(~Blk, ~blk_to, bs), Equal.cong(List<&2, B.Octets>, List<&2, U32>, x => B.Octets.to_list(B.Octets.concat(x)), Md.cr.blks.rev_onto(~B.Octets, Md.cr.octets_of.go(~Blk, ~blk_to, bs, Nil{}), Nil{}), pb.tos(~Blk, ~blk_to, bs, Nil{}), pb.oo(~Blk, ~blk_to, bs, Nil{}, Nil{})), pb.cj(~Blk, ~blk_to, bs))

# the bytes of blocks of 1 + q bytes each are a whole number of them
def pb.modJ(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>, +q: Nat) -> {Laws.crbl.lens(~Blk, ~blk_to, bs) == Laws.crbl.reps(~Blk, 1n+q, bs) : List<&2, Nat>} -> {Nat.mod(B.len(pb.J(~Blk, ~blk_to, bs)), 1n+q) == 0n : Nat}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+b, +t}:
      +h => %Equal.sym(Nat, B.len(B.append(B.Octets.to_list(blk_to(b)), pb.J(~Blk, ~blk_to, t))), Nat.add(B.len(B.Octets.to_list(blk_to(b))), B.len(pb.J(~Blk, ~blk_to, t))), pb.len_append(B.Octets.to_list(blk_to(b)), pb.J(~Blk, ~blk_to, t))) : {Nat.mod(_, 1n+q) == 0n : Nat}
        %Equal.sym(Nat, B.len(B.Octets.to_list(blk_to(b))), 1n+q, pb.lhd(~Blk, ~blk_to, b, t, q, h)) : {Nat.mod(Nat.add(_, B.len(pb.J(~Blk, ~blk_to, t))), 1n+q) == 0n : Nat}
        %Equal.sym(Nat, Nat.mod(Nat.add(1n+q, B.len(pb.J(~Blk, ~blk_to, t))), 1n+q), Nat.mod(B.len(pb.J(~Blk, ~blk_to, t)), 1n+q), pb.mod_add(q, B.len(pb.J(~Blk, ~blk_to, t)))) : {_ == 0n : Nat}
        pb.modJ(~Blk, ~blk_to, t, q)(pb.ltl(~Blk, ~blk_to, b, t, q, h))

# blocks_of of the blocks' bytes, for a block size n of at least 1 (as
# CrModes.blocks_of computes it, with n for its template ~bsize)
def pb.bo(~Blk: Data, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +n: Nat, +bs: List<&2, Blk>, hb: {Nat.is_lt(0n, n) == True{} : Bool}, +hl: {Laws.crbl.lens(~Blk, ~blk_to, bs) == Laws.crbl.reps(~Blk, n, bs) : List<&2, Nat>}, hf: {Laws.crbl.reads(~Blk, ~blk_of, ~blk_to, bs) == Laws.crbl.somes(~Blk, bs) : List<&2, Maybe<&2, Blk>>}) -> {Md.cr.blocks_of.ok(~Blk, Md.cr.divides(Nat.is_lt(0n, n), B.len.fast(B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs))), n), Md.cr.blocks_of.go(~Blk, ~blk_of, Md.cr.chunks(B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs)), n, 0n, Nil{}, Nil{}), Some{Nil{}}), B.len.fast(B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs)))) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}:
  match n:
    case 0n:
      Empty.absurd({Md.cr.blocks_of.ok(~Blk, Md.cr.divides(Nat.is_lt(0n, 0n), B.len.fast(B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs))), 0n), Md.cr.blocks_of.go(~Blk, ~blk_of, Md.cr.chunks(B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs)), 0n, 0n, Nil{}, Nil{}), Some{Nil{}}), B.len.fast(B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs)))) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, pb.bd(hb))
    case 1n+q:
      # the bytes are pb.J
      %Equal.sym(List<&2, U32>, B.Octets.to_list(Md.CrModes.octets_of(~Blk, ~blk_to, bs)), pb.J(~Blk, ~blk_to, bs), pb.tlo(~Blk, ~blk_to, bs)) : {Md.cr.blocks_of.ok(~Blk, Md.cr.divides(True{}, B.len.fast(_), 1n+q), Md.cr.blocks_of.go(~Blk, ~blk_of, Md.cr.chunks(_, 1n+q, 0n, Nil{}, Nil{}), Some{Nil{}}), B.len.fast(_)) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}
      # a whole number of blocks
      %BL.len_fast(pb.J(~Blk, ~blk_to, bs)) : {Md.cr.blocks_of.ok(~Blk, Md.cr.divides(True{}, _, 1n+q), Md.cr.blocks_of.go(~Blk, ~blk_of, Md.cr.chunks(pb.J(~Blk, ~blk_to, bs), 1n+q, 0n, Nil{}, Nil{}), Some{Nil{}}), B.len.fast(pb.J(~Blk, ~blk_to, bs))) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}
      %Equal.sym(Nat, Nat.mod(B.len(pb.J(~Blk, ~blk_to, bs)), 1n+q), 0n, pb.modJ(~Blk, ~blk_to, bs, q)(hl)) : {Md.cr.blocks_of.ok(~Blk, Nat.is_eq(_, 0n), Md.cr.blocks_of.go(~Blk, ~blk_of, Md.cr.chunks(pb.J(~Blk, ~blk_to, bs), 1n+q, 0n, Nil{}, Nil{}), Some{Nil{}}), B.len.fast(pb.J(~Blk, ~blk_to, bs))) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}
      # cut into the blocks' bytes
      %Equal.sym(List<&2, List<&2, U32>>, Md.cr.chunks(pb.J(~Blk, ~blk_to, bs), 1n+q, 0n, Nil{}, Nil{}), pb.pr(~Blk, ~blk_to, bs, Nil{}), pb.chJ(~Blk, ~blk_to, bs, q, Nil{})(hl)) : {Md.cr.blocks_of.ok(~Blk, True{}, Md.cr.blocks_of.go(~Blk, ~blk_of, _, Some{Nil{}}), B.len.fast(pb.J(~Blk, ~blk_to, bs))) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}
      # read back as the blocks
      %Equal.sym(Maybe<&2, List<&2, Blk>>, Md.cr.blocks_of.go(~Blk, ~blk_of, pb.pr(~Blk, ~blk_to, bs, Nil{}), Some{Nil{}}), Md.cr.blocks_of.go(~Blk, ~blk_of, Nil{}, pb.fr(~Blk, ~blk_of, ~blk_to, bs, Some{Nil{}})), pb.gp(~Blk, ~blk_of, ~blk_to, bs, Nil{}, Some{Nil{}})) : {Md.cr.blocks_of.ok(~Blk, True{}, _, B.len.fast(pb.J(~Blk, ~blk_to, bs))) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}
      %Equal.sym(Maybe<&2, List<&2, Blk>>, pb.fr(~Blk, ~blk_of, ~blk_to, bs, Some{Nil{}}), Some{bs}, pb.frs(~Blk, ~blk_of, ~blk_to, bs)(hf)) : {Md.cr.blocks_of.ok(~Blk, True{}, _, B.len.fast(pb.J(~Blk, ~blk_to, bs))) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}
      {==}

def Laws.modes_blocks_of_octets_of(Blk, bsize, blk_of, blk_to, bs, hb, hl, hf):
  pb.bo(~Blk, ~blk_of, ~blk_to, bsize, bs, hb, hl, hf)

# The two formats: each block's bytes are bsize bytes and read back as it

def pb.cm_len(b: M.CmBlock) -> {B.Octets.len(CM.CrBlk128.to_octets(b)) == 16n : Nat}:
  match b:
    case M.CmBlock{U32{x0}, U32{x1}, U32{x2}, U32{x3}}:
      {==}

def pb.cm_fmt(+b: M.CmBlock) -> {CM.CrBlk128.of_octets(CM.CrBlk128.to_octets(b)) == Some{b} : Maybe<&2, M.CmBlock>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(CM.cr.f128.bytes(b))), B.mask(CM.cr.f128.bytes(b)), BL.octets_to_of(CM.cr.f128.bytes(b))) : {CM.cr.f128.block(_) == Some{b} : Maybe<&2, M.CmBlock>}
  Bits.f128_bytes(b)

def pb.lc_len(b: L.LcBlock64) -> {B.Octets.len(L.LcBlock64.to_octets(b)) == 8n : Nat}:
  match b:
    case L.LcBlock64{hi, lo}:
      {==}

def pb.cm_lens(bs: List<&2, M.CmBlock>) -> {Laws.crbl.lens(~M.CmBlock, ~CM.CrBlk128.to_octets, bs) == Laws.crbl.reps(~M.CmBlock, 16n, bs) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, t}:
      %pb.cm_len(b) : {Con{B.Octets.len(CM.CrBlk128.to_octets(b)), Laws.crbl.lens(~M.CmBlock, ~CM.CrBlk128.to_octets, t)} == Con{_, Laws.crbl.reps(~M.CmBlock, 16n, t)} : List<&2, Nat>}
      %pb.cm_lens(t) : {Con{B.Octets.len(CM.CrBlk128.to_octets(b)), Laws.crbl.lens(~M.CmBlock, ~CM.CrBlk128.to_octets, t)} == Con{B.Octets.len(CM.CrBlk128.to_octets(b)), _} : List<&2, Nat>}
      {==}

def pb.cm_reads(bs: List<&2, M.CmBlock>) -> {Laws.crbl.reads(~M.CmBlock, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, bs) == Laws.crbl.somes(~M.CmBlock, bs) : List<&2, Maybe<&2, M.CmBlock>>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, t}:
      %pb.cm_fmt(b) : {Con{CM.CrBlk128.of_octets(CM.CrBlk128.to_octets(b)), Laws.crbl.reads(~M.CmBlock, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, t)} == Con{_, Laws.crbl.somes(~M.CmBlock, t)} : List<&2, Maybe<&2, M.CmBlock>>}
      %pb.cm_reads(t) : {Con{CM.CrBlk128.of_octets(CM.CrBlk128.to_octets(b)), Laws.crbl.reads(~M.CmBlock, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, t)} == Con{CM.CrBlk128.of_octets(CM.CrBlk128.to_octets(b)), _} : List<&2, Maybe<&2, M.CmBlock>>}
      {==}

def pb.lc_lens(bs: List<&2, L.LcBlock64>) -> {Laws.crbl.lens(~L.LcBlock64, ~L.LcBlock64.to_octets, bs) == Laws.crbl.reps(~L.LcBlock64, 8n, bs) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, t}:
      %pb.lc_len(b) : {Con{B.Octets.len(L.LcBlock64.to_octets(b)), Laws.crbl.lens(~L.LcBlock64, ~L.LcBlock64.to_octets, t)} == Con{_, Laws.crbl.reps(~L.LcBlock64, 8n, t)} : List<&2, Nat>}
      %pb.lc_lens(t) : {Con{B.Octets.len(L.LcBlock64.to_octets(b)), Laws.crbl.lens(~L.LcBlock64, ~L.LcBlock64.to_octets, t)} == Con{B.Octets.len(L.LcBlock64.to_octets(b)), _} : List<&2, Nat>}
      {==}

def pb.lc_reads(bs: List<&2, L.LcBlock64>) -> {Laws.crbl.reads(~L.LcBlock64, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, bs) == Laws.crbl.somes(~L.LcBlock64, bs) : List<&2, Maybe<&2, L.LcBlock64>>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, t}:
      %CoreL.block64_octets_round_trip(b) : {Con{L.LcBlock64.of_octets(L.LcBlock64.to_octets(b)), Laws.crbl.reads(~L.LcBlock64, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, t)} == Con{_, Laws.crbl.somes(~L.LcBlock64, t)} : List<&2, Maybe<&2, L.LcBlock64>>}
      %pb.lc_reads(t) : {Con{L.LcBlock64.of_octets(L.LcBlock64.to_octets(b)), Laws.crbl.reads(~L.LcBlock64, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, t)} == Con{L.LcBlock64.of_octets(L.LcBlock64.to_octets(b)), _} : List<&2, Maybe<&2, L.LcBlock64>>}
      {==}

def Laws.cmblock_blocks_of_octets_of(bs):
  Laws.modes_blocks_of_octets_of(~M.CmBlock, ~16n, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, bs, {==}, pb.cm_lens(bs), pb.cm_reads(bs))

def Laws.lcblock64_blocks_of_octets_of(bs):
  Laws.modes_blocks_of_octets_of(~L.LcBlock64, ~8n, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, bs, {==}, pb.lc_lens(bs), pb.lc_reads(bs))

# The modes on bytes, for any format, from its law at the blocks used (f1,
# f2) and the IV block's (fv)

def pb.ecb(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +bs: List<&2, Blk>, f1: {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, f2: {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrEcb.encrypt_blocks(~K, ~Blk, ~enc, k, bs))) == Done{Md.CrEcb.encrypt_blocks(~K, ~Blk, ~enc, k, bs)} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, h: {Md.CrEcb.decrypt_blocks(~K, ~Blk, ~dec, k, Md.CrEcb.encrypt_blocks(~K, ~Blk, ~enc, k, bs)) == bs : List<&2, Blk>}) -> {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Md.CrEcb.encrypt(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, k, Md.CrModes.octets_of(~Blk, ~blk_to, bs)), c => Md.CrEcb.decrypt(~K, ~Blk, ~bsize, ~dec, ~blk_of, ~blk_to, k, c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}:
  %Equal.sym(Result<&2, &2, Cr.CrError, List<&2, Blk>>, Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)), Done{bs}, f1) : {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Result.map(&2, &2, Cr.CrError, List<&2, Blk>, B.Octets, xs => Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrEcb.encrypt_blocks(~K, ~Blk, ~enc, k, xs)), _), c => Md.CrEcb.decrypt(~K, ~Blk, ~bsize, ~dec, ~blk_of, ~blk_to, k, c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, List<&2, Blk>>, Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrEcb.encrypt_blocks(~K, ~Blk, ~enc, k, bs))), Done{Md.CrEcb.encrypt_blocks(~K, ~Blk, ~enc, k, bs)}, f2) : {Result.map(&2, &2, Cr.CrError, List<&2, Blk>, B.Octets, xs => Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrEcb.decrypt_blocks(~K, ~Blk, ~dec, k, xs)), _) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(List<&2, Blk>, Md.CrEcb.decrypt_blocks(~K, ~Blk, ~dec, k, Md.CrEcb.encrypt_blocks(~K, ~Blk, ~enc, k, bs)), bs, h) : {Done{Md.CrModes.octets_of(~Blk, ~blk_to, _)} == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

# CrCbc.encrypt and decrypt, and the same for PCBC, with the IV's and the
# message's blocks as arguments

def pb.ce(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +k: K, rv: Result<&2, &2, Cr.CrError, Blk>, rb: Result<&2, &2, Cr.CrError, List<&2, Blk>>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    v : Blk <- rv
    bs : List<&2, Blk> <- rb
    return Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs))

def pb.cd(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +k: K, rv: Result<&2, &2, Cr.CrError, Blk>, rb: Result<&2, &2, Cr.CrError, List<&2, Blk>>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    v : Blk <- rv
    bs : List<&2, Blk> <- rb
    return Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrCbc.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, k, v, bs))

def pb.pe(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +k: K, rv: Result<&2, &2, Cr.CrError, Blk>, rb: Result<&2, &2, Cr.CrError, List<&2, Blk>>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    v : Blk <- rv
    bs : List<&2, Blk> <- rb
    return Md.CrModes.octets_of(~Blk, ~blk_to, Pc.CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs))

def pb.pd(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +k: K, rv: Result<&2, &2, Cr.CrError, Blk>, rb: Result<&2, &2, Cr.CrError, List<&2, Blk>>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    v : Blk <- rv
    bs : List<&2, Blk> <- rb
    return Md.CrModes.octets_of(~Blk, ~blk_to, Pc.CrPcbc.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, k, v, bs))

def pb.cbc(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +v: Blk, +bs: List<&2, Blk>, +fv: {blk_of(blk_to(v)) == Some{v} : Maybe<&2, Blk>}, f1: {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, f2: {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs))) == Done{Md.CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, h: {Md.CrCbc.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, k, v, Md.CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)) == bs : List<&2, Blk>}) -> {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Md.CrCbc.encrypt(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, k, blk_to(v), Md.CrModes.octets_of(~Blk, ~blk_to, bs)), c => Md.CrCbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, blk_to(v), c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}:
  %Equal.sym(Maybe<&2, Blk>, blk_of(blk_to(v)), Some{v}, fv) : {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, pb.ce(~K, ~Blk, ~enc, ~bxor, ~blk_to, k, Md.cr.iv.pick(~Blk, _, B.Octets.len(blk_to(v))), Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs))), c => Md.CrCbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, blk_to(v), c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, List<&2, Blk>>, Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)), Done{bs}, f1) : {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, pb.ce(~K, ~Blk, ~enc, ~bxor, ~blk_to, k, Done{v}, _), c => Md.CrCbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, blk_to(v), c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Maybe<&2, Blk>, blk_of(blk_to(v)), Some{v}, fv) : {pb.cd(~K, ~Blk, ~dec, ~bxor, ~blk_to, k, Md.cr.iv.pick(~Blk, _, B.Octets.len(blk_to(v))), Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)))) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, List<&2, Blk>>, Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Md.CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs))), Done{Md.CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)}, f2) : {pb.cd(~K, ~Blk, ~dec, ~bxor, ~blk_to, k, Done{v}, _) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(List<&2, Blk>, Md.CrCbc.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, k, v, Md.CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)), bs, h) : {Done{Md.CrModes.octets_of(~Blk, ~blk_to, _)} == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

def pb.pcbc(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +v: Blk, +bs: List<&2, Blk>, +fv: {blk_of(blk_to(v)) == Some{v} : Maybe<&2, Blk>}, f1: {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, f2: {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Pc.CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs))) == Done{Pc.CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, h: {Pc.CrPcbc.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, k, v, Pc.CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)) == bs : List<&2, Blk>}) -> {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Pc.CrPcbc.encrypt(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, k, blk_to(v), Md.CrModes.octets_of(~Blk, ~blk_to, bs)), c => Pc.CrPcbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, blk_to(v), c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}:
  %Equal.sym(Maybe<&2, Blk>, blk_of(blk_to(v)), Some{v}, fv) : {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, pb.pe(~K, ~Blk, ~enc, ~bxor, ~blk_to, k, Md.cr.iv.pick(~Blk, _, B.Octets.len(blk_to(v))), Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs))), c => Pc.CrPcbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, blk_to(v), c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, List<&2, Blk>>, Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)), Done{bs}, f1) : {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, pb.pe(~K, ~Blk, ~enc, ~bxor, ~blk_to, k, Done{v}, _), c => Pc.CrPcbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, blk_to(v), c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Maybe<&2, Blk>, blk_of(blk_to(v)), Some{v}, fv) : {pb.pd(~K, ~Blk, ~dec, ~bxor, ~blk_to, k, Md.cr.iv.pick(~Blk, _, B.Octets.len(blk_to(v))), Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Pc.CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)))) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, List<&2, Blk>>, Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Pc.CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs))), Done{Pc.CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)}, f2) : {pb.pd(~K, ~Blk, ~dec, ~bxor, ~blk_to, k, Done{v}, _) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(List<&2, Blk>, Pc.CrPcbc.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, k, v, Pc.CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs)), bs, h) : {Done{Md.CrModes.octets_of(~Blk, ~blk_to, _)} == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

# CrLrw.encrypt and decrypt on the key pair CrLrwKey{k, k2}, with the index
# and the blocks as arguments

def pb.le(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +k2: G.Gf128, ri: Result<&2, &2, Cr.CrError, G.Gf128>, rb: Result<&2, &2, Cr.CrError, List<&2, Blk>>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    i : G.Gf128 <- ri
    bs : List<&2, Blk> <- rb
    return Md.CrModes.octets_of(~Blk, ~blk_to, Lw.CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs))

def pb.ld(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +k2: G.Gf128, ri: Result<&2, &2, Cr.CrError, G.Gf128>, rb: Result<&2, &2, Cr.CrError, List<&2, Blk>>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    i : G.Gf128 <- ri
    bs : List<&2, Blk> <- rb
    return Md.CrModes.octets_of(~Blk, ~blk_to, Lw.CrLrw.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, i, bs))

def pb.lrw(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +k2: G.Gf128, +i: G.Gf128, +iv: B.Octets, +hi: {G.Gf128.of_octets(iv) == Done{i} : Result<&2, &2, G.Gf128Error, G.Gf128>}, +bs: List<&2, Blk>, f1: {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, f2: {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Lw.CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs))) == Done{Lw.CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs)} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}, h: {Lw.CrLrw.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, i, Lw.CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs)) == bs : List<&2, Blk>}) -> {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Lw.CrLrw.encrypt(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, Lw.CrLrwKey{k, k2}, iv, Md.CrModes.octets_of(~Blk, ~blk_to, bs)), c => Lw.CrLrw.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, Lw.CrLrwKey{k, k2}, iv, c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}:
  %Equal.sym(Result<&2, &2, G.Gf128Error, G.Gf128>, G.Gf128.of_octets(iv), Done{i}, hi) : {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, pb.le(~K, ~Blk, ~enc, ~bxor, ~blk_of, ~blk_to, k, k2, Lw.cr.lrw.index.of(B.Octets.len(iv), _), Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs))), c => Lw.CrLrw.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, Lw.CrLrwKey{k, k2}, iv, c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, List<&2, Blk>>, Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)), Done{bs}, f1) : {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, pb.le(~K, ~Blk, ~enc, ~bxor, ~blk_of, ~blk_to, k, k2, Done{i}, _), c => Lw.CrLrw.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, Lw.CrLrwKey{k, k2}, iv, c)) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, G.Gf128Error, G.Gf128>, G.Gf128.of_octets(iv), Done{i}, hi) : {pb.ld(~K, ~Blk, ~dec, ~bxor, ~blk_of, ~blk_to, k, k2, Lw.cr.lrw.index.of(B.Octets.len(iv), _), Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Lw.CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs)))) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, List<&2, Blk>>, Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, Lw.CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs))), Done{Lw.CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs)}, f2) : {pb.ld(~K, ~Blk, ~dec, ~bxor, ~blk_of, ~blk_to, k, k2, Done{i}, _) == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(List<&2, Blk>, Lw.CrLrw.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, i, Lw.CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs)), bs, h) : {Done{Md.CrModes.octets_of(~Blk, ~blk_to, _)} == Done{Md.CrModes.octets_of(~Blk, ~blk_to, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

def Laws.cmblock_ecb_octets_round_trip(K, enc, dec, k, bs, h):
  pb.ecb(~K, ~M.CmBlock, ~16n, ~enc, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, bs, Laws.cmblock_blocks_of_octets_of(bs), Laws.cmblock_blocks_of_octets_of(Md.CrEcb.encrypt_blocks(~K, ~M.CmBlock, ~enc, k, bs)), h)

def Laws.lcblock64_ecb_octets_round_trip(K, enc, dec, k, bs, h):
  pb.ecb(~K, ~L.LcBlock64, ~8n, ~enc, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, bs, Laws.lcblock64_blocks_of_octets_of(bs), Laws.lcblock64_blocks_of_octets_of(Md.CrEcb.encrypt_blocks(~K, ~L.LcBlock64, ~enc, k, bs)), h)

def Laws.cmblock_cbc_octets_round_trip(K, enc, dec, k, v, bs, h):
  pb.cbc(~K, ~M.CmBlock, ~16n, ~enc, ~dec, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, v, bs, pb.cm_fmt(v), Laws.cmblock_blocks_of_octets_of(bs), Laws.cmblock_blocks_of_octets_of(Md.CrCbc.encrypt_blocks(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.xor, k, v, bs)), h)

def Laws.lcblock64_cbc_octets_round_trip(K, enc, dec, k, v, bs, h):
  pb.cbc(~K, ~L.LcBlock64, ~8n, ~enc, ~dec, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, v, bs, CoreL.block64_octets_round_trip(v), Laws.lcblock64_blocks_of_octets_of(bs), Laws.lcblock64_blocks_of_octets_of(Md.CrCbc.encrypt_blocks(~K, ~L.LcBlock64, ~enc, ~LC.CrBlk64.xor, k, v, bs)), h)

def Laws.cmblock_pcbc_octets_round_trip(K, enc, dec, k, v, bs, h):
  pb.pcbc(~K, ~M.CmBlock, ~16n, ~enc, ~dec, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, v, bs, pb.cm_fmt(v), Laws.cmblock_blocks_of_octets_of(bs), Laws.cmblock_blocks_of_octets_of(Pc.CrPcbc.encrypt_blocks(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.xor, k, v, bs)), h)

def Laws.lcblock64_pcbc_octets_round_trip(K, enc, dec, k, v, bs, h):
  pb.pcbc(~K, ~L.LcBlock64, ~8n, ~enc, ~dec, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, v, bs, CoreL.block64_octets_round_trip(v), Laws.lcblock64_blocks_of_octets_of(bs), Laws.lcblock64_blocks_of_octets_of(Pc.CrPcbc.encrypt_blocks(~K, ~L.LcBlock64, ~enc, ~LC.CrBlk64.xor, k, v, bs)), h)

def Laws.cmblock_lrw_octets_round_trip(K, enc, dec, k, k2, i, iv, hi, bs, h):
  pb.lrw(~K, ~M.CmBlock, ~16n, ~enc, ~dec, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, k2, i, iv, hi, bs, Laws.cmblock_blocks_of_octets_of(bs), Laws.cmblock_blocks_of_octets_of(Lw.CrLrw.encrypt_blocks(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)), h)
