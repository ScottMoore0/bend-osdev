import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./error.bend as E
import ./options.bend as O
import ./csum.bend as K
import ./super.bend as S
import ./inode.bend as N
import ./blockmap.bend as M
import ./extent.bend as X
import ./file.bend as FL
import ./dir.bend as DR
import ./patch.bend as PA
import ./bitmap.bend as BM
import ./meta.bend as T
import ./wopts.bend as WO
import ./extentw.bend as EW
import ./dirw.bend as DW
import ./fsck.bend as FK
import ./ops.bend as P
import ./run.bend as RN
import ./mkfs.bend as MK
import ./ext2.bend as EX
import ./LAWS.bend as Laws

# Natural numbers: the arithmetic the laws about inode numbers need, proved
# from Base's definitions of Nat.add, Nat.mul and Nat.divmod

def Ext2Proof.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Ext2Proof.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def Ext2Proof.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Ext2Proof.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def Ext2Proof.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %Ext2Proof.add_zero(b) : {_ == Nat.add(b, 0n) : Nat}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Ext2Proof.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %Ext2Proof.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def Ext2Proof.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Ext2Proof.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def Ext2Proof.lt_irrefl(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Ext2Proof.lt_irrefl(p)

def Ext2Proof.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Ext2Proof.lt_succ(p)

# Base's division: Nat.divmod(a, 1 + bp) runs go(a, bp, 0, 0), which counts
# m down and r up (m + r == bp throughout) and d once per full round.

def Ext2Proof.dm_lhs(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> Nat:
  Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)))

# quotient times divisor plus remainder: what went in
def Ext2Proof.dm_sum(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> {Nat.add(m, r) == bp : Nat} -> {Ext2Proof.dm_lhs(n, m, d, r, bp) == Nat.add(n, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}:
  match n m:
    case 0n _:
      h => {==}
    case 1n+np 0n:
      +h =>
        +dd = Nat.mul(d, 1n+bp)
        +x = Nat.add(Nat.add(bp, dd), 0n)
        %Equal.sym(Nat, r, bp, h) : {Ext2Proof.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, Nat.add(dd, _)) : Nat}
        %Ext2Proof.add_comm(bp, dd) : {Ext2Proof.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, _) : Nat}
        %Ext2Proof.add_zero(Nat.add(bp, dd)) : {Ext2Proof.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, _) : Nat}
        %Ext2Proof.add_succ(np, x) : {Ext2Proof.dm_lhs(1n+np, 0n, d, r, bp) == _ : Nat}
        Ext2Proof.dm_sum(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, Ext2Proof.add_zero(r), h))
    case 1n+np 1n+mp:
      h =>
        +dd = Nat.mul(d, 1n+bp)
        %Ext2Proof.add_succ(np, Nat.add(dd, r)) : {Ext2Proof.dm_lhs(1n+np, 1n+mp, d, r, bp) == _ : Nat}
        %Ext2Proof.add_succ(dd, r) : {Ext2Proof.dm_lhs(1n+np, 1n+mp, d, r, bp) == Nat.add(np, _) : Nat}
        Ext2Proof.dm_sum(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, Ext2Proof.add_succ(mp, r), h))

def Ext2Proof.div_mod(+k: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.div(k, 1n+bp), 1n+bp), Nat.mod(k, 1n+bp)) == k : Nat}:
  Equal.trans(Nat, Ext2Proof.dm_lhs(k, bp, 0n, 0n, bp), Nat.add(k, 0n), k, Ext2Proof.dm_sum(k, bp, 0n, 0n, bp, Ext2Proof.add_zero(bp)), Ext2Proof.add_zero(k))

def Laws.inode_locate_number(p, k):
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(k, 1n+p), 1n+p), Nat.mod(k, 1n+p)), k, Ext2Proof.div_mod(k, p)) : {1n+_ == 1n+k : Nat}
  {==}

# the remainder is below the divisor
def Ext2Proof.lt_add(+m: Nat, +r: Nat) -> {Nat.is_lt(r, 1n+Nat.add(m, r)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(m, 1n+p), 1n+Nat.add(m, p), Ext2Proof.add_succ(m, p)) : {Nat.is_lt(1n+p, 1n+_) == True{} : Bool}
      Ext2Proof.lt_add(m, p)

def Ext2Proof.dm_lt(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> {Nat.add(m, r) == bp : Nat} -> {Nat.is_lt(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp) == True{} : Bool}:
  match n m:
    case 0n _:
      h =>
        %h : {Nat.is_lt(r, 1n+_) == True{} : Bool}
        Ext2Proof.lt_add(m, r)
    case 1n+np 0n:
      h => Ext2Proof.dm_lt(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, Ext2Proof.add_zero(r), h))
    case 1n+np 1n+mp:
      h => Ext2Proof.dm_lt(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, Ext2Proof.add_succ(mp, r), h))

def Laws.inode_locate_index(p, k):
  Ext2Proof.dm_lt(k, p, 0n, 0n, p, Ext2Proof.add_zero(p))

# The quotient and remainder of g * (1 + bp) + i, for i <= bp, are g and i

def Ext2Proof.bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def Ext2Proof.bool_clash(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : Ext2Proof.bool_disc(_)
  Unit{}

def Ext2Proof.ex_falso(-A: Type, e: Empty) -> A:
  match e:

def Ext2Proof.no_lt_one(+np: Nat) -> {Nat.is_lt(1n+np, 1n) == True{} : Bool} -> Empty:
  match np:
    case 0n:
      h => Ext2Proof.bool_clash(h)
    case 1n+q:
      h => Ext2Proof.bool_clash(h)

# fewer steps than m left in the round: the remainder grows by n
def Ext2Proof.dm_small(+n: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_lt(n, 1n+m) == True{} : Bool} -> {Nat.divmod.go(n, m, d, r) == (d, Nat.add(n, r)) : Nat & Nat}:
  match n m:
    case 0n _:
      h => {==}
    case 1n+np 0n:
      h => Ext2Proof.ex_falso({Nat.divmod.go(1n+np, 0n, d, r) == (d, Nat.add(1n+np, r)) : Nat & Nat}, Ext2Proof.no_lt_one(np, h))
    case 1n+np 1n+mp:
      h =>
        %Ext2Proof.add_succ(np, r) : {Nat.divmod.go(1n+np, 1n+mp, d, r) == (d, _) : Nat & Nat}
        Ext2Proof.dm_small(np, mp, d, 1n+r, h)

# finishing a round: m steps, then one more starts the next
def Ext2Proof.dm_round(+m: Nat, +n: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(Nat.add(m, 1n+n), m, d, r) == Nat.divmod.go(n, Nat.add(m, r), 1n+d, 0n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      %Ext2Proof.add_succ(mp, r) : {Nat.divmod.go(Nat.add(1n+mp, 1n+n), 1n+mp, d, r) == Nat.divmod.go(n, _, 1n+d, 0n) : Nat & Nat}
      Ext2Proof.dm_round(mp, n, d, 1n+r)

def Ext2Proof.dm_rounds(+g: Nat, +i: Nat, +d: Nat, +bp: Nat) -> {Nat.is_lt(i, 1n+bp) == True{} : Bool} -> {Nat.divmod.go(Nat.add(Nat.mul(g, 1n+bp), i), bp, d, 0n) == (Nat.add(g, d), i) : Nat & Nat}:
  match g:
    case 0n:
      h =>
        %Ext2Proof.add_zero(i) : {Nat.divmod.go(i, bp, d, 0n) == (d, _) : Nat & Nat}
        Ext2Proof.dm_small(i, bp, d, 0n, h)
    case 1n+gp:
      h =>
        +gg = Nat.mul(gp, 1n+bp)
        +y = Nat.add(gg, i)
        %Equal.sym(Nat, Nat.add(Nat.add(bp, gg), i), Nat.add(bp, y), Ext2Proof.add_assoc(bp, gg, i)) : {Nat.divmod.go(1n+_, bp, d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %Ext2Proof.add_succ(bp, y) : {Nat.divmod.go(_, bp, d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(bp, 1n+y), bp, d, 0n), Nat.divmod.go(y, Nat.add(bp, 0n), 1n+d, 0n), Ext2Proof.dm_round(bp, y, d, 0n)) : {_ == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %Equal.sym(Nat, Nat.add(bp, 0n), bp, Ext2Proof.add_zero(bp)) : {Nat.divmod.go(y, _, 1n+d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %Ext2Proof.add_succ(gp, d) : {Nat.divmod.go(y, bp, 1n+d, 0n) == (_, i) : Nat & Nat}
        Ext2Proof.dm_rounds(gp, i, 1n+d, bp, h)

def Laws.inode_number_locate(p, g, i, h):
  %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(Nat.mul(g, 1n+p), i), p, 0n, 0n), (Nat.add(g, 0n), i), Ext2Proof.dm_rounds(g, i, 0n, p, h)) : {N.Ext2InodeLoc{Pair.fst(Nat, Nat, _), Pair.snd(Nat, Nat, _)} == N.Ext2InodeLoc{g, i} : N.Ext2InodeLoc}
  %Equal.sym(Nat, Nat.add(g, 0n), g, Ext2Proof.add_zero(g)) : {N.Ext2InodeLoc{_, i} == N.Ext2InodeLoc{g, i} : N.Ext2InodeLoc}
  {==}

# Every block the map answers is inside the filesystem: its last step,
# Ext2Map.final, lets a block through only if it is

def Ext2Proof.some_disc(r: Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>) -> Type:
  match r:
    case Done{Some{x}}:
      Unit
    case _:
      Empty

def Ext2Proof.the_block(r: Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>) -> Nat:
  match r:
    case Done{Some{x}}:
      x
    case _:
      0n

def Ext2Proof.fail_clash(e: E.Ext2Error, q: Nat, h: {Fail{e} == Done{Some{q}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>}) -> Empty:
  %Equal.sym(Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>, Fail{e}, Done{Some{q}}, h) : Ext2Proof.some_disc(_)
  Unit{}

def Ext2Proof.none_clash(q: Nat, h: {Done{None{}} == Done{Some{q}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>}) -> Empty:
  %Equal.sym(Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>, Done{None{}}, Done{Some{q}}, h) : Ext2Proof.some_disc(_)
  Unit{}

def Ext2Proof.and_right(+a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {b == True{} : Bool}:
  match a:
    case True{}:
      h => h
    case False{}:
      h => Ext2Proof.ex_falso({b == True{} : Bool}, Ext2Proof.bool_clash(h))

def Ext2Proof.pick_inside(b: Bool, +fs: S.Ext2Fs, +ino: Nat, +p: Nat, +q: Nat) -> {M.Ext2Map.inside(fs, p) == b : Bool} -> {M.Ext2Map.check_some.pick(b, ino, p) == Done{Some{q}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>} -> {Nat.is_lt(q, S.Ext2Fs.blocks(fs)) == True{} : Bool}:
  match b:
    case True{}:
      hb => h =>
        %Equal.cong(Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>, Nat, Ext2Proof.the_block, Done{Some{p}}, Done{Some{q}}, h) : {Nat.is_lt(_, S.Ext2Fs.blocks(fs)) == True{} : Bool}
        Ext2Proof.and_right(Nat.is_le(U32.to_nat(S.Ext2Super.first_data_block(S.Ext2Fs.sb(fs))), p), Nat.is_lt(p, S.Ext2Fs.blocks(fs)), hb)
    case False{}:
      hb => h => Ext2Proof.ex_falso({Nat.is_lt(q, S.Ext2Fs.blocks(fs)) == True{} : Bool}, Ext2Proof.fail_clash(E.Ext2BadBlockRef{ino, p}, q, h))

def Ext2Proof.some_inside(+fs: S.Ext2Fs, +ino: Nat, m: Maybe<&2, Nat>, +q: Nat) -> {M.Ext2Map.check_some(fs, ino, m) == Done{Some{q}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>} -> {Nat.is_lt(q, S.Ext2Fs.blocks(fs)) == True{} : Bool}:
  match m:
    case None{}:
      h => Ext2Proof.ex_falso({Nat.is_lt(q, S.Ext2Fs.blocks(fs)) == True{} : Bool}, Ext2Proof.none_clash(q, h))
    case Some{+p}:
      h => Ext2Proof.pick_inside(M.Ext2Map.inside(fs, p), fs, ino, p, q, {==}, h)

def Ext2Proof.final_inside(+fs: S.Ext2Fs, +ino: Nat, r: Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>, +q: Nat) -> {M.Ext2Map.final(fs, ino, r) == Done{Some{q}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>} -> {Nat.is_lt(q, S.Ext2Fs.blocks(fs)) == True{} : Bool}:
  match r:
    case Done{m}:
      h => Ext2Proof.some_inside(fs, ino, m, q, h)
    case Fail{e}:
      h => Ext2Proof.ex_falso({Nat.is_lt(q, S.Ext2Fs.blocks(fs)) == True{} : Bool}, Ext2Proof.fail_clash(e, q, h))

def Laws.map_inside(d, fs, i, l, q, h):
  Ext2Proof.final_inside(fs, N.Ext2Inode.number_of(i), FL.Ext2File.map.within(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, Nat.is_lt(l, FL.Ext2File.blocks_needed(fs, i)), d, fs, i, l), q, h)

# Directory entries: decoding an encoded entry splits it where encoding
# joined it. Everything about Octets comes from bytes' interface laws: the
# lengths of the pieces, and take/drop at the length of the first piece of
# an append.

def Ext2Proof.list_len_append(xs: List<&2, U32>, +ys: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Ext2Proof.list_len_append(t, ys) : {1n+List.length(&2, U32, List.append(&2, U32, t, ys)) == 1n+_ : Nat}
      {==}

def Ext2Proof.len_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.len(B.Octets.append(a, b)) == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(a, b)), B.len(B.Octets.to_list(B.Octets.append(a, b))), BL.octets_len_list(B.Octets.append(a, b))) : {_ == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {B.len(_) == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %Equal.sym(Nat, B.Octets.len(a), B.len(B.Octets.to_list(a)), BL.octets_len_list(a)) : {B.len(B.append(B.Octets.to_list(a), B.Octets.to_list(b))) == Nat.add(_, B.Octets.len(b)) : Nat}
  %Equal.sym(Nat, B.Octets.len(b), B.len(B.Octets.to_list(b)), BL.octets_len_list(b)) : {B.len(B.append(B.Octets.to_list(a), B.Octets.to_list(b))) == Nat.add(B.len(B.Octets.to_list(a)), _) : Nat}
  Ext2Proof.list_len_append(B.Octets.to_list(a), B.Octets.to_list(b))

# the length of an Octets made from a list: the list's, masked
def Ext2Proof.len_of_list(+xs: List<&2, U32>) -> {B.Octets.len(B.Octets.of_list(xs)) == B.len(B.mask(xs)) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(xs)), B.len(B.Octets.to_list(B.Octets.of_list(xs))), BL.octets_len_list(B.Octets.of_list(xs))) : {_ == B.len(B.mask(xs)) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {B.len(_) == B.len(B.mask(xs)) : Nat}
  {==}

def Ext2Proof.len4(+i: U32) -> {B.Octets.len(B.Octets.le32(i)) == 4n : Nat}:
  match i:
    case U32{+w}:
      Ext2Proof.len_of_list(B.le32(U32{w}))

def Ext2Proof.len2(+r: U32) -> {B.Octets.len(B.Octets.le16(r)) == 2n : Nat}:
  match r:
    case U32{+w}:
      Ext2Proof.len_of_list(B.le16(U32{w}))

def Ext2Proof.len_nf(+n: U32, +f: U32) -> {B.Octets.len(B.Octets.of_list([n, f])) == 2n : Nat}:
  Ext2Proof.len_of_list([n, f])

def Ext2Proof.len_hx(+r: U32, +n: U32, +f: U32) -> {B.Octets.len(B.Octets.append(B.Octets.le16(r), B.Octets.of_list([n, f]))) == 4n : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(B.Octets.le16(r), B.Octets.of_list([n, f]))), Nat.add(B.Octets.len(B.Octets.le16(r)), B.Octets.len(B.Octets.of_list([n, f]))), Ext2Proof.len_append(B.Octets.le16(r), B.Octets.of_list([n, f]))) : {_ == 4n : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.le16(r)), 2n, Ext2Proof.len2(r)) : {Nat.add(_, B.Octets.len(B.Octets.of_list([n, f]))) == 4n : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list([n, f])), 2n, Ext2Proof.len_nf(n, f)) : {Nat.add(2n, _) == 4n : Nat}
  {==}

def Ext2Proof.len_h(+i: U32, +r: U32, +n: U32, +f: U32) -> {B.Octets.len(DR.Ext2Dirent.header(i, r, n, f)) == 8n : Nat}:
  +x = B.Octets.append(B.Octets.le16(r), B.Octets.of_list([n, f]))
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(B.Octets.le32(i), x)), Nat.add(B.Octets.len(B.Octets.le32(i)), B.Octets.len(x)), Ext2Proof.len_append(B.Octets.le32(i), x)) : {_ == 8n : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.le32(i)), 4n, Ext2Proof.len4(i)) : {Nat.add(_, B.Octets.len(x)) == 8n : Nat}
  %Equal.sym(Nat, B.Octets.len(x), 4n, Ext2Proof.len_hx(r, n, f)) : {Nat.add(4n, _) == 8n : Nat}
  {==}

def Ext2Proof.dirent_rt(+e: DR.Ext2Dirent) -> {B.Octets.len(DR.Ext2Dirent.name(e)) == U32.to_nat(B.byte(DR.Ext2Dirent.name_len(e))) : Nat} -> {DR.Ext2Dirent.decode(True{}, DR.Ext2Dirent.encode(e)) == Some{DR.Ext2Dirent.norm(e)} : Maybe<&2, DR.Ext2Dirent>}:
  match e:
    case DR.Ext2Dirent{+i, +r, +n, +f, +nm}:
      h =>
        +l4 = B.Octets.le32(i)
        +l2 = B.Octets.le16(r)
        +nf = B.Octets.of_list([n, f])
        +x = B.Octets.append(l2, nf)
        +hh = DR.Ext2Dirent.header(i, r, n, f)
        +z = B.Octets.zeros(Nat.sub(U32.to_nat(r), Nat.add(8n, B.Octets.len(nm))))
        +bo = B.Octets.append(nm, z)
        +o = B.Octets.append(hh, bo)
        +res = {Some{DR.Ext2Dirent{i, B.low16(r), B.byte(n), B.byte(f), nm}} : Maybe<&2, DR.Ext2Dirent>}
        %Ext2Proof.len_h(i, r, n, f) : {DR.Ext2Dirent.decode.go(True{}, Nat.is_eq(B.Octets.len(B.Octets.take(_, o)), 8n), B.Octets.take(_, o), B.Octets.drop(_, o)) == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(hh), o), hh, BL.octets_take_append(hh, bo)) : {DR.Ext2Dirent.decode.go(True{}, Nat.is_eq(B.Octets.len(_), 8n), _, B.Octets.drop(B.Octets.len(hh), o)) == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(hh), o), bo, BL.octets_drop_append(hh, bo)) : {DR.Ext2Dirent.decode.go(True{}, Nat.is_eq(B.Octets.len(hh), 8n), hh, _) == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(Nat, B.Octets.len(hh), 8n, Ext2Proof.len_h(i, r, n, f)) : {DR.Ext2Dirent.decode.go(True{}, Nat.is_eq(_, 8n), hh, bo) == res : Maybe<&2, DR.Ext2Dirent>}
        %Ext2Proof.len4(i) : {Some{DR.Ext2Dirent.decode.make(True{}, Maybe.default(&2, U32, B.Octets.le32_at(B.Octets.take(_, hh), 0n), 0), Maybe.default(&2, U32, B.Octets.le16_at(B.Octets.take(2n, B.Octets.drop(4n, hh)), 0n), 0), B.Octets.to_list(B.Octets.drop(2n, B.Octets.drop(4n, hh))), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(l4), hh), l4, BL.octets_take_append(l4, x)) : {Some{DR.Ext2Dirent.decode.make(True{}, Maybe.default(&2, U32, B.Octets.le32_at(_, 0n), 0), Maybe.default(&2, U32, B.Octets.le16_at(B.Octets.take(2n, B.Octets.drop(4n, hh)), 0n), 0), B.Octets.to_list(B.Octets.drop(2n, B.Octets.drop(4n, hh))), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(l4, 0n), Some{i}, BL.octets_le32_round_trip(i)) : {Some{DR.Ext2Dirent.decode.make(True{}, Maybe.default(&2, U32, _, 0), Maybe.default(&2, U32, B.Octets.le16_at(B.Octets.take(2n, B.Octets.drop(4n, hh)), 0n), 0), B.Octets.to_list(B.Octets.drop(2n, B.Octets.drop(4n, hh))), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Ext2Proof.len4(i) : {Some{DR.Ext2Dirent.decode.make(True{}, i, Maybe.default(&2, U32, B.Octets.le16_at(B.Octets.take(2n, B.Octets.drop(_, hh)), 0n), 0), B.Octets.to_list(B.Octets.drop(2n, B.Octets.drop(_, hh))), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(l4), hh), x, BL.octets_drop_append(l4, x)) : {Some{DR.Ext2Dirent.decode.make(True{}, i, Maybe.default(&2, U32, B.Octets.le16_at(B.Octets.take(2n, _), 0n), 0), B.Octets.to_list(B.Octets.drop(2n, _)), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Ext2Proof.len2(r) : {Some{DR.Ext2Dirent.decode.make(True{}, i, Maybe.default(&2, U32, B.Octets.le16_at(B.Octets.take(_, x), 0n), 0), B.Octets.to_list(B.Octets.drop(_, x)), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(l2), x), l2, BL.octets_take_append(l2, nf)) : {Some{DR.Ext2Dirent.decode.make(True{}, i, Maybe.default(&2, U32, B.Octets.le16_at(_, 0n), 0), B.Octets.to_list(B.Octets.drop(B.Octets.len(l2), x)), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(l2), x), nf, BL.octets_drop_append(l2, nf)) : {Some{DR.Ext2Dirent.decode.make(True{}, i, Maybe.default(&2, U32, B.Octets.le16_at(l2, 0n), 0), B.Octets.to_list(_), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(Maybe<&2, U32>, B.Octets.le16_at(l2, 0n), Some{B.low16(r)}, BL.octets_le16_round_trip(r)) : {Some{DR.Ext2Dirent.decode.make(True{}, i, Maybe.default(&2, U32, _, 0), B.Octets.to_list(nf), bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(List<&2, U32>, B.Octets.to_list(nf), B.mask([n, f]), BL.octets_to_of([n, f])) : {Some{DR.Ext2Dirent.decode.make(True{}, i, B.low16(r), _, bo)} == res : Maybe<&2, DR.Ext2Dirent>}
        %h : {Some{DR.Ext2Dirent{i, B.low16(r), B.byte(n), B.byte(f), B.Octets.take(_, bo)}} == res : Maybe<&2, DR.Ext2Dirent>}
        %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(nm), bo), nm, BL.octets_take_append(nm, z)) : {Some{DR.Ext2Dirent{i, B.low16(r), B.byte(n), B.byte(f), _}} == res : Maybe<&2, DR.Ext2Dirent>}
        {==}

def Laws.dirent_round_trip(e, h):
  Ext2Proof.dirent_rt(e, h)

# Vectors

def Laws.mount_sample():
  {==}

def Laws.mount_bad_magic():
  {==}

def Laws.mount_inline_data():
  {==}

def Laws.mount_needs_recovery():
  {==}

def Laws.mount_ext2_only():
  {==}

def Laws.csum_seed():
  {==}

def Laws.csum_group():
  {==}

def Laws.csum_inode():
  {==}

def Laws.locate_vector():
  {==}

def Laws.dirent_dot():
  {==}

def Laws.dirent_no_filetype():
  {==}

def Laws.dirent_bad_rec_len():
  {==}

def Laws.dirent_past_block():
  {==}

def Laws.dirent_ok():
  {==}

def Laws.path_direct():
  {==}

def Laws.path_single():
  {==}

def Laws.path_double():
  {==}

def Laws.path_triple():
  {==}

def Laws.path_beyond():
  {==}

# Witnesses

def Laws.inode_number_locate_witness(p):
  Ext2Proof.lt_succ(p)

def Laws.dirent_round_trip_witness():
  {==}

def Laws.map_past_end_witness(fs, i):
  Ext2Proof.lt_irrefl(FL.Ext2File.blocks_needed(fs, i))

# the filesystem sample_super describes, as mounting it gives
def Ext2Proof.sample_fs() -> S.Ext2Fs:
  S.Ext2Fs{S.Ext2Super.parse(Laws.Ext2Laws.sample_super(61267, 0)), O.Ext2Options.default(), 1024n, 64n, 1n, 32n, 128n, 16n, 0, S.Ext2CsumNone{}}

def Laws.map_inside_witness():
  (Ext2Proof.sample_fs(), {==})

def Laws.extent_depth_bound_witness():
  (Ext2Proof.sample_fs(), {==})

# The checks that come first: the bound, past the end, the end of a reader

def Laws.map_past_end(d, fs, i, l, h):
  %Equal.sym(Bool, Nat.is_lt(l, FL.Ext2File.blocks_needed(fs, i)), False{}, h) : {M.Ext2Map.final(fs, N.Ext2Inode.number_of(i), FL.Ext2File.map.within(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, _, d, fs, i, l)) == Fail{E.Ext2PastEnd{N.Ext2Inode.number_of(i), l}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>}
  {==}

def Laws.extent_depth_bound(d, fs, ino, gen, iblock, l, h):
  %Equal.sym(Bool, Nat.is_le(X.Ext2Extent.root_depth(iblock), O.Ext2Options.max_depth(S.Ext2Fs.opts(fs))), False{}, h) : {X.Ext2Extent.map.depth(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, _, d, fs, ino, gen, iblock, l) == Fail{E.Ext2ExtentTooDeep{ino, X.Ext2Extent.root_depth(iblock)}} : Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>}
  {==}

def Laws.next_at_end(d, fs, i, k, h):
  %Equal.sym(Bool, Nat.is_lt(k, FL.Ext2File.blocks_needed(fs, i)), False{}, h) : {FL.Ext2File.next.go(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, _, d, fs, i, k) == Done{FL.Ext2Eof{}} : Result<&2, &2, E.Ext2Error, FL.Ext2Chunk>}
  {==}

# ---------------------------------------------------------------- writing
# a + (r - a) == r when a + b <= r
def Ext2Proof.add_sub(a: Nat, +b: Nat, r: Nat) -> {Nat.is_le(Nat.add(a, b), r) == True{} : Bool} -> {Nat.add(a, Nat.sub(r, a)) == r : Nat}:
  match a r:
    case 0n 0n:
      h => {==}
    case 0n 1n+rp:
      h => {==}
    case 1n+ap 0n:
      h => Ext2Proof.ex_falso({Nat.add(1n+ap, Nat.sub(0n, 1n+ap)) == 0n : Nat}, Ext2Proof.bool_clash(h))
    case 1n+ap 1n+rp:
      h =>
        %Equal.sym(Nat, Nat.add(ap, Nat.sub(rp, ap)), rp, Ext2Proof.add_sub(ap, b, rp, h)) : {1n+_ == 1n+rp : Nat}
        {==}

def Ext2Proof.total_append(xs: List<&2, DW.Ext2Slot>, +ys: List<&2, DW.Ext2Slot>) -> {DW.Ext2Slots.total(List.append(&2, DW.Ext2Slot, xs, ys)) == Nat.add(DW.Ext2Slots.total(xs), DW.Ext2Slots.total(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +r = DW.Ext2Slot.rec_len(x)
      +tt = DW.Ext2Slots.total(t)
      +ty = DW.Ext2Slots.total(ys)
      %Equal.sym(Nat, Nat.add(Nat.add(r, tt), ty), Nat.add(r, Nat.add(tt, ty)), Ext2Proof.add_assoc(r, tt, ty)) : {Nat.add(r, DW.Ext2Slots.total(List.append(&2, DW.Ext2Slot, t, ys))) == _ : Nat}
      %Ext2Proof.total_append(t, ys) : {Nat.add(r, DW.Ext2Slots.total(List.append(&2, DW.Ext2Slot, t, ys))) == Nat.add(r, _) : Nat}
      {==}

# splitting a slot that fits keeps its record
def Ext2Proof.split_total(u: Bool, s: DW.Ext2Slot, n: DW.Ext2Slot) -> {DW.Ext2Slot.fits.pick(u, s, DW.Ext2Slot.need(n)) == True{} : Bool} -> {DW.Ext2Slots.total(DW.Ext2Slot.split.pick(u, s, n)) == DW.Ext2Slot.rec_len(s) : Nat}:
  match u s n:
    case True{} DW.Ext2Slot{i, +r, f, +nm} DW.Ext2Slot{ni, nr, nf, +nnm}:
      h =>
        +a = DR.Ext2Dirent.min_rec_len(B.Octets.len(nm))
        %Equal.sym(Nat, Nat.add(Nat.sub(r, a), 0n), Nat.sub(r, a), Ext2Proof.add_zero(Nat.sub(r, a))) : {Nat.add(a, _) == r : Nat}
        Ext2Proof.add_sub(a, DR.Ext2Dirent.min_rec_len(B.Octets.len(nnm)), r, h)
    case False{} DW.Ext2Slot{i, +r, f, nm} DW.Ext2Slot{ni, nr, nf, nnm}:
      h => Ext2Proof.add_zero(r)

def Ext2Proof.cons_total(s: DW.Ext2Slot, r: Maybe<&2, List<&2, DW.Ext2Slot>>, +d: Nat) -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.cons_some(s, r), Nat.add(DW.Ext2Slot.rec_len(s), d)) == Nat.add(DW.Ext2Slot.rec_len(s), Laws.Ext2Laws.total_or(r, d)) : Nat}:
  match r:
    case None{}:
      {==}
    case Some{xs}:
      {==}

def Ext2Proof.ins_pick(b: Bool, +u: Bool, +s: DW.Ext2Slot, +t: List<&2, DW.Ext2Slot>, +n: DW.Ext2Slot) -> {DW.Ext2Slot.fits.pick(u, s, DW.Ext2Slot.need(n)) == b : Bool} -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.insert(t, n), DW.Ext2Slots.total(t)) == DW.Ext2Slots.total(t) : Nat} -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.insert.pick(b, u, s, t, n, DW.Ext2Slots.insert(t, n)), Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t))) == Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)) : Nat}:
  match b:
    case True{}:
      hb => ih =>
        +sp = DW.Ext2Slot.split.pick(u, s, n)
        %Equal.sym(Nat, DW.Ext2Slots.total(List.append(&2, DW.Ext2Slot, sp, t)), Nat.add(DW.Ext2Slots.total(sp), DW.Ext2Slots.total(t)), Ext2Proof.total_append(sp, t)) : {_ == Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)) : Nat}
        %Equal.sym(Nat, DW.Ext2Slots.total(sp), DW.Ext2Slot.rec_len(s), Ext2Proof.split_total(u, s, n, hb)) : {Nat.add(_, DW.Ext2Slots.total(t)) == Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)) : Nat}
        {==}
    case False{}:
      hb => ih =>
        %Equal.sym(Nat, Laws.Ext2Laws.total_or(DW.Ext2Slots.cons_some(s, DW.Ext2Slots.insert(t, n)), Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t))), Nat.add(DW.Ext2Slot.rec_len(s), Laws.Ext2Laws.total_or(DW.Ext2Slots.insert(t, n), DW.Ext2Slots.total(t))), Ext2Proof.cons_total(s, DW.Ext2Slots.insert(t, n), DW.Ext2Slots.total(t))) : {_ == Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)) : Nat}
        %Equal.sym(Nat, Laws.Ext2Laws.total_or(DW.Ext2Slots.insert(t, n), DW.Ext2Slots.total(t)), DW.Ext2Slots.total(t), ih) : {Nat.add(DW.Ext2Slot.rec_len(s), _) == Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)) : Nat}
        {==}

# inserting keeps the total of the records (as a function: no hypothesis)
def Ext2Proof.ins_total(ss: List<&2, DW.Ext2Slot>, +n: DW.Ext2Slot) -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.insert(ss, n), DW.Ext2Slots.total(ss)) == DW.Ext2Slots.total(ss) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Ext2Proof.ins_pick(DW.Ext2Slot.fits.pick(DW.Ext2Slot.used(s), s, DW.Ext2Slot.need(n)), DW.Ext2Slot.used(s), s, t, n, {==}, Ext2Proof.ins_total(t, n))

def Ext2Proof.unused_rec(s: DW.Ext2Slot) -> {DW.Ext2Slot.rec_len(DW.Ext2Slot.unused(s)) == DW.Ext2Slot.rec_len(s) : Nat}:
  match s:
    case DW.Ext2Slot{i, r, f, n}:
      {==}

def Ext2Proof.absorb_rec(p: DW.Ext2Slot, +s: DW.Ext2Slot) -> {DW.Ext2Slot.rec_len(DW.Ext2Slot.absorb(p, s)) == Nat.add(DW.Ext2Slot.rec_len(p), DW.Ext2Slot.rec_len(s)) : Nat}:
  match p:
    case DW.Ext2Slot{i, r, f, n}:
      {==}

def Ext2Proof.rm_pick(b: Bool, +prev: DW.Ext2Slot, +s: DW.Ext2Slot, +t: List<&2, DW.Ext2Slot>, +name: B.Octets) -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.rm(t, s, name), Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t))) == Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)) : Nat} -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.rm.pick(b, prev, s, t, DW.Ext2Slots.rm(t, s, name)), Nat.add(DW.Ext2Slot.rec_len(prev), Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)))) == Nat.add(DW.Ext2Slot.rec_len(prev), Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t))) : Nat}:
  match b:
    case True{}:
      ih =>
        +rp = DW.Ext2Slot.rec_len(prev)
        +rs = DW.Ext2Slot.rec_len(s)
        +tt = DW.Ext2Slots.total(t)
        %Equal.sym(Nat, DW.Ext2Slot.rec_len(DW.Ext2Slot.absorb(prev, s)), Nat.add(rp, rs), Ext2Proof.absorb_rec(prev, s)) : {Nat.add(_, tt) == Nat.add(rp, Nat.add(rs, tt)) : Nat}
        Ext2Proof.add_assoc(rp, rs, tt)
    case False{}:
      ih =>
        +rp = DW.Ext2Slot.rec_len(prev)
        +d = Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t))
        %Equal.sym(Nat, Laws.Ext2Laws.total_or(DW.Ext2Slots.cons_some(prev, DW.Ext2Slots.rm(t, s, name)), Nat.add(rp, d)), Nat.add(rp, Laws.Ext2Laws.total_or(DW.Ext2Slots.rm(t, s, name), d)), Ext2Proof.cons_total(prev, DW.Ext2Slots.rm(t, s, name), d)) : {_ == Nat.add(rp, d) : Nat}
        %Equal.sym(Nat, Laws.Ext2Laws.total_or(DW.Ext2Slots.rm(t, s, name), d), d, ih) : {Nat.add(rp, _) == Nat.add(rp, d) : Nat}
        {==}

# the slots after prev, one merged into the slot before it: the total kept
def Ext2Proof.rm_total(ss: List<&2, DW.Ext2Slot>, +prev: DW.Ext2Slot, +name: B.Octets) -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.rm(ss, prev, name), Nat.add(DW.Ext2Slot.rec_len(prev), DW.Ext2Slots.total(ss))) == Nat.add(DW.Ext2Slot.rec_len(prev), DW.Ext2Slots.total(ss)) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Ext2Proof.rm_pick(DW.Ext2Slot.hit(s, name), prev, s, t, name, Ext2Proof.rm_total(t, s, name))

def Ext2Proof.rem_pick(b: Bool, +s: DW.Ext2Slot, +t: List<&2, DW.Ext2Slot>, +name: B.Octets) -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.remove.pick(b, s, t, name), Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t))) == Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Nat, DW.Ext2Slot.rec_len(DW.Ext2Slot.unused(s)), DW.Ext2Slot.rec_len(s), Ext2Proof.unused_rec(s)) : {Nat.add(_, DW.Ext2Slots.total(t)) == Nat.add(DW.Ext2Slot.rec_len(s), DW.Ext2Slots.total(t)) : Nat}
      {==}
    case False{}:
      Ext2Proof.rm_total(t, s, name)

def Ext2Proof.rem_total(ss: List<&2, DW.Ext2Slot>, +name: B.Octets) -> {Laws.Ext2Laws.total_or(DW.Ext2Slots.remove(ss, name), DW.Ext2Slots.total(ss)) == DW.Ext2Slots.total(ss) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Ext2Proof.rem_pick(DW.Ext2Slot.hit(s, name), s, t, name)

def Ext2Proof.opt_disc(m: Maybe<&2, DW.Ext2Slot>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def Ext2Proof.some_clash(x: DW.Ext2Slot, h: {Some{x} == None{} : Maybe<&2, DW.Ext2Slot>}) -> Empty:
  %h : Ext2Proof.opt_disc(_)
  Unit{}

# an unused slot in front of an answer: the names are the answer's
def Ext2Proof.cons_unused(+s: DW.Ext2Slot, r: Maybe<&2, List<&2, DW.Ext2Slot>>, +nnm: B.Octets, +d: List<&2, DW.Ext2Name>) -> {DW.Ext2Slot.used(s) == False{} : Bool} -> {Laws.Ext2Laws.unnamed_or(DW.Ext2Slots.cons_some(s, r), nnm, d) == Laws.Ext2Laws.unnamed_or(r, nnm, d) : List<&2, DW.Ext2Name>}:
  match r:
    case None{}:
      hu => {==}
    case Some{+xs}:
      hu =>
        %Equal.sym(Bool, DW.Ext2Slot.used(s), False{}, hu) : {DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, s, DW.Ext2Slots.names(xs)), nnm) == DW.Ext2Names.unname(DW.Ext2Slots.names(xs), nnm) : List<&2, DW.Ext2Name>}
        {==}

# a used slot, named otherwise, in front of an answer: its name, then the
# answer's
def Ext2Proof.cons_used(+i: U32, +r0: Nat, +f: U32, +nm: B.Octets, r: Maybe<&2, List<&2, DW.Ext2Slot>>, +nnm: B.Octets, +d: List<&2, DW.Ext2Name>) -> {Bool.not(U32.is_eq(i, 0)) == True{} : Bool} -> {B.Octets.is_eq(nm, nnm) == False{} : Bool} -> {Laws.Ext2Laws.unnamed_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{i, r0, f, nm}, r), nnm, Con{DW.Ext2Name{i, f, nm}, d}) == Con{DW.Ext2Name{i, f, nm}, Laws.Ext2Laws.unnamed_or(r, nnm, d)} : List<&2, DW.Ext2Name>}:
  match r:
    case None{}:
      hu => he => {==}
    case Some{+xs}:
      hu => he =>
        +rest = DW.Ext2Slots.names(xs)
        %Equal.sym(Bool, Bool.not(U32.is_eq(i, 0)), True{}, hu) : {DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{i, r0, f, nm}, rest), nnm) == Con{DW.Ext2Name{i, f, nm}, DW.Ext2Names.unname(rest, nnm)} : List<&2, DW.Ext2Name>}
        %Equal.sym(Bool, B.Octets.is_eq(nm, nnm), False{}, he) : {DW.Ext2Names.unname.pick(_, DW.Ext2Name{i, f, nm}, rest, DW.Ext2Names.unname(rest, nnm)) == Con{DW.Ext2Name{i, f, nm}, DW.Ext2Names.unname(rest, nnm)} : List<&2, DW.Ext2Name>}
        {==}

def Ext2Proof.pick_none_false(c: Bool, +s: DW.Ext2Slot, r: Maybe<&2, DW.Ext2Slot>) -> {DW.Ext2Slots.lookup.pick(c, s, r) == None{} : Maybe<&2, DW.Ext2Slot>} -> {c == False{} : Bool}:
  match c:
    case True{}:
      h => Ext2Proof.ex_falso({True{} == False{} : Bool}, Ext2Proof.some_clash(s, h))
    case False{}:
      h => {==}

def Ext2Proof.pick_none_rest(c: Bool, +s: DW.Ext2Slot, r: Maybe<&2, DW.Ext2Slot>) -> {DW.Ext2Slots.lookup.pick(c, s, r) == None{} : Maybe<&2, DW.Ext2Slot>} -> {r == None{} : Maybe<&2, DW.Ext2Slot>}:
  match c:
    case True{}:
      h => Ext2Proof.ex_falso({r == None{} : Maybe<&2, DW.Ext2Slot>}, Ext2Proof.some_clash(s, h))
    case False{}:
      h => h

# the new entry, used, at the front of the slots after it: unnamed, the
# names after it
def Ext2Proof.front_new(+ni: U32, +x: Nat, +nf: U32, +nnm: B.Octets, +rest: List<&2, DW.Ext2Name>) -> {Bool.not(U32.is_eq(ni, 0)) == True{} : Bool} -> {DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(ni, 0)), DW.Ext2Slot{ni, x, nf, nnm}, rest), nnm) == rest : List<&2, DW.Ext2Name>}:
  hn =>
    %Equal.sym(Bool, Bool.not(U32.is_eq(ni, 0)), True{}, hn) : {DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{ni, x, nf, nnm}, rest), nnm) == rest : List<&2, DW.Ext2Name>}
    %Equal.sym(Bool, B.Octets.is_eq(nnm, nnm), True{}, BL.octets_is_eq_refl(nnm)) : {DW.Ext2Names.unname.pick(_, DW.Ext2Name{ni, nf, nnm}, rest, DW.Ext2Names.unname(rest, nnm)) == rest : List<&2, DW.Ext2Name>}
    {==}

def Ext2Proof.ins_names.at(u: Bool, e: Bool, b: Bool, +s: DW.Ext2Slot, +t: List<&2, DW.Ext2Slot>, +ni: U32, +nr: Nat, +nf: U32, +nnm: B.Octets) -> {DW.Ext2Slot.used(s) == u : Bool} -> {B.Octets.is_eq(DW.Ext2Slot.name(s), nnm) == e : Bool} -> {DW.Ext2Slots.lookup.pick(Bool.and(u, e), s, DW.Ext2Slots.lookup(t, nnm)) == None{} : Maybe<&2, DW.Ext2Slot>} -> {Bool.not(U32.is_eq(ni, 0)) == True{} : Bool} -> ({DW.Ext2Slots.lookup(t, nnm) == None{} : Maybe<&2, DW.Ext2Slot>} -> {Laws.Ext2Laws.unnamed_or(DW.Ext2Slots.insert(t, DW.Ext2Slot{ni, nr, nf, nnm}), nnm, DW.Ext2Slots.names(t)) == DW.Ext2Slots.names(t) : List<&2, DW.Ext2Name>}) -> {Laws.Ext2Laws.unnamed_or(DW.Ext2Slots.insert.pick(b, u, s, t, DW.Ext2Slot{ni, nr, nf, nnm}, DW.Ext2Slots.insert(t, DW.Ext2Slot{ni, nr, nf, nnm})), nnm, DW.Ext2Slots.names.keep(u, s, DW.Ext2Slots.names(t))) == DW.Ext2Slots.names.keep(u, s, DW.Ext2Slots.names(t)) : List<&2, DW.Ext2Name>}:
  match u e b:
    case True{} True{} _:
      hu => he => hc => hn => ih => Ext2Proof.ex_falso({Laws.Ext2Laws.unnamed_or(DW.Ext2Slots.insert.pick(b, True{}, s, t, DW.Ext2Slot{ni, nr, nf, nnm}, DW.Ext2Slots.insert(t, DW.Ext2Slot{ni, nr, nf, nnm})), nnm, DW.Ext2Slots.names.keep(True{}, s, DW.Ext2Slots.names(t))) == DW.Ext2Slots.names.keep(True{}, s, DW.Ext2Slots.names(t)) : List<&2, DW.Ext2Name>}, Ext2Proof.some_clash(s, hc))
    case True{} False{} True{}:
      match s:
        case DW.Ext2Slot{+i, +r, +f, +nm}:
          hu => he => hc => hn => ih =>
            +need = DR.Ext2Dirent.min_rec_len(B.Octets.len(nm))
            +a = {DW.Ext2Slot{i, need, f, nm} : DW.Ext2Slot}
            +bs = {DW.Ext2Slot{ni, Nat.sub(r, need), nf, nnm} : DW.Ext2Slot}
            +nt = DW.Ext2Slots.names(t)
            +k = DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(ni, 0)), bs, nt)
            +nn = {DW.Ext2Name{i, f, nm} : DW.Ext2Name}
            %Equal.sym(Bool, Bool.not(U32.is_eq(i, 0)), True{}, hu) : {DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, a, k), nnm) == Con{nn, nt} : List<&2, DW.Ext2Name>}
            %Equal.sym(Bool, B.Octets.is_eq(nm, nnm), False{}, he) : {DW.Ext2Names.unname.pick(_, nn, k, DW.Ext2Names.unname(k, nnm)) == Con{nn, nt} : List<&2, DW.Ext2Name>}
            %Equal.sym(List<&2, DW.Ext2Name>, DW.Ext2Names.unname(k, nnm), nt, Ext2Proof.front_new(ni, Nat.sub(r, need), nf, nnm, nt, hn)) : {Con{nn, _} == Con{nn, nt} : List<&2, DW.Ext2Name>}
            {==}
    case True{} False{} False{}:
      match s:
        case DW.Ext2Slot{+i, +r, +f, +nm}:
          hu => he => hc => hn => ih =>
            +rr = DW.Ext2Slots.insert(t, DW.Ext2Slot{ni, nr, nf, nnm})
            +nt = DW.Ext2Slots.names(t)
            +nn = {DW.Ext2Name{i, f, nm} : DW.Ext2Name}
            %Equal.sym(List<&2, DW.Ext2Name>, Laws.Ext2Laws.unnamed_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{i, r, f, nm}, rr), nnm, Con{nn, nt}), Con{nn, Laws.Ext2Laws.unnamed_or(rr, nnm, nt)}, Ext2Proof.cons_used(i, r, f, nm, rr, nnm, nt, hu, he)) : {_ == Con{nn, nt} : List<&2, DW.Ext2Name>}
            %Equal.sym(List<&2, DW.Ext2Name>, Laws.Ext2Laws.unnamed_or(rr, nnm, nt), nt, ih(Ext2Proof.pick_none_rest(False{}, DW.Ext2Slot{i, r, f, nm}, DW.Ext2Slots.lookup(t, nnm), hc))) : {Con{nn, _} == Con{nn, nt} : List<&2, DW.Ext2Name>}
            {==}
    case False{} _ True{}:
      hu => he => hc => hn => ih => Ext2Proof.front_new(ni, DW.Ext2Slot.rec_len(s), nf, nnm, DW.Ext2Slots.names(t), hn)
    case False{} _ False{}:
      hu => he => hc => hn => ih =>
        +r = DW.Ext2Slots.insert(t, DW.Ext2Slot{ni, nr, nf, nnm})
        %Equal.sym(List<&2, DW.Ext2Name>, Laws.Ext2Laws.unnamed_or(DW.Ext2Slots.cons_some(s, r), nnm, DW.Ext2Slots.names(t)), Laws.Ext2Laws.unnamed_or(r, nnm, DW.Ext2Slots.names(t)), Ext2Proof.cons_unused(s, r, nnm, DW.Ext2Slots.names(t), hu)) : {_ == DW.Ext2Slots.names(t) : List<&2, DW.Ext2Name>}
        ih(Ext2Proof.pick_none_rest(False{}, s, DW.Ext2Slots.lookup(t, nnm), hc))

def Ext2Proof.ins_names(ss: List<&2, DW.Ext2Slot>, +ni: U32, +nr: Nat, +nf: U32, +nnm: B.Octets) -> {DW.Ext2Slots.lookup(ss, nnm) == None{} : Maybe<&2, DW.Ext2Slot>} -> {Bool.not(U32.is_eq(ni, 0)) == True{} : Bool} -> {Laws.Ext2Laws.unnamed_or(DW.Ext2Slots.insert(ss, DW.Ext2Slot{ni, nr, nf, nnm}), nnm, DW.Ext2Slots.names(ss)) == DW.Ext2Slots.names(ss) : List<&2, DW.Ext2Name>}:
  match ss:
    case Nil{}:
      hl => hn => {==}
    case Con{+s, +t}:
      hl => +hn => Ext2Proof.ins_names.at(DW.Ext2Slot.used(s), B.Octets.is_eq(DW.Ext2Slot.name(s), nnm), DW.Ext2Slot.fits.pick(DW.Ext2Slot.used(s), s, DW.Ext2Slot.need(DW.Ext2Slot{ni, nr, nf, nnm})), s, t, ni, nr, nf, nnm, {==}, {==}, hl, hn, ht => Ext2Proof.ins_names(t, ni, nr, nf, nnm, ht, hn))

def Ext2Proof.and_l(a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {a == True{} : Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => Ext2Proof.ex_falso({False{} == True{} : Bool}, Ext2Proof.bool_clash(h))

def Ext2Proof.and_r(a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {b == True{} : Bool}:
  match a:
    case True{}:
      h => h
    case False{}:
      h => Ext2Proof.ex_falso({b == True{} : Bool}, Ext2Proof.bool_clash(h))

def Ext2Proof.and_true_r(a: Bool, +b: Bool) -> {a == True{} : Bool} -> {Bool.and(a, b) == False{} : Bool} -> {b == False{} : Bool}:
  match a:
    case True{}:
      ha => h => h
    case False{}:
      ha => h => Ext2Proof.ex_falso({b == False{} : Bool}, Ext2Proof.bool_clash(ha))

# a used slot (named otherwise) in front of an answer of rm: its name first
def Ext2Proof.cons_names_used(+pi: U32, +pr: Nat, +pf: U32, +pnm: B.Octets, r: Maybe<&2, List<&2, DW.Ext2Slot>>, +d: List<&2, DW.Ext2Name>) -> {Bool.not(U32.is_eq(pi, 0)) == True{} : Bool} -> {Laws.Ext2Laws.names_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{pi, pr, pf, pnm}, r), Con{DW.Ext2Name{pi, pf, pnm}, d}) == Con{DW.Ext2Name{pi, pf, pnm}, Laws.Ext2Laws.names_or(r, d)} : List<&2, DW.Ext2Name>}:
  match r:
    case None{}:
      hu => {==}
    case Some{+xs}:
      hu =>
        %Equal.sym(Bool, Bool.not(U32.is_eq(pi, 0)), True{}, hu) : {DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names(xs)) == Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Slots.names(xs)} : List<&2, DW.Ext2Name>}
        {==}

def Ext2Proof.cons_names_unused(+pi: U32, +pr: Nat, +pf: U32, +pnm: B.Octets, r: Maybe<&2, List<&2, DW.Ext2Slot>>, +d: List<&2, DW.Ext2Name>) -> {Bool.not(U32.is_eq(pi, 0)) == False{} : Bool} -> {Laws.Ext2Laws.names_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{pi, pr, pf, pnm}, r), d) == Laws.Ext2Laws.names_or(r, d) : List<&2, DW.Ext2Name>}:
  match r:
    case None{}:
      hu => {==}
    case Some{+xs}:
      hu =>
        %Equal.sym(Bool, Bool.not(U32.is_eq(pi, 0)), False{}, hu) : {DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names(xs)) == DW.Ext2Slots.names(xs) : List<&2, DW.Ext2Name>}
        {==}

def Ext2Proof.rm_names.step(up: Bool, b2: Bool, +pi: U32, +pr: Nat, +pf: U32, +pnm: B.Octets, +i2: U32, +r2: Nat, +f2: U32, +nm2: B.Octets, +t2: List<&2, DW.Ext2Slot>, +name: B.Octets) -> {Bool.not(U32.is_eq(pi, 0)) == up : Bool} -> {Bool.and(Bool.not(U32.is_eq(pi, 0)), B.Octets.is_eq(pnm, name)) == False{} : Bool} -> {Bool.and(Bool.not(U32.is_eq(i2, 0)), B.Octets.is_eq(nm2, name)) == b2 : Bool} -> ({Bool.and(Bool.not(U32.is_eq(i2, 0)), B.Octets.is_eq(nm2, name)) == False{} : Bool} -> {Laws.Ext2Laws.names_or(DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name) : List<&2, DW.Ext2Name>}) -> {Laws.Ext2Laws.names_or(DW.Ext2Slots.rm.pick(b2, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slot{i2, r2, f2, nm2}, t2, DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name)), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(pi, 0)), DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2))), name)) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(pi, 0)), DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2))), name) : List<&2, DW.Ext2Name>}:
  match up b2:
    case True{} True{}:
      +hup => hp => +hb2 => ih =>
        +hu2 = Ext2Proof.and_l(Bool.not(U32.is_eq(i2, 0)), B.Octets.is_eq(nm2, name), hb2)
        +he2 = Ext2Proof.and_r(Bool.not(U32.is_eq(i2, 0)), B.Octets.is_eq(nm2, name), hb2)
        +hep = Ext2Proof.and_true_r(Bool.not(U32.is_eq(pi, 0)), B.Octets.is_eq(pnm, name), hup, hp)
        %Equal.sym(Bool, Bool.not(U32.is_eq(pi, 0)), True{}, hup) : {DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, Nat.add(pr, r2), pf, pnm}, DW.Ext2Slots.names(t2)) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2))), name) : List<&2, DW.Ext2Name>}
        %Equal.sym(Bool, B.Octets.is_eq(pnm, name), False{}, hep) : {Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Slots.names(t2)} == DW.Ext2Names.unname.pick(_, DW.Ext2Name{pi, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)) : List<&2, DW.Ext2Name>}
        %Equal.sym(Bool, Bool.not(U32.is_eq(i2, 0)), True{}, hu2) : {Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Slots.names(t2)} == Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)} : List<&2, DW.Ext2Name>}
        %Equal.sym(Bool, B.Octets.is_eq(nm2, name), True{}, he2) : {Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Slots.names(t2)} == Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Names.unname.pick(_, DW.Ext2Name{i2, f2, nm2}, DW.Ext2Slots.names(t2), DW.Ext2Names.unname(DW.Ext2Slots.names(t2), name))} : List<&2, DW.Ext2Name>}
        {==}
    case True{} False{}:
      +hup => hp => +hb2 => ih =>
        +hep = Ext2Proof.and_true_r(Bool.not(U32.is_eq(pi, 0)), B.Octets.is_eq(pnm, name), hup, hp)
        %Equal.sym(Bool, Bool.not(U32.is_eq(pi, 0)), True{}, hup) : {Laws.Ext2Laws.names_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name)), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2))), name)) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2))), name) : List<&2, DW.Ext2Name>}
        %Equal.sym(Bool, B.Octets.is_eq(pnm, name), False{}, hep) : {Laws.Ext2Laws.names_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name)), DW.Ext2Names.unname.pick(_, DW.Ext2Name{pi, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name))) == DW.Ext2Names.unname.pick(_, DW.Ext2Name{pi, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)) : List<&2, DW.Ext2Name>}
        %Equal.sym(List<&2, DW.Ext2Name>, Laws.Ext2Laws.names_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name)), Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)}), Con{DW.Ext2Name{pi, pf, pnm}, Laws.Ext2Laws.names_or(DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name))}, Ext2Proof.cons_names_used(pi, pr, pf, pnm, DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name), hup)) : {_ == Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)} : List<&2, DW.Ext2Name>}
        %Equal.sym(List<&2, DW.Ext2Name>, Laws.Ext2Laws.names_or(DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name), ih(hb2)) : {Con{DW.Ext2Name{pi, pf, pnm}, _} == Con{DW.Ext2Name{pi, pf, pnm}, DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)} : List<&2, DW.Ext2Name>}
        {==}
    case False{} True{}:
      +hup => hp => +hb2 => ih =>
        +hu2 = Ext2Proof.and_l(Bool.not(U32.is_eq(i2, 0)), B.Octets.is_eq(nm2, name), hb2)
        +he2 = Ext2Proof.and_r(Bool.not(U32.is_eq(i2, 0)), B.Octets.is_eq(nm2, name), hb2)
        %Equal.sym(Bool, Bool.not(U32.is_eq(pi, 0)), False{}, hup) : {DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, Nat.add(pr, r2), pf, pnm}, DW.Ext2Slots.names(t2)) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2))), name) : List<&2, DW.Ext2Name>}
        %Equal.sym(Bool, Bool.not(U32.is_eq(i2, 0)), True{}, hu2) : {DW.Ext2Slots.names(t2) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name) : List<&2, DW.Ext2Name>}
        %Equal.sym(Bool, B.Octets.is_eq(nm2, name), True{}, he2) : {DW.Ext2Slots.names(t2) == DW.Ext2Names.unname.pick(_, DW.Ext2Name{i2, f2, nm2}, DW.Ext2Slots.names(t2), DW.Ext2Names.unname(DW.Ext2Slots.names(t2), name)) : List<&2, DW.Ext2Name>}
        {==}
    case False{} False{}:
      +hup => hp => +hb2 => ih =>
        %Equal.sym(Bool, Bool.not(U32.is_eq(pi, 0)), False{}, hup) : {Laws.Ext2Laws.names_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name)), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2))), name)) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2))), name) : List<&2, DW.Ext2Name>}
        %Equal.sym(List<&2, DW.Ext2Name>, Laws.Ext2Laws.names_or(DW.Ext2Slots.cons_some(DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name)), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)), Laws.Ext2Laws.names_or(DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name)), Ext2Proof.cons_names_unused(pi, pr, pf, pnm, DW.Ext2Slots.rm(t2, DW.Ext2Slot{i2, r2, f2, nm2}, name), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name), hup)) : {_ == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i2, 0)), DW.Ext2Slot{i2, r2, f2, nm2}, DW.Ext2Slots.names(t2)), name) : List<&2, DW.Ext2Name>}
        ih(hb2)

# the slots after prev (used or not, not named name), one entry named name
# merged into the slot before it: the names are the old ones without it
def Ext2Proof.rm_names(ss: List<&2, DW.Ext2Slot>, +pi: U32, +pr: Nat, +pf: U32, +pnm: B.Octets, +name: B.Octets) -> {Bool.and(Bool.not(U32.is_eq(pi, 0)), B.Octets.is_eq(pnm, name)) == False{} : Bool} -> {Laws.Ext2Laws.names_or(DW.Ext2Slots.rm(ss, DW.Ext2Slot{pi, pr, pf, pnm}, name), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(pi, 0)), DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names(ss)), name)) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(pi, 0)), DW.Ext2Slot{pi, pr, pf, pnm}, DW.Ext2Slots.names(ss)), name) : List<&2, DW.Ext2Name>}:
  match ss:
    case Nil{}:
      hp => {==}
    case Con{DW.Ext2Slot{+i2, +r2, +f2, +nm2}, +t2}:
      hp => Ext2Proof.rm_names.step(Bool.not(U32.is_eq(pi, 0)), Bool.and(Bool.not(U32.is_eq(i2, 0)), B.Octets.is_eq(nm2, name)), pi, pr, pf, pnm, i2, r2, f2, nm2, t2, name, {==}, hp, {==}, hp2 => Ext2Proof.rm_names(t2, i2, r2, f2, nm2, name, hp2))

def Ext2Proof.rem_names.step(b: Bool, +i: U32, +r: Nat, +f: U32, +nm: B.Octets, +t: List<&2, DW.Ext2Slot>, +name: B.Octets) -> {Bool.and(Bool.not(U32.is_eq(i, 0)), B.Octets.is_eq(nm, name)) == b : Bool} -> {Laws.Ext2Laws.names_or(DW.Ext2Slots.remove.pick(b, DW.Ext2Slot{i, r, f, nm}, t, name), DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i, 0)), DW.Ext2Slot{i, r, f, nm}, DW.Ext2Slots.names(t)), name)) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(Bool.not(U32.is_eq(i, 0)), DW.Ext2Slot{i, r, f, nm}, DW.Ext2Slots.names(t)), name) : List<&2, DW.Ext2Name>}:
  match b:
    case True{}:
      +hb =>
        +hu = Ext2Proof.and_l(Bool.not(U32.is_eq(i, 0)), B.Octets.is_eq(nm, name), hb)
        +he = Ext2Proof.and_r(Bool.not(U32.is_eq(i, 0)), B.Octets.is_eq(nm, name), hb)
        %Equal.sym(Bool, Bool.not(U32.is_eq(i, 0)), True{}, hu) : {DW.Ext2Slots.names(t) == DW.Ext2Names.unname(DW.Ext2Slots.names.keep(_, DW.Ext2Slot{i, r, f, nm}, DW.Ext2Slots.names(t)), name) : List<&2, DW.Ext2Name>}
        %Equal.sym(Bool, B.Octets.is_eq(nm, name), True{}, he) : {DW.Ext2Slots.names(t) == DW.Ext2Names.unname.pick(_, DW.Ext2Name{i, f, nm}, DW.Ext2Slots.names(t), DW.Ext2Names.unname(DW.Ext2Slots.names(t), name)) : List<&2, DW.Ext2Name>}
        {==}
    case False{}:
      hb => Ext2Proof.rm_names(t, i, r, f, nm, name, hb)

# removing an entry: the names are the old ones without it
def Ext2Proof.rem_names(ss: List<&2, DW.Ext2Slot>, +name: B.Octets) -> {Laws.Ext2Laws.names_or(DW.Ext2Slots.remove(ss, name), DW.Ext2Names.unname(DW.Ext2Slots.names(ss), name)) == DW.Ext2Names.unname(DW.Ext2Slots.names(ss), name) : List<&2, DW.Ext2Name>}:
  match ss:
    case Nil{}:
      {==}
    case Con{DW.Ext2Slot{+i, +r, +f, +nm}, +t}:
      Ext2Proof.rem_names.step(Bool.and(Bool.not(U32.is_eq(i, 0)), B.Octets.is_eq(nm, name)), i, r, f, nm, t, name, {==})

def Ext2Proof.res_disc(r: Result<&2, &2, E.Ext2Error, Unit>) -> Type:
  match r:
    case Done{u}:
      Unit
    case Fail{e}:
      Empty

def Ext2Proof.res_clash(e: E.Ext2Error, h: {Fail{e} == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>}) -> Empty:
  %Equal.sym(Result<&2, &2, E.Ext2Error, Unit>, Fail{e}, Done{Unit{}}, h) : Ext2Proof.res_disc(_)
  Unit{}

# a check that passed: what its first step checked passed
def Ext2Proof.first_holds(c: Result<&2, &2, E.Ext2Error, Unit>, rest: Unit -> Result<&2, &2, E.Ext2Error, Unit>) -> {Result.bind(&2, &2, E.Ext2Error, Unit, Unit, c, rest) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {Laws.Ext2Laws.holds(c) == True{} : Bool}:
  match c:
    case Done{u}:
      h => {==}
    case Fail{e}:
      h => Ext2Proof.ex_falso({Laws.Ext2Laws.holds(Fail{e}) == True{} : Bool}, Ext2Proof.res_clash(e, h))

# a confirmed result: its device passed the check
def Ext2Proof.confirm_after(p: Result<&2, &2, E.Ext2Error, Unit>, +d2: D.MemDev, q: D.MemDev -> Bool) -> ({p == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {q(d2) == True{} : Bool}) -> {Laws.Ext2Laws.after(RN.Ext2Op.confirm(D.MemDev, p, d2), q) == True{} : Bool}:
  match p:
    case Done{u}:
      match u:
        case Unit{}:
          hp => hp({==})
    case Fail{e}:
      hp => {==}

# every device a checked result answers passes its check (and so satisfies
# q, when the check implies q)
def Ext2Proof.checked_after(r: Result<&2, &2, E.Ext2Error, D.MemDev>, k: D.MemDev -> Result<&2, &2, E.Ext2Error, Unit>, q: D.MemDev -> Bool) -> (@d2: D.MemDev -> {k(d2) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {q(d2) == True{} : Bool}) -> {Laws.Ext2Laws.after(RN.Ext2Op.checked(D.MemDev, r, k), q) == True{} : Bool}:
  match r:
    case Fail{e}:
      hk => {==}
    case Done{+d2}:
      hk => Ext2Proof.confirm_after(k(d2), d2, q, hk(d2))

# A check that passed: the steps after its first passed
def Ext2Proof.then_holds(c: Result<&2, &2, E.Ext2Error, Unit>, rest: Result<&2, &2, E.Ext2Error, Unit>) -> {Result.bind(&2, &2, E.Ext2Error, Unit, Unit, c, v => rest) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {rest == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>}:
  match c:
    case Done{u}:
      h => h
    case Fail{e}:
      h => Ext2Proof.ex_falso({rest == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>}, Ext2Proof.res_clash(e, h))

# ... and its first step passed
def Ext2Proof.first_done(c: Result<&2, &2, E.Ext2Error, Unit>, rest: Unit -> Result<&2, &2, E.Ext2Error, Unit>) -> {Result.bind(&2, &2, E.Ext2Error, Unit, Unit, c, rest) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {c == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>}:
  match c:
    case Done{u}:
      match u:
        case Unit{}:
          h => {==}
    case Fail{e}:
      h => Ext2Proof.ex_falso({Fail{e} == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>}, Ext2Proof.res_clash(e, h))

# a promise required to hold: it held
def Ext2Proof.yes_of(pr: Result<&2, &2, E.Ext2Error, Bool>, +e: E.Ext2Error) -> {Result.bind(&2, &2, E.Ext2Error, Bool, Unit, pr, b => S.Ext2.require(b, e)) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {Laws.Ext2Laws.yes(pr) == True{} : Bool}:
  match pr:
    case Done{b}:
      match b:
        case True{}:
          h => {==}
        case False{}:
          h => Ext2Proof.ex_falso({False{} == True{} : Bool}, Ext2Proof.res_clash(e, h))
    case Fail{x}:
      h => Ext2Proof.ex_falso({False{} == True{} : Bool}, Ext2Proof.res_clash(x, h))

# every device a checked operation answers satisfies q, when passing the
# local check and passing the full one each imply q
def Ext2Proof.run_after(wo: WO.Ext2WriteOptions, +d: D.MemDev, +fs: S.Ext2Fs, +op: P.Ext2Op, q: D.MemDev -> Bool, hl: @d2: D.MemDev -> {RN.Ext2Guard.post(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, WO.Ext2CheckLocal{}, op, d, d2, fs) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {q(d2) == True{} : Bool}, hf: @d2: D.MemDev -> {RN.Ext2Guard.post(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, WO.Ext2CheckFull{}, op, d, d2, fs) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {q(d2) == True{} : Bool}) -> {WO.Ext2CheckLevel.any(WO.Ext2WriteOptions.check(wo)) == True{} : Bool} -> {Laws.Ext2Laws.after(Laws.Ext2Laws.run(op, d, fs, wo), q) == True{} : Bool}:
  match wo:
    case WO.Ext2WriteOptions{+a, +c, k, +x, +t, +u, +g}:
      match k:
        case WO.Ext2CheckNone{}:
          h => Ext2Proof.ex_falso({Laws.Ext2Laws.after(Laws.Ext2Laws.run(op, d, fs, WO.Ext2WriteOptions{a, c, WO.Ext2CheckNone{}, x, t, u, g}), q) == True{} : Bool}, Ext2Proof.bool_clash(h))
        case WO.Ext2CheckLocal{}:
          h => Ext2Proof.checked_after(P.Ext2Op.apply(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, op, d, fs, WO.Ext2WriteOptions{a, c, WO.Ext2CheckLocal{}, x, t, u, g}), d2 => RN.Ext2Guard.post(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, WO.Ext2CheckLocal{}, op, d, d2, fs), q, hl)
        case WO.Ext2CheckFull{}:
          h => Ext2Proof.checked_after(P.Ext2Op.apply(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, op, d, fs, WO.Ext2WriteOptions{a, c, WO.Ext2CheckFull{}, x, t, u, g}), d2 => RN.Ext2Guard.post(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, WO.Ext2CheckFull{}, op, d, d2, fs), q, hf)

# the same with the full check alone
def Ext2Proof.run_after_full(wo: WO.Ext2WriteOptions, +d: D.MemDev, +fs: S.Ext2Fs, +op: P.Ext2Op, q: D.MemDev -> Bool, hf: @d2: D.MemDev -> {RN.Ext2Guard.post(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, WO.Ext2CheckFull{}, op, d, d2, fs) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {q(d2) == True{} : Bool}) -> {WO.Ext2CheckLevel.full(WO.Ext2WriteOptions.check(wo)) == True{} : Bool} -> {Laws.Ext2Laws.after(Laws.Ext2Laws.run(op, d, fs, wo), q) == True{} : Bool}:
  match wo:
    case WO.Ext2WriteOptions{+a, +c, k, +x, +t, +u, +g}:
      match k:
        case WO.Ext2CheckNone{}:
          h => Ext2Proof.ex_falso({Laws.Ext2Laws.after(Laws.Ext2Laws.run(op, d, fs, WO.Ext2WriteOptions{a, c, WO.Ext2CheckNone{}, x, t, u, g}), q) == True{} : Bool}, Ext2Proof.bool_clash(h))
        case WO.Ext2CheckLocal{}:
          h => Ext2Proof.ex_falso({Laws.Ext2Laws.after(Laws.Ext2Laws.run(op, d, fs, WO.Ext2WriteOptions{a, c, WO.Ext2CheckLocal{}, x, t, u, g}), q) == True{} : Bool}, Ext2Proof.bool_clash(h))
        case WO.Ext2CheckFull{}:
          h => Ext2Proof.checked_after(P.Ext2Op.apply(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, op, d, fs, WO.Ext2WriteOptions{a, c, WO.Ext2CheckFull{}, x, t, u, g}), d2 => RN.Ext2Guard.post(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, WO.Ext2CheckFull{}, op, d, d2, fs), q, hf)

def Ext2Proof.promise_error() -> E.Ext2Error:
  E.Ext2CheckFailed{"the operation did not do what it promised"}

# every answer of a checked operation is what it promised
def Ext2Proof.promise_after(wo: WO.Ext2WriteOptions, +d: D.MemDev, +fs: S.Ext2Fs, +op: P.Ext2Op) -> {WO.Ext2CheckLevel.any(WO.Ext2WriteOptions.check(wo)) == True{} : Bool} -> {Laws.Ext2Laws.after(Laws.Ext2Laws.run(op, d, fs, wo), d2 => Laws.Ext2Laws.yes(RN.Ext2Guard.promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs))) == True{} : Bool}:
  Ext2Proof.run_after(wo, d, fs, op, d2 => Laws.Ext2Laws.yes(RN.Ext2Guard.promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs)), +d2 => hp => Ext2Proof.yes_of(RN.Ext2Guard.promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), Ext2Proof.promise_error(), Ext2Proof.then_holds(FK.Ext2Fsck.counts(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), RN.Ext2Guard.kept_promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), hp)), +d2 => hp => Ext2Proof.yes_of(RN.Ext2Guard.promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), Ext2Proof.promise_error(), Ext2Proof.first_done(RN.Ext2Guard.kept_promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), w => FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), Ext2Proof.then_holds(FK.Ext2Fsck.counts(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), Result.bind(&2, &2, E.Ext2Error, Unit, Unit, RN.Ext2Guard.kept_promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), w => FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs)), hp))))

def Laws.run_counts(d, fs, wo, op, h):
  Ext2Proof.run_after(wo, d, fs, op, d2 => Laws.Ext2Laws.holds(FK.Ext2Fsck.counts(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs)), +d2 => hp => Ext2Proof.first_holds(FK.Ext2Fsck.counts(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), v => RN.Ext2Guard.kept_promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), hp), +d2 => hp => Ext2Proof.first_holds(FK.Ext2Fsck.counts(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), v => Result.bind(&2, &2, E.Ext2Error, Unit, Unit, RN.Ext2Guard.kept_promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), w => FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs)), hp), h)

def Laws.run_promise(d, fs, wo, op, h):
  Ext2Proof.promise_after(wo, d, fs, op, h)

def Laws.write_reads_back(d, fs, wo, path, off, data, h):
  Ext2Proof.promise_after(wo, d, fs, P.Ext2OpWrite{path, off, data}, h)

def Laws.create_keeps_others(d, fs, wo, path, mode, h):
  Ext2Proof.promise_after(wo, d, fs, P.Ext2OpCreate{path, mode}, h)

def Laws.unlink_keeps_others(d, fs, wo, path, h):
  Ext2Proof.promise_after(wo, d, fs, P.Ext2OpUnlink{path}, h)

def Laws.run_full(d, fs, wo, op, h):
  Ext2Proof.run_after_full(wo, d, fs, op, d2 => Laws.Ext2Laws.holds(FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs)), +d2 => hp => %Equal.sym(Result<&2, &2, E.Ext2Error, Unit>, FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), Done{Unit{}}, Ext2Proof.then_holds(RN.Ext2Guard.kept_promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), Ext2Proof.then_holds(FK.Ext2Fsck.counts(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), Result.bind(&2, &2, E.Ext2Error, Unit, Unit, RN.Ext2Guard.kept_promise(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, op, d, d2, fs), w => FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs)), hp))) : {Laws.Ext2Laws.holds(_) == True{} : Bool}; {==}, h)

def Laws.run_check_witness():
  {==}

def Laws.run_full_witness():
  {==}

# mkfs: its answers passed Ext2Mkfs.check (they open, and pass the full
# check)
def Ext2Proof.mk_confirm(p: Result<&2, &2, E.Ext2Error, Unit>, +d2: D.MemDev, q: D.MemDev -> Bool) -> ({p == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {q(d2) == True{} : Bool}) -> {Laws.Ext2Laws.after(MK.Ext2Mkfs.confirm(D.MemDev, p, d2), q) == True{} : Bool}:
  match p:
    case Done{u}:
      match u:
        case Unit{}:
          hp => hp({==})
    case Fail{e}:
      hp => {==}

def Ext2Proof.mk_after(r: Result<&2, &2, E.Ext2Error, D.MemDev>, q: D.MemDev -> Bool) -> (@d2: D.MemDev -> {MK.Ext2Mkfs.check(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {q(d2) == True{} : Bool}) -> {Laws.Ext2Laws.after(MK.Ext2Mkfs.checked(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, r), q) == True{} : Bool}:
  match r:
    case Fail{e}:
      hq => {==}
    case Done{+d2}:
      hq => Ext2Proof.mk_confirm(MK.Ext2Mkfs.check(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2), d2, q, hq(d2))

def Ext2Proof.fs_disc(r: Result<&2, &2, E.Ext2Error, S.Ext2Fs>) -> Type:
  match r:
    case Done{x}:
      Unit
    case Fail{e}:
      Empty

def Ext2Proof.opened(x: Result<&2, &2, E.Ext2Error, S.Ext2Fs>, k: S.Ext2Fs -> Result<&2, &2, E.Ext2Error, Unit>) -> {Result.bind(&2, &2, E.Ext2Error, S.Ext2Fs, Unit, x, k) == Done{Unit{}} : Result<&2, &2, E.Ext2Error, Unit>} -> {Result.is_done(&2, &2, E.Ext2Error, S.Ext2Fs, x) == True{} : Bool}:
  match x:
    case Done{fs}:
      h => {==}
    case Fail{e}:
      h => Ext2Proof.ex_falso({Result.is_done(&2, &2, E.Ext2Error, S.Ext2Fs, Fail{e}) == True{} : Bool}, Ext2Proof.res_clash(e, h))

def Ext2Proof.mkfs_opens(r: Result<&2, &2, E.Ext2Error, D.MemDev>) -> {Laws.Ext2Laws.after(MK.Ext2Mkfs.checked(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, r), d2 => Result.is_done(&2, &2, E.Ext2Error, S.Ext2Fs, EX.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, O.Ext2Options.default()))) == True{} : Bool}:
  Ext2Proof.mk_after(r, +d2 => Result.is_done(&2, &2, E.Ext2Error, S.Ext2Fs, EX.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, O.Ext2Options.default())), +d2 => hc => Ext2Proof.opened(EX.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, O.Ext2Options.default()), fs => FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs), hc))

def Ext2Proof.mkfs_consistent(r: Result<&2, &2, E.Ext2Error, D.MemDev>) -> {Laws.Ext2Laws.after(MK.Ext2Mkfs.checked(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, r), d2 => Laws.Ext2Laws.holds(Result.bind(&2, &2, E.Ext2Error, S.Ext2Fs, Unit, EX.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, O.Ext2Options.default()), fs => FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs)))) == True{} : Bool}:
  Ext2Proof.mk_after(r, +d2 => Laws.Ext2Laws.holds(Result.bind(&2, &2, E.Ext2Error, S.Ext2Fs, Unit, EX.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, O.Ext2Options.default()), fs => FK.Ext2Fsck.full(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2, fs))), +d2 => hc => %Equal.sym(Result<&2, &2, E.Ext2Error, Unit>, MK.Ext2Mkfs.check(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d2), Done{Unit{}}, hc) : {Laws.Ext2Laws.holds(_) == True{} : Bool}; {==})

# make is checked applied to what build wrote
def Laws.mkfs_opens(d, o):
  Ext2Proof.mkfs_opens(MK.Ext2Mkfs.build(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, d, o))

def Laws.mkfs_consistent(d, o):
  Ext2Proof.mkfs_consistent(MK.Ext2Mkfs.build(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, d, o))

# Directory blocks

def Laws.slots_insert_total(ss, n, ss2, h):
  +tot = DW.Ext2Slots.total(ss)
  %Equal.sym(Nat, DW.Ext2Slots.total(ss2), Laws.Ext2Laws.total_or(Some{ss2}, tot), {==}) : {_ == tot : Nat}
  %h : {Laws.Ext2Laws.total_or(_, tot) == tot : Nat}
  Ext2Proof.ins_total(ss, n)

def Laws.slots_remove_total(ss, name, ss2, h):
  +tot = DW.Ext2Slots.total(ss)
  %Equal.sym(Nat, DW.Ext2Slots.total(ss2), Laws.Ext2Laws.total_or(Some{ss2}, tot), {==}) : {_ == tot : Nat}
  %h : {Laws.Ext2Laws.total_or(_, tot) == tot : Nat}
  Ext2Proof.rem_total(ss, name)

def Ext2Proof.insert_names(n: DW.Ext2Slot, +ss: List<&2, DW.Ext2Slot>, +ss2: List<&2, DW.Ext2Slot>) -> {DW.Ext2Slots.lookup(ss, DW.Ext2Slot.name(n)) == None{} : Maybe<&2, DW.Ext2Slot>} -> {DW.Ext2Slot.used(n) == True{} : Bool} -> {DW.Ext2Slots.insert(ss, n) == Some{ss2} : Maybe<&2, List<&2, DW.Ext2Slot>>} -> {DW.Ext2Names.unname(DW.Ext2Slots.names(ss2), DW.Ext2Slot.name(n)) == DW.Ext2Slots.names(ss) : List<&2, DW.Ext2Name>}:
  match n:
    case DW.Ext2Slot{+ni, +nr, +nf, +nnm}:
      hl => hu => h =>
        +ns = DW.Ext2Slots.names(ss)
        %Equal.sym(List<&2, DW.Ext2Name>, DW.Ext2Names.unname(DW.Ext2Slots.names(ss2), nnm), Laws.Ext2Laws.unnamed_or(Some{ss2}, nnm, ns), {==}) : {_ == ns : List<&2, DW.Ext2Name>}
        %h : {Laws.Ext2Laws.unnamed_or(_, nnm, ns) == ns : List<&2, DW.Ext2Name>}
        Ext2Proof.ins_names(ss, ni, nr, nf, nnm, hl, hu)

def Laws.slots_insert_names(ss, n, ss2, hl, hu, h):
  Ext2Proof.insert_names(n, ss, ss2, hl, hu, h)

def Laws.slots_remove_names(ss, name, ss2, h):
  +dd = DW.Ext2Names.unname(DW.Ext2Slots.names(ss), name)
  %Equal.sym(List<&2, DW.Ext2Name>, DW.Ext2Slots.names(ss2), Laws.Ext2Laws.names_or(Some{ss2}, dd), {==}) : {_ == dd : List<&2, DW.Ext2Name>}
  %h : {Laws.Ext2Laws.names_or(_, dd) == dd : List<&2, DW.Ext2Name>}
  Ext2Proof.rem_names(ss, name)

def Laws.slots_insert_witness():
  {==}

def Laws.slots_remove_witness():
  {==}

def Laws.slots_insert_vector():
  {==}

def Laws.slots_remove_vector():
  {==}

def Laws.slots_remove_first_vector():
  {==}

def Laws.slots_insert_full_vector():
  {==}

def Laws.bitmap_make_vector():
  {==}

def Laws.bitmap_find_vector():
  {==}

def Laws.bitmap_count_vector():
  {==}

def Laws.patch_vector():
  {==}

def Laws.extent_insert_vector():
  {==}

def Laws.extent_insert_gap_vector():
  {==}

def Laws.extent_cut_vector():
  {==}
