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
