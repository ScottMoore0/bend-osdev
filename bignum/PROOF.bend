import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./bignum.bend as N
import ./modular.bend as Md
import ./prime.bend as Pr
import ./jacobi.bend as J
import ./LAWS.bend as Laws

# OS2IP and I2OSP. A byte of an Octets is a masked word (B.byte), so two of
# them pack into a limb and unpack back by computation on their bits; a
# string of masked bytes packs and unpacks to itself (fit_pack); the bytes
# of an Octets are masked (to_list_mask), and reversing commutes with
# masking (rev_mask) and keeps the length (rev_len).

def le16_pack2(v: U32, w: U32) -> {B.le16(Maybe.default(&2, U32, B.le16.head([B.byte(v), B.byte(w)]), 0)) == [B.byte(v), B.byte(w)] : List<&2, U32>}:
  match v w:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}}:
      {==}

def le16_pack1(v: U32) -> {B.le16(Maybe.default(&2, U32, B.le16.head([B.byte(v), 0]), 0)) == [B.byte(v), 0] : List<&2, U32>}:
  match v:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}}:
      {==}

def fit2(+a: U32, +b: U32, n: Nat, ys: List<&2, U32>, r: List<&2, U32>, h: {N.bn.fit(n, ys) == Some{r} : Maybe<&2, List<&2, U32>>}) -> {N.bn.fit(2n+n, Con{a, Con{b, ys}}) == Some{Con{a, Con{b, r}}} : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, N.bn.fit(n, ys), Some{r}, h) : {Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{a, t}, Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{b, t}, _)) == Some{Con{a, Con{b, r}}} : Maybe<&2, List<&2, U32>>}
  {==}

def fit_pack(+s: List<&2, U32>) -> {N.bn.fit(B.len(B.mask(s)), N.bn.unpack(N.bn.pack(B.mask(s)))) == Some{B.mask(s)} : Maybe<&2, List<&2, U32>>}:
  match s:
    case Nil{}:
      {==}
    case Con{+v, Nil{}}:
      %Equal.sym(List<&2, U32>, B.le16(Maybe.default(&2, U32, B.le16.head([B.byte(v), 0]), 0)), [B.byte(v), 0], le16_pack1(v)) : {N.bn.fit(1n, B.append(_, Nil{})) == Some{[B.byte(v)]} : Maybe<&2, List<&2, U32>>}
      {==}
    case Con{+v, Con{+w, t}}:
      %Equal.sym(List<&2, U32>, B.le16(Maybe.default(&2, U32, B.le16.head([B.byte(v), B.byte(w)]), 0)), [B.byte(v), B.byte(w)], le16_pack2(v, w)) : {N.bn.fit(2n+B.len(B.mask(t)), B.append(_, N.bn.unpack(N.bn.pack(B.mask(t))))) == Some{Con{B.byte(v), Con{B.byte(w), B.mask(t)}}} : Maybe<&2, List<&2, U32>>}
      fit2(B.byte(v), B.byte(w), B.len(B.mask(t)), N.bn.unpack(N.bn.pack(B.mask(t))), B.mask(t), fit_pack(t))

def rev_mask_go(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.rev_onto(B.mask(xs), B.mask(acc)) == B.mask(B.rev_onto(xs, acc)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_mask_go(t, Con{h, acc})

def nat_add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nat_add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def nat_add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nat_add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def rev_len_go(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.len(B.rev_onto(xs, acc)) == Nat.add(B.len(xs), B.len(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Nat, B.len(B.rev_onto(t, Con{h, acc})), Nat.add(B.len(t), B.len(Con{h, acc})), rev_len_go(t, Con{h, acc})) : {_ == 1n+Nat.add(B.len(t), B.len(acc)) : Nat}
      nat_add_succ(B.len(t), B.len(acc))

def rev_len(+xs: List<&2, U32>) -> {B.len(B.rev(xs)) == B.len(xs) : Nat}:
  %Equal.sym(Nat, B.len(B.rev_onto(xs, Nil{})), Nat.add(B.len(xs), B.len(Nil{})), rev_len_go(xs, Nil{})) : {_ == B.len(xs) : Nat}
  nat_add_zero(B.len(xs))

# the bytes of an Octets are masked
def to_list_mask(+o: B.Octets) -> {B.Octets.to_list(o) == B.mask(B.Octets.to_list(o)) : List<&2, U32>}:
  %BL.octets_to_of(B.Octets.to_list(o)) : {B.Octets.to_list(o) == _ : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {B.Octets.to_list(o) == B.Octets.to_list(_) : List<&2, U32>}
  {==}

# the reversed bytes of an Octets are masked
def rev_bytes_mask(+o: B.Octets) -> {B.mask(B.rev(B.Octets.to_list(o))) == B.rev(B.Octets.to_list(o)) : List<&2, U32>}:
  %rev_mask_go(B.Octets.to_list(o), Nil{}) : {_ == B.rev(B.Octets.to_list(o)) : List<&2, U32>}
  %to_list_mask(o) : {B.rev(_) == B.rev(B.Octets.to_list(o)) : List<&2, U32>}
  {==}

def octets_fit(+o: B.Octets) -> {N.bn.fit(B.Octets.len(o), N.bn.unpack(N.bn.pack(B.rev(B.Octets.to_list(o))))) == Some{B.rev(B.Octets.to_list(o))} : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o)) : {N.bn.fit(_, N.bn.unpack(N.bn.pack(B.rev(B.Octets.to_list(o))))) == Some{B.rev(B.Octets.to_list(o))} : Maybe<&2, List<&2, U32>>}
  %rev_len(B.Octets.to_list(o)) : {N.bn.fit(_, N.bn.unpack(N.bn.pack(B.rev(B.Octets.to_list(o))))) == Some{B.rev(B.Octets.to_list(o))} : Maybe<&2, List<&2, U32>>}
  %rev_bytes_mask(o) : {N.bn.fit(B.len(_), N.bn.unpack(N.bn.pack(_))) == Some{_} : Maybe<&2, List<&2, U32>>}
  fit_pack(B.rev(B.Octets.to_list(o)))

def Laws.octets_round_trip(o):
  %Equal.sym(Maybe<&2, List<&2, U32>>, N.bn.fit(B.Octets.len(o), N.bn.unpack(N.bn.pack(B.rev(B.Octets.to_list(o))))), Some{B.rev(B.Octets.to_list(o))}, octets_fit(o)) : {Maybe.map(&2, List<&2, U32>, B.Octets, r => B.Octets.of_list(B.rev(r)), _) == Some{o} : Maybe<&2, B.Octets>}
  %Equal.sym(List<&2, U32>, B.rev(B.rev(B.Octets.to_list(o))), B.Octets.to_list(o), BL.rev_rev(B.Octets.to_list(o))) : {Some{B.Octets.of_list(_)} == Some{o} : Maybe<&2, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {Some{_} == Some{o} : Maybe<&2, B.Octets>}
  {==}

# Small-parameter exhaustive laws

# BEGIN GENERATED by gen/exhaustive.py: exhaustive
def ex.bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ex.absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : ex.bdisc(_)
  Unit{}

def ex.exp_mont_small.c0_0() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c0_1() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c0_2() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c0_3() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c0_4() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c0_5() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c0_6() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c1_0() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c1_1() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c1_2() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c1_3() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c1_4() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c1_5() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c1_6() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c2_0() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c2_1() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c2_2() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c2_3() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c2_4() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c2_5() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c2_6() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c3_0() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c3_1() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c3_2() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c3_3() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c3_4() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c3_5() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c3_6() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c4_0() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c4_1() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c4_2() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c4_3() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c4_4() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c4_5() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c4_6() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c5_0() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c5_1() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c5_2() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c5_3() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c5_4() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c5_5() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c5_6() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c6_0() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(0n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c6_1() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(1n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c6_2() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(2n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c6_3() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(3n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c6_4() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(4n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c6_5() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(5n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def ex.exp_mont_small.c6_6() -> {N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(6n), N.BnNat.of_u32(7))) == True{} : Bool}:
  {==}

def Laws.exp_mont_small(x, e, hx, he):
  match x:
    case 0n:
      match e:
        case 0n:
          ex.exp_mont_small.c0_0()
        case 1n+e0:
          match e0:
            case 0n:
              ex.exp_mont_small.c0_1()
            case 1n+e1:
              match e1:
                case 0n:
                  ex.exp_mont_small.c0_2()
                case 1n+e2:
                  match e2:
                    case 0n:
                      ex.exp_mont_small.c0_3()
                    case 1n+e3:
                      match e3:
                        case 0n:
                          ex.exp_mont_small.c0_4()
                        case 1n+e4:
                          match e4:
                            case 0n:
                              ex.exp_mont_small.c0_5()
                            case 1n+e5:
                              match e5:
                                case 0n:
                                  ex.exp_mont_small.c0_6()
                                case 1n+e6:
                                  match e6:
                                    case 0n:
                                      Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                                    case 1n+ez:
                                      Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(0n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
    case 1n+x0:
      match x0:
        case 0n:
          match e:
            case 0n:
              ex.exp_mont_small.c1_0()
            case 1n+e0:
              match e0:
                case 0n:
                  ex.exp_mont_small.c1_1()
                case 1n+e1:
                  match e1:
                    case 0n:
                      ex.exp_mont_small.c1_2()
                    case 1n+e2:
                      match e2:
                        case 0n:
                          ex.exp_mont_small.c1_3()
                        case 1n+e3:
                          match e3:
                            case 0n:
                              ex.exp_mont_small.c1_4()
                            case 1n+e4:
                              match e4:
                                case 0n:
                                  ex.exp_mont_small.c1_5()
                                case 1n+e5:
                                  match e5:
                                    case 0n:
                                      ex.exp_mont_small.c1_6()
                                    case 1n+e6:
                                      match e6:
                                        case 0n:
                                          Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                                        case 1n+ez:
                                          Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(1n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
        case 1n+x1:
          match x1:
            case 0n:
              match e:
                case 0n:
                  ex.exp_mont_small.c2_0()
                case 1n+e0:
                  match e0:
                    case 0n:
                      ex.exp_mont_small.c2_1()
                    case 1n+e1:
                      match e1:
                        case 0n:
                          ex.exp_mont_small.c2_2()
                        case 1n+e2:
                          match e2:
                            case 0n:
                              ex.exp_mont_small.c2_3()
                            case 1n+e3:
                              match e3:
                                case 0n:
                                  ex.exp_mont_small.c2_4()
                                case 1n+e4:
                                  match e4:
                                    case 0n:
                                      ex.exp_mont_small.c2_5()
                                    case 1n+e5:
                                      match e5:
                                        case 0n:
                                          ex.exp_mont_small.c2_6()
                                        case 1n+e6:
                                          match e6:
                                            case 0n:
                                              Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                                            case 1n+ez:
                                              Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(2n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
            case 1n+x2:
              match x2:
                case 0n:
                  match e:
                    case 0n:
                      ex.exp_mont_small.c3_0()
                    case 1n+e0:
                      match e0:
                        case 0n:
                          ex.exp_mont_small.c3_1()
                        case 1n+e1:
                          match e1:
                            case 0n:
                              ex.exp_mont_small.c3_2()
                            case 1n+e2:
                              match e2:
                                case 0n:
                                  ex.exp_mont_small.c3_3()
                                case 1n+e3:
                                  match e3:
                                    case 0n:
                                      ex.exp_mont_small.c3_4()
                                    case 1n+e4:
                                      match e4:
                                        case 0n:
                                          ex.exp_mont_small.c3_5()
                                        case 1n+e5:
                                          match e5:
                                            case 0n:
                                              ex.exp_mont_small.c3_6()
                                            case 1n+e6:
                                              match e6:
                                                case 0n:
                                                  Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                                                case 1n+ez:
                                                  Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(3n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                case 1n+x3:
                  match x3:
                    case 0n:
                      match e:
                        case 0n:
                          ex.exp_mont_small.c4_0()
                        case 1n+e0:
                          match e0:
                            case 0n:
                              ex.exp_mont_small.c4_1()
                            case 1n+e1:
                              match e1:
                                case 0n:
                                  ex.exp_mont_small.c4_2()
                                case 1n+e2:
                                  match e2:
                                    case 0n:
                                      ex.exp_mont_small.c4_3()
                                    case 1n+e3:
                                      match e3:
                                        case 0n:
                                          ex.exp_mont_small.c4_4()
                                        case 1n+e4:
                                          match e4:
                                            case 0n:
                                              ex.exp_mont_small.c4_5()
                                            case 1n+e5:
                                              match e5:
                                                case 0n:
                                                  ex.exp_mont_small.c4_6()
                                                case 1n+e6:
                                                  match e6:
                                                    case 0n:
                                                      Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                                                    case 1n+ez:
                                                      Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(4n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                    case 1n+x4:
                      match x4:
                        case 0n:
                          match e:
                            case 0n:
                              ex.exp_mont_small.c5_0()
                            case 1n+e0:
                              match e0:
                                case 0n:
                                  ex.exp_mont_small.c5_1()
                                case 1n+e1:
                                  match e1:
                                    case 0n:
                                      ex.exp_mont_small.c5_2()
                                    case 1n+e2:
                                      match e2:
                                        case 0n:
                                          ex.exp_mont_small.c5_3()
                                        case 1n+e3:
                                          match e3:
                                            case 0n:
                                              ex.exp_mont_small.c5_4()
                                            case 1n+e4:
                                              match e4:
                                                case 0n:
                                                  ex.exp_mont_small.c5_5()
                                                case 1n+e5:
                                                  match e5:
                                                    case 0n:
                                                      ex.exp_mont_small.c5_6()
                                                    case 1n+e6:
                                                      match e6:
                                                        case 0n:
                                                          Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                                                        case 1n+ez:
                                                          Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(5n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                        case 1n+x5:
                          match x5:
                            case 0n:
                              match e:
                                case 0n:
                                  ex.exp_mont_small.c6_0()
                                case 1n+e0:
                                  match e0:
                                    case 0n:
                                      ex.exp_mont_small.c6_1()
                                    case 1n+e1:
                                      match e1:
                                        case 0n:
                                          ex.exp_mont_small.c6_2()
                                        case 1n+e2:
                                          match e2:
                                            case 0n:
                                              ex.exp_mont_small.c6_3()
                                            case 1n+e3:
                                              match e3:
                                                case 0n:
                                                  ex.exp_mont_small.c6_4()
                                                case 1n+e4:
                                                  match e4:
                                                    case 0n:
                                                      ex.exp_mont_small.c6_5()
                                                    case 1n+e5:
                                                      match e5:
                                                        case 0n:
                                                          ex.exp_mont_small.c6_6()
                                                        case 1n+e6:
                                                          match e6:
                                                            case 0n:
                                                              Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(7n), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                                                            case 1n+ez:
                                                              Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(6n), Laws.bnlaw.nat(8n+ez), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(he))
                            case 1n+x6:
                              match x6:
                                case 0n:
                                  Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(7n), Laws.bnlaw.nat(e), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(7n), Laws.bnlaw.nat(e), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(hx))
                                case 1n+xz:
                                  Empty.absurd({N.BnNat.is_eq(Md.BnMod.exp(Laws.bnlaw.nat(8n+xz), Laws.bnlaw.nat(e), N.BnNat.of_u32(7)), Md.BnMod.exp_plain(Laws.bnlaw.nat(8n+xz), Laws.bnlaw.nat(e), N.BnNat.of_u32(7))) == True{} : Bool}, ex.absurd(hx))

def ex.inv_small.c0() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(0n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c1() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(1n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c2() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(2n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c3() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(3n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c4() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(4n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c5() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(5n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c6() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(6n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c7() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(7n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c8() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(8n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c9() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(9n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c10() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(10n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def ex.inv_small.c11() -> {Laws.bnlaw.inv_ok(Laws.bnlaw.nat(11n), N.BnNat.of_u32(12)) == True{} : Bool}:
  {==}

def Laws.inv_small(a, ha):
  match a:
    case 0n:
      ex.inv_small.c0()
    case 1n+a0:
      match a0:
        case 0n:
          ex.inv_small.c1()
        case 1n+a1:
          match a1:
            case 0n:
              ex.inv_small.c2()
            case 1n+a2:
              match a2:
                case 0n:
                  ex.inv_small.c3()
                case 1n+a3:
                  match a3:
                    case 0n:
                      ex.inv_small.c4()
                    case 1n+a4:
                      match a4:
                        case 0n:
                          ex.inv_small.c5()
                        case 1n+a5:
                          match a5:
                            case 0n:
                              ex.inv_small.c6()
                            case 1n+a6:
                              match a6:
                                case 0n:
                                  ex.inv_small.c7()
                                case 1n+a7:
                                  match a7:
                                    case 0n:
                                      ex.inv_small.c8()
                                    case 1n+a8:
                                      match a8:
                                        case 0n:
                                          ex.inv_small.c9()
                                        case 1n+a9:
                                          match a9:
                                            case 0n:
                                              ex.inv_small.c10()
                                            case 1n+a10:
                                              match a10:
                                                case 0n:
                                                  ex.inv_small.c11()
                                                case 1n+a11:
                                                  match a11:
                                                    case 0n:
                                                      Empty.absurd({Laws.bnlaw.inv_ok(Laws.bnlaw.nat(12n), N.BnNat.of_u32(12)) == True{} : Bool}, ex.absurd(ha))
                                                    case 1n+az:
                                                      Empty.absurd({Laws.bnlaw.inv_ok(Laws.bnlaw.nat(13n+az), N.BnNat.of_u32(12)) == True{} : Bool}, ex.absurd(ha))

def ex.jacobi_small.c0() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(0n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c1() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(1n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c2() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(2n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c3() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(3n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c4() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(4n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c5() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(5n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c6() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(6n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c7() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(7n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c8() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(8n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c9() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(9n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def ex.jacobi_small.c10() -> {Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(10n), N.BnNat.of_u32(11)) == True{} : Bool}:
  {==}

def Laws.jacobi_small(a, ha):
  match a:
    case 0n:
      ex.jacobi_small.c0()
    case 1n+a0:
      match a0:
        case 0n:
          ex.jacobi_small.c1()
        case 1n+a1:
          match a1:
            case 0n:
              ex.jacobi_small.c2()
            case 1n+a2:
              match a2:
                case 0n:
                  ex.jacobi_small.c3()
                case 1n+a3:
                  match a3:
                    case 0n:
                      ex.jacobi_small.c4()
                    case 1n+a4:
                      match a4:
                        case 0n:
                          ex.jacobi_small.c5()
                        case 1n+a5:
                          match a5:
                            case 0n:
                              ex.jacobi_small.c6()
                            case 1n+a6:
                              match a6:
                                case 0n:
                                  ex.jacobi_small.c7()
                                case 1n+a7:
                                  match a7:
                                    case 0n:
                                      ex.jacobi_small.c8()
                                    case 1n+a8:
                                      match a8:
                                        case 0n:
                                          ex.jacobi_small.c9()
                                        case 1n+a9:
                                          match a9:
                                            case 0n:
                                              ex.jacobi_small.c10()
                                            case 1n+a10:
                                              match a10:
                                                case 0n:
                                                  Empty.absurd({Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(11n), N.BnNat.of_u32(11)) == True{} : Bool}, ex.absurd(ha))
                                                case 1n+az:
                                                  Empty.absurd({Laws.bnlaw.jacobi_ok(Laws.bnlaw.nat(12n+az), N.BnNat.of_u32(11)) == True{} : Bool}, ex.absurd(ha))
# END GENERATED: exhaustive

# Vectors

def Laws.mul_vector():
  {==}

def Laws.divmod_vector():
  {==}

def Laws.modexp_vector():
  {==}

def Laws.gcd_vector():
  {==}

def Laws.inv_vector():
  {==}

def Laws.miller_rabin_561():
  {==}

def Laws.prime_65537():
  {==}

def Laws.jacobi_vector():
  {==}
