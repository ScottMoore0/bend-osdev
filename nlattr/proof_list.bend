# Proof helpers for bend-osdev-nlattr: lists of bytes. Appending, cutting
# and lengths; bytes' mask (computed through bytes' public mask and byte);
# and Octets through bytes' interface laws.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./proof_nat.bend as NN
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

def nq.app_len(xs: List<&2, U32>, +ys: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %nq.app_len(t, ys) : {1n+List.length(&2, U32, List.append(&2, U32, t, ys)) == 1n+_ : Nat}
      {==}

def nq.take0(xs: List<&2, U32>) -> {List.take(&2, U32, xs, 0n) == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def nq.drop0(xs: List<&2, U32>) -> {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def nq.take_app(xs: List<&2, U32>, +ys: List<&2, U32>) -> {List.take(&2, U32, List.append(&2, U32, xs, ys), List.length(&2, U32, xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      nq.take0(ys)
    case Con{+h, +t}:
      %nq.take_app(t, ys) : {Con{h, List.take(&2, U32, List.append(&2, U32, t, ys), List.length(&2, U32, t))} == Con{h, _} : List<&2, U32>}
      {==}

def nq.drop_app(xs: List<&2, U32>, +ys: List<&2, U32>) -> {List.drop(&2, U32, List.append(&2, U32, xs, ys), List.length(&2, U32, xs)) == ys : List<&2, U32>}:
  match xs:
    case Nil{}:
      nq.drop0(ys)
    case Con{h, +t}:
      nq.drop_app(t, ys)

def nq.mask_app(xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.mask(List.append(&2, U32, xs, ys)) == List.append(&2, U32, B.mask(xs), B.mask(ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %nq.mask_app(t, ys) : {Con{B.byte(h), B.mask(List.append(&2, U32, t, ys))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def nq.mask_len(xs: List<&2, U32>) -> {List.length(&2, U32, B.mask(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %nq.mask_len(t) : {1n+List.length(&2, U32, B.mask(t)) == 1n+_ : Nat}
      {==}

def nq.mask_zeros(k: Nat) -> {B.mask(B.zeros(k)) == B.zeros(k) : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %nq.mask_zeros(p) : {Con{0, B.mask(B.zeros(p))} == Con{0, _} : List<&2, U32>}
      {==}

def nq.zeros_len(k: Nat) -> {List.length(&2, U32, B.zeros(k)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %nq.zeros_len(p) : {1n+List.length(&2, U32, B.zeros(p)) == 1n+_ : Nat}
      {==}

# an Octets' bytes are already masked
def nq.mask_to(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.mask(B.Octets.to_list(o)), B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.Octets.to_list(o), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), BL.octets_to_of(B.Octets.to_list(o))), Equal.cong(B.Octets, List<&2, U32>, x => B.Octets.to_list(x), B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)))

def nq.olen(+o: B.Octets) -> {B.Octets.len(o) == List.length(&2, U32, B.Octets.to_list(o)) : Nat}:
  BL.octets_len_list(o)

# the length of the Octets of a list
def nq.olen_of(+xs: List<&2, U32>) -> {B.Octets.len(B.Octets.of_list(xs)) == List.length(&2, U32, xs) : Nat}:
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(xs)), List.length(&2, U32, B.Octets.to_list(B.Octets.of_list(xs))), List.length(&2, U32, xs), BL.octets_len_list(B.Octets.of_list(xs)), Equal.trans(Nat, List.length(&2, U32, B.Octets.to_list(B.Octets.of_list(xs))), List.length(&2, U32, B.mask(xs)), List.length(&2, U32, xs), Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)), nq.mask_len(xs)))

def nq.len_take(xs: List<&2, U32>, k: Nat, +h: {Nat.is_le(k, List.length(&2, U32, xs)) == True{} : Bool}) -> {List.length(&2, U32, List.take(&2, U32, xs, k)) == k : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      Empty.absurd({0n == 1n+j : Nat}, NN.nn.ft(h))
    case Con{b, t} 0n:
      {==}
    case Con{b, +t} 1n+ +j:
      %nq.len_take(t, j, h) : {1n+List.length(&2, U32, List.take(&2, U32, t, j)) == 1n+_ : Nat}
      {==}

# k <= length: k + the length after dropping k = the length
def nq.len_drop(xs: List<&2, U32>, k: Nat, +h: {Nat.is_le(k, List.length(&2, U32, xs)) == True{} : Bool}) -> {Nat.add(k, List.length(&2, U32, List.drop(&2, U32, xs, k))) == List.length(&2, U32, xs) : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      Empty.absurd({Nat.add(1n+j, 0n) == 0n : Nat}, NN.nn.ft(h))
    case Con{b, t} 0n:
      {==}
    case Con{b, +t} 1n+ +j:
      %nq.len_drop(t, j, h) : {1n+Nat.add(j, List.length(&2, U32, List.drop(&2, U32, t, j))) == 1n+_ : Nat}
      {==}

def nq.drop_le(xs: List<&2, U32>, k: Nat) -> {Nat.is_le(List.length(&2, U32, List.drop(&2, U32, xs, k)), List.length(&2, U32, xs)) == True{} : Bool}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{b, +t} 0n:
      UL.nat_le_refl(1n+List.length(&2, U32, t))
    case Con{b, +t} 1n+ +j:
      UO.nat_le_trans(List.length(&2, U32, List.drop(&2, U32, t, j)), List.length(&2, U32, t), 1n+List.length(&2, U32, t), nq.drop_le(t, j), NN.nn.le_succ(List.length(&2, U32, t)))
