# Proof helpers for bend-osdev-asn1: lists of bytes. Appending, cutting
# (bytes' public list layer: take, drop) and lengths; bytes' mask and byte
# (computed through bytes' public mask; byte's idempotence from bytes'
# interface laws); and Octets through bytes' interface laws.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./proof_nat.bend as AN

def al.app(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def al.len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def al.app_len(xs: List<&2, U32>, +ys: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %al.app_len(t, ys) : {1n+List.length(&2, U32, List.append(&2, U32, t, ys)) == 1n+_ : Nat}
      {==}

def al.app_nil(xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %al.app_nil(t) : {Con{h, List.append(&2, U32, t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def al.app_assoc(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>) -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %al.app_assoc(t, ys, zs) : {Con{h, List.append(&2, U32, List.append(&2, U32, t, ys), zs)} == Con{h, _} : List<&2, U32>}
      {==}

def al.take0(xs: List<&2, U32>) -> {B.take(0n, xs) == Nil{} : List<&2, U32>}:
  {==}

def al.take_app(xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.take(List.length(&2, U32, xs), List.append(&2, U32, xs, ys)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %al.take_app(t, ys) : {Con{h, B.take(List.length(&2, U32, t), List.append(&2, U32, t, ys))} == Con{h, _} : List<&2, U32>}
      {==}

def al.drop_app(xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.drop(List.length(&2, U32, xs), List.append(&2, U32, xs, ys)) == ys : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      al.drop_app(t, ys)

def al.len_take(k: Nat, xs: List<&2, U32>, +h: {Nat.is_le(k, List.length(&2, U32, xs)) == True{} : Bool}) -> {List.length(&2, U32, B.take(k, xs)) == k : Nat}:
  match k xs:
    case 0n _:
      {==}
    case 1n+j Nil{}:
      Empty.absurd({0n == 1n+j : Nat}, AN.an.ft(h))
    case 1n+ +j Con{b, +t}:
      %al.len_take(j, t, h) : {1n+List.length(&2, U32, B.take(j, t)) == 1n+_ : Nat}
      {==}

# k <= length: k + the length after dropping k = the length
def al.len_drop(k: Nat, xs: List<&2, U32>, +h: {Nat.is_le(k, List.length(&2, U32, xs)) == True{} : Bool}) -> {Nat.add(k, List.length(&2, U32, B.drop(k, xs))) == List.length(&2, U32, xs) : Nat}:
  match k xs:
    case 0n _:
      {==}
    case 1n+j Nil{}:
      Empty.absurd({Nat.add(1n+j, 0n) == 0n : Nat}, AN.an.ft(h))
    case 1n+ +j Con{b, +t}:
      %al.len_drop(j, t, h) : {1n+Nat.add(j, List.length(&2, U32, B.drop(j, t))) == 1n+_ : Nat}
      {==}

def al.take_drop(+n: Nat, +xs: List<&2, U32>) -> {List.append(&2, U32, B.take(n, xs), B.drop(n, xs)) == xs : List<&2, U32>}:
  BL.take_drop(n, xs)

# Masking

def al.mask_app(xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.mask(List.append(&2, U32, xs, ys)) == List.append(&2, U32, B.mask(xs), B.mask(ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %al.mask_app(t, ys) : {Con{B.byte(h), B.mask(List.append(&2, U32, t, ys))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def al.mask_len(xs: List<&2, U32>) -> {List.length(&2, U32, B.mask(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %al.mask_len(t) : {1n+List.length(&2, U32, B.mask(t)) == 1n+_ : Nat}
      {==}

# an Octets' bytes are already masked
def al.mask_to(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.mask(B.Octets.to_list(o)), B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.Octets.to_list(o), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), BL.octets_to_of(B.Octets.to_list(o))), Equal.cong(B.Octets, List<&2, U32>, x => B.Octets.to_list(x), B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)))

# masking twice is masking once
def al.mask_idem(+xs: List<&2, U32>) -> {B.mask(B.mask(xs)) == B.mask(xs) : List<&2, U32>}:
  %BL.octets_to_of(xs) : {B.mask(_) == B.mask(xs) : List<&2, U32>}
  %BL.octets_to_of(xs) : {B.mask(B.Octets.to_list(B.Octets.of_list(xs))) == _ : List<&2, U32>}
  al.mask_to(B.Octets.of_list(xs))

def al.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h

# a byte is fixed by byte
def al.byte_idem(+x: U32) -> {B.byte(B.byte(x)) == B.byte(x) : U32}:
  Equal.cong(List<&2, U32>, U32, l => al.head(l), B.mask(B.mask([x])), B.mask([x]), al.mask_idem([x]))

def al.mask_take(k: Nat, xs: List<&2, U32>) -> {B.mask(B.take(k, xs)) == B.take(k, B.mask(xs)) : List<&2, U32>}:
  match k xs:
    case 0n _:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+ +j Con{+b, +t}:
      %al.mask_take(j, t) : {Con{B.byte(b), B.mask(B.take(j, t))} == Con{B.byte(b), _} : List<&2, U32>}
      {==}

def al.mask_drop(k: Nat, xs: List<&2, U32>) -> {B.mask(B.drop(k, xs)) == B.drop(k, B.mask(xs)) : List<&2, U32>}:
  match k xs:
    case 0n _:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+ +j Con{b, +t}:
      al.mask_drop(j, t)

# a list fixed by mask: so are its cuts
def al.fixed_take(+xs: List<&2, U32>, +k: Nat, +h: {B.mask(xs) == xs : List<&2, U32>}) -> {B.mask(B.take(k, xs)) == B.take(k, xs) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(B.take(k, xs)), B.take(k, B.mask(xs)), al.mask_take(k, xs)) : {_ == B.take(k, xs) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(xs), xs, h) : {B.take(k, _) == B.take(k, xs) : List<&2, U32>}
  {==}

def al.fixed_drop(+xs: List<&2, U32>, +k: Nat, +h: {B.mask(xs) == xs : List<&2, U32>}) -> {B.mask(B.drop(k, xs)) == B.drop(k, xs) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(B.drop(k, xs)), B.drop(k, B.mask(xs)), al.mask_drop(k, xs)) : {_ == B.drop(k, xs) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(xs), xs, h) : {B.drop(k, _) == B.drop(k, xs) : List<&2, U32>}
  {==}

# a list fixed by mask: so are the two parts of it
def al.fixed_l(+a: List<&2, U32>, +b: List<&2, U32>, +h: {B.mask(List.append(&2, U32, a, b)) == List.append(&2, U32, a, b) : List<&2, U32>}) -> {B.mask(a) == a : List<&2, U32>}:
  +t = al.fixed_take(List.append(&2, U32, a, b), List.length(&2, U32, a), h)
  %al.take_app(a, b) : {B.mask(_) == _ : List<&2, U32>}
  t

def al.fixed_r(+a: List<&2, U32>, +b: List<&2, U32>, +h: {B.mask(List.append(&2, U32, a, b)) == List.append(&2, U32, a, b) : List<&2, U32>}) -> {B.mask(b) == b : List<&2, U32>}:
  +t = al.fixed_drop(List.append(&2, U32, a, b), List.length(&2, U32, a), h)
  %al.drop_app(a, b) : {B.mask(_) == _ : List<&2, U32>}
  t

def al.fixed_app(+a: List<&2, U32>, +b: List<&2, U32>, +ha: {B.mask(a) == a : List<&2, U32>}, +hb: {B.mask(b) == b : List<&2, U32>}) -> {B.mask(List.append(&2, U32, a, b)) == List.append(&2, U32, a, b) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(List.append(&2, U32, a, b)), List.append(&2, U32, B.mask(a), B.mask(b)), al.mask_app(a, b)) : {_ == List.append(&2, U32, a, b) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(a), a, ha) : {List.append(&2, U32, _, B.mask(b)) == List.append(&2, U32, a, b) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(b), b, hb) : {List.append(&2, U32, a, _) == List.append(&2, U32, a, b) : List<&2, U32>}
  {==}

# Octets

def al.olen(+o: B.Octets) -> {B.Octets.len(o) == List.length(&2, U32, B.Octets.to_list(o)) : Nat}:
  BL.octets_len_list(o)

def al.of_to(+o: B.Octets) -> {B.Octets.of_list(B.Octets.to_list(o)) == o : B.Octets}:
  BL.octets_of_to(o)

def al.to_of(+xs: List<&2, U32>) -> {B.Octets.to_list(B.Octets.of_list(xs)) == B.mask(xs) : List<&2, U32>}:
  BL.octets_to_of(xs)
