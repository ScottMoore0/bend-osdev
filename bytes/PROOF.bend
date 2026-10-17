import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./bytes.bend as B
import ./LAWS.bend as Laws

def Laws.le16_round_trip(v):
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.be16_round_trip(v):
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.le32_round_trip(v):
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.be32_round_trip(v):
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# Reading a 32-bit field at the head of a longer string, and skipping it
def le32_head_app(x: U32, r: List<&2, U32>) -> {B.le32.head(B.append(B.le32(x), r)) == Some{x} : Maybe<&2, U32>}:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def be32_head_app(x: U32, r: List<&2, U32>) -> {B.be32.head(B.append(B.be32(x), r)) == Some{x} : Maybe<&2, U32>}:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def drop4_le32(x: U32, r: List<&2, U32>) -> {B.drop(4n, B.append(B.le32(x), r)) == r : List<&2, U32>}:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def drop4_be32(x: U32, r: List<&2, U32>) -> {B.drop(4n, B.append(B.be32(x), r)) == r : List<&2, U32>}:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.le64_round_trip(v):
  %Equal.sym(Maybe<&2, U32>, B.le32_at(B.le64(v), 0n), Some{W.W64.lo(v)}, le32_head_app(W.W64.lo(v), B.le32(W.W64.hi(v)))) : {B.le64.join(_, B.le32_at(B.le64(v), 4n)) == Some{v} : Maybe<&2, W.W64>}
  %Equal.sym(Maybe<&2, U32>, B.le32_at(B.le64(v), 4n), Some{W.W64.hi(v)}, Equal.trans(Maybe<&2, U32>, B.le32_at(B.le64(v), 4n), B.le32.head(B.le32(W.W64.hi(v))), Some{W.W64.hi(v)}, Equal.cong(List<&2, U32>, Maybe<&2, U32>, l => B.le32.head(l), B.drop(4n, B.le64(v)), B.le32(W.W64.hi(v)), drop4_le32(W.W64.lo(v), B.le32(W.W64.hi(v)))), Laws.le32_round_trip(W.W64.hi(v)))) : {B.le64.join(Some{W.W64.lo(v)}, _) == Some{v} : Maybe<&2, W.W64>}
  %WL.parts_of(v) : {Some{W.W64.from_parts(W.W64.hi(v), W.W64.lo(v))} == Some{_} : Maybe<&2, W.W64>}
  {==}

def Laws.be64_round_trip(v):
  %Equal.sym(Maybe<&2, U32>, B.be32_at(B.be64(v), 0n), Some{W.W64.hi(v)}, be32_head_app(W.W64.hi(v), B.be32(W.W64.lo(v)))) : {B.le64.join(B.be32_at(B.be64(v), 4n), _) == Some{v} : Maybe<&2, W.W64>}
  %Equal.sym(Maybe<&2, U32>, B.be32_at(B.be64(v), 4n), Some{W.W64.lo(v)}, Equal.trans(Maybe<&2, U32>, B.be32_at(B.be64(v), 4n), B.be32.head(B.be32(W.W64.lo(v))), Some{W.W64.lo(v)}, Equal.cong(List<&2, U32>, Maybe<&2, U32>, l => B.be32.head(l), B.drop(4n, B.be64(v)), B.be32(W.W64.lo(v)), drop4_be32(W.W64.hi(v), B.be32(W.W64.lo(v)))), Laws.be32_round_trip(W.W64.lo(v)))) : {B.le64.join(_, Some{W.W64.hi(v)}) == Some{v} : Maybe<&2, W.W64>}
  %WL.parts_of(v) : {Some{W.W64.from_parts(W.W64.hi(v), W.W64.lo(v))} == Some{_} : Maybe<&2, W.W64>}
  {==}

def Laws.byte_below_256(b):
  match b:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.take_drop(n, xs):
  match n xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      %Laws.take_drop(p, t) : {Con{h, B.append(B.take(p, t), B.drop(p, t))} == Con{h, _} : List<&2, U32>}
      {==}

def Laws.be32_order():
  {==}

def Laws.le32_order():
  {==}

def Laws.be64_order():
  {==}

def Laws.le16_at_offset():
  {==}

def Laws.short_input():
  {==}

def Laws.at_end():
  {==}

def Laws.masks_elements():
  {==}

def Laws.hex_text():
  {==}

def Laws.octets_le16_round_trip(v):
  Laws.le16_round_trip(v)

def Laws.octets_be16_round_trip(v):
  Laws.be16_round_trip(v)

def Laws.octets_le32_round_trip(v):
  Laws.le32_round_trip(v)

def Laws.octets_be32_round_trip(v):
  Laws.be32_round_trip(v)

def Laws.octets_le64_round_trip(v):
  Laws.le64_round_trip(v)

def Laws.octets_be64_round_trip(v):
  Laws.be64_round_trip(v)

def Laws.octets_take_drop(n, o):
  match o:
    case B.Octets{xs}:
      %Laws.take_drop(n, xs) : {B.Octets{B.append(B.take(n, xs), B.drop(n, xs))} == B.Octets{_} : B.Octets}
      {==}

# masking a byte again changes nothing
def byte_idem(b: U32) -> {B.byte(B.byte(b)) == B.byte(b) : U32}:
  match b:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def mask_idem(xs: List<&2, U32>) -> {B.mask(B.mask(xs)) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %byte_idem(h) : {Con{B.byte(B.byte(h)), B.mask(B.mask(t))} == Con{_, B.mask(t)} : List<&2, U32>}
      %mask_idem(t) : {Con{B.byte(B.byte(h)), B.mask(B.mask(t))} == Con{B.byte(B.byte(h)), _} : List<&2, U32>}
      {==}

def Laws.octets_of_list_idempotent(xs):
  %mask_idem(xs) : {B.Octets{B.mask(B.mask(xs))} == B.Octets{_} : B.Octets}
  {==}

# every word compares equal to itself: induction on its bits
def bool_cmp_self(b: Bool) -> {Word.cmp.fin(b, b, EQ{}) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def word_cmp_self(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)), Word.cmp.fin(b, b, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, x => Word.cmp.fin(b, b, x), Word.cmp(p, t, t), EQ{}, word_cmp_self(p, t)),
            bool_cmp_self(b))

def u32_eq_self(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_self(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def list_eq_self(xs: List<&2, U32>) -> {B.list_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, U32.is_eq(h, h), True{}, u32_eq_self(h)) : {Bool.and(_, B.list_eq(t, t)) == True{} : Bool}
      list_eq_self(t)

def Laws.octets_is_eq_refl(o):
  match o:
    case B.Octets{xs}:
      list_eq_self(xs)

def Laws.octets_masks():
  {==}

def Laws.octets_slice():
  {==}

def Laws.octets_append_list(a, b):
  match a b:
    case B.Octets{xs} B.Octets{ys}:
      {==}
