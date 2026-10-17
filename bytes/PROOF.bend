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
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.octets_be16_round_trip(v):
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.octets_le32_round_trip(v):
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.octets_be32_round_trip(v):
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# the eight bytes of two le32 fields come back unchanged through Octets
def field64_le(x: U32, y: U32) -> {B.w8s.to_list(B.w8s.take(8n, B.w8s.of_list(B.append(B.le32(x), B.le32(y))))) == B.append(B.le32(x), B.le32(y)) : List<&2, U32>}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# the eight bytes of two be32 fields come back unchanged through Octets
def field64_be(x: U32, y: U32) -> {B.w8s.to_list(B.w8s.take(8n, B.w8s.of_list(B.append(B.be32(x), B.be32(y))))) == B.append(B.be32(x), B.be32(y)) : List<&2, U32>}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.octets_le64_round_trip(v):
  %Equal.sym(List<&2, U32>, B.w8s.to_list(B.w8s.take(8n, B.w8s.of_list(B.le64(v)))), B.le64(v), field64_le(W.W64.lo(v), W.W64.hi(v))) : {B.le64_at(_, 0n) == Some{v} : Maybe<&2, W.W64>}
  Laws.le64_round_trip(v)

def Laws.octets_be64_round_trip(v):
  %Equal.sym(List<&2, U32>, B.w8s.to_list(B.w8s.take(8n, B.w8s.of_list(B.be64(v)))), B.be64(v), field64_be(W.W64.hi(v), W.W64.lo(v))) : {B.be64_at(_, 0n) == Some{v} : Maybe<&2, W.W64>}
  Laws.be64_round_trip(v)

# Word lists: the lemmas the Octets laws are built from

def bits8_of_bits8(w: Word(8n)) -> {B.bits8(B.of_bits8(w)) == w : Word(8n)}:
  match w:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}:
      {==}

def w8s_of_to(ws: List<&2, Word(8n)>) -> {B.w8s.of_list(B.w8s.to_list(ws)) == ws : List<&2, Word(8n)>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      %bits8_of_bits8(h) : {Con{B.bits8(B.of_bits8(h)), B.w8s.of_list(B.w8s.to_list(t))} == Con{_, t} : List<&2, Word(8n)>}
      %w8s_of_to(t) : {Con{B.bits8(B.of_bits8(h)), B.w8s.of_list(B.w8s.to_list(t))} == Con{B.bits8(B.of_bits8(h)), _} : List<&2, Word(8n)>}
      {==}

def w8s_to_of(xs: List<&2, U32>) -> {B.w8s.to_list(B.w8s.of_list(xs)) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %w8s_to_of(t) : {Con{B.of_bits8(B.bits8(h)), B.w8s.to_list(B.w8s.of_list(t))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def w8s_to_app(xs: List<&2, Word(8n)>, ys: List<&2, Word(8n)>) -> {B.w8s.to_list(List.append(&2, Word(8n), xs, ys)) == B.append(B.w8s.to_list(xs), B.w8s.to_list(ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %w8s_to_app(t, ys) : {Con{B.of_bits8(h), B.w8s.to_list(List.append(&2, Word(8n), t, ys))} == Con{B.of_bits8(h), _} : List<&2, U32>}
      {==}

def w8s_len(ws: List<&2, Word(8n)>) -> {List.length(&2, Word(8n), ws) == List.length(&2, U32, B.w8s.to_list(ws)) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Word(8n), t), List.length(&2, U32, B.w8s.to_list(t)), w8s_len(t))

def w8s_take_drop(n: Nat, ws: List<&2, Word(8n)>) -> {List.append(&2, Word(8n), B.w8s.take(n, ws), B.w8s.drop(n, ws)) == ws : List<&2, Word(8n)>}:
  match n ws:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      %w8s_take_drop(p, t) : {Con{h, List.append(&2, Word(8n), B.w8s.take(p, t), B.w8s.drop(p, t))} == Con{h, _} : List<&2, Word(8n)>}
      {==}

def w8s_take_app(xs: List<&2, Word(8n)>, ys: List<&2, Word(8n)>) -> {B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys)) == xs : List<&2, Word(8n)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %w8s_take_app(t, ys) : {Con{h, B.w8s.take(List.length(&2, Word(8n), t), List.append(&2, Word(8n), t, ys))} == Con{h, _} : List<&2, Word(8n)>}
      {==}

def w8s_drop_app(xs: List<&2, Word(8n)>, ys: List<&2, Word(8n)>) -> {B.w8s.drop(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys)) == ys : List<&2, Word(8n)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      w8s_drop_app(t, ys)

def w8s_len_app(xs: List<&2, Word(8n)>, ys: List<&2, Word(8n)>) -> {List.length(&2, Word(8n), List.append(&2, Word(8n), xs, ys)) == Nat.add(List.length(&2, Word(8n), xs), List.length(&2, Word(8n), ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Word(8n), List.append(&2, Word(8n), t, ys)), Nat.add(List.length(&2, Word(8n), t), List.length(&2, Word(8n), ys)), w8s_len_app(t, ys))

def nat_le_add(n: Nat, m: Nat) -> {Nat.is_le(n, Nat.add(n, m)) == True{} : Bool}:
  match n:
    case 0n:
      match m:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      nat_le_add(p, m)

# The Octets laws

def Laws.octets_take_drop(n, o):
  match o:
    case B.Octets{ws}:
      Equal.cong(List<&2, Word(8n)>, B.Octets, l => B.Octets{l}, List.append(&2, Word(8n), B.w8s.take(n, ws), B.w8s.drop(n, ws)), ws, w8s_take_drop(n, ws))

def Laws.octets_of_to(o):
  match o:
    case B.Octets{ws}:
      Equal.cong(List<&2, Word(8n)>, B.Octets, l => B.Octets{l}, B.w8s.of_list(B.w8s.to_list(ws)), ws, w8s_of_to(ws))

def Laws.octets_to_of(xs):
  w8s_to_of(xs)

def Laws.octets_of_list_idempotent(xs):
  Laws.octets_of_to(B.Octets.of_list(xs))


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
  list_eq_self(B.Octets.to_list(o))

def Laws.octets_masks():
  {==}

def Laws.octets_slice():
  {==}

def Laws.octets_append_list(a, b):
  match a b:
    case B.Octets{xs} B.Octets{ys}:
      w8s_to_app(xs, ys)

def Laws.octets_len_list(o):
  match o:
    case B.Octets{ws}:
      w8s_len(ws)

def Laws.octets_take_append(a, b):
  match a b:
    case B.Octets{xs} B.Octets{ys}:
      Equal.cong(List<&2, Word(8n)>, B.Octets, l => B.Octets{l}, B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys)), xs, w8s_take_app(xs, ys))

def Laws.octets_drop_append(a, b):
  match a b:
    case B.Octets{xs} B.Octets{ys}:
      Equal.cong(List<&2, Word(8n)>, B.Octets, l => B.Octets{l}, B.w8s.drop(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys)), ys, w8s_drop_app(xs, ys))

def Laws.octets_split_at_append(a, b):
  match a b:
    case B.Octets{xs} B.Octets{ys}:
      %Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), xs, ys)), Nat.add(List.length(&2, Word(8n), xs), List.length(&2, Word(8n), ys)), w8s_len_app(xs, ys)) : {B.Octets.split_at.pick(Nat.is_le(List.length(&2, Word(8n), xs), _), List.length(&2, Word(8n), xs), B.Octets{List.append(&2, Word(8n), xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %Equal.sym(Bool, Nat.is_le(List.length(&2, Word(8n), xs), Nat.add(List.length(&2, Word(8n), xs), List.length(&2, Word(8n), ys))), True{}, nat_le_add(List.length(&2, Word(8n), xs), List.length(&2, Word(8n), ys))) : {B.Octets.split_at.pick(_, List.length(&2, Word(8n), xs), B.Octets{List.append(&2, Word(8n), xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %w8s_take_app(xs, ys) : {Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}, B.Octets{B.w8s.drop(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}}} == Some{B.OctetsSplit{B.Octets{_}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %w8s_drop_app(xs, ys) : {Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}, B.Octets{B.w8s.drop(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}}} == Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}, B.Octets{_}}} : Maybe<&2, B.OctetsSplit>}
      {==}

def Laws.octets_split_short():
  {==}

def Laws.octets_split_text():
  {==}

def Laws.octets_zeros_list(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{0, l}, B.w8s.to_list(B.w8s.zeros(p)), B.zeros(p), Laws.octets_zeros_list(p))

def Laws.octets_cons_list(b, o):
  match o:
    case B.Octets{ws}:
      {==}
