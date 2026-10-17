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
def field64_le(x: U32, y: U32) -> {B.w8s.to_list.fast(B.w8s.take.fast(8n, B.w8s.of_list.fast(B.append(B.le32(x), B.le32(y))))) == B.append(B.le32(x), B.le32(y)) : List<&2, U32>}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# the eight bytes of two be32 fields come back unchanged through Octets
def field64_be(x: U32, y: U32) -> {B.w8s.to_list.fast(B.w8s.take.fast(8n, B.w8s.of_list.fast(B.append(B.be32(x), B.be32(y))))) == B.append(B.be32(x), B.be32(y)) : List<&2, U32>}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.octets_le64_round_trip(v):
  %Equal.sym(List<&2, U32>, B.w8s.to_list.fast(B.w8s.take.fast(8n, B.w8s.of_list.fast(B.le64(v)))), B.le64(v), field64_le(W.W64.lo(v), W.W64.hi(v))) : {B.le64_at(_, 0n) == Some{v} : Maybe<&2, W.W64>}
  Laws.le64_round_trip(v)

def Laws.octets_be64_round_trip(v):
  %Equal.sym(List<&2, U32>, B.w8s.to_list.fast(B.w8s.take.fast(8n, B.w8s.of_list.fast(B.be64(v)))), B.be64(v), field64_be(W.W64.hi(v), W.W64.lo(v))) : {B.be64_at(_, 0n) == Some{v} : Maybe<&2, W.W64>}
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

# Fast forms equal structural forms, for every input. bytes.bend's Octets
# runs the tail-recursive *.fast defs; these lemmas (each stated
# ref == fast, the direction rewrites use) carry every law proved about the
# structural defs over to them.

def r8_rr(ws: List<&2, Word(8n)>, acc: List<&2, Word(8n)>, b: List<&2, Word(8n)>) -> {B.w8s.rev_onto(B.w8s.rev_onto(ws, acc), b) == B.w8s.rev_onto(acc, List.append(&2, Word(8n), ws, b)) : List<&2, Word(8n)>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      r8_rr(t, Con{h, acc}, b)

def ru_rr(xs: List<&2, U32>, acc: List<&2, U32>, b: List<&2, U32>) -> {B.u32s.rev_onto(B.u32s.rev_onto(xs, acc), b) == B.u32s.rev_onto(acc, List.append(&2, U32, xs, b)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      ru_rr(t, Con{h, acc}, b)

def app_nil8(+ws: List<&2, Word(8n)>) -> {List.append(&2, Word(8n), ws, Nil{}) == ws : List<&2, Word(8n)>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, l => Con{h, l}, List.append(&2, Word(8n), t, Nil{}), t, app_nil8(t))

def app_nilu(+xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{h, l}, List.append(&2, U32, t, Nil{}), t, app_nilu(t))

def g_of(xs: List<&2, U32>, acc: List<&2, Word(8n)>) -> {B.w8s.of_list.go(xs, acc) == B.w8s.rev_onto(B.w8s.of_list(xs), acc) : List<&2, Word(8n)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      g_of(t, Con{B.bits8(h), acc})

def F_of(+xs: List<&2, U32>) -> {B.w8s.of_list(xs) == B.w8s.of_list.fast(xs) : List<&2, Word(8n)>}:
  Equal.sym(List<&2, Word(8n)>, B.w8s.of_list.fast(xs), B.w8s.of_list(xs),
    Equal.trans(List<&2, Word(8n)>, B.w8s.of_list.fast(xs), B.w8s.rev_onto(B.w8s.rev_onto(B.w8s.of_list(xs), Nil{}), Nil{}), B.w8s.of_list(xs),
      Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, l => B.w8s.rev_onto(l, Nil{}), B.w8s.of_list.go(xs, Nil{}), B.w8s.rev_onto(B.w8s.of_list(xs), Nil{}), g_of(xs, Nil{})),
      Equal.trans(List<&2, Word(8n)>, B.w8s.rev_onto(B.w8s.rev_onto(B.w8s.of_list(xs), Nil{}), Nil{}), List.append(&2, Word(8n), B.w8s.of_list(xs), Nil{}), B.w8s.of_list(xs),
        r8_rr(B.w8s.of_list(xs), Nil{}, Nil{}), app_nil8(B.w8s.of_list(xs)))))

def g_to(ws: List<&2, Word(8n)>, acc: List<&2, U32>) -> {B.w8s.to_list.go(ws, acc) == B.u32s.rev_onto(B.w8s.to_list(ws), acc) : List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      g_to(t, Con{B.of_bits8(h), acc})

def F_to(+ws: List<&2, Word(8n)>) -> {B.w8s.to_list(ws) == B.w8s.to_list.fast(ws) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.w8s.to_list.fast(ws), B.w8s.to_list(ws),
    Equal.trans(List<&2, U32>, B.w8s.to_list.fast(ws), B.u32s.rev_onto(B.u32s.rev_onto(B.w8s.to_list(ws), Nil{}), Nil{}), B.w8s.to_list(ws),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => B.u32s.rev_onto(l, Nil{}), B.w8s.to_list.go(ws, Nil{}), B.u32s.rev_onto(B.w8s.to_list(ws), Nil{}), g_to(ws, Nil{})),
      Equal.trans(List<&2, U32>, B.u32s.rev_onto(B.u32s.rev_onto(B.w8s.to_list(ws), Nil{}), Nil{}), List.append(&2, U32, B.w8s.to_list(ws), Nil{}), B.w8s.to_list(ws),
        ru_rr(B.w8s.to_list(ws), Nil{}, Nil{}), app_nilu(B.w8s.to_list(ws)))))

def g_take(n: Nat, ws: List<&2, Word(8n)>, acc: List<&2, Word(8n)>) -> {B.w8s.take.go(n, ws, acc) == B.w8s.rev_onto(B.w8s.take(n, ws), acc) : List<&2, Word(8n)>}:
  match n ws:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      g_take(p, t, Con{h, acc})

def F_take(+n: Nat, +ws: List<&2, Word(8n)>) -> {B.w8s.take(n, ws) == B.w8s.take.fast(n, ws) : List<&2, Word(8n)>}:
  Equal.sym(List<&2, Word(8n)>, B.w8s.take.fast(n, ws), B.w8s.take(n, ws),
    Equal.trans(List<&2, Word(8n)>, B.w8s.take.fast(n, ws), B.w8s.rev_onto(B.w8s.rev_onto(B.w8s.take(n, ws), Nil{}), Nil{}), B.w8s.take(n, ws),
      Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, l => B.w8s.rev_onto(l, Nil{}), B.w8s.take.go(n, ws, Nil{}), B.w8s.rev_onto(B.w8s.take(n, ws), Nil{}), g_take(n, ws, Nil{})),
      Equal.trans(List<&2, Word(8n)>, B.w8s.rev_onto(B.w8s.rev_onto(B.w8s.take(n, ws), Nil{}), Nil{}), List.append(&2, Word(8n), B.w8s.take(n, ws), Nil{}), B.w8s.take(n, ws),
        r8_rr(B.w8s.take(n, ws), Nil{}, Nil{}), app_nil8(B.w8s.take(n, ws)))))

def F_app(+xs: List<&2, Word(8n)>, +ys: List<&2, Word(8n)>) -> {List.append(&2, Word(8n), xs, ys) == B.w8s.append.fast(xs, ys) : List<&2, Word(8n)>}:
  Equal.sym(List<&2, Word(8n)>, B.w8s.append.fast(xs, ys), List.append(&2, Word(8n), xs, ys), r8_rr(xs, Nil{}, ys))

def add_succ(+a: Nat, +n: Nat) -> {Nat.add(a, 1n+n) == 1n+Nat.add(a, n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+n), 1n+Nat.add(p, n), add_succ(p, n))

def add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, add_zero(p))

def g_len(+ws: List<&2, Word(8n)>, +n: Nat) -> {B.w8s.len.go(ws, n) == Nat.add(List.length(&2, Word(8n), ws), n) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(Nat, B.w8s.len.go(t, 1n+n), Nat.add(List.length(&2, Word(8n), t), 1n+n), 1n+Nat.add(List.length(&2, Word(8n), t), n),
        g_len(t, 1n+n), add_succ(List.length(&2, Word(8n), t), n))

def F_len(+ws: List<&2, Word(8n)>) -> {List.length(&2, Word(8n), ws) == B.w8s.len.fast(ws) : Nat}:
  Equal.sym(Nat, B.w8s.len.fast(ws), List.length(&2, Word(8n), ws),
    Equal.trans(Nat, B.w8s.len.go(ws, 0n), Nat.add(List.length(&2, Word(8n), ws), 0n), List.length(&2, Word(8n), ws),
      g_len(ws, 0n), add_zero(List.length(&2, Word(8n), ws))))

def zeros_cons(+p: Nat, +acc: List<&2, Word(8n)>) -> {List.append(&2, Word(8n), B.w8s.zeros(p), Con{Word.zero(8n), acc}) == Con{Word.zero(8n), List.append(&2, Word(8n), B.w8s.zeros(p), acc)} : List<&2, Word(8n)>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, l => Con{Word.zero(8n), l}, List.append(&2, Word(8n), B.w8s.zeros(q), Con{Word.zero(8n), acc}), Con{Word.zero(8n), List.append(&2, Word(8n), B.w8s.zeros(q), acc)}, zeros_cons(q, acc))

def g_zeros(+n: Nat, +acc: List<&2, Word(8n)>) -> {B.w8s.zeros.go(n, acc) == List.append(&2, Word(8n), B.w8s.zeros(n), acc) : List<&2, Word(8n)>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(List<&2, Word(8n)>, B.w8s.zeros.go(p, Con{Word.zero(8n), acc}), List.append(&2, Word(8n), B.w8s.zeros(p), Con{Word.zero(8n), acc}), Con{Word.zero(8n), List.append(&2, Word(8n), B.w8s.zeros(p), acc)},
        g_zeros(p, Con{Word.zero(8n), acc}), zeros_cons(p, acc))

def F_zeros(+n: Nat) -> {B.w8s.zeros(n) == B.w8s.zeros.fast(n) : List<&2, Word(8n)>}:
  Equal.sym(List<&2, Word(8n)>, B.w8s.zeros.fast(n), B.w8s.zeros(n),
    Equal.trans(List<&2, Word(8n)>, B.w8s.zeros.go(n, Nil{}), List.append(&2, Word(8n), B.w8s.zeros(n), Nil{}), B.w8s.zeros(n),
      g_zeros(n, Nil{}), app_nil8(B.w8s.zeros(n))))

def w8s_zeros_list(+n: Nat) -> {B.w8s.to_list(B.w8s.zeros(n)) == B.zeros(n) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{0, l}, B.w8s.to_list(B.w8s.zeros(p)), B.zeros(p), w8s_zeros_list(p))

# The Octets laws: each rewrites Octets' fast forms to the structural ones,
# then uses the word-list lemmas

def p_octets_take_drop(+n: Nat, +o: B.Octets) -> {B.Octets.append(B.Octets.take(n, o), B.Octets.drop(n, o)) == o : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_app(B.w8s.take.fast(n, ws), B.w8s.drop(n, ws)) : {B.Octets{_} == B.Octets{ws} : B.Octets}
      %F_take(n, ws) : {B.Octets{List.append(&2, Word(8n), _, B.w8s.drop(n, ws))} == B.Octets{ws} : B.Octets}
      Equal.cong(List<&2, Word(8n)>, B.Octets, l => B.Octets{l}, List.append(&2, Word(8n), B.w8s.take(n, ws), B.w8s.drop(n, ws)), ws, w8s_take_drop(n, ws))

def Laws.octets_take_drop(n, o):
  p_octets_take_drop(n, o)

def p_octets_of_to(+o: B.Octets) -> {B.Octets.of_list(B.Octets.to_list(o)) == o : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_of(B.w8s.to_list.fast(ws)) : {B.Octets{_} == B.Octets{ws} : B.Octets}
      %F_to(ws) : {B.Octets{B.w8s.of_list(_)} == B.Octets{ws} : B.Octets}
      Equal.cong(List<&2, Word(8n)>, B.Octets, l => B.Octets{l}, B.w8s.of_list(B.w8s.to_list(ws)), ws, w8s_of_to(ws))

def Laws.octets_of_to(o):
  p_octets_of_to(o)

def p_octets_to_of(+xs: List<&2, U32>) -> {B.Octets.to_list(B.Octets.of_list(xs)) == B.mask(xs) : List<&2, U32>}:
  %F_to(B.w8s.of_list.fast(xs)) : {_ == B.mask(xs) : List<&2, U32>}
  %F_of(xs) : {B.w8s.to_list(_) == B.mask(xs) : List<&2, U32>}
  w8s_to_of(xs)

def Laws.octets_to_of(xs):
  p_octets_to_of(xs)

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

def w8s_eq_self(ws: List<&2, Word(8n)>) -> {B.w8s.eq(ws, ws, True{}) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Cmp, Word.cmp(8n, h, h), EQ{}, word_cmp_self(8n, h)) : {B.w8s.eq(t, t, Bool.and(True{}, Cmp.is_eq(_))) == True{} : Bool}
      w8s_eq_self(t)

def Laws.octets_is_eq_refl(o):
  match o:
    case B.Octets{+ws}:
      w8s_eq_self(ws)

def Laws.octets_masks():
  {==}

def Laws.octets_slice():
  {==}

def p_octets_append_list(+a: B.Octets, +b: B.Octets) -> {B.Octets.to_list(B.Octets.append(a, b)) == B.append(B.Octets.to_list(a), B.Octets.to_list(b)) : List<&2, U32>}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_to(B.w8s.append.fast(xs, ys)) : {_ == B.append(B.w8s.to_list.fast(xs), B.w8s.to_list.fast(ys)) : List<&2, U32>}
      %F_app(xs, ys) : {B.w8s.to_list(_) == B.append(B.w8s.to_list.fast(xs), B.w8s.to_list.fast(ys)) : List<&2, U32>}
      %F_to(xs) : {B.w8s.to_list(List.append(&2, Word(8n), xs, ys)) == B.append(_, B.w8s.to_list.fast(ys)) : List<&2, U32>}
      %F_to(ys) : {B.w8s.to_list(List.append(&2, Word(8n), xs, ys)) == B.append(B.w8s.to_list(xs), _) : List<&2, U32>}
      w8s_to_app(xs, ys)

def Laws.octets_append_list(a, b):
  p_octets_append_list(a, b)

def p_octets_len_list(+o: B.Octets) -> {B.Octets.len(o) == B.len(B.Octets.to_list(o)) : Nat}:
  match o:
    case B.Octets{+ws}:
      %F_len(ws) : {_ == B.len(B.w8s.to_list.fast(ws)) : Nat}
      %F_to(ws) : {List.length(&2, Word(8n), ws) == B.len(_) : Nat}
      w8s_len(ws)

def Laws.octets_len_list(o):
  p_octets_len_list(o)

def p_octets_take_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.take(B.Octets.len(a), B.Octets.append(a, b)) == a : B.Octets}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_take(B.w8s.len.fast(xs), B.w8s.append.fast(xs, ys)) : {B.Octets{_} == B.Octets{xs} : B.Octets}
      %F_len(xs) : {B.Octets{B.w8s.take(_, B.w8s.append.fast(xs, ys))} == B.Octets{xs} : B.Octets}
      %F_app(xs, ys) : {B.Octets{B.w8s.take(List.length(&2, Word(8n), xs), _)} == B.Octets{xs} : B.Octets}
      Equal.cong(List<&2, Word(8n)>, B.Octets, l => B.Octets{l}, B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys)), xs, w8s_take_app(xs, ys))

def Laws.octets_take_append(a, b):
  p_octets_take_append(a, b)

def p_octets_drop_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.drop(B.Octets.len(a), B.Octets.append(a, b)) == b : B.Octets}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_len(xs) : {B.Octets{B.w8s.drop(_, B.w8s.append.fast(xs, ys))} == B.Octets{ys} : B.Octets}
      %F_app(xs, ys) : {B.Octets{B.w8s.drop(List.length(&2, Word(8n), xs), _)} == B.Octets{ys} : B.Octets}
      Equal.cong(List<&2, Word(8n)>, B.Octets, l => B.Octets{l}, B.w8s.drop(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys)), ys, w8s_drop_app(xs, ys))

def Laws.octets_drop_append(a, b):
  p_octets_drop_append(a, b)

def p_octets_split_at_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.split_at(B.Octets.len(a), B.Octets.append(a, b)) == Some{B.OctetsSplit{a, b}} : Maybe<&2, B.OctetsSplit>}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_app(xs, ys) : {B.Octets.split_at.pick(Nat.is_le(B.w8s.len.fast(xs), B.w8s.len.fast(_)), B.w8s.len.fast(xs), B.Octets{B.w8s.append.fast(xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_app(xs, ys) : {B.Octets.split_at.pick(Nat.is_le(B.w8s.len.fast(xs), B.w8s.len.fast(List.append(&2, Word(8n), xs, ys))), B.w8s.len.fast(xs), B.Octets{_}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_len(List.append(&2, Word(8n), xs, ys)) : {B.Octets.split_at.pick(Nat.is_le(B.w8s.len.fast(xs), _), B.w8s.len.fast(xs), B.Octets{List.append(&2, Word(8n), xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_len(xs) : {B.Octets.split_at.pick(Nat.is_le(_, List.length(&2, Word(8n), List.append(&2, Word(8n), xs, ys))), B.w8s.len.fast(xs), B.Octets{List.append(&2, Word(8n), xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_len(xs) : {B.Octets.split_at.pick(Nat.is_le(List.length(&2, Word(8n), xs), List.length(&2, Word(8n), List.append(&2, Word(8n), xs, ys))), _, B.Octets{List.append(&2, Word(8n), xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), xs, ys)), Nat.add(List.length(&2, Word(8n), xs), List.length(&2, Word(8n), ys)), w8s_len_app(xs, ys)) : {B.Octets.split_at.pick(Nat.is_le(List.length(&2, Word(8n), xs), _), List.length(&2, Word(8n), xs), B.Octets{List.append(&2, Word(8n), xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %Equal.sym(Bool, Nat.is_le(List.length(&2, Word(8n), xs), Nat.add(List.length(&2, Word(8n), xs), List.length(&2, Word(8n), ys))), True{}, nat_le_add(List.length(&2, Word(8n), xs), List.length(&2, Word(8n), ys))) : {B.Octets.split_at.pick(_, List.length(&2, Word(8n), xs), B.Octets{List.append(&2, Word(8n), xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys)) : {Some{B.OctetsSplit{B.Octets{_}, B.Octets{B.w8s.drop(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}}} == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %w8s_take_app(xs, ys) : {Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}, B.Octets{B.w8s.drop(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}}} == Some{B.OctetsSplit{B.Octets{_}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %w8s_drop_app(xs, ys) : {Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}, B.Octets{B.w8s.drop(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}}} == Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys))}, B.Octets{_}}} : Maybe<&2, B.OctetsSplit>}
      {==}

def Laws.octets_split_at_append(a, b):
  p_octets_split_at_append(a, b)

def Laws.octets_split_short():
  {==}

def Laws.octets_split_text():
  {==}

def p_octets_zeros_list(+n: Nat) -> {B.Octets.to_list(B.Octets.zeros(n)) == B.zeros(n) : List<&2, U32>}:
  %F_to(B.w8s.zeros.fast(n)) : {_ == B.zeros(n) : List<&2, U32>}
  %F_zeros(n) : {B.w8s.to_list(_) == B.zeros(n) : List<&2, U32>}
  w8s_zeros_list(n)

def Laws.octets_zeros_list(n):
  p_octets_zeros_list(n)

def p_octets_cons_list(+b: U32, +o: B.Octets) -> {B.Octets.to_list(B.Octets.cons(b, o)) == Con{B.byte(b), B.Octets.to_list(o)} : List<&2, U32>}:
  match o:
    case B.Octets{+ws}:
      %F_to(Con{B.bits8(b), ws}) : {_ == Con{B.byte(b), B.w8s.to_list.fast(ws)} : List<&2, U32>}
      %F_to(ws) : {Con{B.of_bits8(B.bits8(b)), B.w8s.to_list(ws)} == Con{B.byte(b), _} : List<&2, U32>}
      {==}

def Laws.octets_cons_list(b, o):
  p_octets_cons_list(b, o)

