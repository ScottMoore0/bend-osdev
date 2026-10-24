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

def bits8_of_bits8(w: B.OctByte) -> {B.oct.of(B.oct.to(w)) == w : B.OctByte}:
  match w:
    case B.OctByte{a0, a1, a2, a3, a4, a5, a6, a7}:
      {==}

def w8s_of_to(ws: List<&2, B.OctByte>) -> {B.w8s.of_list(B.w8s.to_list(ws)) == ws : List<&2, B.OctByte>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      %bits8_of_bits8(h) : {Con{B.oct.of(B.oct.to(h)), B.w8s.of_list(B.w8s.to_list(t))} == Con{_, t} : List<&2, B.OctByte>}
      %w8s_of_to(t) : {Con{B.oct.of(B.oct.to(h)), B.w8s.of_list(B.w8s.to_list(t))} == Con{B.oct.of(B.oct.to(h)), _} : List<&2, B.OctByte>}
      {==}

# a word through one OctByte and back is its byte
def oct_byte(h: U32) -> {B.oct.to(B.oct.of(h)) == B.byte(h) : U32}:
  match h:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def w8s_to_of(xs: List<&2, U32>) -> {B.w8s.to_list(B.w8s.of_list(xs)) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %w8s_to_of(t) : {Con{B.oct.to(B.oct.of(h)), B.w8s.to_list(B.w8s.of_list(t))} == Con{B.byte(h), _} : List<&2, U32>}
      %oct_byte(h) : {Con{B.oct.to(B.oct.of(h)), B.w8s.to_list(B.w8s.of_list(t))} == Con{_, B.w8s.to_list(B.w8s.of_list(t))} : List<&2, U32>}
      {==}

def w8s_to_app(xs: List<&2, B.OctByte>, ys: List<&2, B.OctByte>) -> {B.w8s.to_list(List.append(&2, B.OctByte, xs, ys)) == B.append(B.w8s.to_list(xs), B.w8s.to_list(ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %w8s_to_app(t, ys) : {Con{B.oct.to(h), B.w8s.to_list(List.append(&2, B.OctByte, t, ys))} == Con{B.oct.to(h), _} : List<&2, U32>}
      {==}

def w8s_len(ws: List<&2, B.OctByte>) -> {List.length(&2, B.OctByte, ws) == List.length(&2, U32, B.w8s.to_list(ws)) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, B.OctByte, t), List.length(&2, U32, B.w8s.to_list(t)), w8s_len(t))

def w8s_take_drop(n: Nat, ws: List<&2, B.OctByte>) -> {List.append(&2, B.OctByte, B.w8s.take(n, ws), B.w8s.drop(n, ws)) == ws : List<&2, B.OctByte>}:
  match n ws:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      %w8s_take_drop(p, t) : {Con{h, List.append(&2, B.OctByte, B.w8s.take(p, t), B.w8s.drop(p, t))} == Con{h, _} : List<&2, B.OctByte>}
      {==}

def w8s_take_app(xs: List<&2, B.OctByte>, ys: List<&2, B.OctByte>) -> {B.w8s.take(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys)) == xs : List<&2, B.OctByte>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %w8s_take_app(t, ys) : {Con{h, B.w8s.take(List.length(&2, B.OctByte, t), List.append(&2, B.OctByte, t, ys))} == Con{h, _} : List<&2, B.OctByte>}
      {==}

def w8s_drop_app(xs: List<&2, B.OctByte>, ys: List<&2, B.OctByte>) -> {B.w8s.drop(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys)) == ys : List<&2, B.OctByte>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      w8s_drop_app(t, ys)

def w8s_len_app(xs: List<&2, B.OctByte>, ys: List<&2, B.OctByte>) -> {List.length(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys)) == Nat.add(List.length(&2, B.OctByte, xs), List.length(&2, B.OctByte, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, B.OctByte, List.append(&2, B.OctByte, t, ys)), Nat.add(List.length(&2, B.OctByte, t), List.length(&2, B.OctByte, ys)), w8s_len_app(t, ys))

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

def r8_rr(ws: List<&2, B.OctByte>, acc: List<&2, B.OctByte>, b: List<&2, B.OctByte>) -> {B.w8s.rev_onto(B.w8s.rev_onto(ws, acc), b) == B.w8s.rev_onto(acc, List.append(&2, B.OctByte, ws, b)) : List<&2, B.OctByte>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      r8_rr(t, Con{h, acc}, b)

def ru_rr(xs: List<&2, U32>, acc: List<&2, U32>, b: List<&2, U32>) -> {B.rev_onto(B.rev_onto(xs, acc), b) == B.rev_onto(acc, List.append(&2, U32, xs, b)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      ru_rr(t, Con{h, acc}, b)

def app_nil8(+ws: List<&2, B.OctByte>) -> {List.append(&2, B.OctByte, ws, Nil{}) == ws : List<&2, B.OctByte>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => Con{h, l}, List.append(&2, B.OctByte, t, Nil{}), t, app_nil8(t))

def app_nilu(+xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{h, l}, List.append(&2, U32, t, Nil{}), t, app_nilu(t))

def g_of(xs: List<&2, U32>, acc: List<&2, B.OctByte>) -> {B.w8s.of_list.go(xs, acc) == B.w8s.rev_onto(B.w8s.of_list(xs), acc) : List<&2, B.OctByte>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      g_of(t, Con{B.oct.of(h), acc})

def F_of(+xs: List<&2, U32>) -> {B.w8s.of_list(xs) == B.w8s.of_list.fast(xs) : List<&2, B.OctByte>}:
  Equal.sym(List<&2, B.OctByte>, B.w8s.of_list.fast(xs), B.w8s.of_list(xs),
    Equal.trans(List<&2, B.OctByte>, B.w8s.of_list.fast(xs), B.w8s.rev_onto(B.w8s.rev_onto(B.w8s.of_list(xs), Nil{}), Nil{}), B.w8s.of_list(xs),
      Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => B.w8s.rev_onto(l, Nil{}), B.w8s.of_list.go(xs, Nil{}), B.w8s.rev_onto(B.w8s.of_list(xs), Nil{}), g_of(xs, Nil{})),
      Equal.trans(List<&2, B.OctByte>, B.w8s.rev_onto(B.w8s.rev_onto(B.w8s.of_list(xs), Nil{}), Nil{}), List.append(&2, B.OctByte, B.w8s.of_list(xs), Nil{}), B.w8s.of_list(xs),
        r8_rr(B.w8s.of_list(xs), Nil{}, Nil{}), app_nil8(B.w8s.of_list(xs)))))

def g_to(ws: List<&2, B.OctByte>, acc: List<&2, U32>) -> {B.w8s.to_list.go(ws, acc) == B.rev_onto(B.w8s.to_list(ws), acc) : List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      g_to(t, Con{B.oct.to(h), acc})

def F_to(+ws: List<&2, B.OctByte>) -> {B.w8s.to_list(ws) == B.w8s.to_list.fast(ws) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.w8s.to_list.fast(ws), B.w8s.to_list(ws),
    Equal.trans(List<&2, U32>, B.w8s.to_list.fast(ws), B.rev_onto(B.rev_onto(B.w8s.to_list(ws), Nil{}), Nil{}), B.w8s.to_list(ws),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => B.rev_onto(l, Nil{}), B.w8s.to_list.go(ws, Nil{}), B.rev_onto(B.w8s.to_list(ws), Nil{}), g_to(ws, Nil{})),
      Equal.trans(List<&2, U32>, B.rev_onto(B.rev_onto(B.w8s.to_list(ws), Nil{}), Nil{}), List.append(&2, U32, B.w8s.to_list(ws), Nil{}), B.w8s.to_list(ws),
        ru_rr(B.w8s.to_list(ws), Nil{}, Nil{}), app_nilu(B.w8s.to_list(ws)))))

def g_take(n: Nat, ws: List<&2, B.OctByte>, acc: List<&2, B.OctByte>) -> {B.w8s.take.go(n, ws, acc) == B.w8s.rev_onto(B.w8s.take(n, ws), acc) : List<&2, B.OctByte>}:
  match n ws:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      g_take(p, t, Con{h, acc})

def F_take(+n: Nat, +ws: List<&2, B.OctByte>) -> {B.w8s.take(n, ws) == B.w8s.take.fast(n, ws) : List<&2, B.OctByte>}:
  Equal.sym(List<&2, B.OctByte>, B.w8s.take.fast(n, ws), B.w8s.take(n, ws),
    Equal.trans(List<&2, B.OctByte>, B.w8s.take.fast(n, ws), B.w8s.rev_onto(B.w8s.rev_onto(B.w8s.take(n, ws), Nil{}), Nil{}), B.w8s.take(n, ws),
      Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => B.w8s.rev_onto(l, Nil{}), B.w8s.take.go(n, ws, Nil{}), B.w8s.rev_onto(B.w8s.take(n, ws), Nil{}), g_take(n, ws, Nil{})),
      Equal.trans(List<&2, B.OctByte>, B.w8s.rev_onto(B.w8s.rev_onto(B.w8s.take(n, ws), Nil{}), Nil{}), List.append(&2, B.OctByte, B.w8s.take(n, ws), Nil{}), B.w8s.take(n, ws),
        r8_rr(B.w8s.take(n, ws), Nil{}, Nil{}), app_nil8(B.w8s.take(n, ws)))))

def F_app(+xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>) -> {List.append(&2, B.OctByte, xs, ys) == B.w8s.append.fast(xs, ys) : List<&2, B.OctByte>}:
  Equal.sym(List<&2, B.OctByte>, B.w8s.append.fast(xs, ys), List.append(&2, B.OctByte, xs, ys), r8_rr(xs, Nil{}, ys))

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

def g_len(+ws: List<&2, B.OctByte>, +n: Nat) -> {B.w8s.len.go(ws, n) == Nat.add(List.length(&2, B.OctByte, ws), n) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(Nat, B.w8s.len.go(t, 1n+n), Nat.add(List.length(&2, B.OctByte, t), 1n+n), 1n+Nat.add(List.length(&2, B.OctByte, t), n),
        g_len(t, 1n+n), add_succ(List.length(&2, B.OctByte, t), n))

def F_len(+ws: List<&2, B.OctByte>) -> {List.length(&2, B.OctByte, ws) == B.w8s.len.fast(ws) : Nat}:
  Equal.sym(Nat, B.w8s.len.fast(ws), List.length(&2, B.OctByte, ws),
    Equal.trans(Nat, B.w8s.len.go(ws, 0n), Nat.add(List.length(&2, B.OctByte, ws), 0n), List.length(&2, B.OctByte, ws),
      g_len(ws, 0n), add_zero(List.length(&2, B.OctByte, ws))))

def zeros_cons(+p: Nat, +acc: List<&2, B.OctByte>) -> {List.append(&2, B.OctByte, B.w8s.zeros(p), Con{B.oct.zero(), acc}) == Con{B.oct.zero(), List.append(&2, B.OctByte, B.w8s.zeros(p), acc)} : List<&2, B.OctByte>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => Con{B.oct.zero(), l}, List.append(&2, B.OctByte, B.w8s.zeros(q), Con{B.oct.zero(), acc}), Con{B.oct.zero(), List.append(&2, B.OctByte, B.w8s.zeros(q), acc)}, zeros_cons(q, acc))

def g_zeros(+n: Nat, +acc: List<&2, B.OctByte>) -> {B.w8s.zeros.go(n, acc) == List.append(&2, B.OctByte, B.w8s.zeros(n), acc) : List<&2, B.OctByte>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(List<&2, B.OctByte>, B.w8s.zeros.go(p, Con{B.oct.zero(), acc}), List.append(&2, B.OctByte, B.w8s.zeros(p), Con{B.oct.zero(), acc}), Con{B.oct.zero(), List.append(&2, B.OctByte, B.w8s.zeros(p), acc)},
        g_zeros(p, Con{B.oct.zero(), acc}), zeros_cons(p, acc))

def F_zeros(+n: Nat) -> {B.w8s.zeros(n) == B.w8s.zeros.fast(n) : List<&2, B.OctByte>}:
  Equal.sym(List<&2, B.OctByte>, B.w8s.zeros.fast(n), B.w8s.zeros(n),
    Equal.trans(List<&2, B.OctByte>, B.w8s.zeros.go(n, Nil{}), List.append(&2, B.OctByte, B.w8s.zeros(n), Nil{}), B.w8s.zeros(n),
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
      %F_take(n, ws) : {B.Octets{List.append(&2, B.OctByte, _, B.w8s.drop(n, ws))} == B.Octets{ws} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, List.append(&2, B.OctByte, B.w8s.take(n, ws), B.w8s.drop(n, ws)), ws, w8s_take_drop(n, ws))

def Laws.octets_take_drop(n, o):
  p_octets_take_drop(n, o)

def p_octets_of_to(+o: B.Octets) -> {B.Octets.of_list(B.Octets.to_list(o)) == o : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_of(B.w8s.to_list.fast(ws)) : {B.Octets{_} == B.Octets{ws} : B.Octets}
      %F_to(ws) : {B.Octets{B.w8s.of_list(_)} == B.Octets{ws} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.of_list(B.w8s.to_list(ws)), ws, w8s_of_to(ws))

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

def w8s_eq_self(ws: List<&2, B.OctByte>) -> {B.w8s.eq(ws, ws, True{}) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, U32.is_eq(B.oct.to(h), B.oct.to(h)), True{}, u32_eq_self(B.oct.to(h))) : {B.w8s.eq(t, t, Bool.and(True{}, _)) == True{} : Bool}
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
      %F_to(xs) : {B.w8s.to_list(List.append(&2, B.OctByte, xs, ys)) == B.append(_, B.w8s.to_list.fast(ys)) : List<&2, U32>}
      %F_to(ys) : {B.w8s.to_list(List.append(&2, B.OctByte, xs, ys)) == B.append(B.w8s.to_list(xs), _) : List<&2, U32>}
      w8s_to_app(xs, ys)

def Laws.octets_append_list(a, b):
  p_octets_append_list(a, b)

def p_octets_len_list(+o: B.Octets) -> {B.Octets.len(o) == B.len(B.Octets.to_list(o)) : Nat}:
  match o:
    case B.Octets{+ws}:
      %F_len(ws) : {_ == B.len(B.w8s.to_list.fast(ws)) : Nat}
      %F_to(ws) : {List.length(&2, B.OctByte, ws) == B.len(_) : Nat}
      w8s_len(ws)

def Laws.octets_len_list(o):
  p_octets_len_list(o)

def p_octets_take_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.take(B.Octets.len(a), B.Octets.append(a, b)) == a : B.Octets}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_take(B.w8s.len.fast(xs), B.w8s.append.fast(xs, ys)) : {B.Octets{_} == B.Octets{xs} : B.Octets}
      %F_len(xs) : {B.Octets{B.w8s.take(_, B.w8s.append.fast(xs, ys))} == B.Octets{xs} : B.Octets}
      %F_app(xs, ys) : {B.Octets{B.w8s.take(List.length(&2, B.OctByte, xs), _)} == B.Octets{xs} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.take(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys)), xs, w8s_take_app(xs, ys))

def Laws.octets_take_append(a, b):
  p_octets_take_append(a, b)

def p_octets_drop_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.drop(B.Octets.len(a), B.Octets.append(a, b)) == b : B.Octets}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_len(xs) : {B.Octets{B.w8s.drop(_, B.w8s.append.fast(xs, ys))} == B.Octets{ys} : B.Octets}
      %F_app(xs, ys) : {B.Octets{B.w8s.drop(List.length(&2, B.OctByte, xs), _)} == B.Octets{ys} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.drop(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys)), ys, w8s_drop_app(xs, ys))

def Laws.octets_drop_append(a, b):
  p_octets_drop_append(a, b)

def p_octets_split_at_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.split_at(B.Octets.len(a), B.Octets.append(a, b)) == Some{B.OctetsSplit{a, b}} : Maybe<&2, B.OctetsSplit>}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_app(xs, ys) : {B.Octets.split_at.pick(Nat.is_le(B.w8s.len.fast(xs), B.w8s.len.fast(_)), B.w8s.len.fast(xs), B.Octets{B.w8s.append.fast(xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_app(xs, ys) : {B.Octets.split_at.pick(Nat.is_le(B.w8s.len.fast(xs), B.w8s.len.fast(List.append(&2, B.OctByte, xs, ys))), B.w8s.len.fast(xs), B.Octets{_}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_len(List.append(&2, B.OctByte, xs, ys)) : {B.Octets.split_at.pick(Nat.is_le(B.w8s.len.fast(xs), _), B.w8s.len.fast(xs), B.Octets{List.append(&2, B.OctByte, xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_len(xs) : {B.Octets.split_at.pick(Nat.is_le(_, List.length(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys))), B.w8s.len.fast(xs), B.Octets{List.append(&2, B.OctByte, xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_len(xs) : {B.Octets.split_at.pick(Nat.is_le(List.length(&2, B.OctByte, xs), List.length(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys))), _, B.Octets{List.append(&2, B.OctByte, xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %Equal.sym(Nat, List.length(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys)), Nat.add(List.length(&2, B.OctByte, xs), List.length(&2, B.OctByte, ys)), w8s_len_app(xs, ys)) : {B.Octets.split_at.pick(Nat.is_le(List.length(&2, B.OctByte, xs), _), List.length(&2, B.OctByte, xs), B.Octets{List.append(&2, B.OctByte, xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %Equal.sym(Bool, Nat.is_le(List.length(&2, B.OctByte, xs), Nat.add(List.length(&2, B.OctByte, xs), List.length(&2, B.OctByte, ys))), True{}, nat_le_add(List.length(&2, B.OctByte, xs), List.length(&2, B.OctByte, ys))) : {B.Octets.split_at.pick(_, List.length(&2, B.OctByte, xs), B.Octets{List.append(&2, B.OctByte, xs, ys)}) == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %F_take(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys)) : {Some{B.OctetsSplit{B.Octets{_}, B.Octets{B.w8s.drop(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys))}}} == Some{B.OctetsSplit{B.Octets{xs}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %w8s_take_app(xs, ys) : {Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys))}, B.Octets{B.w8s.drop(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys))}}} == Some{B.OctetsSplit{B.Octets{_}, B.Octets{ys}}} : Maybe<&2, B.OctetsSplit>}
      %w8s_drop_app(xs, ys) : {Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys))}, B.Octets{B.w8s.drop(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys))}}} == Some{B.OctetsSplit{B.Octets{B.w8s.take(List.length(&2, B.OctByte, xs), List.append(&2, B.OctByte, xs, ys))}, B.Octets{_}}} : Maybe<&2, B.OctetsSplit>}
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
      %F_to(Con{B.oct.of(b), ws}) : {_ == Con{B.byte(b), B.w8s.to_list.fast(ws)} : List<&2, U32>}
      %F_to(ws) : {Con{B.oct.to(B.oct.of(b)), B.w8s.to_list(ws)} == Con{B.byte(b), _} : List<&2, U32>}
      %oct_byte(b) : {Con{B.oct.to(B.oct.of(b)), B.w8s.to_list(ws)} == Con{_, B.w8s.to_list(ws)} : List<&2, U32>}
      {==}

def Laws.octets_cons_list(b, o):
  p_octets_cons_list(b, o)

# The tail-recursive list layer equals the structural one

def ru_app_nil(+xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  app_nilu(xs)

def g_lenu(+xs: List<&2, U32>, +n: Nat) -> {B.len.go(xs, n) == Nat.add(B.len(xs), n) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(Nat, B.len.go(t, 1n+n), Nat.add(B.len(t), 1n+n), 1n+Nat.add(B.len(t), n),
        g_lenu(t, 1n+n), add_succ(B.len(t), n))

def p_len_fast(+xs: List<&2, U32>) -> {B.len(xs) == B.len.fast(xs) : Nat}:
  Equal.sym(Nat, B.len.fast(xs), B.len(xs),
    Equal.trans(Nat, B.len.go(xs, 0n), Nat.add(B.len(xs), 0n), B.len(xs), g_lenu(xs, 0n), add_zero(B.len(xs))))

def Laws.len_fast(xs):
  p_len_fast(xs)

# a structural list, reversed onto Nil and back, is itself
def rr_back(+zs: List<&2, U32>) -> {B.rev_onto(B.rev_onto(zs, Nil{}), Nil{}) == zs : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.rev_onto(B.rev_onto(zs, Nil{}), Nil{}), List.append(&2, U32, zs, Nil{}), zs, ru_rr(zs, Nil{}, Nil{}), app_nilu(zs))

def g_takeu(+n: Nat, +xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.take.go(n, xs, acc) == B.rev_onto(B.take(n, xs), acc) : List<&2, U32>}:
  match n xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      g_takeu(p, t, Con{h, acc})

def p_take_fast(+n: Nat, +xs: List<&2, U32>) -> {B.take(n, xs) == B.take.fast(n, xs) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.take.fast(n, xs), B.take(n, xs),
    Equal.trans(List<&2, U32>, B.take.fast(n, xs), B.rev_onto(B.rev_onto(B.take(n, xs), Nil{}), Nil{}), B.take(n, xs),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => B.rev_onto(l, Nil{}), B.take.go(n, xs, Nil{}), B.rev_onto(B.take(n, xs), Nil{}), g_takeu(n, xs, Nil{})),
      rr_back(B.take(n, xs))))

def Laws.take_fast(n, xs):
  p_take_fast(n, xs)

def p_append_fast(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.append(xs, ys) == B.append.fast(xs, ys) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.append.fast(xs, ys), B.append(xs, ys), ru_rr(xs, Nil{}, ys))

def Laws.append_fast(xs, ys):
  p_append_fast(xs, ys)

def zeros_consu(+p: Nat, +acc: List<&2, U32>) -> {List.append(&2, U32, B.zeros(p), Con{0, acc}) == Con{0, List.append(&2, U32, B.zeros(p), acc)} : List<&2, U32>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{0, l}, List.append(&2, U32, B.zeros(q), Con{0, acc}), Con{0, List.append(&2, U32, B.zeros(q), acc)}, zeros_consu(q, acc))

def g_zerosu(+n: Nat, +acc: List<&2, U32>) -> {B.zeros.go(n, acc) == List.append(&2, U32, B.zeros(n), acc) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(List<&2, U32>, B.zeros.go(p, Con{0, acc}), List.append(&2, U32, B.zeros(p), Con{0, acc}), Con{0, List.append(&2, U32, B.zeros(p), acc)},
        g_zerosu(p, Con{0, acc}), zeros_consu(p, acc))

def p_zeros_fast(+n: Nat) -> {B.zeros(n) == B.zeros.fast(n) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.zeros.fast(n), B.zeros(n),
    Equal.trans(List<&2, U32>, B.zeros.go(n, Nil{}), List.append(&2, U32, B.zeros(n), Nil{}), B.zeros(n), g_zerosu(n, Nil{}), app_nilu(B.zeros(n))))

def Laws.zeros_fast(n):
  p_zeros_fast(n)

def g_mask(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.mask.go(xs, acc) == B.rev_onto(B.mask(xs), acc) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      g_mask(t, Con{B.byte(h), acc})

def p_mask_fast(+xs: List<&2, U32>) -> {B.mask(xs) == B.mask.fast(xs) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.mask.fast(xs), B.mask(xs),
    Equal.trans(List<&2, U32>, B.mask.fast(xs), B.rev_onto(B.rev_onto(B.mask(xs), Nil{}), Nil{}), B.mask(xs),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => B.rev_onto(l, Nil{}), B.mask.go(xs, Nil{}), B.rev_onto(B.mask(xs), Nil{}), g_mask(xs, Nil{})),
      rr_back(B.mask(xs))))

def Laws.mask_fast(xs):
  p_mask_fast(xs)

def g_of_string(+s: String, +acc: List<&2, U32>) -> {B.of_string.go(s, acc) == B.rev_onto(B.of_string(s), acc) : List<&2, U32>}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      g_of_string(t, Con{B.byte(c), acc})

def p_of_string_fast(+s: String) -> {B.of_string(s) == B.of_string.fast(s) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.of_string.fast(s), B.of_string(s),
    Equal.trans(List<&2, U32>, B.of_string.fast(s), B.rev_onto(B.rev_onto(B.of_string(s), Nil{}), Nil{}), B.of_string(s),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => B.rev_onto(l, Nil{}), B.of_string.go(s, Nil{}), B.rev_onto(B.of_string(s), Nil{}), g_of_string(s, Nil{})),
      rr_back(B.of_string(s))))

def Laws.of_string_fast(s):
  p_of_string_fast(s)

# text: building from the back onto acc is the structural cat
def t_go(+xs: List<&2, U32>, +r: List<&2, U32>, +acc: String) -> {B.to_string.go(B.rev_onto(xs, r), acc) == B.to_string.go(r, B.to_string.cat(xs, acc)) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      t_go(t, Con{h, r}, acc)

def t_cat(+xs: List<&2, U32>) -> {B.to_string.cat(xs, SNil{}) == B.to_string(xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(String, String, x => SCon{Chr{B.byte(h)}, x}, B.to_string.cat(t, SNil{}), B.to_string(t), t_cat(t))

def p_to_string_fast(+xs: List<&2, U32>) -> {B.to_string(xs) == B.to_string.fast(xs) : String}:
  Equal.sym(String, B.to_string.fast(xs), B.to_string(xs),
    Equal.trans(String, B.to_string.go(B.rev_onto(xs, Nil{}), SNil{}), B.to_string.cat(xs, SNil{}), B.to_string(xs), t_go(xs, Nil{}, SNil{}), t_cat(xs)))

def Laws.to_string_fast(xs):
  p_to_string_fast(xs)

def h_go(+xs: List<&2, U32>, +r: List<&2, U32>, +acc: String) -> {B.hex.go(B.rev_onto(xs, r), acc) == B.hex.go(r, B.hex.cat(xs, acc)) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      h_go(t, Con{h, r}, acc)

def h_cat(+xs: List<&2, U32>) -> {B.hex.cat(xs, SNil{}) == B.hex(xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(String, String, x => SCon{B.hex.digit(U32.shrn(B.byte(h), 4n)), SCon{B.hex.digit(U32.and(B.byte(h), 15)), x}}, B.hex.cat(t, SNil{}), B.hex(t), h_cat(t))

def p_hex_fast(+xs: List<&2, U32>) -> {B.hex(xs) == B.hex.fast(xs) : String}:
  Equal.sym(String, B.hex.fast(xs), B.hex(xs),
    Equal.trans(String, B.hex.go(B.rev_onto(xs, Nil{}), SNil{}), B.hex.cat(xs, SNil{}), B.hex(xs), h_go(xs, Nil{}, SNil{}), h_cat(xs)))

def Laws.hex_fast(xs):
  p_hex_fast(xs)

def eq_go(+xs: List<&2, U32>, +ys: List<&2, U32>, +ok: Bool) -> {B.list_eq.go(xs, ys, ok) == Bool.and(ok, B.list_eq(xs, ys)) : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{a, s} Con{b, t}:
      match ok:
        case True{}:
          eq_go(s, t, U32.is_eq(a, b))
        case False{}:
          eq_go(s, t, False{})
    case Nil{} Con{b, t}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{a, s} Nil{}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}

def p_list_eq_fast(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.list_eq(xs, ys) == B.list_eq.fast(xs, ys) : Bool}:
  Equal.sym(Bool, B.list_eq.fast(xs, ys), B.list_eq(xs, ys), eq_go(xs, ys, True{}))

def Laws.list_eq_fast(xs, ys):
  p_list_eq_fast(xs, ys)

def Laws.rev_rev(xs):
  rr_back(xs)

# Octets' text and hex: each word read through bits8/of_bits8 is its byte
def w_t_go(+ws: List<&2, B.OctByte>, +r: List<&2, B.OctByte>, +acc: String) -> {B.w8s.text.go(B.w8s.rev_onto(ws, r), acc) == B.w8s.text.go(r, B.to_string.cat(B.w8s.to_list(ws), acc)) : String}:
  match ws:
    case Nil{}:
      {==}
    case Con{B.OctByte{a0, a1, a2, a3, a4, a5, a6, a7}, t}:
      w_t_go(t, Con{B.OctByte{a0, a1, a2, a3, a4, a5, a6, a7}, r}, acc)

def p_octets_to_string_list(+o: B.Octets) -> {B.Octets.to_string(o) == B.to_string(B.Octets.to_list(o)) : String}:
  match o:
    case B.Octets{+ws}:
      %F_to(ws) : {B.w8s.text.go(B.w8s.rev_onto(ws, Nil{}), SNil{}) == B.to_string(_) : String}
      Equal.trans(String, B.w8s.text.go(B.w8s.rev_onto(ws, Nil{}), SNil{}), B.to_string.cat(B.w8s.to_list(ws), SNil{}), B.to_string(B.w8s.to_list(ws)), w_t_go(ws, Nil{}, SNil{}), t_cat(B.w8s.to_list(ws)))

def Laws.octets_to_string_list(o):
  p_octets_to_string_list(o)

def w_h_go(+ws: List<&2, B.OctByte>, +r: List<&2, B.OctByte>, +acc: String) -> {B.w8s.hex.go(B.w8s.rev_onto(ws, r), acc) == B.w8s.hex.go(r, B.hex.cat(B.w8s.to_list(ws), acc)) : String}:
  match ws:
    case Nil{}:
      {==}
    case Con{B.OctByte{a0, a1, a2, a3, a4, a5, a6, a7}, t}:
      w_h_go(t, Con{B.OctByte{a0, a1, a2, a3, a4, a5, a6, a7}, r}, acc)

def p_octets_hex_list(+o: B.Octets) -> {B.Octets.hex(o) == B.hex(B.Octets.to_list(o)) : String}:
  match o:
    case B.Octets{+ws}:
      %F_to(ws) : {B.w8s.hex.go(B.w8s.rev_onto(ws, Nil{}), SNil{}) == B.hex(_) : String}
      Equal.trans(String, B.w8s.hex.go(B.w8s.rev_onto(ws, Nil{}), SNil{}), B.hex.cat(B.w8s.to_list(ws), SNil{}), B.hex(B.w8s.to_list(ws)), w_h_go(ws, Nil{}, SNil{}), h_cat(B.w8s.to_list(ws)))

def Laws.octets_hex_list(o):
  p_octets_hex_list(o)

# concat: pushing each piece's words is reversing the joined words
def rev_app8(+xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>, +acc: List<&2, B.OctByte>) -> {B.w8s.rev_onto(List.append(&2, B.OctByte, xs, ys), acc) == B.w8s.rev_onto(ys, B.w8s.rev_onto(xs, acc)) : List<&2, B.OctByte>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_app8(t, ys, Con{h, acc})

def concat_step(+ws: List<&2, B.OctByte>, +c: B.Octets, +acc: List<&2, B.OctByte>) -> {B.w8s.rev_onto(B.Octets.words(c), B.w8s.rev_onto(ws, acc)) == B.w8s.rev_onto(B.Octets.words(B.Octets.append(B.Octets{ws}, c)), acc) : List<&2, B.OctByte>}:
  match c:
    case B.Octets{+zs}:
      %F_app(ws, zs) : {B.w8s.rev_onto(zs, B.w8s.rev_onto(ws, acc)) == B.w8s.rev_onto(_, acc) : List<&2, B.OctByte>}
      Equal.sym(List<&2, B.OctByte>, B.w8s.rev_onto(List.append(&2, B.OctByte, ws, zs), acc), B.w8s.rev_onto(zs, B.w8s.rev_onto(ws, acc)), rev_app8(ws, zs, acc))

def concat_go(+os: List<&2, B.Octets>, +acc: List<&2, B.OctByte>) -> {B.w8s.concat.go(os, acc) == B.w8s.rev_onto(B.Octets.words(B.Octets.concat.ref(os)), acc) : List<&2, B.OctByte>}:
  match os:
    case Nil{}:
      {==}
    case Con{B.Octets{+ws}, t}:
      Equal.trans(List<&2, B.OctByte>, B.w8s.concat.go(t, B.w8s.rev_onto(ws, acc)), B.w8s.rev_onto(B.Octets.words(B.Octets.concat.ref(t)), B.w8s.rev_onto(ws, acc)), B.w8s.rev_onto(B.Octets.words(B.Octets.append(B.Octets{ws}, B.Octets.concat.ref(t))), acc),
        concat_go(t, B.w8s.rev_onto(ws, acc)), concat_step(ws, B.Octets.concat.ref(t), acc))

def octets_eta(+o: B.Octets) -> {B.Octets{B.Octets.words(o)} == o : B.Octets}:
  match o:
    case B.Octets{ws}:
      {==}

def rr8_back(+zs: List<&2, B.OctByte>) -> {B.w8s.rev_onto(B.w8s.rev_onto(zs, Nil{}), Nil{}) == zs : List<&2, B.OctByte>}:
  Equal.trans(List<&2, B.OctByte>, B.w8s.rev_onto(B.w8s.rev_onto(zs, Nil{}), Nil{}), List.append(&2, B.OctByte, zs, Nil{}), zs, r8_rr(zs, Nil{}, Nil{}), app_nil8(zs))

def concat_ref(+os: List<&2, B.Octets>) -> {B.Octets.concat(os) == B.Octets.concat.ref(os) : B.Octets}:
  Equal.trans(B.Octets, B.Octets.concat(os), B.Octets{B.Octets.words(B.Octets.concat.ref(os))}, B.Octets.concat.ref(os),
    Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.rev_onto(B.w8s.concat.go(os, Nil{}), Nil{}), B.Octets.words(B.Octets.concat.ref(os)),
      Equal.trans(List<&2, B.OctByte>, B.w8s.rev_onto(B.w8s.concat.go(os, Nil{}), Nil{}), B.w8s.rev_onto(B.w8s.rev_onto(B.Octets.words(B.Octets.concat.ref(os)), Nil{}), Nil{}), B.Octets.words(B.Octets.concat.ref(os)),
        Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => B.w8s.rev_onto(l, Nil{}), B.w8s.concat.go(os, Nil{}), B.w8s.rev_onto(B.Octets.words(B.Octets.concat.ref(os)), Nil{}), concat_go(os, Nil{})),
        rr8_back(B.Octets.words(B.Octets.concat.ref(os))))),
    octets_eta(B.Octets.concat.ref(os)))

def Laws.octets_concat_nil():
  {==}

def p_octets_concat_cons(+h: B.Octets, +t: List<&2, B.Octets>) -> {B.Octets.concat(Con{h, t}) == B.Octets.append(h, B.Octets.concat(t)) : B.Octets}:
  %Equal.sym(B.Octets, B.Octets.concat(t), B.Octets.concat.ref(t), concat_ref(t)) : {B.Octets.concat(Con{h, t}) == B.Octets.append(h, _) : B.Octets}
  concat_ref(Con{h, t})

def Laws.octets_concat_cons(h, t):
  p_octets_concat_cons(h, t)

# Reading at offsets: lemmas

def off.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def off.clash(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : off.disc(_)
  Unit{}

def off.absurd(-A: Type, e: Empty) -> A:
  match e:

def off.no(-A: Type, h: {False{} == True{} : Bool}) -> A:
  off.absurd(A, off.clash(h))

# Natural numbers

def off.le_zero(+m: Nat) -> {Nat.is_le(0n, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

# i + n <= m: i <= m
def off.le_add_l(+i: Nat, +n: Nat, +m: Nat) -> {Nat.is_le(Nat.add(i, n), m) == True{} : Bool} -> {Nat.is_le(i, m) == True{} : Bool}:
  match i m:
    case 0n _:
      h => off.le_zero(m)
    case 1n+p 0n:
      h => off.no({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      h => off.le_add_l(p, n, q, h)

# i + n <= m: n <= m - i
def off.le_sub(+i: Nat, +n: Nat, +m: Nat) -> {Nat.is_le(Nat.add(i, n), m) == True{} : Bool} -> {Nat.is_le(n, Nat.sub(m, i)) == True{} : Bool}:
  match i m:
    case 0n 0n:
      h => h
    case 0n 1n+q:
      h => h
    case 1n+p 0n:
      h => off.no({Nat.is_le(n, Nat.sub(0n, 1n+p)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      h => off.le_sub(p, n, q, h)

# n <= k: min(n, k) == n
def off.min_le(+n: Nat, +k: Nat) -> {Nat.is_le(n, k) == True{} : Bool} -> {Nat.min(n, k) == n : Nat}:
  match n k:
    case 0n _:
      h => {==}
    case 1n+p 0n:
      h => off.no({Nat.min(1n+p, 0n) == 1n+p : Nat}, h)
    case 1n+p 1n+q:
      h => Equal.cong(Nat, Nat, x => 1n+x, Nat.min(p, q), p, off.min_le(p, q, h))

# Word lists

def off.drop_nil(+i: Nat) -> {B.w8s.drop(i, Nil{}) == Nil{} : List<&2, B.OctByte>}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def off.take_nil(+i: Nat) -> {B.w8s.take(i, Nil{}) == Nil{} : List<&2, B.OctByte>}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def off.drop_app_add(xs: List<&2, B.OctByte>, +n: Nat, +ys: List<&2, B.OctByte>) -> {B.w8s.drop(Nat.add(List.length(&2, B.OctByte, xs), n), List.append(&2, B.OctByte, xs, ys)) == B.w8s.drop(n, ys) : List<&2, B.OctByte>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      off.drop_app_add(t, n, ys)

def off.take_app_add(xs: List<&2, B.OctByte>, +n: Nat, +ys: List<&2, B.OctByte>) -> {B.w8s.take(Nat.add(List.length(&2, B.OctByte, xs), n), List.append(&2, B.OctByte, xs, ys)) == List.append(&2, B.OctByte, xs, B.w8s.take(n, ys)) : List<&2, B.OctByte>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => Con{h, l}, B.w8s.take(Nat.add(List.length(&2, B.OctByte, t), n), List.append(&2, B.OctByte, t, ys)), List.append(&2, B.OctByte, t, B.w8s.take(n, ys)), off.take_app_add(t, n, ys))

def off.take_app_le(+n: Nat, xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>) -> {Nat.is_le(n, List.length(&2, B.OctByte, xs)) == True{} : Bool} -> {B.w8s.take(n, List.append(&2, B.OctByte, xs, ys)) == B.w8s.take(n, xs) : List<&2, B.OctByte>}:
  match n xs:
    case 0n _:
      h => {==}
    case 1n+p Nil{}:
      h => off.no({B.w8s.take(1n+p, ys) == Nil{} : List<&2, B.OctByte>}, h)
    case 1n+p Con{x, t}:
      h => Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => Con{x, l}, B.w8s.take(p, List.append(&2, B.OctByte, t, ys)), B.w8s.take(p, t), off.take_app_le(p, t, ys, h))

def off.drop_app_le(+n: Nat, xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>) -> {Nat.is_le(n, List.length(&2, B.OctByte, xs)) == True{} : Bool} -> {B.w8s.drop(n, List.append(&2, B.OctByte, xs, ys)) == List.append(&2, B.OctByte, B.w8s.drop(n, xs), ys) : List<&2, B.OctByte>}:
  match n xs:
    case 0n _:
      h => {==}
    case 1n+p Nil{}:
      h => off.no({B.w8s.drop(1n+p, ys) == ys : List<&2, B.OctByte>}, h)
    case 1n+p Con{x, t}:
      h => off.drop_app_le(p, t, ys, h)

def off.drop_drop(+j: Nat, +i: Nat, ws: List<&2, B.OctByte>) -> {B.w8s.drop(i, B.w8s.drop(j, ws)) == B.w8s.drop(Nat.add(j, i), ws) : List<&2, B.OctByte>}:
  match j ws:
    case 0n _:
      {==}
    case 1n+q Nil{}:
      off.drop_nil(i)
    case 1n+q Con{x, t}:
      off.drop_drop(q, i, t)

def off.take_take(+i: Nat, +j: Nat, ws: List<&2, B.OctByte>) -> {B.w8s.take(i, B.w8s.take(j, ws)) == B.w8s.take(Nat.min(i, j), ws) : List<&2, B.OctByte>}:
  match i j ws:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      {==}
    case 1n+p 1n+q Nil{}:
      {==}
    case 1n+p 1n+q Con{x, t}:
      Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => Con{x, l}, B.w8s.take(p, B.w8s.take(q, t)), B.w8s.take(Nat.min(p, q), t), off.take_take(p, q, t))

def off.take_drop(+i: Nat, +j: Nat, ws: List<&2, B.OctByte>) -> {B.w8s.take(i, B.w8s.drop(j, ws)) == B.w8s.drop(j, B.w8s.take(Nat.add(j, i), ws)) : List<&2, B.OctByte>}:
  match j ws:
    case 0n _:
      {==}
    case 1n+q Nil{}:
      off.take_nil(i)
    case 1n+q Con{x, t}:
      off.take_drop(i, q, t)

def off.drop_take(+i: Nat, +j: Nat, ws: List<&2, B.OctByte>) -> {B.w8s.drop(i, B.w8s.take(j, ws)) == B.w8s.take(Nat.sub(j, i), B.w8s.drop(i, ws)) : List<&2, B.OctByte>}:
  match i j ws:
    case 0n 0n _:
      {==}
    case 0n 1n+q _:
      {==}
    case 1n+p 0n _:
      {==}
    case 1n+p 1n+q Nil{}:
      Equal.sym(List<&2, B.OctByte>, B.w8s.take(Nat.sub(q, p), Nil{}), Nil{}, off.take_nil(Nat.sub(q, p)))
    case 1n+p 1n+q Con{x, t}:
      off.drop_take(p, q, t)

def off.len_take(+n: Nat, ws: List<&2, B.OctByte>) -> {List.length(&2, B.OctByte, B.w8s.take(n, ws)) == Nat.min(n, List.length(&2, B.OctByte, ws)) : Nat}:
  match n ws:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{x, t}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, B.OctByte, B.w8s.take(p, t)), Nat.min(p, List.length(&2, B.OctByte, t)), off.len_take(p, t))

def off.len_drop(+n: Nat, ws: List<&2, B.OctByte>) -> {List.length(&2, B.OctByte, B.w8s.drop(n, ws)) == Nat.sub(List.length(&2, B.OctByte, ws), n) : Nat}:
  match n ws:
    case 0n Nil{}:
      {==}
    case 0n Con{x, t}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{x, t}:
      off.len_drop(p, t)

def off.len_zeros(+n: Nat) -> {List.length(&2, B.OctByte, B.w8s.zeros(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, B.OctByte, B.w8s.zeros(p)), p, off.len_zeros(p))

def off.len_of(xs: List<&2, U32>) -> {List.length(&2, B.OctByte, B.w8s.of_list(xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, B.OctByte, B.w8s.of_list(t)), B.len(t), off.len_of(t))

def off.app_assoc(xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>, +zs: List<&2, B.OctByte>) -> {List.append(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys), zs) == List.append(&2, B.OctByte, xs, List.append(&2, B.OctByte, ys, zs)) : List<&2, B.OctByte>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => Con{h, l}, List.append(&2, B.OctByte, List.append(&2, B.OctByte, t, ys), zs), List.append(&2, B.OctByte, t, List.append(&2, B.OctByte, ys, zs)), off.app_assoc(t, ys, zs))

# a byte: at the head of what is left after the offset

def off.at_app_lt(+i: Nat, xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>) -> {Nat.is_lt(i, List.length(&2, B.OctByte, xs)) == True{} : Bool} -> {B.w8s.at(B.w8s.drop(i, List.append(&2, B.OctByte, xs, ys))) == B.w8s.at(B.w8s.drop(i, xs)) : Maybe<&2, U32>}:
  match i xs:
    case 0n Nil{}:
      h => off.no({B.w8s.at(ys) == None{} : Maybe<&2, U32>}, h)
    case 1n+p Nil{}:
      h => off.no({B.w8s.at(B.w8s.drop(1n+p, ys)) == None{} : Maybe<&2, U32>}, h)
    case 0n Con{x, t}:
      h => {==}
    case 1n+p Con{x, t}:
      h => off.at_app_lt(p, t, ys, h)

def off.at_take(+i: Nat, +n: Nat, ws: List<&2, B.OctByte>) -> {Nat.is_lt(i, n) == True{} : Bool} -> {B.w8s.at(B.w8s.drop(i, B.w8s.take(n, ws))) == B.w8s.at(B.w8s.drop(i, ws)) : Maybe<&2, U32>}:
  match i n ws:
    case 0n 0n _:
      h => off.no({B.w8s.at(Nil{}) == B.w8s.at(ws) : Maybe<&2, U32>}, h)
    case 1n+p 0n _:
      h => off.no({B.w8s.at(B.w8s.drop(1n+p, Nil{})) == B.w8s.at(B.w8s.drop(1n+p, ws)) : Maybe<&2, U32>}, h)
    case 0n 1n+q Nil{}:
      h => {==}
    case 0n 1n+q Con{x, t}:
      h => {==}
    case 1n+p 1n+q Nil{}:
      h => {==}
    case 1n+p 1n+q Con{x, t}:
      h => off.at_take(p, q, t, h)

def off.at_to(+i: Nat, ws: List<&2, B.OctByte>) -> {B.w8s.at(B.w8s.drop(i, ws)) == B.at(B.w8s.to_list(ws), i) : Maybe<&2, U32>}:
  match i ws:
    case 0n Nil{}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 0n Con{B.OctByte{a0, a1, a2, a3, a4, a5, a6, a7}, t}:
      {==}
    case 1n+p Con{x, t}:
      off.at_to(p, t)

# The list layer

def off.ldrop_app_add(a: List<&2, U32>, +n: Nat, +b: List<&2, U32>) -> {B.drop(Nat.add(B.len(a), n), B.append(a, b)) == B.drop(n, b) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      off.ldrop_app_add(t, n, b)

def off.lat_app_lt(+i: Nat, a: List<&2, U32>, +b: List<&2, U32>) -> {Nat.is_lt(i, B.len(a)) == True{} : Bool} -> {B.at(B.append(a, b), i) == B.at(a, i) : Maybe<&2, U32>}:
  match i a:
    case 0n Nil{}:
      h => off.no({B.at(b, 0n) == None{} : Maybe<&2, U32>}, h)
    case 1n+p Nil{}:
      h => off.no({B.at(b, 1n+p) == B.at(Nil{}, 1n+p) : Maybe<&2, U32>}, h)
    case 0n Con{x, t}:
      h => {==}
    case 1n+p Con{x, t}:
      h => off.lat_app_lt(p, t, b, h)

def off.ldrop_nil(+i: Nat) -> {B.drop(i, Nil{}) == Nil{} : List<&2, U32>}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def off.ldrop_drop(+j: Nat, +i: Nat, xs: List<&2, U32>) -> {B.drop(i, B.drop(j, xs)) == B.drop(Nat.add(j, i), xs) : List<&2, U32>}:
  match j xs:
    case 0n _:
      {==}
    case 1n+q Nil{}:
      off.ldrop_nil(i)
    case 1n+q Con{x, t}:
      off.ldrop_drop(q, i, t)

def off.lat_take(+i: Nat, +n: Nat, xs: List<&2, U32>) -> {Nat.is_lt(i, n) == True{} : Bool} -> {B.at(B.take(n, xs), i) == B.at(xs, i) : Maybe<&2, U32>}:
  match i n xs:
    case 0n 0n _:
      h => off.no({B.at(Nil{}, 0n) == B.at(xs, 0n) : Maybe<&2, U32>}, h)
    case 1n+p 0n _:
      h => off.no({B.at(Nil{}, 1n+p) == B.at(xs, 1n+p) : Maybe<&2, U32>}, h)
    case 0n 1n+q Nil{}:
      h => {==}
    case 0n 1n+q Con{x, t}:
      h => {==}
    case 1n+p 1n+q Nil{}:
      h => {==}
    case 1n+p 1n+q Con{x, t}:
      h => off.lat_take(p, q, t, h)

def off.llen_app(a: List<&2, U32>, +b: List<&2, U32>) -> {B.len(B.append(a, b)) == Nat.add(B.len(a), B.len(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, B.len(B.append(t, b)), Nat.add(B.len(t), B.len(b)), off.llen_app(t, b))

def off.llen_le32(+v: U32) -> {B.len(B.le32(v)) == 4n : Nat}:
  match v:
    case U32{w}:
      {==}

def off.llen_be32(+v: U32) -> {B.len(B.be32(v)) == 4n : Nat}:
  match v:
    case U32{w}:
      {==}

def off.llen_le16(+v: U32) -> {B.len(B.le16(v)) == 2n : Nat}:
  match v:
    case U32{w}:
      {==}

def off.llen_be16(+v: U32) -> {B.len(B.be16(v)) == 2n : Nat}:
  match v:
    case U32{w}:
      {==}

def off.add_le32(+x: U32, +y: U32) -> {Nat.add(B.len(B.le32(x)), B.len(B.le32(y))) == 8n : Nat}:
  match x y:
    case U32{a} U32{b}:
      {==}

def off.add_be32(+x: U32, +y: U32) -> {Nat.add(B.len(B.be32(x)), B.len(B.be32(y))) == 8n : Nat}:
  match x y:
    case U32{a} U32{b}:
      {==}

def off.llen_le64(+v: W.W64) -> {B.len(B.le64(v)) == 8n : Nat}:
  Equal.trans(Nat, B.len(B.le64(v)), Nat.add(B.len(B.le32(W.W64.lo(v))), B.len(B.le32(W.W64.hi(v)))), 8n, off.llen_app(B.le32(W.W64.lo(v)), B.le32(W.W64.hi(v))), off.add_le32(W.W64.lo(v), W.W64.hi(v)))

def off.llen_be64(+v: W.W64) -> {B.len(B.be64(v)) == 8n : Nat}:
  Equal.trans(Nat, B.len(B.be64(v)), Nat.add(B.len(B.be32(W.W64.hi(v))), B.len(B.be32(W.W64.lo(v)))), 8n, off.llen_app(B.be32(W.W64.hi(v)), B.be32(W.W64.lo(v))), off.add_be32(W.W64.hi(v), W.W64.lo(v)))

# Octets: lengths

def p_len_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.len(B.Octets.append(a, b)) == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_app(xs, ys) : {B.w8s.len.fast(_) == Nat.add(B.w8s.len.fast(xs), B.w8s.len.fast(ys)) : Nat}
      %F_len(List.append(&2, B.OctByte, xs, ys)) : {_ == Nat.add(B.w8s.len.fast(xs), B.w8s.len.fast(ys)) : Nat}
      %F_len(xs) : {List.length(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys)) == Nat.add(_, B.w8s.len.fast(ys)) : Nat}
      %F_len(ys) : {List.length(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys)) == Nat.add(List.length(&2, B.OctByte, xs), _) : Nat}
      w8s_len_app(xs, ys)

def p_len_take(+n: Nat, +o: B.Octets) -> {B.Octets.len(B.Octets.take(n, o)) == Nat.min(n, B.Octets.len(o)) : Nat}:
  match o:
    case B.Octets{+ws}:
      %F_take(n, ws) : {B.w8s.len.fast(_) == Nat.min(n, B.w8s.len.fast(ws)) : Nat}
      %F_len(B.w8s.take(n, ws)) : {_ == Nat.min(n, B.w8s.len.fast(ws)) : Nat}
      %F_len(ws) : {List.length(&2, B.OctByte, B.w8s.take(n, ws)) == Nat.min(n, _) : Nat}
      off.len_take(n, ws)

def p_len_drop(+n: Nat, +o: B.Octets) -> {B.Octets.len(B.Octets.drop(n, o)) == Nat.sub(B.Octets.len(o), n) : Nat}:
  match o:
    case B.Octets{+ws}:
      %F_len(B.w8s.drop(n, ws)) : {_ == Nat.sub(B.w8s.len.fast(ws), n) : Nat}
      %F_len(ws) : {List.length(&2, B.OctByte, B.w8s.drop(n, ws)) == Nat.sub(_, n) : Nat}
      off.len_drop(n, ws)

def p_len_take_le(+n: Nat, +o: B.Octets, h: {Nat.is_le(n, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.len(B.Octets.take(n, o)) == n : Nat}:
  Equal.trans(Nat, B.Octets.len(B.Octets.take(n, o)), Nat.min(n, B.Octets.len(o)), n, p_len_take(n, o), off.min_le(n, B.Octets.len(o), h))

def p_len_slice(+i: Nat, +n: Nat, +o: B.Octets) -> {B.Octets.len(B.Octets.slice(i, n, o)) == Nat.min(n, Nat.sub(B.Octets.len(o), i)) : Nat}:
  Equal.trans(Nat, B.Octets.len(B.Octets.take(n, B.Octets.drop(i, o))), Nat.min(n, B.Octets.len(B.Octets.drop(i, o))), Nat.min(n, Nat.sub(B.Octets.len(o), i)),
    p_len_take(n, B.Octets.drop(i, o)),
    Equal.cong(Nat, Nat, k => Nat.min(n, k), B.Octets.len(B.Octets.drop(i, o)), Nat.sub(B.Octets.len(o), i), p_len_drop(i, o)))

def p_len_slice_le(+i: Nat, +n: Nat, +o: B.Octets, h: {Nat.is_le(Nat.add(i, n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.len(B.Octets.slice(i, n, o)) == n : Nat}:
  Equal.trans(Nat, B.Octets.len(B.Octets.slice(i, n, o)), Nat.min(n, Nat.sub(B.Octets.len(o), i)), n, p_len_slice(i, n, o), off.min_le(n, Nat.sub(B.Octets.len(o), i), off.le_sub(i, n, B.Octets.len(o), h)))

def p_len_zeros(+n: Nat) -> {B.Octets.len(B.Octets.zeros(n)) == n : Nat}:
  %F_zeros(n) : {B.w8s.len.fast(_) == n : Nat}
  %F_len(B.w8s.zeros(n)) : {_ == n : Nat}
  off.len_zeros(n)

def p_len_of_list(+xs: List<&2, U32>) -> {B.Octets.len(B.Octets.of_list(xs)) == B.len(xs) : Nat}:
  %F_of(xs) : {B.w8s.len.fast(_) == B.len(xs) : Nat}
  %F_len(B.w8s.of_list(xs)) : {_ == B.len(xs) : Nat}
  off.len_of(xs)

def p_append_assoc(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.append(B.Octets.append(a, b), c) == B.Octets.append(a, B.Octets.append(b, c)) : B.Octets}:
  match a b c:
    case B.Octets{+xs} B.Octets{+ys} B.Octets{+zs}:
      %F_app(xs, ys) : {B.Octets{B.w8s.append.fast(_, zs)} == B.Octets{B.w8s.append.fast(xs, B.w8s.append.fast(ys, zs))} : B.Octets}
      %F_app(ys, zs) : {B.Octets{B.w8s.append.fast(List.append(&2, B.OctByte, xs, ys), zs)} == B.Octets{B.w8s.append.fast(xs, _)} : B.Octets}
      %F_app(List.append(&2, B.OctByte, xs, ys), zs) : {B.Octets{_} == B.Octets{B.w8s.append.fast(xs, List.append(&2, B.OctByte, ys, zs))} : B.Octets}
      %F_app(xs, List.append(&2, B.OctByte, ys, zs)) : {B.Octets{List.append(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys), zs)} == B.Octets{_} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, List.append(&2, B.OctByte, List.append(&2, B.OctByte, xs, ys), zs), List.append(&2, B.OctByte, xs, List.append(&2, B.OctByte, ys, zs)), off.app_assoc(xs, ys, zs))

# Octets: take and drop composed

def p_drop_drop(+j: Nat, +i: Nat, +o: B.Octets) -> {B.Octets.drop(i, B.Octets.drop(j, o)) == B.Octets.drop(Nat.add(j, i), o) : B.Octets}:
  match o:
    case B.Octets{+ws}:
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.drop(i, B.w8s.drop(j, ws)), B.w8s.drop(Nat.add(j, i), ws), off.drop_drop(j, i, ws))

def p_take_take(+i: Nat, +j: Nat, +o: B.Octets) -> {B.Octets.take(i, B.Octets.take(j, o)) == B.Octets.take(Nat.min(i, j), o) : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_take(j, ws) : {B.Octets{B.w8s.take.fast(i, _)} == B.Octets{B.w8s.take.fast(Nat.min(i, j), ws)} : B.Octets}
      %F_take(i, B.w8s.take(j, ws)) : {B.Octets{_} == B.Octets{B.w8s.take.fast(Nat.min(i, j), ws)} : B.Octets}
      %F_take(Nat.min(i, j), ws) : {B.Octets{B.w8s.take(i, B.w8s.take(j, ws))} == B.Octets{_} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.take(i, B.w8s.take(j, ws)), B.w8s.take(Nat.min(i, j), ws), off.take_take(i, j, ws))

def p_take_drop(+i: Nat, +j: Nat, +o: B.Octets) -> {B.Octets.take(i, B.Octets.drop(j, o)) == B.Octets.drop(j, B.Octets.take(Nat.add(j, i), o)) : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_take(i, B.w8s.drop(j, ws)) : {B.Octets{_} == B.Octets{B.w8s.drop(j, B.w8s.take.fast(Nat.add(j, i), ws))} : B.Octets}
      %F_take(Nat.add(j, i), ws) : {B.Octets{B.w8s.take(i, B.w8s.drop(j, ws))} == B.Octets{B.w8s.drop(j, _)} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.take(i, B.w8s.drop(j, ws)), B.w8s.drop(j, B.w8s.take(Nat.add(j, i), ws)), off.take_drop(i, j, ws))

def p_drop_take(+i: Nat, +j: Nat, +o: B.Octets) -> {B.Octets.drop(i, B.Octets.take(j, o)) == B.Octets.take(Nat.sub(j, i), B.Octets.drop(i, o)) : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_take(j, ws) : {B.Octets{B.w8s.drop(i, _)} == B.Octets{B.w8s.take.fast(Nat.sub(j, i), B.w8s.drop(i, ws))} : B.Octets}
      %F_take(Nat.sub(j, i), B.w8s.drop(i, ws)) : {B.Octets{B.w8s.drop(i, B.w8s.take(j, ws))} == B.Octets{_} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.drop(i, B.w8s.take(j, ws)), B.w8s.take(Nat.sub(j, i), B.w8s.drop(i, ws)), off.drop_take(i, j, ws))

# Octets: take and drop inside joined bytes

def off.len_fast_le(+n: Nat, +xs: List<&2, B.OctByte>, h: {Nat.is_le(n, B.w8s.len.fast(xs)) == True{} : Bool}) -> {Nat.is_le(n, List.length(&2, B.OctByte, xs)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(n, List.length(&2, B.OctByte, xs)), Nat.is_le(n, B.w8s.len.fast(xs)), True{}, Equal.cong(Nat, Bool, k => Nat.is_le(n, k), List.length(&2, B.OctByte, xs), B.w8s.len.fast(xs), F_len(xs)), h)

def off.len_fast_lt(+n: Nat, +xs: List<&2, B.OctByte>, h: {Nat.is_lt(n, B.w8s.len.fast(xs)) == True{} : Bool}) -> {Nat.is_lt(n, List.length(&2, B.OctByte, xs)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(n, List.length(&2, B.OctByte, xs)), Nat.is_lt(n, B.w8s.len.fast(xs)), True{}, Equal.cong(Nat, Bool, k => Nat.is_lt(n, k), List.length(&2, B.OctByte, xs), B.w8s.len.fast(xs), F_len(xs)), h)

def q_take_app_le(+n: Nat, +xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>, h: {Nat.is_le(n, List.length(&2, B.OctByte, xs)) == True{} : Bool}) -> {B.Octets{B.w8s.take.fast(n, B.w8s.append.fast(xs, ys))} == B.Octets{B.w8s.take.fast(n, xs)} : B.Octets}:
  %F_app(xs, ys) : {B.Octets{B.w8s.take.fast(n, _)} == B.Octets{B.w8s.take.fast(n, xs)} : B.Octets}
  %F_take(n, List.append(&2, B.OctByte, xs, ys)) : {B.Octets{_} == B.Octets{B.w8s.take.fast(n, xs)} : B.Octets}
  %F_take(n, xs) : {B.Octets{B.w8s.take(n, List.append(&2, B.OctByte, xs, ys))} == B.Octets{_} : B.Octets}
  Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.take(n, List.append(&2, B.OctByte, xs, ys)), B.w8s.take(n, xs), off.take_app_le(n, xs, ys, h))

def p_take_append_le(+n: Nat, +a: B.Octets, +b: B.Octets) -> {Nat.is_le(n, B.Octets.len(a)) == True{} : Bool} -> {B.Octets.take(n, B.Octets.append(a, b)) == B.Octets.take(n, a) : B.Octets}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      h => q_take_app_le(n, xs, ys, off.len_fast_le(n, xs, h))

def p_take_append_add(+a: B.Octets, +n: Nat, +b: B.Octets) -> {B.Octets.take(Nat.add(B.Octets.len(a), n), B.Octets.append(a, b)) == B.Octets.append(a, B.Octets.take(n, b)) : B.Octets}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_app(xs, ys) : {B.Octets{B.w8s.take.fast(Nat.add(B.w8s.len.fast(xs), n), _)} == B.Octets{B.w8s.append.fast(xs, B.w8s.take.fast(n, ys))} : B.Octets}
      %F_len(xs) : {B.Octets{B.w8s.take.fast(Nat.add(_, n), List.append(&2, B.OctByte, xs, ys))} == B.Octets{B.w8s.append.fast(xs, B.w8s.take.fast(n, ys))} : B.Octets}
      %F_take(Nat.add(List.length(&2, B.OctByte, xs), n), List.append(&2, B.OctByte, xs, ys)) : {B.Octets{_} == B.Octets{B.w8s.append.fast(xs, B.w8s.take.fast(n, ys))} : B.Octets}
      %F_take(n, ys) : {B.Octets{B.w8s.take(Nat.add(List.length(&2, B.OctByte, xs), n), List.append(&2, B.OctByte, xs, ys))} == B.Octets{B.w8s.append.fast(xs, _)} : B.Octets}
      %F_app(xs, B.w8s.take(n, ys)) : {B.Octets{B.w8s.take(Nat.add(List.length(&2, B.OctByte, xs), n), List.append(&2, B.OctByte, xs, ys))} == B.Octets{_} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.take(Nat.add(List.length(&2, B.OctByte, xs), n), List.append(&2, B.OctByte, xs, ys)), List.append(&2, B.OctByte, xs, B.w8s.take(n, ys)), off.take_app_add(xs, n, ys))

def q_drop_app_le(+n: Nat, +xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>, h: {Nat.is_le(n, List.length(&2, B.OctByte, xs)) == True{} : Bool}) -> {B.Octets{B.w8s.drop(n, B.w8s.append.fast(xs, ys))} == B.Octets{B.w8s.append.fast(B.w8s.drop(n, xs), ys)} : B.Octets}:
  %F_app(xs, ys) : {B.Octets{B.w8s.drop(n, _)} == B.Octets{B.w8s.append.fast(B.w8s.drop(n, xs), ys)} : B.Octets}
  %F_app(B.w8s.drop(n, xs), ys) : {B.Octets{B.w8s.drop(n, List.append(&2, B.OctByte, xs, ys))} == B.Octets{_} : B.Octets}
  Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.drop(n, List.append(&2, B.OctByte, xs, ys)), List.append(&2, B.OctByte, B.w8s.drop(n, xs), ys), off.drop_app_le(n, xs, ys, h))

def p_drop_append_le(+n: Nat, +a: B.Octets, +b: B.Octets) -> {Nat.is_le(n, B.Octets.len(a)) == True{} : Bool} -> {B.Octets.drop(n, B.Octets.append(a, b)) == B.Octets.append(B.Octets.drop(n, a), b) : B.Octets}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      h => q_drop_app_le(n, xs, ys, off.len_fast_le(n, xs, h))

def p_drop_append_add(+a: B.Octets, +n: Nat, +b: B.Octets) -> {B.Octets.drop(Nat.add(B.Octets.len(a), n), B.Octets.append(a, b)) == B.Octets.drop(n, b) : B.Octets}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_app(xs, ys) : {B.Octets{B.w8s.drop(Nat.add(B.w8s.len.fast(xs), n), _)} == B.Octets{B.w8s.drop(n, ys)} : B.Octets}
      %F_len(xs) : {B.Octets{B.w8s.drop(Nat.add(_, n), List.append(&2, B.OctByte, xs, ys))} == B.Octets{B.w8s.drop(n, ys)} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.drop(Nat.add(List.length(&2, B.OctByte, xs), n), List.append(&2, B.OctByte, xs, ys)), B.w8s.drop(n, ys), off.drop_app_add(xs, n, ys))

# Octets: slices

def p_slice_append_add(+a: B.Octets, +i: Nat, +n: Nat, +b: B.Octets) -> {B.Octets.slice(Nat.add(B.Octets.len(a), i), n, B.Octets.append(a, b)) == B.Octets.slice(i, n, b) : B.Octets}:
  Equal.cong(B.Octets, B.Octets, x => B.Octets.take(n, x), B.Octets.drop(Nat.add(B.Octets.len(a), i), B.Octets.append(a, b)), B.Octets.drop(i, b), p_drop_append_add(a, i, b))

def p_slice_append_le(+i: Nat, +n: Nat, +a: B.Octets, +b: B.Octets, +h: {Nat.is_le(Nat.add(i, n), B.Octets.len(a)) == True{} : Bool}) -> {B.Octets.slice(i, n, B.Octets.append(a, b)) == B.Octets.slice(i, n, a) : B.Octets}:
  Equal.trans(B.Octets, B.Octets.take(n, B.Octets.drop(i, B.Octets.append(a, b))), B.Octets.take(n, B.Octets.append(B.Octets.drop(i, a), b)), B.Octets.take(n, B.Octets.drop(i, a)),
    Equal.cong(B.Octets, B.Octets, x => B.Octets.take(n, x), B.Octets.drop(i, B.Octets.append(a, b)), B.Octets.append(B.Octets.drop(i, a), b), p_drop_append_le(i, a, b, off.le_add_l(i, n, B.Octets.len(a), h))),
    p_take_append_le(n, B.Octets.drop(i, a), b,
      Equal.trans(Bool, Nat.is_le(n, B.Octets.len(B.Octets.drop(i, a))), Nat.is_le(n, Nat.sub(B.Octets.len(a), i)), True{},
        Equal.cong(Nat, Bool, k => Nat.is_le(n, k), B.Octets.len(B.Octets.drop(i, a)), Nat.sub(B.Octets.len(a), i), p_len_drop(i, a)),
        off.le_sub(i, n, B.Octets.len(a), h))))

def p_slice_drop(+j: Nat, +i: Nat, +n: Nat, +o: B.Octets) -> {B.Octets.slice(i, n, B.Octets.drop(j, o)) == B.Octets.slice(Nat.add(j, i), n, o) : B.Octets}:
  Equal.cong(B.Octets, B.Octets, x => B.Octets.take(n, x), B.Octets.drop(i, B.Octets.drop(j, o)), B.Octets.drop(Nat.add(j, i), o), p_drop_drop(j, i, o))

def p_slice_take(+m: Nat, +i: Nat, +n: Nat, +o: B.Octets, +h: {Nat.is_le(Nat.add(i, n), m) == True{} : Bool}) -> {B.Octets.slice(i, n, B.Octets.take(m, o)) == B.Octets.slice(i, n, o) : B.Octets}:
  Equal.trans(B.Octets, B.Octets.take(n, B.Octets.drop(i, B.Octets.take(m, o))), B.Octets.take(n, B.Octets.take(Nat.sub(m, i), B.Octets.drop(i, o))), B.Octets.take(n, B.Octets.drop(i, o)),
    Equal.cong(B.Octets, B.Octets, x => B.Octets.take(n, x), B.Octets.drop(i, B.Octets.take(m, o)), B.Octets.take(Nat.sub(m, i), B.Octets.drop(i, o)), p_drop_take(i, m, o)),
    Equal.trans(B.Octets, B.Octets.take(n, B.Octets.take(Nat.sub(m, i), B.Octets.drop(i, o))), B.Octets.take(Nat.min(n, Nat.sub(m, i)), B.Octets.drop(i, o)), B.Octets.take(n, B.Octets.drop(i, o)),
      p_take_take(n, Nat.sub(m, i), B.Octets.drop(i, o)),
      Equal.cong(Nat, B.Octets, k => B.Octets.take(k, B.Octets.drop(i, o)), Nat.min(n, Nat.sub(m, i)), n, off.min_le(n, Nat.sub(m, i), off.le_sub(i, n, m, h)))))

# Octets: a byte at an offset

def p_at_list(+o: B.Octets, +i: Nat) -> {B.Octets.at(o, i) == B.at(B.Octets.to_list(o), i) : Maybe<&2, U32>}:
  match o:
    case B.Octets{+ws}:
      %F_to(ws) : {B.w8s.at(B.w8s.drop(i, ws)) == B.at(_, i) : Maybe<&2, U32>}
      off.at_to(i, ws)

def p_at_append_add(+a: B.Octets, +b: B.Octets, +i: Nat) -> {B.Octets.at(B.Octets.append(a, b), Nat.add(B.Octets.len(a), i)) == B.Octets.at(b, i) : Maybe<&2, U32>}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      %F_app(xs, ys) : {B.w8s.at(B.w8s.drop(Nat.add(B.w8s.len.fast(xs), i), _)) == B.w8s.at(B.w8s.drop(i, ys)) : Maybe<&2, U32>}
      %F_len(xs) : {B.w8s.at(B.w8s.drop(Nat.add(_, i), List.append(&2, B.OctByte, xs, ys))) == B.w8s.at(B.w8s.drop(i, ys)) : Maybe<&2, U32>}
      Equal.cong(List<&2, B.OctByte>, Maybe<&2, U32>, l => B.w8s.at(l), B.w8s.drop(Nat.add(List.length(&2, B.OctByte, xs), i), List.append(&2, B.OctByte, xs, ys)), B.w8s.drop(i, ys), off.drop_app_add(xs, i, ys))

def q_at_app_lt(+i: Nat, +xs: List<&2, B.OctByte>, +ys: List<&2, B.OctByte>, h: {Nat.is_lt(i, List.length(&2, B.OctByte, xs)) == True{} : Bool}) -> {B.w8s.at(B.w8s.drop(i, B.w8s.append.fast(xs, ys))) == B.w8s.at(B.w8s.drop(i, xs)) : Maybe<&2, U32>}:
  %F_app(xs, ys) : {B.w8s.at(B.w8s.drop(i, _)) == B.w8s.at(B.w8s.drop(i, xs)) : Maybe<&2, U32>}
  off.at_app_lt(i, xs, ys, h)

def p_at_append_lt(+a: B.Octets, +b: B.Octets, +i: Nat) -> {Nat.is_lt(i, B.Octets.len(a)) == True{} : Bool} -> {B.Octets.at(B.Octets.append(a, b), i) == B.Octets.at(a, i) : Maybe<&2, U32>}:
  match a b:
    case B.Octets{+xs} B.Octets{+ys}:
      h => q_at_app_lt(i, xs, ys, off.len_fast_lt(i, xs, h))

def p_at_drop(+j: Nat, +o: B.Octets, +i: Nat) -> {B.Octets.at(B.Octets.drop(j, o), i) == B.Octets.at(o, Nat.add(j, i)) : Maybe<&2, U32>}:
  match o:
    case B.Octets{+ws}:
      Equal.cong(List<&2, B.OctByte>, Maybe<&2, U32>, l => B.w8s.at(l), B.w8s.drop(i, B.w8s.drop(j, ws)), B.w8s.drop(Nat.add(j, i), ws), off.drop_drop(j, i, ws))

def p_at_take(+n: Nat, +o: B.Octets, +i: Nat, h: {Nat.is_lt(i, n) == True{} : Bool}) -> {B.Octets.at(B.Octets.take(n, o), i) == B.Octets.at(o, i) : Maybe<&2, U32>}:
  match o:
    case B.Octets{+ws}:
      %F_take(n, ws) : {B.w8s.at(B.w8s.drop(i, _)) == B.w8s.at(B.w8s.drop(i, ws)) : Maybe<&2, U32>}
      off.at_take(i, n, ws, h)

# Every word ANDed with zero is zero (for low16_mask)

def off.band_f(+b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def off.wand_zero(+n: Nat, w: Word(n)) -> {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, t}:
          %Equal.sym(Bool, Bool.and(b, False{}), False{}, off.band_f(b)) : {WCon{_, Word.and(p, t, Word.zero(p))} == Word.zero(1n+p) : Word(1n+p)}
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.and(p, t, Word.zero(p)), Word.zero(p), off.wand_zero(p, t))

# The laws

def Laws.octets_len_append(a, b):
  p_len_append(a, b)

def Laws.octets_len_take(n, o):
  p_len_take(n, o)

def Laws.octets_len_take_le(n, o, h):
  p_len_take_le(n, o, h)

def Laws.octets_len_drop(n, o):
  p_len_drop(n, o)

def Laws.octets_len_slice(i, n, o):
  p_len_slice(i, n, o)

def Laws.octets_len_slice_le(i, n, o, h):
  p_len_slice_le(i, n, o, h)

def Laws.octets_len_zeros(n):
  p_len_zeros(n)

def Laws.octets_len_of_list(xs):
  p_len_of_list(xs)

def Laws.octets_append_assoc(a, b, c):
  p_append_assoc(a, b, c)

def p_append_empty_l(+o: B.Octets) -> {B.Octets.append(B.Octets.empty(), o) == o : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_app(Nil{}, ws) : {B.Octets{_} == B.Octets{ws} : B.Octets}
      {==}

def p_append_empty_r(+o: B.Octets) -> {B.Octets.append(o, B.Octets.empty()) == o : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_app(ws, Nil{}) : {B.Octets{_} == B.Octets{ws} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, List.append(&2, B.OctByte, ws, Nil{}), ws, app_nil8(ws))

def off.take_len(ws: List<&2, B.OctByte>) -> {B.w8s.take(List.length(&2, B.OctByte, ws), ws) == ws : List<&2, B.OctByte>}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, B.OctByte>, List<&2, B.OctByte>, l => Con{h, l}, B.w8s.take(List.length(&2, B.OctByte, t), t), t, off.take_len(t))

def p_take_len(+o: B.Octets) -> {B.Octets.take(B.Octets.len(o), o) == o : B.Octets}:
  match o:
    case B.Octets{+ws}:
      %F_take(B.w8s.len.fast(ws), ws) : {B.Octets{_} == B.Octets{ws} : B.Octets}
      %F_len(ws) : {B.Octets{B.w8s.take(_, ws)} == B.Octets{ws} : B.Octets}
      Equal.cong(List<&2, B.OctByte>, B.Octets, l => B.Octets{l}, B.w8s.take(List.length(&2, B.OctByte, ws), ws), ws, off.take_len(ws))

def Laws.octets_drop_zero(o):
  match o:
    case B.Octets{ws}:
      {==}

def Laws.octets_take_len(o):
  p_take_len(o)

def Laws.octets_append_empty_l(o):
  p_append_empty_l(o)

def Laws.octets_append_empty_r(o):
  p_append_empty_r(o)

def Laws.octets_drop_drop(j, i, o):
  p_drop_drop(j, i, o)

def Laws.octets_take_take(i, j, o):
  p_take_take(i, j, o)

def Laws.octets_take_drop_comm(i, j, o):
  p_take_drop(i, j, o)

def Laws.octets_drop_take_comm(i, j, o):
  p_drop_take(i, j, o)

def Laws.octets_take_append_le(n, a, b, h):
  p_take_append_le(n, a, b, h)

def Laws.octets_take_append_add(a, n, b):
  p_take_append_add(a, n, b)

def Laws.octets_drop_append_le(n, a, b, h):
  p_drop_append_le(n, a, b, h)

def Laws.octets_drop_append_add(a, n, b):
  p_drop_append_add(a, n, b)

def Laws.octets_slice_append_add(a, i, n, b):
  p_slice_append_add(a, i, n, b)

def Laws.octets_slice_append_le(i, n, a, b, h):
  p_slice_append_le(i, n, a, b, h)

def Laws.octets_slice_drop(j, i, n, o):
  p_slice_drop(j, i, n, o)

def Laws.octets_slice_take(m, i, n, o, h):
  p_slice_take(m, i, n, o, h)

def Laws.octets_at_list(o, i):
  p_at_list(o, i)

def Laws.octets_at_append_add(a, b, i):
  p_at_append_add(a, b, i)

def Laws.octets_at_append_lt(a, b, i, h):
  p_at_append_lt(a, b, i, h)

def Laws.octets_at_drop(j, o, i):
  p_at_drop(j, o, i)

def Laws.octets_at_take(n, o, i, h):
  p_at_take(n, o, i, h)

def Laws.at_append_add(a, b, i):
  Equal.cong(List<&2, U32>, Maybe<&2, U32>, l => B.at.head(l), B.drop(Nat.add(B.len(a), i), B.append(a, b)), B.drop(i, b), off.ldrop_app_add(a, i, b))

def Laws.at_append_lt(a, b, i, h):
  off.lat_app_lt(i, a, b, h)

def Laws.at_drop(j, xs, i):
  Equal.cong(List<&2, U32>, Maybe<&2, U32>, l => B.at.head(l), B.drop(i, B.drop(j, xs)), B.drop(Nat.add(j, i), xs), off.ldrop_drop(j, i, xs))

def Laws.at_take(n, xs, i, h):
  off.lat_take(i, n, xs, h)

def Laws.octets_len_le16(v):
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(B.le16(v))), B.len(B.le16(v)), 2n, p_len_of_list(B.le16(v)), off.llen_le16(v))

def Laws.octets_len_be16(v):
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(B.be16(v))), B.len(B.be16(v)), 2n, p_len_of_list(B.be16(v)), off.llen_be16(v))

def Laws.octets_len_le32(v):
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(B.le32(v))), B.len(B.le32(v)), 4n, p_len_of_list(B.le32(v)), off.llen_le32(v))

def Laws.octets_len_be32(v):
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(B.be32(v))), B.len(B.be32(v)), 4n, p_len_of_list(B.be32(v)), off.llen_be32(v))

def Laws.octets_len_le64(v):
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(B.le64(v))), B.len(B.le64(v)), 8n, p_len_of_list(B.le64(v)), off.llen_le64(v))

def Laws.octets_len_be64(v):
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(B.be64(v))), B.len(B.be64(v)), 8n, p_len_of_list(B.be64(v)), off.llen_be64(v))

def Laws.octets_le16_at_append_add(a, b, i):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.le16.head(B.Octets.to_list(s)), B.Octets.slice(Nat.add(B.Octets.len(a), i), 2n, B.Octets.append(a, b)), B.Octets.slice(i, 2n, b), p_slice_append_add(a, i, 2n, b))

def Laws.octets_le16_at_append_le(a, b, i, h):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.le16.head(B.Octets.to_list(s)), B.Octets.slice(i, 2n, B.Octets.append(a, b)), B.Octets.slice(i, 2n, a), p_slice_append_le(i, 2n, a, b, h))

def Laws.octets_le16_at_drop(j, o, i):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.le16.head(B.Octets.to_list(s)), B.Octets.slice(i, 2n, B.Octets.drop(j, o)), B.Octets.slice(Nat.add(j, i), 2n, o), p_slice_drop(j, i, 2n, o))

def Laws.octets_le16_at_take(n, o, i, h):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.le16.head(B.Octets.to_list(s)), B.Octets.slice(i, 2n, B.Octets.take(n, o)), B.Octets.slice(i, 2n, o), p_slice_take(n, i, 2n, o, h))

def Laws.octets_be16_at_append_add(a, b, i):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.be16.head(B.Octets.to_list(s)), B.Octets.slice(Nat.add(B.Octets.len(a), i), 2n, B.Octets.append(a, b)), B.Octets.slice(i, 2n, b), p_slice_append_add(a, i, 2n, b))

def Laws.octets_be16_at_append_le(a, b, i, h):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.be16.head(B.Octets.to_list(s)), B.Octets.slice(i, 2n, B.Octets.append(a, b)), B.Octets.slice(i, 2n, a), p_slice_append_le(i, 2n, a, b, h))

def Laws.octets_be16_at_drop(j, o, i):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.be16.head(B.Octets.to_list(s)), B.Octets.slice(i, 2n, B.Octets.drop(j, o)), B.Octets.slice(Nat.add(j, i), 2n, o), p_slice_drop(j, i, 2n, o))

def Laws.octets_be16_at_take(n, o, i, h):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.be16.head(B.Octets.to_list(s)), B.Octets.slice(i, 2n, B.Octets.take(n, o)), B.Octets.slice(i, 2n, o), p_slice_take(n, i, 2n, o, h))

def Laws.octets_le32_at_append_add(a, b, i):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.le32.head(B.Octets.to_list(s)), B.Octets.slice(Nat.add(B.Octets.len(a), i), 4n, B.Octets.append(a, b)), B.Octets.slice(i, 4n, b), p_slice_append_add(a, i, 4n, b))

def Laws.octets_le32_at_append_le(a, b, i, h):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.le32.head(B.Octets.to_list(s)), B.Octets.slice(i, 4n, B.Octets.append(a, b)), B.Octets.slice(i, 4n, a), p_slice_append_le(i, 4n, a, b, h))

def Laws.octets_le32_at_drop(j, o, i):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.le32.head(B.Octets.to_list(s)), B.Octets.slice(i, 4n, B.Octets.drop(j, o)), B.Octets.slice(Nat.add(j, i), 4n, o), p_slice_drop(j, i, 4n, o))

def Laws.octets_le32_at_take(n, o, i, h):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.le32.head(B.Octets.to_list(s)), B.Octets.slice(i, 4n, B.Octets.take(n, o)), B.Octets.slice(i, 4n, o), p_slice_take(n, i, 4n, o, h))

def Laws.octets_be32_at_append_add(a, b, i):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.be32.head(B.Octets.to_list(s)), B.Octets.slice(Nat.add(B.Octets.len(a), i), 4n, B.Octets.append(a, b)), B.Octets.slice(i, 4n, b), p_slice_append_add(a, i, 4n, b))

def Laws.octets_be32_at_append_le(a, b, i, h):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.be32.head(B.Octets.to_list(s)), B.Octets.slice(i, 4n, B.Octets.append(a, b)), B.Octets.slice(i, 4n, a), p_slice_append_le(i, 4n, a, b, h))

def Laws.octets_be32_at_drop(j, o, i):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.be32.head(B.Octets.to_list(s)), B.Octets.slice(i, 4n, B.Octets.drop(j, o)), B.Octets.slice(Nat.add(j, i), 4n, o), p_slice_drop(j, i, 4n, o))

def Laws.octets_be32_at_take(n, o, i, h):
  Equal.cong(B.Octets, Maybe<&2, U32>, s => B.be32.head(B.Octets.to_list(s)), B.Octets.slice(i, 4n, B.Octets.take(n, o)), B.Octets.slice(i, 4n, o), p_slice_take(n, i, 4n, o, h))

def Laws.octets_le64_at_append_add(a, b, i):
  Equal.cong(B.Octets, Maybe<&2, W.W64>, s => B.le64_at(B.Octets.to_list(s), 0n), B.Octets.slice(Nat.add(B.Octets.len(a), i), 8n, B.Octets.append(a, b)), B.Octets.slice(i, 8n, b), p_slice_append_add(a, i, 8n, b))

def Laws.octets_le64_at_append_le(a, b, i, h):
  Equal.cong(B.Octets, Maybe<&2, W.W64>, s => B.le64_at(B.Octets.to_list(s), 0n), B.Octets.slice(i, 8n, B.Octets.append(a, b)), B.Octets.slice(i, 8n, a), p_slice_append_le(i, 8n, a, b, h))

def Laws.octets_le64_at_drop(j, o, i):
  Equal.cong(B.Octets, Maybe<&2, W.W64>, s => B.le64_at(B.Octets.to_list(s), 0n), B.Octets.slice(i, 8n, B.Octets.drop(j, o)), B.Octets.slice(Nat.add(j, i), 8n, o), p_slice_drop(j, i, 8n, o))

def Laws.octets_le64_at_take(n, o, i, h):
  Equal.cong(B.Octets, Maybe<&2, W.W64>, s => B.le64_at(B.Octets.to_list(s), 0n), B.Octets.slice(i, 8n, B.Octets.take(n, o)), B.Octets.slice(i, 8n, o), p_slice_take(n, i, 8n, o, h))

def Laws.octets_be64_at_append_add(a, b, i):
  Equal.cong(B.Octets, Maybe<&2, W.W64>, s => B.be64_at(B.Octets.to_list(s), 0n), B.Octets.slice(Nat.add(B.Octets.len(a), i), 8n, B.Octets.append(a, b)), B.Octets.slice(i, 8n, b), p_slice_append_add(a, i, 8n, b))

def Laws.octets_be64_at_append_le(a, b, i, h):
  Equal.cong(B.Octets, Maybe<&2, W.W64>, s => B.be64_at(B.Octets.to_list(s), 0n), B.Octets.slice(i, 8n, B.Octets.append(a, b)), B.Octets.slice(i, 8n, a), p_slice_append_le(i, 8n, a, b, h))

def Laws.octets_be64_at_drop(j, o, i):
  Equal.cong(B.Octets, Maybe<&2, W.W64>, s => B.be64_at(B.Octets.to_list(s), 0n), B.Octets.slice(i, 8n, B.Octets.drop(j, o)), B.Octets.slice(Nat.add(j, i), 8n, o), p_slice_drop(j, i, 8n, o))

def Laws.octets_be64_at_take(n, o, i, h):
  Equal.cong(B.Octets, Maybe<&2, W.W64>, s => B.be64_at(B.Octets.to_list(s), 0n), B.Octets.slice(i, 8n, B.Octets.take(n, o)), B.Octets.slice(i, 8n, o), p_slice_take(n, i, 8n, o, h))

def Laws.low16_mask(v):
  match v:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, t}}}}}}}}}}}}}}}}}:
      Equal.cong(Word(16n), U32, z => U32{WCon{Bool.and(x0, True{}), WCon{Bool.and(x1, True{}), WCon{Bool.and(x2, True{}), WCon{Bool.and(x3, True{}), WCon{Bool.and(x4, True{}), WCon{Bool.and(x5, True{}), WCon{Bool.and(x6, True{}), WCon{Bool.and(x7, True{}), WCon{Bool.and(x8, True{}), WCon{Bool.and(x9, True{}), WCon{Bool.and(x10, True{}), WCon{Bool.and(x11, True{}), WCon{Bool.and(x12, True{}), WCon{Bool.and(x13, True{}), WCon{Bool.and(x14, True{}), WCon{Bool.and(x15, True{}), z}}}}}}}}}}}}}}}}}, Word.zero(16n), Word.and(16n, t, Word.zero(16n)), Equal.sym(Word(16n), Word.and(16n, t, Word.zero(16n)), Word.zero(16n), off.wand_zero(16n, t)))
