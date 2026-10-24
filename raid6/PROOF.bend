# Proofs. The field algebra comes from bend-osdev-gf's laws (commutativity,
# associativity, distributivity, 1, 0, inverses in the paper's field,
# powers) and its public bit representation Gf8Bits; blocks are reasoned
# about through bytes' interface laws (octets_of_to, octets_to_of,
# octets_len_list, octets_zeros_list) and xorblocks' laws (its algebra, and
# xor_list, the bytewise meaning of Xorb.xor), never through how Octets
# stores its bytes or how xorblocks computes.
#
# The plan:
#   A. elements: Gf8.elt, B.byte and the field's operations agree on bytes;
#   B. scaling a block: Raid6.scale's laws, bytewise from gf's laws;
#   C. the syndromes: p_split and q_split by induction on the blocks;
#   D. lengths: blocks of equal length keep every syndrome no longer than
#      them, so XORing in a syndrome twice cancels to nothing;
#   E. the generator: g^x, x < 255, are nonzero and distinct, from one
#      computed walk through the 254 powers (r6p.walk) and gf's laws;
#   F. recovery, case by case, from A to E.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../gf/gf.bend as G
import ../gf/LAWS.bend as GL
import ../gf/PROOF.bend as GP
import ../xorblocks/xorblocks.bend as X
import ../xorblocks/LAWS.bend as XL
import ../xorblocks/PROOF.bend as XP
import ./scale.bend as S
import ./raid6.bend as R
import ./recover.bend as V
import ./LAWS.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

# Contradictions

def r6p.bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def r6p.ft(+e: {False{} == True{} : Bool}) -> Empty:
  %e : r6p.bdisc(_)
  Unit{}

def r6p.tf(+e: {True{} == False{} : Bool}) -> Empty:
  r6p.ft(Equal.sym(Bool, True{}, False{}, e))

# A. Elements

def r6p.of_to(r: G.Gf8Bits) -> {G.Gf8Bits.of(G.Gf8Bits.to(r)) == r : G.Gf8Bits}:
  match r:
    case G.Gf8Bits{b0, b1, b2, b3, b4, b5, b6, b7}:
      {==}

def r6p.elt_to(+r: G.Gf8Bits) -> {G.Gf8.elt(G.Gf8Bits.to(r)) == G.Gf8Bits.to(r) : U32}:
  %r6p.of_to(r) : {G.Gf8.elt(G.Gf8Bits.to(r)) == G.Gf8Bits.to(_) : U32}
  {==}

def r6p.elt_mul(f: G.Gf8Field, +a: U32, +b: U32) -> {G.Gf8.elt(G.Gf8.mul(f, a, b)) == G.Gf8.mul(f, a, b) : U32}:
  match f:
    case G.Gf8Field{+poly, gen}:
      r6p.elt_to(G.Gf8Bits.mul(G.Gf8Bits.of(a), G.Gf8Bits.of(b), G.Gf8Bits.of(poly)))

def r6p.elt_add(+a: U32, +b: U32) -> {G.Gf8.elt(G.Gf8.add(a, b)) == G.Gf8.add(a, b) : U32}:
  r6p.elt_to(G.Gf8Bits.xor(G.Gf8Bits.of(a), G.Gf8Bits.of(b)))

def r6p.elt_elt(+a: U32) -> {G.Gf8.elt(G.Gf8.elt(a)) == G.Gf8.elt(a) : U32}:
  r6p.elt_to(G.Gf8Bits.of(a))

def r6p.elt_pow(+f: G.Gf8Field, +a: U32, n: Nat) -> {G.Gf8.elt(G.Gf8.pow(f, a, n)) == G.Gf8.pow(f, a, n) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      r6p.elt_mul(f, a, G.Gf8.pow(f, a, k))

def r6p.mul_elt_r(f: G.Gf8Field, +a: U32, +b: U32) -> {G.Gf8.mul(f, a, G.Gf8.elt(b)) == G.Gf8.mul(f, a, b) : U32}:
  match f:
    case G.Gf8Field{+poly, +gen}:
      %r6p.of_to(G.Gf8Bits.of(b)) : {G.Gf8.mul(G.Gf8Field{poly, gen}, a, G.Gf8.elt(b)) == G.Gf8Bits.to(G.Gf8Bits.mul(G.Gf8Bits.of(a), _, G.Gf8Bits.of(poly))) : U32}
      {==}

def r6p.mul_elt_l(f: G.Gf8Field, +a: U32, +b: U32) -> {G.Gf8.mul(f, G.Gf8.elt(a), b) == G.Gf8.mul(f, a, b) : U32}:
  match f:
    case G.Gf8Field{+poly, +gen}:
      %r6p.of_to(G.Gf8Bits.of(a)) : {G.Gf8.mul(G.Gf8Field{poly, gen}, G.Gf8.elt(a), b) == G.Gf8Bits.to(G.Gf8Bits.mul(_, G.Gf8Bits.of(b), G.Gf8Bits.of(poly))) : U32}
      {==}

def r6p.add_elt_l(+a: U32, +b: U32) -> {G.Gf8.add(G.Gf8.elt(a), b) == G.Gf8.add(a, b) : U32}:
  %r6p.of_to(G.Gf8Bits.of(a)) : {G.Gf8.add(G.Gf8.elt(a), b) == G.Gf8Bits.to(G.Gf8Bits.xor(_, G.Gf8Bits.of(b))) : U32}
  {==}

# bytes and elements are the same low eight bits
def r6p.byte_elt(x: U32) -> {B.byte(x) == G.Gf8.elt(x) : U32}:
  match x:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, xr}}}}}}}}}:
      {==}

def r6p.elt_byte(x: U32) -> {G.Gf8.elt(B.byte(x)) == B.byte(x) : U32}:
  match x:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, xr}}}}}}}}}:
      {==}

def r6p.xor_byte_add(x: U32, y: U32) -> {U32.xor(B.byte(x), B.byte(y)) == G.Gf8.add(x, y) : U32}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, xr}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, yr}}}}}}}}}:
      {==}

def r6p.xor_to(r1: G.Gf8Bits, r2: G.Gf8Bits) -> {U32.xor(G.Gf8Bits.to(r1), G.Gf8Bits.to(r2)) == G.Gf8.add(G.Gf8Bits.to(r1), G.Gf8Bits.to(r2)) : U32}:
  match r1 r2:
    case G.Gf8Bits{a0, a1, a2, a3, a4, a5, a6, a7} G.Gf8Bits{b0, b1, b2, b3, b4, b5, b6, b7}:
      {==}

def r6p.xor_mul(f: G.Gf8Field, +c: U32, +x: U32, +d: U32, +y: U32) -> {U32.xor(G.Gf8.mul(f, c, x), G.Gf8.mul(f, d, y)) == G.Gf8.add(G.Gf8.mul(f, c, x), G.Gf8.mul(f, d, y)) : U32}:
  match f:
    case G.Gf8Field{+poly, gen}:
      r6p.xor_to(G.Gf8Bits.mul(G.Gf8Bits.of(c), G.Gf8Bits.of(x), G.Gf8Bits.of(poly)), G.Gf8Bits.mul(G.Gf8Bits.of(d), G.Gf8Bits.of(y), G.Gf8Bits.of(poly)))

def r6p.mul_byte_r(+f: G.Gf8Field, +c: U32, +x: U32) -> {G.Gf8.mul(f, c, B.byte(x)) == G.Gf8.mul(f, c, x) : U32}:
  %Equal.sym(U32, B.byte(x), G.Gf8.elt(x), r6p.byte_elt(x)) : {G.Gf8.mul(f, c, _) == G.Gf8.mul(f, c, x) : U32}
  r6p.mul_elt_r(f, c, x)

def r6p.byte_mul(+f: G.Gf8Field, +c: U32, +x: U32) -> {B.byte(G.Gf8.mul(f, c, x)) == G.Gf8.mul(f, c, x) : U32}:
  %Equal.sym(U32, B.byte(G.Gf8.mul(f, c, x)), G.Gf8.elt(G.Gf8.mul(f, c, x)), r6p.byte_elt(G.Gf8.mul(f, c, x))) : {_ == G.Gf8.mul(f, c, x) : U32}
  r6p.elt_mul(f, c, x)

# B. Scaling: byte lists

def r6p.scale_go(xs: List<&2, U32>, +f: G.Gf8Field, +c: U32, acc: List<&2, U32>) -> {B.rev_onto(acc, S.r6.scale.list(f, c, xs)) == S.r6.scale.go(xs, f, c, acc) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      r6p.scale_go(t, f, c, Con{G.Gf8.mul(f, c, x), acc})

def r6p.mask_sl(+f: G.Gf8Field, +c: U32, xs: List<&2, U32>) -> {B.mask(S.r6.scale.list(f, c, xs)) == S.r6.scale.list(f, c, xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %r6p.byte_mul(f, c, x) : {Con{B.byte(G.Gf8.mul(f, c, x)), B.mask(S.r6.scale.list(f, c, t))} == Con{_, S.r6.scale.list(f, c, t)} : List<&2, U32>}
      %r6p.mask_sl(f, c, t) : {Con{B.byte(G.Gf8.mul(f, c, x)), B.mask(S.r6.scale.list(f, c, t))} == Con{B.byte(G.Gf8.mul(f, c, x)), _} : List<&2, U32>}
      {==}

# c (x + y) = c x + c y, on bytes
def r6p.el_xor(+f: G.Gf8Field, +c: U32, +x: U32, +y: U32) -> {G.Gf8.mul(f, c, U32.xor(B.byte(x), B.byte(y))) == U32.xor(G.Gf8.mul(f, c, B.byte(x)), G.Gf8.mul(f, c, B.byte(y))) : U32}:
  %Equal.sym(U32, U32.xor(B.byte(x), B.byte(y)), G.Gf8.add(x, y), r6p.xor_byte_add(x, y)) : {G.Gf8.mul(f, c, _) == U32.xor(G.Gf8.mul(f, c, B.byte(x)), G.Gf8.mul(f, c, B.byte(y))) : U32}
  %Equal.sym(U32, G.Gf8.mul(f, c, G.Gf8.add(x, y)), G.Gf8.add(G.Gf8.mul(f, c, x), G.Gf8.mul(f, c, y)), GL.mul_distrib(f, c, x, y)) : {_ == U32.xor(G.Gf8.mul(f, c, B.byte(x)), G.Gf8.mul(f, c, B.byte(y))) : U32}
  %Equal.sym(U32, G.Gf8.mul(f, c, B.byte(x)), G.Gf8.mul(f, c, x), r6p.mul_byte_r(f, c, x)) : {G.Gf8.add(G.Gf8.mul(f, c, x), G.Gf8.mul(f, c, y)) == U32.xor(_, G.Gf8.mul(f, c, B.byte(y))) : U32}
  %Equal.sym(U32, G.Gf8.mul(f, c, B.byte(y)), G.Gf8.mul(f, c, y), r6p.mul_byte_r(f, c, y)) : {G.Gf8.add(G.Gf8.mul(f, c, x), G.Gf8.mul(f, c, y)) == U32.xor(G.Gf8.mul(f, c, x), _) : U32}
  Equal.sym(U32, U32.xor(G.Gf8.mul(f, c, x), G.Gf8.mul(f, c, y)), G.Gf8.add(G.Gf8.mul(f, c, x), G.Gf8.mul(f, c, y)), r6p.xor_mul(f, c, x, c, y))

def r6p.sl_xl(+f: G.Gf8Field, +c: U32, xs: List<&2, U32>, ys: List<&2, U32>) -> {S.r6.scale.list(f, c, X.Xorb.xor_list(B.mask(xs), B.mask(ys))) == X.Xorb.xor_list(S.r6.scale.list(f, c, B.mask(xs)), S.r6.scale.list(f, c, B.mask(ys))) : List<&2, U32>}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{+x, +s} Con{+y, +t}:
      %r6p.el_xor(f, c, x, y) : {Con{G.Gf8.mul(f, c, U32.xor(B.byte(x), B.byte(y))), S.r6.scale.list(f, c, X.Xorb.xor_list(B.mask(s), B.mask(t)))} == Con{_, X.Xorb.xor_list(S.r6.scale.list(f, c, B.mask(s)), S.r6.scale.list(f, c, B.mask(t)))} : List<&2, U32>}
      %r6p.sl_xl(f, c, s, t) : {Con{G.Gf8.mul(f, c, U32.xor(B.byte(x), B.byte(y))), S.r6.scale.list(f, c, X.Xorb.xor_list(B.mask(s), B.mask(t)))} == Con{G.Gf8.mul(f, c, U32.xor(B.byte(x), B.byte(y))), _} : List<&2, U32>}
      {==}

def r6p.sl_sl(+f: G.Gf8Field, +c: U32, +d: U32, xs: List<&2, U32>) -> {S.r6.scale.list(f, c, S.r6.scale.list(f, d, xs)) == S.r6.scale.list(f, G.Gf8.mul(f, c, d), xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(U32, G.Gf8.mul(f, G.Gf8.mul(f, c, d), x), G.Gf8.mul(f, c, G.Gf8.mul(f, d, x)), GL.mul_assoc(f, c, d, x)) : {Con{G.Gf8.mul(f, c, G.Gf8.mul(f, d, x)), S.r6.scale.list(f, c, S.r6.scale.list(f, d, t))} == Con{_, S.r6.scale.list(f, G.Gf8.mul(f, c, d), t)} : List<&2, U32>}
      %r6p.sl_sl(f, c, d, t) : {Con{G.Gf8.mul(f, c, G.Gf8.mul(f, d, x)), S.r6.scale.list(f, c, S.r6.scale.list(f, d, t))} == Con{G.Gf8.mul(f, c, G.Gf8.mul(f, d, x)), _} : List<&2, U32>}
      {==}

# c x + d x = (c + d) x
def r6p.el_add(+f: G.Gf8Field, +c: U32, +d: U32, +x: U32) -> {U32.xor(G.Gf8.mul(f, c, x), G.Gf8.mul(f, d, x)) == G.Gf8.mul(f, G.Gf8.add(c, d), x) : U32}:
  %Equal.sym(U32, U32.xor(G.Gf8.mul(f, c, x), G.Gf8.mul(f, d, x)), G.Gf8.add(G.Gf8.mul(f, c, x), G.Gf8.mul(f, d, x)), r6p.xor_mul(f, c, x, d, x)) : {_ == G.Gf8.mul(f, G.Gf8.add(c, d), x) : U32}
  %GL.mul_comm(f, x, c) : {G.Gf8.add(_, G.Gf8.mul(f, d, x)) == G.Gf8.mul(f, G.Gf8.add(c, d), x) : U32}
  %GL.mul_comm(f, x, d) : {G.Gf8.add(G.Gf8.mul(f, x, c), _) == G.Gf8.mul(f, G.Gf8.add(c, d), x) : U32}
  %GL.mul_distrib(f, x, c, d) : {_ == G.Gf8.mul(f, G.Gf8.add(c, d), x) : U32}
  GL.mul_comm(f, x, G.Gf8.add(c, d))

def r6p.sl_add(+f: G.Gf8Field, +c: U32, +d: U32, xs: List<&2, U32>) -> {X.Xorb.xor_list(S.r6.scale.list(f, c, xs), S.r6.scale.list(f, d, xs)) == S.r6.scale.list(f, G.Gf8.add(c, d), xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %r6p.el_add(f, c, d, x) : {Con{U32.xor(G.Gf8.mul(f, c, x), G.Gf8.mul(f, d, x)), X.Xorb.xor_list(S.r6.scale.list(f, c, t), S.r6.scale.list(f, d, t))} == Con{_, S.r6.scale.list(f, G.Gf8.add(c, d), t)} : List<&2, U32>}
      %r6p.sl_add(f, c, d, t) : {Con{U32.xor(G.Gf8.mul(f, c, x), G.Gf8.mul(f, d, x)), X.Xorb.xor_list(S.r6.scale.list(f, c, t), S.r6.scale.list(f, d, t))} == Con{U32.xor(G.Gf8.mul(f, c, x), G.Gf8.mul(f, d, x)), _} : List<&2, U32>}
      {==}

def r6p.el_one(+f: G.Gf8Field, +x: U32) -> {G.Gf8.mul(f, 1, B.byte(x)) == B.byte(x) : U32}:
  Equal.trans(U32, G.Gf8.mul(f, 1, B.byte(x)), G.Gf8.elt(B.byte(x)), B.byte(x), GL.mul_one(f, B.byte(x)), r6p.elt_byte(x))

def r6p.sl_one(+f: G.Gf8Field, xs: List<&2, U32>) -> {S.r6.scale.list(f, 1, B.mask(xs)) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %r6p.el_one(f, x) : {Con{G.Gf8.mul(f, 1, B.byte(x)), S.r6.scale.list(f, 1, B.mask(t))} == Con{_, B.mask(t)} : List<&2, U32>}
      %r6p.sl_one(f, t) : {Con{G.Gf8.mul(f, 1, B.byte(x)), S.r6.scale.list(f, 1, B.mask(t))} == Con{G.Gf8.mul(f, 1, B.byte(x)), _} : List<&2, U32>}
      {==}

def r6p.sl_zero(+f: G.Gf8Field, xs: List<&2, U32>) -> {S.r6.scale.list(f, 0, xs) == B.zeros(B.len(xs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %GL.mul_zero(f, x) : {Con{G.Gf8.mul(f, 0, x), S.r6.scale.list(f, 0, t)} == Con{_, B.zeros(B.len(t))} : List<&2, U32>}
      %r6p.sl_zero(f, t) : {Con{G.Gf8.mul(f, 0, x), S.r6.scale.list(f, 0, t)} == Con{G.Gf8.mul(f, 0, x), _} : List<&2, U32>}
      {==}

def r6p.sl_len(+f: G.Gf8Field, +c: U32, xs: List<&2, U32>) -> {B.len(S.r6.scale.list(f, c, xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %r6p.sl_len(f, c, t) : {1n+B.len(S.r6.scale.list(f, c, t)) == 1n+_ : Nat}
      {==}

# B. Scaling: blocks

def r6p.tl_mask(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  %BL.octets_of_to(o) : {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(_) : List<&2, U32>}
  Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), BL.octets_to_of(B.Octets.to_list(o)))

def r6p.lift(+x: B.Octets, +y: B.Octets, e: {B.Octets.to_list(x) == B.Octets.to_list(y) : List<&2, U32>}) -> {x == y : B.Octets}:
  %BL.octets_of_to(x) : {_ == y : B.Octets}
  %BL.octets_of_to(y) : {B.Octets.of_list(B.Octets.to_list(x)) == _ : B.Octets}
  %e : {B.Octets.of_list(B.Octets.to_list(x)) == B.Octets.of_list(_) : B.Octets}
  {==}

def r6p.to_scale(+f: G.Gf8Field, +c: U32, +b: B.Octets) -> {S.r6.scale.list(f, c, B.Octets.to_list(b)) == B.Octets.to_list(S.Raid6.scale(f, c, b)) : List<&2, U32>}:
  %r6p.scale_go(B.Octets.to_list(b), f, c, Nil{}) : {S.r6.scale.list(f, c, B.Octets.to_list(b)) == B.Octets.to_list(B.Octets.of_list(_)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(S.r6.scale.list(f, c, B.Octets.to_list(b)))), B.mask(S.r6.scale.list(f, c, B.Octets.to_list(b))), BL.octets_to_of(S.r6.scale.list(f, c, B.Octets.to_list(b)))) : {S.r6.scale.list(f, c, B.Octets.to_list(b)) == _ : List<&2, U32>}
  Equal.sym(List<&2, U32>, B.mask(S.r6.scale.list(f, c, B.Octets.to_list(b))), S.r6.scale.list(f, c, B.Octets.to_list(b)), r6p.mask_sl(f, c, B.Octets.to_list(b)))

def r6p.xl_sym(+a: B.Octets, +b: B.Octets) -> {X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)) == B.Octets.to_list(X.Xorb.xor(a, b)) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.Octets.to_list(X.Xorb.xor(a, b)), X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)), XL.xor_list(a, b))

def r6p.scale_xor_list(+f: G.Gf8Field, +c: U32, +a: B.Octets, +b: B.Octets) -> {B.Octets.to_list(S.Raid6.scale(f, c, X.Xorb.xor(a, b))) == B.Octets.to_list(X.Xorb.xor(S.Raid6.scale(f, c, a), S.Raid6.scale(f, c, b))) : List<&2, U32>}:
  %r6p.to_scale(f, c, X.Xorb.xor(a, b)) : {_ == B.Octets.to_list(X.Xorb.xor(S.Raid6.scale(f, c, a), S.Raid6.scale(f, c, b))) : List<&2, U32>}
  %r6p.xl_sym(a, b) : {S.r6.scale.list(f, c, _) == B.Octets.to_list(X.Xorb.xor(S.Raid6.scale(f, c, a), S.Raid6.scale(f, c, b))) : List<&2, U32>}
  %r6p.xl_sym(S.Raid6.scale(f, c, a), S.Raid6.scale(f, c, b)) : {S.r6.scale.list(f, c, X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b))) == _ : List<&2, U32>}
  %r6p.to_scale(f, c, a) : {S.r6.scale.list(f, c, X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b))) == X.Xorb.xor_list(_, B.Octets.to_list(S.Raid6.scale(f, c, b))) : List<&2, U32>}
  %r6p.to_scale(f, c, b) : {S.r6.scale.list(f, c, X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b))) == X.Xorb.xor_list(S.r6.scale.list(f, c, B.Octets.to_list(a)), _) : List<&2, U32>}
  %r6p.tl_mask(a) : {S.r6.scale.list(f, c, X.Xorb.xor_list(_, B.Octets.to_list(b))) == X.Xorb.xor_list(S.r6.scale.list(f, c, _), S.r6.scale.list(f, c, B.Octets.to_list(b))) : List<&2, U32>}
  %r6p.tl_mask(b) : {S.r6.scale.list(f, c, X.Xorb.xor_list(B.mask(B.Octets.to_list(a)), _)) == X.Xorb.xor_list(S.r6.scale.list(f, c, B.mask(B.Octets.to_list(a))), S.r6.scale.list(f, c, _)) : List<&2, U32>}
  r6p.sl_xl(f, c, B.Octets.to_list(a), B.Octets.to_list(b))

def Laws.scale_xor(f, c, a, b):
  r6p.lift(S.Raid6.scale(f, c, X.Xorb.xor(a, b)), X.Xorb.xor(S.Raid6.scale(f, c, a), S.Raid6.scale(f, c, b)), r6p.scale_xor_list(f, c, a, b))

def r6p.scale_scale_list(+f: G.Gf8Field, +c: U32, +d: U32, +a: B.Octets) -> {B.Octets.to_list(S.Raid6.scale(f, c, S.Raid6.scale(f, d, a))) == B.Octets.to_list(S.Raid6.scale(f, G.Gf8.mul(f, c, d), a)) : List<&2, U32>}:
  %r6p.to_scale(f, c, S.Raid6.scale(f, d, a)) : {_ == B.Octets.to_list(S.Raid6.scale(f, G.Gf8.mul(f, c, d), a)) : List<&2, U32>}
  %r6p.to_scale(f, d, a) : {S.r6.scale.list(f, c, _) == B.Octets.to_list(S.Raid6.scale(f, G.Gf8.mul(f, c, d), a)) : List<&2, U32>}
  %r6p.to_scale(f, G.Gf8.mul(f, c, d), a) : {S.r6.scale.list(f, c, S.r6.scale.list(f, d, B.Octets.to_list(a))) == _ : List<&2, U32>}
  r6p.sl_sl(f, c, d, B.Octets.to_list(a))

def Laws.scale_scale(f, c, d, a):
  r6p.lift(S.Raid6.scale(f, c, S.Raid6.scale(f, d, a)), S.Raid6.scale(f, G.Gf8.mul(f, c, d), a), r6p.scale_scale_list(f, c, d, a))

def r6p.scale_add_list(+f: G.Gf8Field, +c: U32, +d: U32, +a: B.Octets) -> {B.Octets.to_list(X.Xorb.xor(S.Raid6.scale(f, c, a), S.Raid6.scale(f, d, a))) == B.Octets.to_list(S.Raid6.scale(f, G.Gf8.add(c, d), a)) : List<&2, U32>}:
  %r6p.xl_sym(S.Raid6.scale(f, c, a), S.Raid6.scale(f, d, a)) : {_ == B.Octets.to_list(S.Raid6.scale(f, G.Gf8.add(c, d), a)) : List<&2, U32>}
  %r6p.to_scale(f, c, a) : {X.Xorb.xor_list(_, B.Octets.to_list(S.Raid6.scale(f, d, a))) == B.Octets.to_list(S.Raid6.scale(f, G.Gf8.add(c, d), a)) : List<&2, U32>}
  %r6p.to_scale(f, d, a) : {X.Xorb.xor_list(S.r6.scale.list(f, c, B.Octets.to_list(a)), _) == B.Octets.to_list(S.Raid6.scale(f, G.Gf8.add(c, d), a)) : List<&2, U32>}
  %r6p.to_scale(f, G.Gf8.add(c, d), a) : {X.Xorb.xor_list(S.r6.scale.list(f, c, B.Octets.to_list(a)), S.r6.scale.list(f, d, B.Octets.to_list(a))) == _ : List<&2, U32>}
  r6p.sl_add(f, c, d, B.Octets.to_list(a))

def Laws.scale_add(f, c, d, a):
  r6p.lift(X.Xorb.xor(S.Raid6.scale(f, c, a), S.Raid6.scale(f, d, a)), S.Raid6.scale(f, G.Gf8.add(c, d), a), r6p.scale_add_list(f, c, d, a))

def r6p.scale_one_list(+f: G.Gf8Field, +a: B.Octets) -> {B.Octets.to_list(S.Raid6.scale(f, 1, a)) == B.Octets.to_list(a) : List<&2, U32>}:
  %r6p.to_scale(f, 1, a) : {_ == B.Octets.to_list(a) : List<&2, U32>}
  %r6p.tl_mask(a) : {S.r6.scale.list(f, 1, _) == _ : List<&2, U32>}
  r6p.sl_one(f, B.Octets.to_list(a))

def Laws.scale_one(f, a):
  r6p.lift(S.Raid6.scale(f, 1, a), a, r6p.scale_one_list(f, a))

def r6p.scale_zero_list(+f: G.Gf8Field, +a: B.Octets) -> {B.Octets.to_list(S.Raid6.scale(f, 0, a)) == B.Octets.to_list(B.Octets.zeros(B.Octets.len(a))) : List<&2, U32>}:
  %r6p.to_scale(f, 0, a) : {_ == B.Octets.to_list(B.Octets.zeros(B.Octets.len(a))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.zeros(B.Octets.len(a))), B.zeros(B.Octets.len(a)), BL.octets_zeros_list(B.Octets.len(a))) : {S.r6.scale.list(f, 0, B.Octets.to_list(a)) == _ : List<&2, U32>}
  %Equal.sym(Nat, B.Octets.len(a), B.len(B.Octets.to_list(a)), BL.octets_len_list(a)) : {S.r6.scale.list(f, 0, B.Octets.to_list(a)) == B.zeros(_) : List<&2, U32>}
  r6p.sl_zero(f, B.Octets.to_list(a))

def Laws.scale_zero(f, a):
  r6p.lift(S.Raid6.scale(f, 0, a), B.Octets.zeros(B.Octets.len(a)), r6p.scale_zero_list(f, a))

def Laws.scale_len(f, c, a):
  %Equal.sym(Nat, B.Octets.len(S.Raid6.scale(f, c, a)), B.len(B.Octets.to_list(S.Raid6.scale(f, c, a))), BL.octets_len_list(S.Raid6.scale(f, c, a))) : {_ == B.Octets.len(a) : Nat}
  %r6p.to_scale(f, c, a) : {B.len(_) == B.Octets.len(a) : Nat}
  %Equal.sym(Nat, B.Octets.len(a), B.len(B.Octets.to_list(a)), BL.octets_len_list(a)) : {B.len(S.r6.scale.list(f, c, B.Octets.to_list(a))) == _ : Nat}
  r6p.sl_len(f, c, B.Octets.to_list(a))

# C. The syndromes

# XOR shuffles, from xorblocks' laws
def r6p.empty_l(+d: B.Octets) -> {X.Xorb.xor(B.Octets.empty(), d) == d : B.Octets}:
  Equal.trans(B.Octets, X.Xorb.xor(B.Octets.empty(), d), X.Xorb.xor(d, B.Octets.empty()), d, XL.xor_comm(B.Octets.empty(), d), XL.xor_empty(d))

def r6p.sw(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {X.Xorb.xor(a, X.Xorb.xor(b, c)) == X.Xorb.xor(b, X.Xorb.xor(a, c)) : B.Octets}:
  %XL.xor_assoc(a, b, c) : {_ == X.Xorb.xor(b, X.Xorb.xor(a, c)) : B.Octets}
  %XL.xor_comm(b, a) : {X.Xorb.xor(_, c) == X.Xorb.xor(b, X.Xorb.xor(a, c)) : B.Octets}
  XL.xor_assoc(b, a, c)

# (a + b) + (c + d) = (a + c) + (b + d)
def r6p.sw4(+a: B.Octets, +b: B.Octets, +c: B.Octets, +d: B.Octets) -> {X.Xorb.xor(X.Xorb.xor(a, b), X.Xorb.xor(c, d)) == X.Xorb.xor(X.Xorb.xor(a, c), X.Xorb.xor(b, d)) : B.Octets}:
  %Equal.sym(B.Octets, X.Xorb.xor(X.Xorb.xor(a, b), X.Xorb.xor(c, d)), X.Xorb.xor(a, X.Xorb.xor(b, X.Xorb.xor(c, d))), XL.xor_assoc(a, b, X.Xorb.xor(c, d))) : {_ == X.Xorb.xor(X.Xorb.xor(a, c), X.Xorb.xor(b, d)) : B.Octets}
  %Equal.sym(B.Octets, X.Xorb.xor(b, X.Xorb.xor(c, d)), X.Xorb.xor(c, X.Xorb.xor(b, d)), r6p.sw(b, c, d)) : {X.Xorb.xor(a, _) == X.Xorb.xor(X.Xorb.xor(a, c), X.Xorb.xor(b, d)) : B.Octets}
  Equal.sym(B.Octets, X.Xorb.xor(X.Xorb.xor(a, c), X.Xorb.xor(b, d)), X.Xorb.xor(a, X.Xorb.xor(c, X.Xorb.xor(b, d))), XL.xor_assoc(a, c, X.Xorb.xor(b, d)))

def r6p.all_cons(+d: B.Octets, +ds: List<&2, B.Octets>) -> {X.Xorb.all(Con{d, ds}) == X.Xorb.xor(d, X.Xorb.all(ds)) : B.Octets}:
  %Equal.sym(B.Octets, X.Xorb.into(B.Octets.empty(), Con{d, ds}), X.Xorb.into(X.Xorb.xor(B.Octets.empty(), d), ds), XL.into_cons(B.Octets.empty(), d, ds)) : {_ == X.Xorb.xor(d, X.Xorb.all(ds)) : B.Octets}
  %Equal.sym(B.Octets, X.Xorb.into(X.Xorb.xor(B.Octets.empty(), d), ds), X.Xorb.xor(X.Xorb.xor(B.Octets.empty(), d), X.Xorb.all(ds)), XL.into_all(X.Xorb.xor(B.Octets.empty(), d), ds)) : {_ == X.Xorb.xor(d, X.Xorb.all(ds)) : B.Octets}
  %r6p.empty_l(d) : {X.Xorb.xor(X.Xorb.xor(B.Octets.empty(), d), X.Xorb.all(ds)) == X.Xorb.xor(_, X.Xorb.all(ds)) : B.Octets}
  {==}

def Laws.p_cons(d, ds):
  r6p.all_cons(d, ds)

def Laws.q_cons(s, d, ds):
  {==}

def r6p.p_split(ds: List<&2, B.Octets>, +x: Nat) -> {X.Xorb.all(ds) == X.Xorb.xor(R.Raid6.block(ds, x), X.Xorb.all(R.Raid6.set_block(ds, x, B.Octets.empty()))) : B.Octets}:
  match ds:
    case Nil{}:
      Equal.sym(B.Octets, X.Xorb.xor(B.Octets.empty(), X.Xorb.all(Nil{})), X.Xorb.all(Nil{}), r6p.empty_l(X.Xorb.all(Nil{})))
    case Con{+d, +r}:
      match x:
        case 0n:
          %Equal.sym(B.Octets, X.Xorb.all(Con{d, r}), X.Xorb.xor(d, X.Xorb.all(r)), r6p.all_cons(d, r)) : {_ == X.Xorb.xor(d, X.Xorb.all(Con{B.Octets.empty(), r})) : B.Octets}
          %Equal.sym(B.Octets, X.Xorb.all(Con{B.Octets.empty(), r}), X.Xorb.xor(B.Octets.empty(), X.Xorb.all(r)), r6p.all_cons(B.Octets.empty(), r)) : {X.Xorb.xor(d, X.Xorb.all(r)) == X.Xorb.xor(d, _) : B.Octets}
          %Equal.sym(B.Octets, X.Xorb.xor(B.Octets.empty(), X.Xorb.all(r)), X.Xorb.all(r), r6p.empty_l(X.Xorb.all(r))) : {X.Xorb.xor(d, X.Xorb.all(r)) == X.Xorb.xor(d, _) : B.Octets}
          {==}
        case 1n+k:
          %Equal.sym(B.Octets, X.Xorb.all(Con{d, r}), X.Xorb.xor(d, X.Xorb.all(r)), r6p.all_cons(d, r)) : {_ == X.Xorb.xor(R.Raid6.block(r, k), X.Xorb.all(Con{d, R.Raid6.set_block(r, k, B.Octets.empty())})) : B.Octets}
          %Equal.sym(B.Octets, X.Xorb.all(r), X.Xorb.xor(R.Raid6.block(r, k), X.Xorb.all(R.Raid6.set_block(r, k, B.Octets.empty()))), r6p.p_split(r, k)) : {X.Xorb.xor(d, _) == X.Xorb.xor(R.Raid6.block(r, k), X.Xorb.all(Con{d, R.Raid6.set_block(r, k, B.Octets.empty())})) : B.Octets}
          %Equal.sym(B.Octets, X.Xorb.all(Con{d, R.Raid6.set_block(r, k, B.Octets.empty())}), X.Xorb.xor(d, X.Xorb.all(R.Raid6.set_block(r, k, B.Octets.empty()))), r6p.all_cons(d, R.Raid6.set_block(r, k, B.Octets.empty()))) : {X.Xorb.xor(d, X.Xorb.xor(R.Raid6.block(r, k), X.Xorb.all(R.Raid6.set_block(r, k, B.Octets.empty())))) == X.Xorb.xor(R.Raid6.block(r, k), _) : B.Octets}
          r6p.sw(d, R.Raid6.block(r, k), X.Xorb.all(R.Raid6.set_block(r, k, B.Octets.empty())))

def Laws.p_split(ds, x):
  r6p.p_split(ds, x)

def r6p.q_split(+s: R.Raid6Spec, ds: List<&2, B.Octets>, +x: Nat) -> {R.Raid6.q(s, ds) == X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, x), R.Raid6.block(ds, x)), R.Raid6.q(s, R.Raid6.set_block(ds, x, B.Octets.empty()))) : B.Octets}:
  match ds:
    case Nil{}:
      Equal.sym(B.Octets, X.Xorb.xor(B.Octets.empty(), B.Octets.empty()), B.Octets.empty(), r6p.empty_l(B.Octets.empty()))
    case Con{+d, +r}:
      match x:
        case 0n:
          %Equal.sym(B.Octets, S.Raid6.scale(R.Raid6.field(s), 1, d), d, Laws.scale_one(R.Raid6.field(s), d)) : {R.Raid6.q(s, Con{d, r}) == X.Xorb.xor(_, X.Xorb.xor(B.Octets.empty(), S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r)))) : B.Octets}
          %Equal.sym(B.Octets, X.Xorb.xor(B.Octets.empty(), S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r))), S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r)), r6p.empty_l(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r)))) : {R.Raid6.q(s, Con{d, r}) == X.Xorb.xor(d, _) : B.Octets}
          {==}
        case 1n+k:
          %Equal.sym(B.Octets, R.Raid6.q(s, r), X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, k), R.Raid6.block(r, k)), R.Raid6.q(s, R.Raid6.set_block(r, k, B.Octets.empty()))), r6p.q_split(s, r, k)) : {X.Xorb.xor(d, S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), _)) == X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, 1n+k), R.Raid6.block(r, k)), R.Raid6.q(s, Con{d, R.Raid6.set_block(r, k, B.Octets.empty())})) : B.Octets}
          %Equal.sym(B.Octets, S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, k), R.Raid6.block(r, k)), R.Raid6.q(s, R.Raid6.set_block(r, k, B.Octets.empty())))), X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, k), R.Raid6.block(r, k))), S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, R.Raid6.set_block(r, k, B.Octets.empty())))), Laws.scale_xor(R.Raid6.field(s), R.Raid6.gen(s), S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, k), R.Raid6.block(r, k)), R.Raid6.q(s, R.Raid6.set_block(r, k, B.Octets.empty())))) : {X.Xorb.xor(d, _) == X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, 1n+k), R.Raid6.block(r, k)), R.Raid6.q(s, Con{d, R.Raid6.set_block(r, k, B.Octets.empty())})) : B.Octets}
          %Equal.sym(B.Octets, S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, k), R.Raid6.block(r, k))), S.Raid6.scale(R.Raid6.field(s), G.Gf8.mul(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.gpow(s, k)), R.Raid6.block(r, k)), Laws.scale_scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.gpow(s, k), R.Raid6.block(r, k))) : {X.Xorb.xor(d, X.Xorb.xor(_, S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, R.Raid6.set_block(r, k, B.Octets.empty()))))) == X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, 1n+k), R.Raid6.block(r, k)), R.Raid6.q(s, Con{d, R.Raid6.set_block(r, k, B.Octets.empty())})) : B.Octets}
          r6p.sw(d, S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, 1n+k), R.Raid6.block(r, k)), S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, R.Raid6.set_block(r, k, B.Octets.empty()))))

def Laws.q_split(s, ds, x):
  r6p.q_split(s, ds, x)

# Blocks by index

def r6p.blk_set_e(ds: List<&2, B.Octets>, x: Nat) -> {R.Raid6.block(R.Raid6.set_block(ds, x, B.Octets.empty()), x) == B.Octets.empty() : B.Octets}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, r}:
      match x:
        case 0n:
          {==}
        case 1n+k:
          r6p.blk_set_e(r, k)

def r6p.blk_set_ne(ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +b: B.Octets, ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {R.Raid6.block(R.Raid6.set_block(ds, x, b), y) == R.Raid6.block(ds, y) : B.Octets}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, r}:
      match x y:
        case 0n 0n:
          Empty.absurd({R.Raid6.block(R.Raid6.set_block(Con{d, r}, 0n, b), 0n) == R.Raid6.block(Con{d, r}, 0n) : B.Octets}, r6p.ft(ne))
        case 0n 1n+k:
          {==}
        case 1n+j 0n:
          {==}
        case 1n+j 1n+k:
          r6p.blk_set_ne(r, j, k, b, ne)

def r6p.set_set(ds: List<&2, B.Octets>, +x: Nat, +a: B.Octets, +b: B.Octets) -> {R.Raid6.set_block(R.Raid6.set_block(ds, x, a), x, b) == R.Raid6.set_block(ds, x, b) : List<&2, B.Octets>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      match x:
        case 0n:
          {==}
        case 1n+k:
          %r6p.set_set(r, k, a, b) : {Con{d, R.Raid6.set_block(R.Raid6.set_block(r, k, a), k, b)} == Con{d, _} : List<&2, B.Octets>}
          {==}

def r6p.set_get(ds: List<&2, B.Octets>, +x: Nat) -> {R.Raid6.set_block(ds, x, R.Raid6.block(ds, x)) == ds : List<&2, B.Octets>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      match x:
        case 0n:
          {==}
        case 1n+k:
          %r6p.set_get(r, k) : {Con{d, R.Raid6.set_block(r, k, R.Raid6.block(r, k))} == Con{d, _} : List<&2, B.Octets>}
          {==}

# a block that already holds b is unchanged by setting it to b
def r6p.set_same(ds: List<&2, B.Octets>, +x: Nat, +b: B.Octets, h: {R.Raid6.block(ds, x) == b : B.Octets}) -> {R.Raid6.set_block(ds, x, b) == ds : List<&2, B.Octets>}:
  %h : {R.Raid6.set_block(ds, x, _) == ds : List<&2, B.Octets>}
  r6p.set_get(ds, x)

def r6p.set_comm(ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +a: B.Octets, +b: B.Octets, ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {R.Raid6.set_block(R.Raid6.set_block(ds, x, a), y, b) == R.Raid6.set_block(R.Raid6.set_block(ds, y, b), x, a) : List<&2, B.Octets>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      match x y:
        case 0n 0n:
          Empty.absurd({R.Raid6.set_block(R.Raid6.set_block(Con{d, r}, 0n, a), 0n, b) == R.Raid6.set_block(R.Raid6.set_block(Con{d, r}, 0n, b), 0n, a) : List<&2, B.Octets>}, r6p.ft(ne))
        case 0n 1n+k:
          {==}
        case 1n+j 0n:
          {==}
        case 1n+j 1n+k:
          %r6p.set_comm(r, j, k, a, b, ne) : {Con{d, R.Raid6.set_block(R.Raid6.set_block(r, j, a), k, b)} == Con{d, _} : List<&2, B.Octets>}
          {==}

def r6p.width_set(ds: List<&2, B.Octets>, +x: Nat, +b: B.Octets) -> {R.Raid6.width(R.Raid6.set_block(ds, x, b)) == R.Raid6.width(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      match x:
        case 0n:
          {==}
        case 1n+k:
          %r6p.width_set(r, k, b) : {1n+R.Raid6.width(R.Raid6.set_block(r, k, b)) == 1n+_ : Nat}
          {==}

# block x of a stripe with x and y erased is empty
def r6p.blk_set2(ds: List<&2, B.Octets>, +x: Nat, +y: Nat) -> {R.Raid6.block(R.Raid6.set_block(R.Raid6.set_block(ds, x, B.Octets.empty()), y, B.Octets.empty()), x) == B.Octets.empty() : B.Octets}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      match x y:
        case 0n 0n:
          {==}
        case 0n 1n+k:
          {==}
        case 1n+j 0n:
          r6p.blk_set_e(r, j)
        case 1n+j 1n+k:
          r6p.blk_set2(r, j, k)

# D. Lengths

def r6p.and_l(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, r6p.ft(h))

def r6p.and_r(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, r6p.ft(h))

def r6p.and_i(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def r6p.not_t(+a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, r6p.ft(h))
    case False{}:
      {==}

def r6p.le_zero(+n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def r6p.le_max(+a: Nat, +b: Nat, +l: Nat, ha: {Nat.is_le(a, l) == True{} : Bool}, hb: {Nat.is_le(b, l) == True{} : Bool}) -> {Nat.is_le(Nat.max(a, b), l) == True{} : Bool}:
  match a b:
    case 0n _:
      hb
    case 1n+i 0n:
      ha
    case 1n+i 1n+j:
      match l:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.max(1n+i, 1n+j), 0n) == True{} : Bool}, r6p.ft(ha))
        case 1n+m:
          r6p.le_max(i, j, m, ha, hb)

def r6p.le_max_l(+a: Nat, +l: Nat, +b: Nat, h: {Nat.is_le(a, l) == True{} : Bool}) -> {Nat.is_le(a, Nat.max(l, b)) == True{} : Bool}:
  match a:
    case 0n:
      r6p.le_zero(Nat.max(l, b))
    case 1n+i:
      match l:
        case 0n:
          Empty.absurd({Nat.is_le(1n+i, Nat.max(0n, b)) == True{} : Bool}, r6p.ft(h))
        case 1n+m:
          match b:
            case 0n:
              h
            case 1n+j:
              r6p.le_max_l(i, m, j, h)

def r6p.cmp_eq_le(+c: Cmp, h: {Cmp.is_eq(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_le(LT{}) == True{} : Bool}, r6p.ft(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, r6p.ft(h))

def r6p.eq_le(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  r6p.cmp_eq_le(Nat.cmp(a, b), h)

def r6p.nat_eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      Empty.absurd({0n == 1n+j : Nat}, r6p.ft(h))
    case 1n+i 0n:
      Empty.absurd({1n+i == 0n : Nat}, r6p.ft(h))
    case 1n+i 1n+j:
      %r6p.nat_eq(i, j, h) : {1n+i == 1n+_ : Nat}
      {==}

def r6p.to_le(+a: Nat, +l: Nat, e: {a == l : Nat}) -> {Nat.is_le(a, l) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  UL.nat_le_refl(a)

# every block no longer than l
def r6p.within(+l: Nat, ds: List<&2, B.Octets>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, r}:
      Bool.and(Nat.is_le(B.Octets.len(d), l), r6p.within(l, r))

# the first block's length
def r6p.hlen(ds: List<&2, B.Octets>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, r}:
      B.Octets.len(d)

def r6p.within_p(+l: Nat, ds: List<&2, B.Octets>, +h: {r6p.within(l, ds) == True{} : Bool}) -> {Nat.is_le(B.Octets.len(X.Xorb.all(ds)), l) == True{} : Bool}:
  match ds:
    case Nil{}:
      r6p.le_zero(l)
    case Con{+d, +r}:
      %Equal.sym(B.Octets, X.Xorb.all(Con{d, r}), X.Xorb.xor(d, X.Xorb.all(r)), r6p.all_cons(d, r)) : {Nat.is_le(B.Octets.len(_), l) == True{} : Bool}
      %Equal.sym(Nat, B.Octets.len(X.Xorb.xor(d, X.Xorb.all(r))), Nat.max(B.Octets.len(d), B.Octets.len(X.Xorb.all(r))), XL.xor_len(d, X.Xorb.all(r))) : {Nat.is_le(_, l) == True{} : Bool}
      r6p.le_max(B.Octets.len(d), B.Octets.len(X.Xorb.all(r)), l, r6p.and_l(Nat.is_le(B.Octets.len(d), l), r6p.within(l, r), h), r6p.within_p(l, r, r6p.and_r(Nat.is_le(B.Octets.len(d), l), r6p.within(l, r), h)))

def r6p.within_q(+s: R.Raid6Spec, +l: Nat, ds: List<&2, B.Octets>, +h: {r6p.within(l, ds) == True{} : Bool}) -> {Nat.is_le(B.Octets.len(R.Raid6.q(s, ds)), l) == True{} : Bool}:
  match ds:
    case Nil{}:
      r6p.le_zero(l)
    case Con{+d, +r}:
      %Equal.sym(Nat, B.Octets.len(X.Xorb.xor(d, S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r)))), Nat.max(B.Octets.len(d), B.Octets.len(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r)))), XL.xor_len(d, S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r)))) : {Nat.is_le(_, l) == True{} : Bool}
      %Equal.sym(Nat, B.Octets.len(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r))), B.Octets.len(R.Raid6.q(s, r)), Laws.scale_len(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, r))) : {Nat.is_le(Nat.max(B.Octets.len(d), _), l) == True{} : Bool}
      r6p.le_max(B.Octets.len(d), B.Octets.len(R.Raid6.q(s, r)), l, r6p.and_l(Nat.is_le(B.Octets.len(d), l), r6p.within(l, r), h), r6p.within_q(s, l, r, r6p.and_r(Nat.is_le(B.Octets.len(d), l), r6p.within(l, r), h)))

def r6p.within_set(+l: Nat, ds: List<&2, B.Octets>, +x: Nat, +h: {r6p.within(l, ds) == True{} : Bool}) -> {r6p.within(l, R.Raid6.set_block(ds, x, B.Octets.empty())) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      match x:
        case 0n:
          r6p.and_i(Nat.is_le(0n, l), r6p.within(l, r), r6p.le_zero(l), r6p.and_r(Nat.is_le(B.Octets.len(d), l), r6p.within(l, r), h))
        case 1n+k:
          r6p.and_i(Nat.is_le(B.Octets.len(d), l), r6p.within(l, R.Raid6.set_block(r, k, B.Octets.empty())), r6p.and_l(Nat.is_le(B.Octets.len(d), l), r6p.within(l, r), h), r6p.within_set(l, r, k, r6p.and_r(Nat.is_le(B.Octets.len(d), l), r6p.within(l, r), h)))

def r6p.same_within(+n: Nat, ds: List<&2, B.Octets>, +h: {R.r6.same(n, ds) == True{} : Bool}) -> {r6p.within(n, ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      r6p.and_i(Nat.is_le(B.Octets.len(d), n), r6p.within(n, r), r6p.eq_le(B.Octets.len(d), n, r6p.and_l(Nat.is_eq(B.Octets.len(d), n), R.r6.same(n, r), h)), r6p.same_within(n, r, r6p.and_r(Nat.is_eq(B.Octets.len(d), n), R.r6.same(n, r), h)))

def r6p.uniform_within(ds: List<&2, B.Octets>, h: {R.Raid6.uniform(ds) == True{} : Bool}) -> {r6p.within(r6p.hlen(ds), ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      r6p.and_i(Nat.is_le(B.Octets.len(d), B.Octets.len(d)), r6p.within(B.Octets.len(d), r), UL.nat_le_refl(B.Octets.len(d)), r6p.same_within(B.Octets.len(d), r, h))

def r6p.same_len(+n: Nat, ds: List<&2, B.Octets>, +k: Nat, +h: {R.r6.same(n, ds) == True{} : Bool}, +hk: {Nat.is_lt(k, R.Raid6.width(ds)) == True{} : Bool}) -> {B.Octets.len(R.Raid6.block(ds, k)) == n : Nat}:
  match ds:
    case Nil{}:
      match k:
        case 0n:
          Empty.absurd({B.Octets.len(R.Raid6.block(Nil{}, 0n)) == n : Nat}, r6p.ft(hk))
        case 1n+j:
          Empty.absurd({B.Octets.len(R.Raid6.block(Nil{}, 1n+j)) == n : Nat}, r6p.ft(hk))
    case Con{+d, +r}:
      match k:
        case 0n:
          r6p.nat_eq(B.Octets.len(d), n, r6p.and_l(Nat.is_eq(B.Octets.len(d), n), R.r6.same(n, r), h))
        case 1n+j:
          r6p.same_len(n, r, j, r6p.and_r(Nat.is_eq(B.Octets.len(d), n), R.r6.same(n, r), h), hk)

def r6p.blk_len(ds: List<&2, B.Octets>, +x: Nat, +h: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}) -> {B.Octets.len(R.Raid6.block(ds, x)) == r6p.hlen(ds) : Nat}:
  match ds:
    case Nil{}:
      match x:
        case 0n:
          Empty.absurd({B.Octets.len(R.Raid6.block(Nil{}, 0n)) == 0n : Nat}, r6p.ft(hx))
        case 1n+j:
          Empty.absurd({B.Octets.len(R.Raid6.block(Nil{}, 1n+j)) == 0n : Nat}, r6p.ft(hx))
    case Con{+d, +r}:
      match x:
        case 0n:
          {==}
        case 1n+k:
          r6p.same_len(B.Octets.len(d), r, k, h, hx)

# E. The generator, in the paper's field

def r6p.iz_true(c: U32, h: {G.Gf8.is_zero(c) == True{} : Bool}) -> {G.Gf8.elt(c) == 0 : U32}:
  match c:
    case U32{WCon{True{}, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      Empty.absurd({G.Gf8.elt(U32{WCon{True{}, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}) == 0 : U32}, r6p.ft(h))
    case U32{WCon{False{}, WCon{True{}, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      Empty.absurd({G.Gf8.elt(U32{WCon{False{}, WCon{True{}, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}) == 0 : U32}, r6p.ft(h))
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      Empty.absurd({G.Gf8.elt(U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}) == 0 : U32}, r6p.ft(h))
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      Empty.absurd({G.Gf8.elt(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}) == 0 : U32}, r6p.ft(h))
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      Empty.absurd({G.Gf8.elt(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}) == 0 : U32}, r6p.ft(h))
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{b6, WCon{b7, r}}}}}}}}}:
      Empty.absurd({G.Gf8.elt(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{b6, WCon{b7, r}}}}}}}}}) == 0 : U32}, r6p.ft(h))
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{b7, r}}}}}}}}}:
      Empty.absurd({G.Gf8.elt(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{b7, r}}}}}}}}}) == 0 : U32}, r6p.ft(h))
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}}}}}}}:
      Empty.absurd({G.Gf8.elt(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}}}}}}}) == 0 : U32}, r6p.ft(h))
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}}}}}}:
      {==}

def r6p.iz_elt(+b: U32) -> {G.Gf8.is_zero(G.Gf8.elt(b)) == G.Gf8.is_zero(b) : Bool}:
  %r6p.of_to(G.Gf8Bits.of(b)) : {G.Gf8.is_zero(G.Gf8.elt(b)) == G.Gf8Bits.is_zero(_) : Bool}
  {==}

def r6p.pn.em(+a: U32, +b: U32, +ez: {G.Gf8.is_zero(G.Gf8.mul(G.Gf8.raid6(), a, b)) == True{} : Bool}) -> {G.Gf8.mul(G.Gf8.raid6(), a, b) == 0 : U32}:
  Equal.trans(U32, G.Gf8.mul(G.Gf8.raid6(), a, b), G.Gf8.elt(G.Gf8.mul(G.Gf8.raid6(), a, b)), 0, Equal.sym(U32, G.Gf8.elt(G.Gf8.mul(G.Gf8.raid6(), a, b)), G.Gf8.mul(G.Gf8.raid6(), a, b), r6p.elt_mul(G.Gf8.raid6(), a, b)), r6p.iz_true(G.Gf8.mul(G.Gf8.raid6(), a, b), ez))

# a^-1 a = 1 for a nonzero
def r6p.inv_l(+a: U32, ha: {G.Gf8.is_zero(a) == False{} : Bool}) -> {G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), a), a) == 1 : U32}:
  Equal.trans(U32, G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), a), a), G.Gf8.mul(G.Gf8.raid6(), a, G.Gf8.inv(G.Gf8.raid6(), a)), 1, GL.mul_comm(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), a), a), GL.mul_inv_rs(a, ha))

def r6p.pn.eb(+a: U32, +b: U32, +ez: {G.Gf8.is_zero(G.Gf8.mul(G.Gf8.raid6(), a, b)) == True{} : Bool}, +ha: {G.Gf8.is_zero(a) == False{} : Bool}) -> {G.Gf8.elt(b) == 0 : U32}:
  %GL.mul_one(G.Gf8.raid6(), b) : {_ == 0 : U32}
  %r6p.inv_l(a, ha) : {G.Gf8.mul(G.Gf8.raid6(), _, b) == 0 : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), a), a), b), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), a), G.Gf8.mul(G.Gf8.raid6(), a, b)), GL.mul_assoc(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), a), a, b)) : {_ == 0 : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), a, b), 0, r6p.pn.em(a, b, ez)) : {G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), a), _) == 0 : U32}
  %GL.mul_comm(G.Gf8.raid6(), 0, G.Gf8.inv(G.Gf8.raid6(), a)) : {_ == 0 : U32}
  GL.mul_zero(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), a))

def r6p.pn.bz(+a: U32, +b: U32, +ez: {G.Gf8.is_zero(G.Gf8.mul(G.Gf8.raid6(), a, b)) == True{} : Bool}, +ha: {G.Gf8.is_zero(a) == False{} : Bool}) -> {G.Gf8.is_zero(b) == True{} : Bool}:
  %r6p.iz_elt(b) : {_ == True{} : Bool}
  %Equal.sym(U32, G.Gf8.elt(b), 0, r6p.pn.eb(a, b, ez, ha)) : {G.Gf8.is_zero(_) == True{} : Bool}
  {==}

# a nonzero element times a nonzero element is nonzero
def r6p.pn.go(z: Bool, +a: U32, +b: U32, +ez: {G.Gf8.is_zero(G.Gf8.mul(G.Gf8.raid6(), a, b)) == z : Bool}, +ha: {G.Gf8.is_zero(a) == False{} : Bool}, +hb: {G.Gf8.is_zero(b) == False{} : Bool}) -> {G.Gf8.is_zero(G.Gf8.mul(G.Gf8.raid6(), a, b)) == False{} : Bool}:
  match z:
    case False{}:
      ez
    case True{}:
      Empty.absurd({G.Gf8.is_zero(G.Gf8.mul(G.Gf8.raid6(), a, b)) == False{} : Bool}, r6p.tf(Equal.trans(Bool, True{}, G.Gf8.is_zero(b), False{}, Equal.sym(Bool, G.Gf8.is_zero(b), True{}, r6p.pn.bz(a, b, ez, ha)), hb)))

def r6p.prod_nz(+a: U32, +b: U32, +ha: {G.Gf8.is_zero(a) == False{} : Bool}, +hb: {G.Gf8.is_zero(b) == False{} : Bool}) -> {G.Gf8.is_zero(G.Gf8.mul(G.Gf8.raid6(), a, b)) == False{} : Bool}:
  r6p.pn.go(G.Gf8.is_zero(G.Gf8.mul(G.Gf8.raid6(), a, b)), a, b, {==}, ha, hb)

# g^x is nonzero
def r6p.gp_nz(+x: Nat) -> {G.Gf8.is_zero(G.Gf8.pow(G.Gf8.raid6(), 2, x)) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+k:
      r6p.prod_nz(2, G.Gf8.pow(G.Gf8.raid6(), 2, k), {==}, r6p.gp_nz(k))

def Laws.gpow_nonzero(x):
  r6p.gp_nz(x)

# The walk through g^1 .. g^n from v: none of them is 1
def r6p.walk(n: Nat, +v: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(Bool.not(U32.is_eq(G.Gf8.mul(G.Gf8.raid6(), 2, v), 1)), r6p.walk(m, G.Gf8.mul(G.Gf8.raid6(), 2, v)))

# computed: g^1 .. g^254 are not 1
def r6p.walk_ok() -> {r6p.walk(254n, G.Gf8.pow(G.Gf8.raid6(), 2, 0n)) == True{} : Bool}:
  {==}

def r6p.walk_ne(+n: Nat, +d: Nat, +i: Nat, +h: {r6p.walk(n, G.Gf8.pow(G.Gf8.raid6(), 2, d)) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+Nat.add(i, d)), 1) == False{} : Bool}:
  match n:
    case 0n:
      match i:
        case 0n:
          Empty.absurd({U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+Nat.add(0n, d)), 1) == False{} : Bool}, r6p.ft(hi))
        case 1n+j:
          Empty.absurd({U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+Nat.add(1n+j, d)), 1) == False{} : Bool}, r6p.ft(hi))
    case 1n+m:
      match i:
        case 0n:
          r6p.not_t(U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+d), 1), r6p.and_l(Bool.not(U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+d), 1)), r6p.walk(m, G.Gf8.pow(G.Gf8.raid6(), 2, 1n+d)), h))
        case 1n+j:
          %UL.nat_add_succ(j, d) : {U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+_), 1) == False{} : Bool}
          r6p.walk_ne(m, 1n+d, j, r6p.and_r(Bool.not(U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+d), 1)), r6p.walk(m, G.Gf8.pow(G.Gf8.raid6(), 2, 1n+d)), h), hi)

# g^(1+k) is not 1, for k < 254
def r6p.wf(+k: Nat, +hk: {Nat.is_lt(k, 254n) == True{} : Bool}) -> {U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+k), 1) == False{} : Bool}:
  %UL.nat_add_zero(k) : {U32.is_eq(G.Gf8.pow(G.Gf8.raid6(), 2, 1n+_), 1) == False{} : Bool}
  r6p.walk_ne(254n, 0n, k, r6p.walk_ok(), hk)

def r6p.lt_succ(i: Nat, n: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(i, 1n+n) == True{} : Bool}:
  match i n:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 1n) == True{} : Bool}, r6p.ft(h))
    case 0n 1n+m:
      {==}
    case 1n+j 0n:
      Empty.absurd({Nat.is_lt(1n+j, 1n) == True{} : Bool}, r6p.ft(h))
    case 1n+j 1n+m:
      r6p.lt_succ(j, m, h)

# 2^-1 2 = 1
def r6p.inv2() -> {G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), 2) == 1 : U32}:
  r6p.inv_l(2, {==})

# cancelling a factor 2
def r6p.cancel2(+a: U32, +b: U32, +e: {G.Gf8.mul(G.Gf8.raid6(), 2, a) == G.Gf8.mul(G.Gf8.raid6(), 2, b) : U32}) -> {G.Gf8.elt(a) == G.Gf8.elt(b) : U32}:
  %GL.mul_one(G.Gf8.raid6(), a) : {_ == G.Gf8.elt(b) : U32}
  %GL.mul_one(G.Gf8.raid6(), b) : {G.Gf8.mul(G.Gf8.raid6(), 1, a) == _ : U32}
  %r6p.inv2() : {G.Gf8.mul(G.Gf8.raid6(), _, a) == G.Gf8.mul(G.Gf8.raid6(), _, b) : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), 2), a), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), G.Gf8.mul(G.Gf8.raid6(), 2, a)), GL.mul_assoc(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), 2, a)) : {_ == G.Gf8.mul(G.Gf8.raid6(), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), 2), b) : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), 2), b), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), G.Gf8.mul(G.Gf8.raid6(), 2, b)), GL.mul_assoc(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), 2, b)) : {G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), G.Gf8.mul(G.Gf8.raid6(), 2, a)) == _ : U32}
  %e : {G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), G.Gf8.mul(G.Gf8.raid6(), 2, a)) == G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), 2), _) : U32}
  {==}

def r6p.pow_eq(+j: Nat, +k: Nat, +e: {G.Gf8.pow(G.Gf8.raid6(), 2, 1n+j) == G.Gf8.pow(G.Gf8.raid6(), 2, 1n+k) : U32}) -> {G.Gf8.pow(G.Gf8.raid6(), 2, j) == G.Gf8.pow(G.Gf8.raid6(), 2, k) : U32}:
  %r6p.elt_pow(G.Gf8.raid6(), 2, j) : {_ == G.Gf8.pow(G.Gf8.raid6(), 2, k) : U32}
  %r6p.elt_pow(G.Gf8.raid6(), 2, k) : {G.Gf8.elt(G.Gf8.pow(G.Gf8.raid6(), 2, j)) == _ : U32}
  r6p.cancel2(G.Gf8.pow(G.Gf8.raid6(), 2, j), G.Gf8.pow(G.Gf8.raid6(), 2, k), e)

# 1 == g^(1+k) is impossible for k < 254
def r6p.one_ne(+k: Nat, +hk: {Nat.is_lt(k, 254n) == True{} : Bool}, +e: {G.Gf8.pow(G.Gf8.raid6(), 2, 1n+k) == 1 : U32}) -> {U32.is_eq(1, 1) == False{} : Bool}:
  %e : {U32.is_eq(_, 1) == False{} : Bool}
  r6p.wf(k, hk)

# g^x, x < 255, are distinct
def r6p.dist(+x: Nat, +y: Nat, +hx: {Nat.is_lt(x, 255n) == True{} : Bool}, +hy: {Nat.is_lt(y, 255n) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}, +e: {G.Gf8.pow(G.Gf8.raid6(), 2, x) == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}) -> Empty:
  match x y:
    case 0n 0n:
      r6p.ft(ne)
    case 0n 1n+k:
      r6p.tf(r6p.one_ne(k, hy, Equal.sym(U32, 1, G.Gf8.pow(G.Gf8.raid6(), 2, 1n+k), e)))
    case 1n+j 0n:
      r6p.tf(r6p.one_ne(j, hx, e))
    case 1n+j 1n+k:
      r6p.dist(j, k, r6p.lt_succ(j, 254n, hx), r6p.lt_succ(k, 254n, hy), ne, r6p.pow_eq(j, k, e))

def Laws.gpow_distinct(x, y, hx, hy, ne):
  e => r6p.dist(x, y, hx, hy, ne, e)

# For two lost data blocks x != y: g^y g^-x + 1 is nonzero

def r6p.zz.m1(+gx: U32, +gy: U32, +ez: {G.Gf8.is_zero(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1)) == True{} : Bool}) -> {G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)) == 1 : U32}:
  %r6p.elt_mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)) : {_ == 1 : U32}
  %GL.add_zero(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx))) : {_ == 1 : U32}
  %GL.add_self(1) : {G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), _) == 1 : U32}
  %GL.add_assoc(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1, 1) : {_ == 1 : U32}
  %Equal.sym(U32, G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1), 0, Equal.trans(U32, G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1), G.Gf8.elt(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1)), 0, Equal.sym(U32, G.Gf8.elt(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1)), G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1), r6p.elt_add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1)), r6p.iz_true(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), gy, G.Gf8.inv(G.Gf8.raid6(), gx)), 1), ez))) : {G.Gf8.add(_, 1) == 1 : U32}
  {==}

def r6p.zz.eq(+x: Nat, +y: Nat, +ez: {G.Gf8.is_zero(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x))), 1)) == True{} : Bool}) -> {G.Gf8.pow(G.Gf8.raid6(), 2, x) == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}:
  %r6p.elt_pow(G.Gf8.raid6(), 2, x) : {_ == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}
  %GL.mul_one(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x)) : {_ == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}
  %r6p.zz.m1(G.Gf8.pow(G.Gf8.raid6(), 2, x), G.Gf8.pow(G.Gf8.raid6(), 2, y), ez) : {G.Gf8.mul(G.Gf8.raid6(), _, G.Gf8.pow(G.Gf8.raid6(), 2, x)) == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x))), G.Gf8.pow(G.Gf8.raid6(), 2, x)), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x)), G.Gf8.pow(G.Gf8.raid6(), 2, x))), GL.mul_assoc(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x)), G.Gf8.pow(G.Gf8.raid6(), 2, x))) : {_ == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x)), G.Gf8.pow(G.Gf8.raid6(), 2, x)), 1, r6p.inv_l(G.Gf8.pow(G.Gf8.raid6(), 2, x), r6p.gp_nz(x))) : {G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), _) == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}
  %GL.mul_comm(G.Gf8.raid6(), 1, G.Gf8.pow(G.Gf8.raid6(), 2, y)) : {_ == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), 1, G.Gf8.pow(G.Gf8.raid6(), 2, y)), G.Gf8.elt(G.Gf8.pow(G.Gf8.raid6(), 2, y)), GL.mul_one(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y))) : {_ == G.Gf8.pow(G.Gf8.raid6(), 2, y) : U32}
  r6p.elt_pow(G.Gf8.raid6(), 2, y)

def r6p.zz.go(z: Bool, +x: Nat, +y: Nat, +ez: {G.Gf8.is_zero(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x))), 1)) == z : Bool}, +hx: {Nat.is_lt(x, 255n) == True{} : Bool}, +hy: {Nat.is_lt(y, 255n) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {G.Gf8.is_zero(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x))), 1)) == False{} : Bool}:
  match z:
    case False{}:
      ez
    case True{}:
      Empty.absurd({G.Gf8.is_zero(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x))), 1)) == False{} : Bool}, r6p.dist(x, y, hx, hy, ne, r6p.zz.eq(x, y, ez)))

def r6p.zden(+x: Nat, +y: Nat, +hx: {Nat.is_lt(x, 255n) == True{} : Bool}, +hy: {Nat.is_lt(y, 255n) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {G.Gf8.is_zero(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x))), 1)) == False{} : Bool}:
  r6p.zz.go(G.Gf8.is_zero(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, y), G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x))), 1)), x, y, {==}, hx, hy, ne)

# F. Recovery

# Abbreviations (each unfolds to what it names)

def r6p.F() -> G.Gf8Field:
  G.Gf8.raid6()

def r6p.E() -> B.Octets:
  B.Octets.empty()

def r6p.xo(a: B.Octets, b: B.Octets) -> B.Octets:
  X.Xorb.xor(a, b)

def r6p.sc(c: U32, b: B.Octets) -> B.Octets:
  S.Raid6.scale(G.Gf8.raid6(), c, b)

def r6p.e1(ds: List<&2, B.Octets>, x: Nat) -> List<&2, B.Octets>:
  R.Raid6.set_block(ds, x, B.Octets.empty())

def r6p.e2(ds: List<&2, B.Octets>, x: Nat, y: Nat) -> List<&2, B.Octets>:
  R.Raid6.set_block(R.Raid6.set_block(ds, x, B.Octets.empty()), y, B.Octets.empty())

def r6p.QQ(ds: List<&2, B.Octets>) -> B.Octets:
  R.Raid6.q(R.Raid6.spec(), ds)

def r6p.g(x: Nat) -> U32:
  G.Gf8.pow(G.Gf8.raid6(), 2, x)

def r6p.ix(x: Nat) -> U32:
  G.Gf8.inv(G.Gf8.raid6(), G.Gf8.pow(G.Gf8.raid6(), 2, x))

def r6p.gyx(x: Nat, y: Nat) -> U32:
  G.Gf8.mul(G.Gf8.raid6(), r6p.g(y), r6p.ix(x))

def r6p.den(+x: Nat, +y: Nat) -> U32:
  G.Gf8.inv(G.Gf8.raid6(), G.Gf8.add(r6p.gyx(x, y), 1))

def r6p.A(+x: Nat, +y: Nat) -> U32:
  G.Gf8.mul(G.Gf8.raid6(), r6p.gyx(x, y), r6p.den(x, y))

def r6p.Bc(+x: Nat, +y: Nat) -> U32:
  G.Gf8.mul(G.Gf8.raid6(), r6p.ix(x), r6p.den(x, y))

# XORing r in twice leaves a, when r is no longer than a
def r6p.canc(+a: B.Octets, +r: B.Octets, +h: {Nat.is_le(B.Octets.len(r), B.Octets.len(a)) == True{} : Bool}) -> {r6p.xo(r6p.xo(a, r), r) == a : B.Octets}:
  %Equal.sym(B.Octets, r6p.xo(r6p.xo(a, r), r), r6p.xo(a, r6p.xo(r, r)), XL.xor_assoc(a, r, r)) : {_ == a : B.Octets}
  %Equal.sym(B.Octets, r6p.xo(r, r), B.Octets.zeros(B.Octets.len(r)), XL.xor_self(r)) : {r6p.xo(a, _) == a : B.Octets}
  XL.xor_zeros(a, B.Octets.len(r), h)

# n no more than the common length is no more than block x's
def r6p.le_blk(+ds: List<&2, B.Octets>, +x: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}, +n: Nat, +hn: {Nat.is_le(n, r6p.hlen(ds)) == True{} : Bool}) -> {Nat.is_le(n, B.Octets.len(R.Raid6.block(ds, x))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(R.Raid6.block(ds, x)), r6p.hlen(ds), r6p.blk_len(ds, x, u, hx)) : {Nat.is_le(n, _) == True{} : Bool}
  hn

def r6p.w1(+ds: List<&2, B.Octets>, +x: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}) -> {r6p.within(r6p.hlen(ds), r6p.e1(ds, x)) == True{} : Bool}:
  r6p.within_set(r6p.hlen(ds), ds, x, r6p.uniform_within(ds, u))

def r6p.w2(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}) -> {r6p.within(r6p.hlen(ds), r6p.e2(ds, x, y)) == True{} : Bool}:
  r6p.within_set(r6p.hlen(ds), r6p.e1(ds, x), y, r6p.w1(ds, x, u))

# One data block from P

def r6p.from_p_ok(+ds: List<&2, B.Octets>, +x: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}) -> {r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e1(ds, x))) == R.Raid6.block(ds, x) : B.Octets}:
  %Equal.sym(B.Octets, X.Xorb.all(ds), r6p.xo(R.Raid6.block(ds, x), X.Xorb.all(r6p.e1(ds, x))), r6p.p_split(ds, x)) : {r6p.xo(_, X.Xorb.all(r6p.e1(ds, x))) == R.Raid6.block(ds, x) : B.Octets}
  r6p.canc(R.Raid6.block(ds, x), X.Xorb.all(r6p.e1(ds, x)), r6p.le_blk(ds, x, u, hx, B.Octets.len(X.Xorb.all(r6p.e1(ds, x))), r6p.within_p(r6p.hlen(ds), r6p.e1(ds, x), r6p.w1(ds, x, u))))

# a block put back where it was erased
def r6p.put_back(+ds: List<&2, B.Octets>, +x: Nat) -> {R.Raid6.set_block(r6p.e1(ds, x), x, R.Raid6.block(ds, x)) == ds : List<&2, B.Octets>}:
  %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e1(ds, x), x, R.Raid6.block(ds, x)), R.Raid6.set_block(ds, x, R.Raid6.block(ds, x)), r6p.set_set(ds, x, B.Octets.empty(), R.Raid6.block(ds, x))) : {_ == ds : List<&2, B.Octets>}
  r6p.set_get(ds, x)

def r6p.data_ok(+ds: List<&2, B.Octets>, +x: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}) -> {R.Raid6.set_block(r6p.e1(ds, x), x, r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e1(ds, x)))) == ds : List<&2, B.Octets>}:
  %Equal.sym(B.Octets, r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e1(ds, x))), R.Raid6.block(ds, x), r6p.from_p_ok(ds, x, u, hx)) : {R.Raid6.set_block(r6p.e1(ds, x), x, _) == ds : List<&2, B.Octets>}
  r6p.put_back(ds, x)

# One data block from Q (equation 5)

def r6p.le_sq(+ds: List<&2, B.Octets>, +x: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}) -> {Nat.is_le(B.Octets.len(r6p.QQ(r6p.e1(ds, x))), B.Octets.len(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(r6p.sc(r6p.g(x), R.Raid6.block(ds, x))), B.Octets.len(R.Raid6.block(ds, x)), Laws.scale_len(G.Gf8.raid6(), r6p.g(x), R.Raid6.block(ds, x))) : {Nat.is_le(B.Octets.len(r6p.QQ(r6p.e1(ds, x))), _) == True{} : Bool}
  r6p.le_blk(ds, x, u, hx, B.Octets.len(r6p.QQ(r6p.e1(ds, x))), r6p.within_q(R.Raid6.spec(), r6p.hlen(ds), r6p.e1(ds, x), r6p.w1(ds, x, u)))

def r6p.from_q_ok(+ds: List<&2, B.Octets>, +x: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}) -> {r6p.sc(r6p.ix(x), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e1(ds, x)))) == R.Raid6.block(ds, x) : B.Octets}:
  %Equal.sym(B.Octets, r6p.QQ(ds), r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.QQ(r6p.e1(ds, x))), r6p.q_split(R.Raid6.spec(), ds, x)) : {r6p.sc(r6p.ix(x), r6p.xo(_, r6p.QQ(r6p.e1(ds, x)))) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.xo(r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.QQ(r6p.e1(ds, x))), r6p.QQ(r6p.e1(ds, x))), r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.canc(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.QQ(r6p.e1(ds, x)), r6p.le_sq(ds, x, u, hx))) : {r6p.sc(r6p.ix(x), _) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.sc(r6p.ix(x), r6p.sc(r6p.g(x), R.Raid6.block(ds, x))), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.ix(x), r6p.g(x)), R.Raid6.block(ds, x)), Laws.scale_scale(G.Gf8.raid6(), r6p.ix(x), r6p.g(x), R.Raid6.block(ds, x))) : {_ == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), r6p.ix(x), r6p.g(x)), 1, r6p.inv_l(r6p.g(x), r6p.gp_nz(x))) : {r6p.sc(_, R.Raid6.block(ds, x)) == R.Raid6.block(ds, x) : B.Octets}
  Laws.scale_one(G.Gf8.raid6(), R.Raid6.block(ds, x))

def r6p.datap_ok(+ds: List<&2, B.Octets>, +x: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}) -> {R.Raid6.set_block(r6p.e1(ds, x), x, r6p.sc(r6p.ix(x), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e1(ds, x))))) == ds : List<&2, B.Octets>}:
  %Equal.sym(B.Octets, r6p.sc(r6p.ix(x), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e1(ds, x)))), R.Raid6.block(ds, x), r6p.from_q_ok(ds, x, u, hx)) : {R.Raid6.set_block(r6p.e1(ds, x), x, _) == ds : List<&2, B.Octets>}
  r6p.put_back(ds, x)

# Two data blocks: P + P_xy = D_x + D_y and Q + Q_xy = g^x D_x + g^y D_y

def r6p.le_xy(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}, +n: Nat, +hn: {Nat.is_le(n, r6p.hlen(ds)) == True{} : Bool}) -> {Nat.is_le(n, B.Octets.len(r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y))), Nat.max(B.Octets.len(R.Raid6.block(ds, x)), B.Octets.len(R.Raid6.block(ds, y))), XL.xor_len(R.Raid6.block(ds, x), R.Raid6.block(ds, y))) : {Nat.is_le(n, _) == True{} : Bool}
  r6p.le_max_l(n, B.Octets.len(R.Raid6.block(ds, x)), B.Octets.len(R.Raid6.block(ds, y)), r6p.le_blk(ds, x, u, hx, n, hn))

def r6p.pd_ok(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y))) == r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)) : B.Octets}:
  %Equal.sym(B.Octets, X.Xorb.all(ds), r6p.xo(R.Raid6.block(ds, x), X.Xorb.all(r6p.e1(ds, x))), r6p.p_split(ds, x)) : {r6p.xo(_, X.Xorb.all(r6p.e2(ds, x, y))) == r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)) : B.Octets}
  %Equal.sym(B.Octets, X.Xorb.all(r6p.e1(ds, x)), r6p.xo(R.Raid6.block(r6p.e1(ds, x), y), X.Xorb.all(r6p.e2(ds, x, y))), r6p.p_split(r6p.e1(ds, x), y)) : {r6p.xo(r6p.xo(R.Raid6.block(ds, x), _), X.Xorb.all(r6p.e2(ds, x, y))) == r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)) : B.Octets}
  %Equal.sym(B.Octets, R.Raid6.block(r6p.e1(ds, x), y), R.Raid6.block(ds, y), r6p.blk_set_ne(ds, x, y, B.Octets.empty(), ne)) : {r6p.xo(r6p.xo(R.Raid6.block(ds, x), r6p.xo(_, X.Xorb.all(r6p.e2(ds, x, y)))), X.Xorb.all(r6p.e2(ds, x, y))) == r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)) : B.Octets}
  %XL.xor_assoc(R.Raid6.block(ds, x), R.Raid6.block(ds, y), X.Xorb.all(r6p.e2(ds, x, y))) : {r6p.xo(_, X.Xorb.all(r6p.e2(ds, x, y))) == r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)) : B.Octets}
  r6p.canc(r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)), X.Xorb.all(r6p.e2(ds, x, y)), r6p.le_xy(ds, x, y, u, hx, B.Octets.len(X.Xorb.all(r6p.e2(ds, x, y))), r6p.within_p(r6p.hlen(ds), r6p.e2(ds, x, y), r6p.w2(ds, x, y, u))))

def r6p.le_q2(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}) -> {Nat.is_le(B.Octets.len(r6p.QQ(r6p.e2(ds, x, y))), B.Octets.len(r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y)))), Nat.max(B.Octets.len(r6p.sc(r6p.g(x), R.Raid6.block(ds, x))), B.Octets.len(r6p.sc(r6p.g(y), R.Raid6.block(ds, y)))), XL.xor_len(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y)))) : {Nat.is_le(B.Octets.len(r6p.QQ(r6p.e2(ds, x, y))), _) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(r6p.sc(r6p.g(x), R.Raid6.block(ds, x))), B.Octets.len(R.Raid6.block(ds, x)), Laws.scale_len(G.Gf8.raid6(), r6p.g(x), R.Raid6.block(ds, x))) : {Nat.is_le(B.Octets.len(r6p.QQ(r6p.e2(ds, x, y))), Nat.max(_, B.Octets.len(r6p.sc(r6p.g(y), R.Raid6.block(ds, y))))) == True{} : Bool}
  r6p.le_max_l(B.Octets.len(r6p.QQ(r6p.e2(ds, x, y))), B.Octets.len(R.Raid6.block(ds, x)), B.Octets.len(r6p.sc(r6p.g(y), R.Raid6.block(ds, y))), r6p.le_blk(ds, x, u, hx, B.Octets.len(r6p.QQ(r6p.e2(ds, x, y))), r6p.within_q(R.Raid6.spec(), r6p.hlen(ds), r6p.e2(ds, x, y), r6p.w2(ds, x, y, u))))

def r6p.qd_ok(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y))) == r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))) : B.Octets}:
  %Equal.sym(B.Octets, r6p.QQ(ds), r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.QQ(r6p.e1(ds, x))), r6p.q_split(R.Raid6.spec(), ds, x)) : {r6p.xo(_, r6p.QQ(r6p.e2(ds, x, y))) == r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))) : B.Octets}
  %Equal.sym(B.Octets, r6p.QQ(r6p.e1(ds, x)), r6p.xo(r6p.sc(r6p.g(y), R.Raid6.block(r6p.e1(ds, x), y)), r6p.QQ(r6p.e2(ds, x, y))), r6p.q_split(R.Raid6.spec(), r6p.e1(ds, x), y)) : {r6p.xo(r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), _), r6p.QQ(r6p.e2(ds, x, y))) == r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))) : B.Octets}
  %Equal.sym(B.Octets, R.Raid6.block(r6p.e1(ds, x), y), R.Raid6.block(ds, y), r6p.blk_set_ne(ds, x, y, B.Octets.empty(), ne)) : {r6p.xo(r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.xo(r6p.sc(r6p.g(y), _), r6p.QQ(r6p.e2(ds, x, y)))), r6p.QQ(r6p.e2(ds, x, y))) == r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))) : B.Octets}
  %XL.xor_assoc(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y)), r6p.QQ(r6p.e2(ds, x, y))) : {r6p.xo(_, r6p.QQ(r6p.e2(ds, x, y))) == r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))) : B.Octets}
  r6p.canc(r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))), r6p.QQ(r6p.e2(ds, x, y)), r6p.le_q2(ds, x, y, u, hx))

# The coefficients of equations 17 and 18: A + B g^x = 1 and A + B g^y = 0

def r6p.coef1(+x: Nat, +y: Nat, +hx: {Nat.is_lt(x, 255n) == True{} : Bool}, +hy: {Nat.is_lt(y, 255n) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x))) == 1 : U32}:
  %GL.mul_comm(G.Gf8.raid6(), r6p.den(x, y), r6p.ix(x)) : {G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), _, r6p.g(x))) == 1 : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), r6p.ix(x)), r6p.g(x)), G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.ix(x), r6p.g(x))), GL.mul_assoc(G.Gf8.raid6(), r6p.den(x, y), r6p.ix(x), r6p.g(x))) : {G.Gf8.add(r6p.A(x, y), _) == 1 : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), r6p.ix(x), r6p.g(x)), 1, r6p.inv_l(r6p.g(x), r6p.gp_nz(x))) : {G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), _)) == 1 : U32}
  %GL.mul_comm(G.Gf8.raid6(), r6p.den(x, y), r6p.gyx(x, y)) : {G.Gf8.add(_, G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), 1)) == 1 : U32}
  %GL.mul_distrib(G.Gf8.raid6(), r6p.den(x, y), r6p.gyx(x, y), 1) : {_ == 1 : U32}
  %GL.mul_comm(G.Gf8.raid6(), G.Gf8.add(r6p.gyx(x, y), 1), r6p.den(x, y)) : {_ == 1 : U32}
  GL.mul_inv_rs(G.Gf8.add(r6p.gyx(x, y), 1), r6p.zden(x, y, hx, hy, ne))

def r6p.coef0(+x: Nat, +y: Nat) -> {G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y))) == 0 : U32}:
  %GL.mul_comm(G.Gf8.raid6(), r6p.den(x, y), r6p.ix(x)) : {G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), _, r6p.g(y))) == 0 : U32}
  %Equal.sym(U32, G.Gf8.mul(G.Gf8.raid6(), G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), r6p.ix(x)), r6p.g(y)), G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.ix(x), r6p.g(y))), GL.mul_assoc(G.Gf8.raid6(), r6p.den(x, y), r6p.ix(x), r6p.g(y))) : {G.Gf8.add(r6p.A(x, y), _) == 0 : U32}
  %GL.mul_comm(G.Gf8.raid6(), r6p.g(y), r6p.ix(x)) : {G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), _)) == 0 : U32}
  %GL.mul_comm(G.Gf8.raid6(), r6p.den(x, y), r6p.gyx(x, y)) : {G.Gf8.add(_, G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), r6p.gyx(x, y))) == 0 : U32}
  GL.add_self(G.Gf8.mul(G.Gf8.raid6(), r6p.den(x, y), r6p.gyx(x, y)))

def r6p.ne_sym(x: Nat, y: Nat, +ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {Nat.is_ne(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_ne(0n, 0n) == True{} : Bool}, r6p.ft(ne))
    case 0n 1n+k:
      {==}
    case 1n+j 0n:
      {==}
    case 1n+j 1n+k:
      r6p.ne_sym(j, k, ne)

# D_x = A (P + P_xy) + B (Q + Q_xy)   (equation 19)
def r6p.dx_ok(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}, +hy: {Nat.is_lt(y, R.Raid6.width(ds)) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}, +hx2: {Nat.is_lt(x, 255n) == True{} : Bool}, +hy2: {Nat.is_lt(y, 255n) == True{} : Bool}) -> {r6p.xo(r6p.sc(r6p.A(x, y), r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y)))), r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y))))) == R.Raid6.block(ds, x) : B.Octets}:
  %Equal.sym(B.Octets, r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y))), r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)), r6p.pd_ok(ds, x, y, u, hx, ne)) : {r6p.xo(r6p.sc(r6p.A(x, y), _), r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y))))) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y))), r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))), r6p.qd_ok(ds, x, y, u, hx, ne)) : {r6p.xo(r6p.sc(r6p.A(x, y), r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y))), r6p.sc(r6p.Bc(x, y), _)) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.sc(r6p.A(x, y), r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y))), r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, x)), r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y))), Laws.scale_xor(G.Gf8.raid6(), r6p.A(x, y), R.Raid6.block(ds, x), R.Raid6.block(ds, y))) : {r6p.xo(_, r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))))) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y)))), r6p.xo(r6p.sc(r6p.Bc(x, y), r6p.sc(r6p.g(x), R.Raid6.block(ds, x))), r6p.sc(r6p.Bc(x, y), r6p.sc(r6p.g(y), R.Raid6.block(ds, y)))), Laws.scale_xor(G.Gf8.raid6(), r6p.Bc(x, y), r6p.sc(r6p.g(x), R.Raid6.block(ds, x)), r6p.sc(r6p.g(y), R.Raid6.block(ds, y)))) : {r6p.xo(r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, x)), r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y))), _) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.sc(r6p.Bc(x, y), r6p.sc(r6p.g(x), R.Raid6.block(ds, x))), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x)), R.Raid6.block(ds, x)), Laws.scale_scale(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x), R.Raid6.block(ds, x))) : {r6p.xo(r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, x)), r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y))), r6p.xo(_, r6p.sc(r6p.Bc(x, y), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))))) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.sc(r6p.Bc(x, y), r6p.sc(r6p.g(y), R.Raid6.block(ds, y))), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y)), R.Raid6.block(ds, y)), Laws.scale_scale(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y), R.Raid6.block(ds, y))) : {r6p.xo(r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, x)), r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y))), r6p.xo(r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x)), R.Raid6.block(ds, x)), _)) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.xo(r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, x)), r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y))), r6p.xo(r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x)), R.Raid6.block(ds, x)), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y)), R.Raid6.block(ds, y)))), r6p.xo(r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, x)), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x)), R.Raid6.block(ds, x))), r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y)), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y)), R.Raid6.block(ds, y)))), r6p.sw4(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, x)), r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y)), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x)), R.Raid6.block(ds, x)), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y)), R.Raid6.block(ds, y)))) : {_ == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, x)), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x)), R.Raid6.block(ds, x))), r6p.sc(G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x))), R.Raid6.block(ds, x)), Laws.scale_add(G.Gf8.raid6(), r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x)), R.Raid6.block(ds, x))) : {r6p.xo(_, r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y)), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y)), R.Raid6.block(ds, y)))) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.xo(r6p.sc(r6p.A(x, y), R.Raid6.block(ds, y)), r6p.sc(G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y)), R.Raid6.block(ds, y))), r6p.sc(G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y))), R.Raid6.block(ds, y)), Laws.scale_add(G.Gf8.raid6(), r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y)), R.Raid6.block(ds, y))) : {r6p.xo(r6p.sc(G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x))), R.Raid6.block(ds, x)), _) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(U32, G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(x))), 1, r6p.coef1(x, y, hx2, hy2, ne)) : {r6p.xo(r6p.sc(_, R.Raid6.block(ds, x)), r6p.sc(G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y))), R.Raid6.block(ds, y))) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(U32, G.Gf8.add(r6p.A(x, y), G.Gf8.mul(G.Gf8.raid6(), r6p.Bc(x, y), r6p.g(y))), 0, r6p.coef0(x, y)) : {r6p.xo(r6p.sc(1, R.Raid6.block(ds, x)), r6p.sc(_, R.Raid6.block(ds, y))) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.sc(1, R.Raid6.block(ds, x)), R.Raid6.block(ds, x), Laws.scale_one(G.Gf8.raid6(), R.Raid6.block(ds, x))) : {r6p.xo(_, r6p.sc(0, R.Raid6.block(ds, y))) == R.Raid6.block(ds, x) : B.Octets}
  %Equal.sym(B.Octets, r6p.sc(0, R.Raid6.block(ds, y)), B.Octets.zeros(B.Octets.len(R.Raid6.block(ds, y))), Laws.scale_zero(G.Gf8.raid6(), R.Raid6.block(ds, y))) : {r6p.xo(R.Raid6.block(ds, x), _) == R.Raid6.block(ds, x) : B.Octets}
  XL.xor_zeros(R.Raid6.block(ds, x), B.Octets.len(R.Raid6.block(ds, y)), r6p.le_blk(ds, x, u, hx, B.Octets.len(R.Raid6.block(ds, y)), r6p.to_le(B.Octets.len(R.Raid6.block(ds, y)), r6p.hlen(ds), r6p.blk_len(ds, y, u, hy))))

# D_y = (P + P_xy) + D_x   (equation 20)
def r6p.dy_ok(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}, +hy: {Nat.is_lt(y, R.Raid6.width(ds)) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}) -> {r6p.xo(r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y))), R.Raid6.block(ds, x)) == R.Raid6.block(ds, y) : B.Octets}:
  %Equal.sym(B.Octets, r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y))), r6p.xo(R.Raid6.block(ds, x), R.Raid6.block(ds, y)), r6p.pd_ok(ds, x, y, u, hx, ne)) : {r6p.xo(_, R.Raid6.block(ds, x)) == R.Raid6.block(ds, y) : B.Octets}
  %XL.xor_comm(R.Raid6.block(ds, y), R.Raid6.block(ds, x)) : {r6p.xo(_, R.Raid6.block(ds, x)) == R.Raid6.block(ds, y) : B.Octets}
  r6p.canc(R.Raid6.block(ds, y), R.Raid6.block(ds, x), r6p.le_blk(ds, y, u, hy, B.Octets.len(R.Raid6.block(ds, x)), r6p.to_le(B.Octets.len(R.Raid6.block(ds, x)), r6p.hlen(ds), r6p.blk_len(ds, x, u, hx))))

# both put back
def r6p.dd_ok(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +hx: {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}, +hy: {Nat.is_lt(y, R.Raid6.width(ds)) == True{} : Bool}, +ne: {Nat.is_ne(x, y) == True{} : Bool}, +hx2: {Nat.is_lt(x, 255n) == True{} : Bool}, +hy2: {Nat.is_lt(y, 255n) == True{} : Bool}) -> {R.Raid6.set_block(R.Raid6.set_block(r6p.e2(ds, x, y), x, r6p.xo(r6p.sc(r6p.A(x, y), r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y)))), r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y)))))), y, r6p.xo(r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y))), r6p.xo(r6p.sc(r6p.A(x, y), r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y)))), r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y))))))) == ds : List<&2, B.Octets>}:
  %Equal.sym(B.Octets, r6p.xo(r6p.sc(r6p.A(x, y), r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y)))), r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y))))), R.Raid6.block(ds, x), r6p.dx_ok(ds, x, y, u, hx, hy, ne, hx2, hy2)) : {R.Raid6.set_block(R.Raid6.set_block(r6p.e2(ds, x, y), x, _), y, r6p.xo(r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y))), _)) == ds : List<&2, B.Octets>}
  %Equal.sym(B.Octets, r6p.xo(r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y))), R.Raid6.block(ds, x)), R.Raid6.block(ds, y), r6p.dy_ok(ds, x, y, u, hx, hy, ne)) : {R.Raid6.set_block(R.Raid6.set_block(r6p.e2(ds, x, y), x, R.Raid6.block(ds, x)), y, _) == ds : List<&2, B.Octets>}
  %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(R.Raid6.set_block(r6p.e1(ds, x), y, B.Octets.empty()), x, R.Raid6.block(ds, x)), R.Raid6.set_block(R.Raid6.set_block(r6p.e1(ds, x), x, R.Raid6.block(ds, x)), y, B.Octets.empty()), r6p.set_comm(r6p.e1(ds, x), y, x, B.Octets.empty(), R.Raid6.block(ds, x), r6p.ne_sym(x, y, ne))) : {R.Raid6.set_block(_, y, R.Raid6.block(ds, y)) == ds : List<&2, B.Octets>}
  %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e1(ds, x), x, R.Raid6.block(ds, x)), ds, r6p.put_back(ds, x)) : {R.Raid6.set_block(R.Raid6.set_block(_, y, B.Octets.empty()), y, R.Raid6.block(ds, y)) == ds : List<&2, B.Octets>}
  r6p.put_back(ds, y)

# What Raid6.check accepting a loss says

def r6p.mdisc(m: Maybe<&2, V.Raid6Error>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{v}:
      Unit

def r6p.msome(-v: V.Raid6Error, +e: {Some{v} == None{} : Maybe<&2, V.Raid6Error>}) -> Empty:
  %e : r6p.mdisc(_)
  Unit{}

def r6p.size_t(b: Bool, +n: Nat, +lost: V.Raid6Lost, +h: {V.r6.chk.size(b, n, lost) == None{} : Maybe<&2, V.Raid6Error>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, r6p.msome(V.Raid6TooManyDisks{n}, h))

def r6p.size_l(b: Bool, +n: Nat, +lost: V.Raid6Lost, +h: {V.r6.chk.size(b, n, lost) == None{} : Maybe<&2, V.Raid6Error>}) -> {V.r6.chk.lost(n, lost) == None{} : Maybe<&2, V.Raid6Error>}:
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({V.r6.chk.lost(n, lost) == None{} : Maybe<&2, V.Raid6Error>}, r6p.msome(V.Raid6TooManyDisks{n}, h))

def r6p.idx_t(b: Bool, +i: Nat, +h: {V.r6.chk.index(b, i) == None{} : Maybe<&2, V.Raid6Error>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, r6p.msome(V.Raid6BadIndex{i}, h))

def r6p.two_x(ex: Maybe<&2, V.Raid6Error>, ey: Maybe<&2, V.Raid6Error>, ne: Bool, +x: Nat, +h: {V.r6.chk.two(ex, ey, ne, x) == None{} : Maybe<&2, V.Raid6Error>}) -> {ex == None{} : Maybe<&2, V.Raid6Error>}:
  match ex:
    case Some{v}:
      Empty.absurd({Some{v} == None{} : Maybe<&2, V.Raid6Error>}, r6p.msome(v, h))
    case None{}:
      {==}

def r6p.two_y(ex: Maybe<&2, V.Raid6Error>, ey: Maybe<&2, V.Raid6Error>, ne: Bool, +x: Nat, +h: {V.r6.chk.two(ex, ey, ne, x) == None{} : Maybe<&2, V.Raid6Error>}) -> {ey == None{} : Maybe<&2, V.Raid6Error>}:
  match ex:
    case Some{v}:
      Empty.absurd({ey == None{} : Maybe<&2, V.Raid6Error>}, r6p.msome(v, h))
    case None{}:
      match ey:
        case Some{w}:
          Empty.absurd({Some{w} == None{} : Maybe<&2, V.Raid6Error>}, r6p.msome(w, h))
        case None{}:
          {==}

def r6p.two_n(ex: Maybe<&2, V.Raid6Error>, ey: Maybe<&2, V.Raid6Error>, ne: Bool, +x: Nat, +h: {V.r6.chk.two(ex, ey, ne, x) == None{} : Maybe<&2, V.Raid6Error>}) -> {ne == True{} : Bool}:
  match ex:
    case Some{v}:
      Empty.absurd({ne == True{} : Bool}, r6p.msome(v, h))
    case None{}:
      match ey:
        case Some{w}:
          Empty.absurd({ne == True{} : Bool}, r6p.msome(w, h))
        case None{}:
          match ne:
            case True{}:
              {==}
            case False{}:
              Empty.absurd({False{} == True{} : Bool}, r6p.msome(V.Raid6SameIndex{x}, h))

def r6p.dd_lost(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +ok: {V.Raid6.check(R.Raid6.width(ds), V.Raid6LostDataData{x, y}) == None{} : Maybe<&2, V.Raid6Error>}) -> {V.r6.chk.lost(R.Raid6.width(ds), V.Raid6LostDataData{x, y}) == None{} : Maybe<&2, V.Raid6Error>}:
  r6p.size_l(Nat.is_le(R.Raid6.width(ds), 255n), R.Raid6.width(ds), V.Raid6LostDataData{x, y}, ok)

def r6p.dd_hx(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +ok: {V.Raid6.check(R.Raid6.width(ds), V.Raid6LostDataData{x, y}) == None{} : Maybe<&2, V.Raid6Error>}) -> {Nat.is_lt(x, R.Raid6.width(ds)) == True{} : Bool}:
  r6p.idx_t(Nat.is_lt(x, R.Raid6.width(ds)), x, r6p.two_x(V.r6.chk.index(Nat.is_lt(x, R.Raid6.width(ds)), x), V.r6.chk.index(Nat.is_lt(y, R.Raid6.width(ds)), y), Nat.is_ne(x, y), x, r6p.dd_lost(ds, x, y, ok)))

def r6p.dd_hy(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +ok: {V.Raid6.check(R.Raid6.width(ds), V.Raid6LostDataData{x, y}) == None{} : Maybe<&2, V.Raid6Error>}) -> {Nat.is_lt(y, R.Raid6.width(ds)) == True{} : Bool}:
  r6p.idx_t(Nat.is_lt(y, R.Raid6.width(ds)), y, r6p.two_y(V.r6.chk.index(Nat.is_lt(x, R.Raid6.width(ds)), x), V.r6.chk.index(Nat.is_lt(y, R.Raid6.width(ds)), y), Nat.is_ne(x, y), x, r6p.dd_lost(ds, x, y, ok)))

def r6p.dd_ne(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +ok: {V.Raid6.check(R.Raid6.width(ds), V.Raid6LostDataData{x, y}) == None{} : Maybe<&2, V.Raid6Error>}) -> {Nat.is_ne(x, y) == True{} : Bool}:
  r6p.two_n(V.r6.chk.index(Nat.is_lt(x, R.Raid6.width(ds)), x), V.r6.chk.index(Nat.is_lt(y, R.Raid6.width(ds)), y), Nat.is_ne(x, y), x, r6p.dd_lost(ds, x, y, ok))

# Erasing

def r6p.w_erase(st: R.Raid6Stripe, lost: V.Raid6Lost) -> {V.r6.width(V.Raid6.erase(st, lost)) == V.r6.width(st) : Nat}:
  match st:
    case R.Raid6Stripe{+ds, p, q}:
      match lost:
        case V.Raid6LostNone{}:
          {==}
        case V.Raid6LostData{+x}:
          r6p.width_set(ds, x, B.Octets.empty())
        case V.Raid6LostP{}:
          {==}
        case V.Raid6LostQ{}:
          {==}
        case V.Raid6LostDataData{+x, +y}:
          Equal.trans(Nat, R.Raid6.width(r6p.e2(ds, x, y)), R.Raid6.width(r6p.e1(ds, x)), R.Raid6.width(ds), r6p.width_set(r6p.e1(ds, x), y, B.Octets.empty()), r6p.width_set(ds, x, B.Octets.empty()))
        case V.Raid6LostDataP{+x}:
          r6p.width_set(ds, x, B.Octets.empty())
        case V.Raid6LostDataQ{+x}:
          r6p.width_set(ds, x, B.Octets.empty())
        case V.Raid6LostPQ{}:
          {==}

def r6p.erase_idem(st: R.Raid6Stripe, lost: V.Raid6Lost) -> {V.Raid6.erase(V.Raid6.erase(st, lost), lost) == V.Raid6.erase(st, lost) : R.Raid6Stripe}:
  match st:
    case R.Raid6Stripe{+ds, +p, +q}:
      match lost:
        case V.Raid6LostNone{}:
          {==}
        case V.Raid6LostData{+x}:
          %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e1(ds, x), x, B.Octets.empty()), r6p.e1(ds, x), r6p.set_set(ds, x, B.Octets.empty(), B.Octets.empty())) : {R.Raid6Stripe{_, p, q} == R.Raid6Stripe{r6p.e1(ds, x), p, q} : R.Raid6Stripe}
          {==}
        case V.Raid6LostP{}:
          {==}
        case V.Raid6LostQ{}:
          {==}
        case V.Raid6LostDataData{+x, +y}:
          %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e2(ds, x, y), x, B.Octets.empty()), r6p.e2(ds, x, y), r6p.set_same(r6p.e2(ds, x, y), x, B.Octets.empty(), r6p.blk_set2(ds, x, y))) : {R.Raid6Stripe{R.Raid6.set_block(_, y, B.Octets.empty()), p, q} == R.Raid6Stripe{r6p.e2(ds, x, y), p, q} : R.Raid6Stripe}
          %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e2(ds, x, y), y, B.Octets.empty()), r6p.e2(ds, x, y), r6p.set_same(r6p.e2(ds, x, y), y, B.Octets.empty(), r6p.blk_set_e(r6p.e1(ds, x), y))) : {R.Raid6Stripe{_, p, q} == R.Raid6Stripe{r6p.e2(ds, x, y), p, q} : R.Raid6Stripe}
          {==}
        case V.Raid6LostDataP{+x}:
          %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e1(ds, x), x, B.Octets.empty()), r6p.e1(ds, x), r6p.set_set(ds, x, B.Octets.empty(), B.Octets.empty())) : {R.Raid6Stripe{_, B.Octets.empty(), q} == R.Raid6Stripe{r6p.e1(ds, x), B.Octets.empty(), q} : R.Raid6Stripe}
          {==}
        case V.Raid6LostDataQ{+x}:
          %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e1(ds, x), x, B.Octets.empty()), r6p.e1(ds, x), r6p.set_set(ds, x, B.Octets.empty(), B.Octets.empty())) : {R.Raid6Stripe{_, p, B.Octets.empty()} == R.Raid6Stripe{r6p.e1(ds, x), p, B.Octets.empty()} : R.Raid6Stripe}
          {==}
        case V.Raid6LostPQ{}:
          {==}

# Rebuilding, case by case

def r6p.rebuild_ok(+ds: List<&2, B.Octets>, lost: V.Raid6Lost, +u: {R.Raid6.uniform(ds) == True{} : Bool}, +ok: {V.Raid6.check(R.Raid6.width(ds), lost) == None{} : Maybe<&2, V.Raid6Error>}) -> {V.r6.rebuild(R.Raid6.spec(), V.Raid6.erase(R.Raid6.encode(R.Raid6.spec(), ds), lost), lost) == R.Raid6.encode(R.Raid6.spec(), ds) : R.Raid6Stripe}:
  match lost:
    case V.Raid6LostNone{}:
      {==}
    case V.Raid6LostData{+x}:
      %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e1(ds, x), x, r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e1(ds, x)))), ds, r6p.data_ok(ds, x, u, r6p.idx_t(Nat.is_lt(x, R.Raid6.width(ds)), x, r6p.size_l(Nat.is_le(R.Raid6.width(ds), 255n), R.Raid6.width(ds), V.Raid6LostData{x}, ok)))) : {R.Raid6Stripe{_, X.Xorb.all(ds), r6p.QQ(ds)} == R.Raid6Stripe{ds, X.Xorb.all(ds), r6p.QQ(ds)} : R.Raid6Stripe}
      {==}
    case V.Raid6LostP{}:
      {==}
    case V.Raid6LostQ{}:
      {==}
    case V.Raid6LostDataData{+x, +y}:
      %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(R.Raid6.set_block(r6p.e2(ds, x, y), x, r6p.xo(r6p.sc(r6p.A(x, y), r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y)))), r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y)))))), y, r6p.xo(r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y))), r6p.xo(r6p.sc(r6p.A(x, y), r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e2(ds, x, y)))), r6p.sc(r6p.Bc(x, y), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e2(ds, x, y))))))), ds, r6p.dd_ok(ds, x, y, u, r6p.dd_hx(ds, x, y, ok), r6p.dd_hy(ds, x, y, ok), r6p.dd_ne(ds, x, y, ok), UO.nat_lt_le_trans(x, R.Raid6.width(ds), 255n, r6p.dd_hx(ds, x, y, ok), r6p.size_t(Nat.is_le(R.Raid6.width(ds), 255n), R.Raid6.width(ds), V.Raid6LostDataData{x, y}, ok)), UO.nat_lt_le_trans(y, R.Raid6.width(ds), 255n, r6p.dd_hy(ds, x, y, ok), r6p.size_t(Nat.is_le(R.Raid6.width(ds), 255n), R.Raid6.width(ds), V.Raid6LostDataData{x, y}, ok)))) : {R.Raid6Stripe{_, X.Xorb.all(ds), r6p.QQ(ds)} == R.Raid6Stripe{ds, X.Xorb.all(ds), r6p.QQ(ds)} : R.Raid6Stripe}
      {==}
    case V.Raid6LostDataP{+x}:
      %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e1(ds, x), x, r6p.sc(r6p.ix(x), r6p.xo(r6p.QQ(ds), r6p.QQ(r6p.e1(ds, x))))), ds, r6p.datap_ok(ds, x, u, r6p.idx_t(Nat.is_lt(x, R.Raid6.width(ds)), x, r6p.size_l(Nat.is_le(R.Raid6.width(ds), 255n), R.Raid6.width(ds), V.Raid6LostDataP{x}, ok)))) : {R.Raid6Stripe{_, X.Xorb.all(_), r6p.QQ(ds)} == R.Raid6Stripe{ds, X.Xorb.all(ds), r6p.QQ(ds)} : R.Raid6Stripe}
      {==}
    case V.Raid6LostDataQ{+x}:
      %Equal.sym(List<&2, B.Octets>, R.Raid6.set_block(r6p.e1(ds, x), x, r6p.xo(X.Xorb.all(ds), X.Xorb.all(r6p.e1(ds, x)))), ds, r6p.data_ok(ds, x, u, r6p.idx_t(Nat.is_lt(x, R.Raid6.width(ds)), x, r6p.size_l(Nat.is_le(R.Raid6.width(ds), 255n), R.Raid6.width(ds), V.Raid6LostDataQ{x}, ok)))) : {R.Raid6Stripe{_, X.Xorb.all(ds), r6p.QQ(_)} == R.Raid6Stripe{ds, X.Xorb.all(ds), r6p.QQ(ds)} : R.Raid6Stripe}
      {==}
    case V.Raid6LostPQ{}:
      {==}

def Laws.recover_any(ds, lost, same, ok):
  %Equal.sym(Nat, V.r6.width(V.Raid6.erase(R.Raid6.encode(R.Raid6.spec(), ds), lost)), V.r6.width(R.Raid6.encode(R.Raid6.spec(), ds)), r6p.w_erase(R.Raid6.encode(R.Raid6.spec(), ds), lost)) : {V.r6.recover.pick(V.Raid6.check(_, lost), R.Raid6.spec(), V.Raid6.erase(R.Raid6.encode(R.Raid6.spec(), ds), lost), lost) == Done{R.Raid6.encode(R.Raid6.spec(), ds)} : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}
  %Equal.sym(Maybe<&2, V.Raid6Error>, V.Raid6.check(R.Raid6.width(ds), lost), None{}, ok) : {V.r6.recover.pick(_, R.Raid6.spec(), V.Raid6.erase(R.Raid6.encode(R.Raid6.spec(), ds), lost), lost) == Done{R.Raid6.encode(R.Raid6.spec(), ds)} : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}
  %Equal.sym(R.Raid6Stripe, V.Raid6.erase(V.Raid6.erase(R.Raid6.encode(R.Raid6.spec(), ds), lost), lost), V.Raid6.erase(R.Raid6.encode(R.Raid6.spec(), ds), lost), r6p.erase_idem(R.Raid6.encode(R.Raid6.spec(), ds), lost)) : {Done{V.r6.rebuild(R.Raid6.spec(), _, lost)} == Done{R.Raid6.encode(R.Raid6.spec(), ds)} : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}
  %Equal.sym(R.Raid6Stripe, V.r6.rebuild(R.Raid6.spec(), V.Raid6.erase(R.Raid6.encode(R.Raid6.spec(), ds), lost), lost), R.Raid6.encode(R.Raid6.spec(), ds), r6p.rebuild_ok(ds, lost, same, ok)) : {Done{_} == Done{R.Raid6.encode(R.Raid6.spec(), ds)} : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}
  {==}

def r6p.pick_er(err: Maybe<&2, V.Raid6Error>, +s: R.Raid6Spec, +st: R.Raid6Stripe, +lost: V.Raid6Lost) -> {V.r6.recover.pick(err, s, st, lost) == V.r6.recover.pick(err, s, V.Raid6.erase(st, lost), lost) : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}:
  match err:
    case Some{e}:
      {==}
    case None{}:
      %Equal.sym(R.Raid6Stripe, V.Raid6.erase(V.Raid6.erase(st, lost), lost), V.Raid6.erase(st, lost), r6p.erase_idem(st, lost)) : {Done{V.r6.rebuild(s, V.Raid6.erase(st, lost), lost)} == Done{V.r6.rebuild(s, _, lost)} : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}
      {==}

def Laws.recover_ignores(s, st, lost):
  %Equal.sym(Nat, V.r6.width(V.Raid6.erase(st, lost)), V.r6.width(st), r6p.w_erase(st, lost)) : {V.r6.recover.pick(V.Raid6.check(V.r6.width(st), lost), s, st, lost) == V.r6.recover.pick(V.Raid6.check(_, lost), s, V.Raid6.erase(st, lost), lost) : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}
  r6p.pick_er(V.Raid6.check(V.r6.width(st), lost), s, st, lost)

# Vectors

def Laws.v_g8():
  {==}

def Laws.v_g4():
  {==}

def Laws.v_log():
  {==}

def Laws.v_8d():
  {==}

def Laws.v_p():
  {==}

def Laws.v_q():
  {==}

def Laws.v_recover():
  {==}

def Laws.v_check_index():
  {==}

def Laws.v_check_same():
  {==}

def Laws.v_check_size():
  {==}
