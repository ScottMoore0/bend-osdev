# Properties, for every input:
#   * the syndromes: P is the XOR of the data blocks and Q is computed by
#     Horner's rule (the paper's equations 1, 2 and 21: p_cons, q_cons);
#     each splits off any one block x: P = D_x + P_x and Q = g^x D_x + Q_x,
#     where P_x and Q_x are computed with D_x set to zero (the paper's
#     equations 3 and 6: p_split, q_split), for every field;
#   * scaling a block by a field element: it distributes over XOR, scaling
#     twice is scaling by the product, scaling by a sum is the XOR of the
#     scalings, 1 leaves a block alone, 0 zeroes it, and the length is kept,
#     for every field;
#   * g^x, x < 255, are distinct (the paper, section 1, item 13), and
#     nonzero, in the paper's field;
#   * recovery: for every stripe of data blocks of equal length and every
#     choice of up to two lost blocks (data, P or Q) that Raid6.check
#     accepts, recovering the stripe with those blocks erased gives the
#     stripe back (recover_any); and recovery never reads a lost block
#     (recover_ignores), so overwriting lost blocks with anything changes
#     nothing.
# Vectors: the paper's examples ({02}^8 = {1d}, log {10} = 4, the
# decomposition of A {8d}), the syndromes and recovery of a small stripe,
# and Raid6.check's refusals.
import Base
import ../bytes/bytes.bend as B
import ../gf/gf.bend as G
import ../xorblocks/xorblocks.bend as X
import ./scale.bend as S
import ./raid6.bend as R
import ./recover.bend as V

# The syndromes

law p_cons:
  for +d: B.Octets
  for +ds: List<&2, B.Octets>
  {R.Raid6.p(Con{d, ds}) == X.Xorb.xor(d, R.Raid6.p(ds)) : B.Octets}

law q_cons:
  for +s: R.Raid6Spec
  for +d: B.Octets
  for +ds: List<&2, B.Octets>
  {R.Raid6.q(s, Con{d, ds}) == X.Xorb.xor(d, S.Raid6.scale(R.Raid6.field(s), R.Raid6.gen(s), R.Raid6.q(s, ds))) : B.Octets}

law p_split:
  for +ds: List<&2, B.Octets>
  for +x: Nat
  {R.Raid6.p(ds) == X.Xorb.xor(R.Raid6.block(ds, x), R.Raid6.p(R.Raid6.set_block(ds, x, B.Octets.empty()))) : B.Octets}

law q_split:
  for +s: R.Raid6Spec
  for +ds: List<&2, B.Octets>
  for +x: Nat
  {R.Raid6.q(s, ds) == X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), R.Raid6.gpow(s, x), R.Raid6.block(ds, x)), R.Raid6.q(s, R.Raid6.set_block(ds, x, B.Octets.empty()))) : B.Octets}

# Scaling

law scale_xor:
  for +f: G.Gf8Field
  for +c: U32
  for +a: B.Octets
  for +b: B.Octets
  {S.Raid6.scale(f, c, X.Xorb.xor(a, b)) == X.Xorb.xor(S.Raid6.scale(f, c, a), S.Raid6.scale(f, c, b)) : B.Octets}

law scale_scale:
  for +f: G.Gf8Field
  for +c: U32
  for +d: U32
  for +a: B.Octets
  {S.Raid6.scale(f, c, S.Raid6.scale(f, d, a)) == S.Raid6.scale(f, G.Gf8.mul(f, c, d), a) : B.Octets}

law scale_add:
  for +f: G.Gf8Field
  for +c: U32
  for +d: U32
  for +a: B.Octets
  {X.Xorb.xor(S.Raid6.scale(f, c, a), S.Raid6.scale(f, d, a)) == S.Raid6.scale(f, G.Gf8.add(c, d), a) : B.Octets}

law scale_one:
  for +f: G.Gf8Field
  for +a: B.Octets
  {S.Raid6.scale(f, 1, a) == a : B.Octets}

law scale_zero:
  for +f: G.Gf8Field
  for +a: B.Octets
  {S.Raid6.scale(f, 0, a) == B.Octets.zeros(B.Octets.len(a)) : B.Octets}

law scale_len:
  for +f: G.Gf8Field
  for +c: U32
  for +a: B.Octets
  {B.Octets.len(S.Raid6.scale(f, c, a)) == B.Octets.len(a) : Nat}

# The generator's powers, in the paper's field

law gpow_nonzero:
  for +x: Nat
  {G.Gf8.is_zero(R.Raid6.gpow(R.Raid6.spec(), x)) == False{} : Bool}

law gpow_distinct:
  for +x: Nat
  for +y: Nat
  for hx: {Nat.is_lt(x, 255n) == True{} : Bool}
  for hy: {Nat.is_lt(y, 255n) == True{} : Bool}
  for ne: {Nat.is_ne(x, y) == True{} : Bool}
  {R.Raid6.gpow(R.Raid6.spec(), x) != R.Raid6.gpow(R.Raid6.spec(), y) : U32}

# Recovery

law recover_any:
  for +ds: List<&2, B.Octets>
  for +lost: V.Raid6Lost
  for +same: {R.Raid6.uniform(ds) == True{} : Bool}
  for +ok: {V.Raid6.check(R.Raid6.width(ds), lost) == None{} : Maybe<&2, V.Raid6Error>}
  {V.Raid6.recover(R.Raid6.spec(), V.Raid6.erase(R.Raid6.encode(R.Raid6.spec(), ds), lost), lost) == Done{R.Raid6.encode(R.Raid6.spec(), ds)} : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}

law recover_ignores:
  for +s: R.Raid6Spec
  for +st: R.Raid6Stripe
  for +lost: V.Raid6Lost
  {V.Raid6.recover(s, st, lost) == V.Raid6.recover(s, V.Raid6.erase(st, lost), lost) : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}

# Vectors: the paper's examples (section 1, items 11 and 14)

# {02}^8 = {1d}, {02}^4 = {10}
law v_g8:
  {R.Raid6.gpow(R.Raid6.spec(), 8n) == 29 : U32}

law v_g4:
  {R.Raid6.gpow(R.Raid6.spec(), 4n) == 16 : U32}

# log {10} = 4
law v_log:
  {G.Gf8.log(R.Raid6.field(R.Raid6.spec()), 16) == 4n : Nat}

# A {8d} = A {02}^7 + A {02}^3 + A {02}^2 + A, for A = {57}
law v_8d:
  {G.Gf8.mul(G.Gf8.raid6(), 87, 141) == G.Gf8.add(G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), 87, R.Raid6.gpow(R.Raid6.spec(), 7n)), G.Gf8.mul(G.Gf8.raid6(), 87, R.Raid6.gpow(R.Raid6.spec(), 3n))), G.Gf8.add(G.Gf8.mul(G.Gf8.raid6(), 87, R.Raid6.gpow(R.Raid6.spec(), 2n)), 87)) : U32}

# A small stripe: 01020304, 10203040, fffefdfc (P = eedcceb8, Q = fa9db053,
# from an independent model, ref/gen.py)
law v_p:
  {B.Octets.hex(R.Raid6.p([B.Octets.of_list([1, 2, 3, 4]), B.Octets.of_list([16, 32, 48, 64]), B.Octets.of_list([255, 254, 253, 252])])) == "eedcceb8" : String}

law v_q:
  {B.Octets.hex(R.Raid6.q(R.Raid6.spec(), [B.Octets.of_list([1, 2, 3, 4]), B.Octets.of_list([16, 32, 48, 64]), B.Octets.of_list([255, 254, 253, 252])])) == "fa9db053" : String}

# D_0 and D_2 rebuilt from D_1, P and Q
law v_recover:
  {V.Raid6.recover(R.Raid6.spec(), R.Raid6Stripe{[B.Octets.empty(), B.Octets.of_list([16, 32, 48, 64]), B.Octets.empty()], B.Octets.of_list([238, 220, 206, 184]), B.Octets.of_list([250, 157, 176, 83])}, V.Raid6LostDataData{2n, 0n}) == Done{R.Raid6Stripe{[B.Octets.of_list([1, 2, 3, 4]), B.Octets.of_list([16, 32, 48, 64]), B.Octets.of_list([255, 254, 253, 252])], B.Octets.of_list([238, 220, 206, 184]), B.Octets.of_list([250, 157, 176, 83])}} : Result<&2, &2, V.Raid6Error, R.Raid6Stripe>}

law v_check_index:
  {V.Raid6.check(3n, V.Raid6LostDataP{3n}) == Some{V.Raid6BadIndex{3n}} : Maybe<&2, V.Raid6Error>}

law v_check_same:
  {V.Raid6.check(3n, V.Raid6LostDataData{1n, 1n}) == Some{V.Raid6SameIndex{1n}} : Maybe<&2, V.Raid6Error>}

law v_check_size:
  {V.Raid6.check(256n, V.Raid6LostQ{}) == Some{V.Raid6TooManyDisks{256n}} : Maybe<&2, V.Raid6Error>}
