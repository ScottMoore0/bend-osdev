# Properties, for every input:
#   * Xorb.xor (zero padding) is commutative and associative, the empty
#     block is its identity, a block XORed with itself gives as many zero
#     bytes as it has, XORing in zeros no longer than a block leaves it as it
#     is, and the result is as long as the longer block;
#   * blocks of equal length can be XORed a piece at a time: the XOR of two
#     joined blocks is the join of the pieces' XORs (the streaming law);
#   * Xorb.xor_cut is commutative and associative, its result is as long as
#     the shorter block, and on blocks of equal length it is Xorb.xor;
#   * Xorb.into (xor_blocks) XORs the sources one at a time, and is the
#     destination XORed with the XOR of all the sources (Xorb.all);
#   * Xorb.xor_with picks the policy's XOR;
#   * the interface laws for dependents' proofs: the bytes of Xorb.xor and
#     Xorb.xor_cut are Xorb.xor_list and Xorb.xor_cut_list of the blocks'
#     bytes (each byte the XOR of the bytes at its offset).
# Vectors: small blocks of each length policy.
import Base
import ../bytes/bytes.bend as B
import ./xorblocks.bend as X

law xor_list:
  for +a: B.Octets
  for +b: B.Octets
  {B.Octets.to_list(X.Xorb.xor(a, b)) == X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)) : List<&2, U32>}

law xor_cut_list:
  for +a: B.Octets
  for +b: B.Octets
  {B.Octets.to_list(X.Xorb.xor_cut(a, b)) == X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)) : List<&2, U32>}

law xor_comm:
  for +a: B.Octets
  for +b: B.Octets
  {X.Xorb.xor(a, b) == X.Xorb.xor(b, a) : B.Octets}

law xor_assoc:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {X.Xorb.xor(X.Xorb.xor(a, b), c) == X.Xorb.xor(a, X.Xorb.xor(b, c)) : B.Octets}

law xor_empty:
  for +a: B.Octets
  {X.Xorb.xor(a, B.Octets.empty()) == a : B.Octets}

law xor_self:
  for +a: B.Octets
  {X.Xorb.xor(a, a) == B.Octets.zeros(B.Octets.len(a)) : B.Octets}

law xor_zeros:
  for +a: B.Octets
  for +n: Nat
  for le: {Nat.is_le(n, B.Octets.len(a)) == True{} : Bool}
  {X.Xorb.xor(a, B.Octets.zeros(n)) == a : B.Octets}

law xor_len:
  for +a: B.Octets
  for +b: B.Octets
  {B.Octets.len(X.Xorb.xor(a, b)) == Nat.max(B.Octets.len(a), B.Octets.len(b)) : Nat}

law xor_append:
  for +a1: B.Octets
  for +a2: B.Octets
  for +b1: B.Octets
  for +b2: B.Octets
  for same: {B.Octets.len(a1) == B.Octets.len(b1) : Nat}
  {X.Xorb.xor(B.Octets.append(a1, a2), B.Octets.append(b1, b2)) == B.Octets.append(X.Xorb.xor(a1, b1), X.Xorb.xor(a2, b2)) : B.Octets}

law xor_cut_comm:
  for +a: B.Octets
  for +b: B.Octets
  {X.Xorb.xor_cut(a, b) == X.Xorb.xor_cut(b, a) : B.Octets}

law xor_cut_assoc:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {X.Xorb.xor_cut(X.Xorb.xor_cut(a, b), c) == X.Xorb.xor_cut(a, X.Xorb.xor_cut(b, c)) : B.Octets}

law xor_cut_len:
  for +a: B.Octets
  for +b: B.Octets
  {B.Octets.len(X.Xorb.xor_cut(a, b)) == Nat.min(B.Octets.len(a), B.Octets.len(b)) : Nat}

law xor_cut_same:
  for +a: B.Octets
  for +b: B.Octets
  for same: {B.Octets.len(a) == B.Octets.len(b) : Nat}
  {X.Xorb.xor_cut(a, b) == X.Xorb.xor(a, b) : B.Octets}

law xor_with_longer:
  for +a: B.Octets
  for +b: B.Octets
  {X.Xorb.xor_with(X.XorbLonger{}, a, b) == X.Xorb.xor(a, b) : B.Octets}

law xor_with_shorter:
  for +a: B.Octets
  for +b: B.Octets
  {X.Xorb.xor_with(X.XorbShorter{}, a, b) == X.Xorb.xor_cut(a, b) : B.Octets}

law into_nil:
  for +d: B.Octets
  {X.Xorb.into(d, Nil{}) == d : B.Octets}

law into_cons:
  for +d: B.Octets
  for +s: B.Octets
  for r: List<&2, B.Octets>
  {X.Xorb.into(d, Con{s, r}) == X.Xorb.into(X.Xorb.xor(d, s), r) : B.Octets}

law into_all:
  for +d: B.Octets
  for +srcs: List<&2, B.Octets>
  {X.Xorb.into(d, srcs) == X.Xorb.xor(d, X.Xorb.all(srcs)) : B.Octets}

# Vectors

# 01 02 03 xor ff 0f = fe 0d 03 (padded) and fe 0d (cut)
law v_xor:
  {B.Octets.hex(X.Xorb.xor(B.Octets.of_list([1, 2, 3]), B.Octets.of_list([255, 15]))) == "fe0d03" : String}

law v_xor_cut:
  {B.Octets.hex(X.Xorb.xor_cut(B.Octets.of_list([1, 2, 3]), B.Octets.of_list([255, 15]))) == "fe0d" : String}

# xor_blocks of three sources into a destination
law v_into:
  {B.Octets.hex(X.Xorb.into(B.Octets.of_list([170, 85]), [B.Octets.of_list([1, 2]), B.Octets.of_list([4, 8]), B.Octets.of_list([16, 32])])) == "bf7f" : String}
