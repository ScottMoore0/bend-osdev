# The fill bounds of the B-tree (Maple32.balanced): every leaf at depth
# height, every node but the root holding from half of order + 1 to order
# items, the root at most order (and, if a branch, at least 2). Properties,
# for every tree, range, index and value type, for the U32 default:
#
# * the empty tree is balanced, and its order (Maple.order) is at least 3;
# * set_range, clear_range and erase keep the order, and keep a tree of
#   order at least 3 balanced;
# * the height bound: a balanced tree of height g + 1 holds at least
#   2 m^(g+1) entries, for every m with 2m <= order + 1.
#
# A tree's order is at least 3 when it is built by Maple32.empty or
# Maple32.empty_with (an order below 3 is taken as 3), and every operation
# keeps it, so the hypothesis holds for every tree the interface builds.
# (With an order below 3 the bounds cannot hold: a node of order 1 that
# overflows splits into two halves of one item, under a root of two slots,
# more than order.)
#
# Vectors: the order of the empty trees, the bounds through stores that
# split leaves and a clear that merges them, at order 3, and the height
# bound on the result (height 2, 9 entries, m = 2).
import Base
import ./node.bend as N
import ./maple.bend as T

law balanced_empty:
  for -V: Data
  {T.Maple32.balanced(V, T.Maple32.empty(V)) == True{} : Bool}

law balanced_empty_with:
  for -V: Data
  for +o: N.MapleOptions
  {T.Maple32.balanced(V, T.Maple32.empty_with(V, o)) == True{} : Bool}

law order_empty_with:
  for -V: Data
  for +o: N.MapleOptions
  {Nat.is_le(3n, T.Maple.order(U32, V, T.Maple32.empty_with(V, o))) == True{} : Bool}

law order_set_range:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  {T.Maple.order(U32, V, T.Maple32.set_range(V, t, a, b, v)) == T.Maple.order(U32, V, t) : Nat}

law order_clear_range:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  {T.Maple.order(U32, V, T.Maple32.clear_range(V, t, a, b)) == T.Maple.order(U32, V, t) : Nat}

law order_erase:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  {T.Maple.order(U32, V, T.Maple32.erase(V, t, i)) == T.Maple.order(U32, V, t) : Nat}

law balanced_set_range:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +v: V
  for +e: {T.Maple32.balanced(V, t) == True{} : Bool}
  for +f: {Nat.is_le(3n, T.Maple.order(U32, V, t)) == True{} : Bool}
  {T.Maple32.balanced(V, T.Maple32.set_range(V, t, a, b, v)) == True{} : Bool}

law balanced_clear_range:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +a: U32
  for +b: U32
  for +e: {T.Maple32.balanced(V, t) == True{} : Bool}
  for +f: {Nat.is_le(3n, T.Maple.order(U32, V, t)) == True{} : Bool}
  {T.Maple32.balanced(V, T.Maple32.clear_range(V, t, a, b)) == True{} : Bool}

law balanced_erase:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +i: U32
  for +e: {T.Maple32.balanced(V, t) == True{} : Bool}
  for +f: {Nat.is_le(3n, T.Maple.order(U32, V, t)) == True{} : Bool}
  {T.Maple32.balanced(V, T.Maple32.erase(V, t, i)) == True{} : Bool}

# the height bound: a balanced tree of height g + 1 holds at least
# 2 m^(g+1) entries, for every m with 2m <= order + 1 (so at least
# 2 half(order + 1)^height, and its height is at most log base
# half(order + 1) of half its size)
law size_bound:
  for -V: Data
  for +t: N.MapleTree<U32, V>
  for +m: Nat
  for +g: Nat
  for +e: {T.Maple32.balanced(V, t) == True{} : Bool}
  for +f: {Nat.is_le(Nat.double(m), 1n+T.Maple.order(U32, V, t)) == True{} : Bool}
  for +h: {T.Maple32.height(V, t) == 1n+g : Nat}
  {Nat.is_le(Nat.mul(2n, Nat.pow(m, 1n+g)), T.Maple32.size(V, t)) == True{} : Bool}

# Vectors

law example_order:
  {T.Maple.order(U32, U32, T.Maple32.empty(U32)) == 16n : Nat}

law example_order_small:
  {T.Maple.order(U32, U32, T.Maple32.empty_with(U32, N.MapleOptions{1n})) == 3n : Nat}

# ten ranges stored at order 3 (leaves split, height 2), then a clear
# across five of them (nodes merge): balanced throughout
law example_fill:
  {Bool.and(T.Maple32.balanced(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty_with(U32, N.MapleOptions{3n}), 80, 89, 8), 90, 99, 9), 0, 9, 0), 10, 19, 1), 20, 29, 2), 30, 39, 3), 40, 49, 4), 50, 59, 5), 60, 69, 6), 70, 79, 7)), T.Maple32.balanced(U32, T.Maple32.clear_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty_with(U32, N.MapleOptions{3n}), 80, 89, 8), 90, 99, 9), 0, 9, 0), 10, 19, 1), 20, 29, 2), 30, 39, 3), 40, 49, 4), 50, 59, 5), 60, 69, 6), 70, 79, 7), 25, 44))) == True{} : Bool}

# the cleared tree of example_fill has height 2 and 9 entries: with m = 2
# (2 * 2 <= 3 + 1), 2 * 2^2 <= 9
law example_size_bound:
  {Bool.and(Nat.is_eq(T.Maple32.height(U32, T.Maple32.clear_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty_with(U32, N.MapleOptions{3n}), 80, 89, 8), 90, 99, 9), 0, 9, 0), 10, 19, 1), 20, 29, 2), 30, 39, 3), 40, 49, 4), 50, 59, 5), 60, 69, 6), 70, 79, 7), 25, 44)), 2n), Bool.and(Nat.is_le(Nat.double(2n), 1n+T.Maple.order(U32, U32, T.Maple32.clear_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty_with(U32, N.MapleOptions{3n}), 80, 89, 8), 90, 99, 9), 0, 9, 0), 10, 19, 1), 20, 29, 2), 30, 39, 3), 40, 49, 4), 50, 59, 5), 60, 69, 6), 70, 79, 7), 25, 44))), Nat.is_le(Nat.mul(2n, Nat.pow(2n, 2n)), T.Maple32.size(U32, T.Maple32.clear_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty_with(U32, N.MapleOptions{3n}), 80, 89, 8), 90, 99, 9), 0, 9, 0), 10, 19, 1), 20, 29, 2), 30, 39, 3), 40, 49, 4), 50, 59, 5), 60, 69, 6), 70, 79, 7), 25, 44))))) == True{} : Bool}
