# bend-osdev-maple: the search for a free run of indices (mas_empty_area).
#
# empty_area(t, min, max, size) answers the lowest s such that the size
# indices s, s + 1, ..., s + size - 1 lie within [min, max] and none of them
# is stored. It fails with MapleBadSize for size 0, MapleBadRange if
# max < min, and MapleBusy when there is no such run.
#
# The search walks the entries in index order with a cursor, the lowest
# start not yet ruled out (min at first): an entry ending before the cursor
# changes nothing; the run [cur, cur + size - 1] fits before the next entry,
# or the cursor moves past that entry. A subtree whose pivot is below the
# cursor is skipped whole. The run's end is computed as cur + (size - 1),
# and accepted only if it did not wrap past the top of the index type.
import Base
import ./model.bend as M
import ./node.bend as N

def MapleGap.probe(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, n: N.MapleNode<K, V>, st: M.MapleGap<K>) -> Cmp:
  match st:
    case M.MapleGapScan{+cur}:
      N.MapleNode.probe(~K, ~cmp, V, n, cur)
    case M.MapleGapFound{s}:
      EQ{}
    case M.MapleGapBusy{}:
      EQ{}

# the search state after the entries of n, from st; c = MapleGap.probe(n, st)
def MapleGap.node(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~add: K -> K -> K, -V: Data, n: N.MapleNode<K, V>, st: M.MapleGap<K>, c: Cmp, +d: K, +max: K) -> M.MapleGap<K>:
  match n:
    case N.MapleLeaf{es}:
      M.MapleModel.gap_scan(~K, ~cmp, ~inc, ~add, V, es, st, d, max)
    case N.MapleNil{}:
      st
    case N.MapleSlot{p, +ch, +r}:
      match st:
        case M.MapleGapScan{+cur}:
          match c:
            case LT{}:
              MapleGap.node(~K, ~cmp, ~inc, ~add, V, r, M.MapleGapScan{cur}, N.MapleNode.probe(~K, ~cmp, V, r, cur), d, max)
            case o:
              +s = MapleGap.node(~K, ~cmp, ~inc, ~add, V, ch, M.MapleGapScan{cur}, N.MapleNode.probe(~K, ~cmp, V, ch, cur), d, max)
              MapleGap.node(~K, ~cmp, ~inc, ~add, V, r, s, MapleGap.probe(~K, ~cmp, V, r, s), d, max)
        case M.MapleGapFound{s}:
          M.MapleGapFound{s}
        case M.MapleGapBusy{}:
          M.MapleGapBusy{}

def Maple.empty_area.go(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, ~add: K -> K -> K, -V: Data, zero_size: Bool, inverted: Bool, +root: N.MapleNode<K, V>, +min: K, +max: K, +size: K) -> Result<&2, &2, M.MapleError<K>, K>:
  match zero_size:
    case True{}:
      Fail{M.MapleBadSize{}}
    case False{}:
      match inverted:
        case True{}:
          Fail{M.MapleBadRange{min, max}}
        case False{}:
          +d = dec(size)
          M.MapleModel.gap_end(~K, ~cmp, ~add, MapleGap.node(~K, ~cmp, ~inc, ~add, V, root, M.MapleGapScan{min}, N.MapleNode.probe(~K, ~cmp, V, root, min), d, max), d, max)

# the lowest s with [s, s + size - 1] free and within [min, max]
def Maple.empty_area(~K: Data, ~cmp: K -> K -> Cmp, ~inc: K -> K, ~dec: K -> K, ~add: K -> K -> K, ~zero: K, -V: Data, t: N.MapleTree<K, V>, +min: K, +max: K, +size: K) -> Result<&2, &2, M.MapleError<K>, K>:
  match t:
    case N.MapleTree{o, h, root}:
      Maple.empty_area.go(~K, ~cmp, ~inc, ~dec, ~add, V, Cmp.is_eq(cmp(size, zero)), M.MapleKey.lt(~K, ~cmp, max, min), root, min, max, size)

def Maple32.empty_area(-V: Data, t: N.MapleTree<U32, V>, +min: U32, +max: U32, +size: U32) -> Result<&2, &2, M.MapleError<U32>, U32>:
  Maple.empty_area(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, ~M.MapleKey32.add, ~0, V, t, min, max, size)
