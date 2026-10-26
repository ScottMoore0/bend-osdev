# The law that a resize finishes, for every key type K and value type V,
# every key encoding (~kenc), every hash function (~hash), every policy p
# and every trace tr, over the public interface only.
#
# A table built through the interface (RHash.replay: RHash.new, then any
# inserts, removes, migration steps and explicit resizes, in any order) is
# not resizing after RHash.drain: one migration step per old bucket
# empties the old array, whatever operations ran while the resize was
# under way. For an arbitrary table value this need not hold, and
# lookups do not depend on it (LAWS.bend; README.md, "Laws").
import Base
import ./rhash.bend as R

law drain_finishes:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +p: R.RhParams
  for +tr: List<&2, R.RhOp<K, V>>
  {R.RHash.resizing(~K, ~V, R.RHash.drain(~K, ~V, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, tr))) == False{} : Bool}
