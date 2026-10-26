# The registry's entries are valid Oids (oid.bend's Oid.valid), for every
# position in it whose entry's arcs are all below 10000 (86 of the 127):
#
# * entries_valid: the entry at a position (List.get on Oid.registry()),
#   when each of its arcs is below 10000, is a valid Oid.
#
# oidlaw.below(arcs, b) is whether each of arcs is below b.
import Base
import ./oid.bend as O
import ./registry.bend as R

def oidlaw.below(arcs: List<&2, Nat>, +b: Nat) -> Bool:
  match arcs:
    case Nil{}:
      True{}
    case Con{a, t}:
      Bool.and(Nat.is_lt(a, b), oidlaw.below(t, b))

law entries_valid:
  for i: Nat
  for +e: R.OidEntry
  for h: {List.get(&2, R.OidEntry, R.Oid.registry(), i) == Some{e} : Maybe<&2, R.OidEntry>}
  for hb: {oidlaw.below(R.OidEntry.arcs(e), 10000n) == True{} : Bool}
  {O.Oid.valid(O.Oid{R.OidEntry.arcs(e)}) == True{} : Bool}
