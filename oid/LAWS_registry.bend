# The registry's contents (registry.bend), for every position in it:
#
# * registry_size: it has 127 entries;
# * names_unique, arcs_unique: two entries at different positions have
#   different names and different arcs;
# * lookup_found, name_found: each entry is found again by its Oid (its
#   arcs), with its name;
# * named_found: each entry's name gives back its Oid.
#
# Positions are those of List.get on Oid.registry(); "different" is
# String.eq and Oid.is_eq answering False.
import Base
import ./oid.bend as O
import ./registry.bend as R

law registry_size:
  {List.length(&2, R.OidEntry, R.Oid.registry()) == 127n : Nat}

law names_unique:
  for +i: Nat
  for +j: Nat
  for e1: R.OidEntry
  for e2: R.OidEntry
  for h1: {List.get(&2, R.OidEntry, R.Oid.registry(), i) == Some{e1} : Maybe<&2, R.OidEntry>}
  for h2: {List.get(&2, R.OidEntry, R.Oid.registry(), j) == Some{e2} : Maybe<&2, R.OidEntry>}
  for h3: {Nat.is_lt(i, j) == True{} : Bool}
  {String.eq(R.OidEntry.name(e1), R.OidEntry.name(e2)) == False{} : Bool}

law arcs_unique:
  for +i: Nat
  for +j: Nat
  for e1: R.OidEntry
  for e2: R.OidEntry
  for h1: {List.get(&2, R.OidEntry, R.Oid.registry(), i) == Some{e1} : Maybe<&2, R.OidEntry>}
  for h2: {List.get(&2, R.OidEntry, R.Oid.registry(), j) == Some{e2} : Maybe<&2, R.OidEntry>}
  for h3: {Nat.is_lt(i, j) == True{} : Bool}
  {O.Oid.is_eq(O.Oid{R.OidEntry.arcs(e1)}, O.Oid{R.OidEntry.arcs(e2)}) == False{} : Bool}

law lookup_found:
  for i: Nat
  for +e: R.OidEntry
  for h: {List.get(&2, R.OidEntry, R.Oid.registry(), i) == Some{e} : Maybe<&2, R.OidEntry>}
  {R.Oid.lookup(O.Oid{R.OidEntry.arcs(e)}) == Some{e} : Maybe<&2, R.OidEntry>}

law name_found:
  for i: Nat
  for +e: R.OidEntry
  for h: {List.get(&2, R.OidEntry, R.Oid.registry(), i) == Some{e} : Maybe<&2, R.OidEntry>}
  {R.Oid.name(O.Oid{R.OidEntry.arcs(e)}) == Some{R.OidEntry.name(e)} : Maybe<&2, String>}

law named_found:
  for i: Nat
  for +e: R.OidEntry
  for h: {List.get(&2, R.OidEntry, R.Oid.registry(), i) == Some{e} : Maybe<&2, R.OidEntry>}
  {R.Oid.named(R.OidEntry.name(e)) == Some{O.Oid{R.OidEntry.arcs(e)}} : Maybe<&2, O.Oid>}
