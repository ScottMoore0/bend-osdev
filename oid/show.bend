# bend-osdev-oid, an Oid for people: its registered name, or else its
# dotted text.
import Base
import ./oid.bend as O
import ./text.bend as T
import ./registry.bend as R

def oid.show.pick(m: Maybe<&2, String>, +o: O.Oid) -> String:
  match m:
    case Some{n}:
      n
    case None{}:
      T.Oid.to_text(o)

def Oid.show(+o: O.Oid) -> String:
  oid.show.pick(R.Oid.name(o), o)
