# Laws of bend-osdev-oid, for every Oid, text and octets:
#
# * der_round_trip: an Oid's DER octets decode to it;
# * der_canonical: an Oid decoded from octets encodes to those octets (DER
#   leaves no choice);
# * text_round_trip: a valid Oid's dotted text reads back as it, under any
#   text rules;
# * der_text_der: octets decoded to an Oid, written as text, read back and
#   encoded, are the same octets;
# * text_der_text: an Oid read from text, encoded and decoded, is the same
#   Oid (so it has the same text);
# * valid_of_der, valid_of_text: every Oid read is valid.
#
# Vectors: commonName (2.5.4.3) and basicConstraints (2.5.29.19) in DER
# and as text, and text refused.
import Base
import ../bytes/bytes.bend as B
import ./oid.bend as O
import ./text.bend as T

law der_round_trip:
  for +o: O.Oid
  for +b: B.Octets
  for +e: {O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}
  {O.Oid.of_der(b) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}

law der_canonical:
  for +b: B.Octets
  for +o: O.Oid
  for +e: {O.Oid.of_der(b) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}
  {O.Oid.to_der(o) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}

law text_round_trip:
  for +r: T.OidTextRules
  for +o: O.Oid
  for +hv: {O.Oid.valid(o) == True{} : Bool}
  {T.Oid.of_text(r, T.Oid.to_text(o)) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}

law valid_of_der:
  for +b: B.Octets
  for +o: O.Oid
  for +e: {O.Oid.of_der(b) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}
  {O.Oid.valid(o) == True{} : Bool}

law valid_of_text:
  for +r: T.OidTextRules
  for +s: String
  for +o: O.Oid
  for +e: {T.Oid.of_text(r, s) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}
  {O.Oid.valid(o) == True{} : Bool}

law der_text_der:
  for +r: T.OidTextRules
  for +b: B.Octets
  for +o: O.Oid
  for +e: {O.Oid.of_der(b) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}
  {Result.bind(&2, &2, O.OidError, O.Oid, B.Octets, T.Oid.of_text(r, T.Oid.to_text(o)), x => O.Oid.to_der(x)) == Done{b} : Result<&2, &2, O.OidError, B.Octets>}

law text_der_text:
  for +r: T.OidTextRules
  for +s: String
  for +o: O.Oid
  for +e: {T.Oid.of_text(r, s) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}
  {Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.Oid.to_der(o), x => O.Oid.of_der(x)) == Done{o} : Result<&2, &2, O.OidError, O.Oid>}

# Vectors (RFC 5280 Appendix A: id-at-commonName is {id-at 3}, id-at is
# 2.5.4; id-ce-basicConstraints is {id-ce 19}, id-ce is 2.5.29)

law vec_cn_der:
  {O.Oid.to_der(O.Oid{[2n, 5n, 4n, 3n]}) == Done{B.Octets.of_list([6, 3, 85, 4, 3])} : Result<&2, &2, O.OidError, B.Octets>}

law vec_cn_text:
  {T.Oid.to_text(O.Oid{[2n, 5n, 4n, 3n]}) == "2.5.4.3" : String}

law vec_bc_text:
  {T.Oid.of_text(T.Oid.text_rules(), "2.5.29.19") == Done{O.Oid{[2n, 5n, 29n, 19n]}} : Result<&2, &2, O.OidError, O.Oid>}

law vec_bad_text:
  {(T.Oid.of_text(T.Oid.text_rules(), "2.05.4"), T.Oid.of_text(T.Oid.text_rules(), "1.40"), T.Oid.of_text(T.Oid.text_rules(), "1..2")) == (Fail{O.OidBadText{}}, Fail{O.OidBadArcs{}}, Fail{O.OidBadText{}}) : Result<&2, &2, O.OidError, O.Oid> & Result<&2, &2, O.OidError, O.Oid> & Result<&2, &2, O.OidError, O.Oid>}
