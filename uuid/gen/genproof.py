#!/usr/bin/env python3
"""Writes uuid/PROOF.bend (run from anywhere: python3 uuid/gen/genproof.py)."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
import itertools
def w8(p):
    s = "WNil{}"
    for i in reversed(range(8)): s = "WCon{%s%d, %s}" % (p, i, s)
    return s
P = "U.Uuid{" + ", ".join(w8("x%s_" % chr(97+k)) for k in range(16)) + "}"
L = []
def w(s=""): L.append(s)
w("import Base")
w("import ../word64/word64.bend as W")
w("import ../bytes/bytes.bend as B")
w("import ./uuid.bend as U")
w("import ../bytes/LAWS.bend as BL")
w("import ../bytes/PROOF.bend as BP")
w("import ./LAWS.bend as Laws")
w()
w("# Converting a list to Octets and back masks each element: bytes' interface")
w("# law octets_to_of, so nothing here depends on how Octets stores its bytes.")
w("def octets_list(xs: List<&2, U32>) -> {B.mask(xs) == B.Octets.to_list(B.Octets.of_list(xs)) : List<&2, U32>}:")
w("  Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs))")
w()
w("# The text round trips. show writes two hex digits per octet; parse reads them")
w("# back two at a time. A nibble's digit reads back as the nibble (16 cases), so")
w("# an octet's two digits read back as the octet, and so, by induction, does a")
w("# list of octets. The dashes are concrete in show's output, so the rest is")
w("# computation.")
w()
for name, f in [("nib", "U.Uuid.hexval(U.Uuid.hexdigit(n))"), ("nib_upper", "U.Uuid.hexval(Char.to_upper(U.Uuid.hexdigit(n)))")]:
    w("def %s(n: Word(4n)) -> {Some{n} == %s : Maybe<&2, Word(4n)>}:" % (name, f))
    w("  match n:")
    for bits in itertools.product(["False{}", "True{}"], repeat=4):
        w("    case WCon{%s, WCon{%s, WCon{%s, WCon{%s, WNil{}}}}}:" % bits)
        w("      {==}")
    w()
w("# the upper-case digits of a list of octets")
w("def udigits(bs: List<&2, Word(8n)>) -> List<&2, Char>:")
w("  match bs:")
w("    case Nil{}:")
w("      Nil{}")
w("    case Con{+b, t}:")
w("      Con{Char.to_upper(U.Uuid.hexdigit(U.Uuid.nibble.hi(b))), Con{Char.to_upper(U.Uuid.hexdigit(U.Uuid.nibble.lo(b))), udigits(t)}}")
w()
HI = "WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}"
LO = "WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}}"
BY = "WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}}}}}"
PB = "WCon{+x0, WCon{+x1, WCon{+x2, WCon{+x3, WCon{+x4, WCon{+x5, WCon{+x6, WCon{+x7, WNil{}}}}}}}}}"
for name, nib, dig in [("rd", "nib", "U.Uuid.hexdigit(%s)"), ("rd_upper", "nib_upper", "Char.to_upper(U.Uuid.hexdigit(%s))")]:
    w("def %s(b: Word(8n)) -> {Some{b} == U.Uuid.rdbyte(%s, %s) : Maybe<&2, Word(8n)>}:" % (name, dig % "U.Uuid.nibble.hi(b)", dig % "U.Uuid.nibble.lo(b)"))
    w("  match b:")
    w("    case %s:" % PB)
    w("      %%%s(%s) : {Some{%s} == U.Uuid.hexval.join(_, U.Uuid.hexval(%s)) : Maybe<&2, Word(8n)>}" % (nib, HI, BY, dig % LO))
    w("      %%%s(%s) : {Some{%s} == U.Uuid.hexval.join(Some{%s}, _) : Maybe<&2, Word(8n)>}" % (nib, LO, BY, HI))
    w("      {==}")
    w()
for name, rd, dg in [("hexlist_digits", "rd", "U.Uuid.digits"), ("hexlist_udigits", "rd_upper", "udigits")]:
    T = "Maybe<&2, List<&2, Word(8n)>>"
    w("def %s(bs: List<&2, Word(8n)>) -> {Some{bs} == U.Uuid.hexlist(%s(bs)) : %s}:" % (name, dg, T))
    w("  match bs:")
    w("    case Nil{}:")
    w("      {==}")
    w("    case Con{+b, +t}:")
    w("      %%%s(b) : {Some{Con{b, t}} == U.Uuid.cons_m(_, U.Uuid.hexlist(%s(t))) : %s}" % (rd, dg, T))
    w("      %%%s(t) : {Some{Con{b, t}} == U.Uuid.cons_m(Some{b}, _) : %s}" % (name, T))
    w("      {==}")
    w()
F = ", ".join("+b%d" % i for i in range(16))
F2 = ", ".join("b%d" % i for i in range(16))
R = "Result<&2, &2, U.UuidError, U.Uuid>"
for law, enc, dec in [("bytes_round_trip", "U.Uuid.to_list", "U.Uuid.of_list"), ("guid_round_trip", "U.Uuid.guid_list", "U.Uuid.of_guid_list")]:
    w("def Laws.%s(u):" % law)
    w("  match u:")
    w("    case %s:" % P)
    w("      %%octets_list(%s(%s)) : {U.Uuid.length_ok(%s(_)) == Done{%s} : %s}" % (enc, P, dec, P, R))
    w("      {==}")
    w()
w("def Laws.guid_list_round_trip(u):")
w("  match u:")
w("    case %s:" % P)
w("      {==}")
w()
w("def Laws.make_bytes(u):")
w("  match u:")
w("    case %s:" % P)
w("      {==}")
w()
A = "[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]"
A2 = "[a3, a2, a1, a0, a5, a4, a7, a6, a8, a9, a10, a11, a12, a13, a14, a15]"
w("def Laws.guid_layout(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15):")
w("  %%octets_list(%s) : {U.Uuid.length_ok(U.Uuid.of_guid_list(_)) == U.Uuid.length_ok(U.Uuid.of_list(B.Octets.to_list(B.Octets.of_list(%s)))) : %s}" % (A, A2, R))
w("  %%octets_list(%s) : {U.Uuid.length_ok(U.Uuid.of_guid_list(B.mask(%s))) == U.Uuid.length_ok(U.Uuid.of_list(_)) : %s}" % (A2, A, R))
w("  {==}")
w()
for name, lem in [("text_round_trip", "hexlist_digits"), ("text_upper_round_trip", "hexlist_udigits")]:
    w("def Laws.%s(u):" % name)
    w("  match u:")
    w("    case U.Uuid{%s}:" % F)
    w("      %%%s([%s]) : {U.Uuid.of_digits(_) == Done{U.Uuid{%s}} : Result<&2, &2, U.UuidError, U.Uuid>}" % (lem, F2, F2))
    w("      {==}")
    w()
w("def Laws.text_length(u):")
w("  match u:")
w("    case U.Uuid{%s}:" % F2)
w("      {==}")
w()
import re
laws = re.findall(r"^law (\w+):\n  \{", open(os.path.join(PKG, "LAWS.bend"), encoding="utf-8").read(), re.M)
for l in laws:
    w("def Laws.%s():" % l)
    w("  {==}")
    w()
open(os.path.join(PKG, "PROOF.bend"), "w", encoding="utf-8", newline="\n").write("\n".join(L).rstrip() + "\n")
