#!/usr/bin/env python3
"""Writes partition/PROOF.bend from LAWS.bend and parts.py. Run from
anywhere: python3 partition/gen/genproof.py."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
import re, sys
LAWS = open(os.path.join(PKG, "LAWS.bend"), encoding="utf-8").read()
L = []
def w(s=""): L.append(s)
def bits(p, n=32):
    s = "WNil{}"
    for i in reversed(range(n)): s = "WCon{%s%d, %s}" % (p, i, s)
    return s
def u32(p): return "U32{%s}" % bits(p)
w("import Base")
w("import ../word64/word64.bend as W")
w("import ../bytes/bytes.bend as B")
w("import ../crc/crc.bend as C")
w("import ../uuid/uuid.bend as U")
w("import ./mbr.bend as M")
w("import ./gpt.bend as G")
w("import ./partition.bend as P")
w("import ../word64/LAWS.bend as WL")
w("import ../word64/PROOF.bend as WP")
w("import ../uuid/LAWS.bend as UL")
w("import ../uuid/PROOF.bend as UP")
w("import ../bytes/LAWS.bend as BL")
w("import ../bytes/PROOF.bend as BP")
w("import ./LAWS.bend as Laws")
w()
# the proofs of the properties (parts.py), then the vectors
exec(open(os.path.join(HERE, "parts.py"), encoding="utf-8").read())
vecs = re.findall(r"^law (\w+):\n  \{", LAWS, re.M)
for l in vecs:
    w("def Laws.%s():" % l)
    w("  {==}")
    w()
open(os.path.join(PKG, "PROOF.bend"), "w", encoding="utf-8", newline="\n").write("\n".join(L).rstrip() + "\n")
