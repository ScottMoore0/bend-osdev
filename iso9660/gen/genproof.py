#!/usr/bin/env python3
"""Writes ../PROOF.bend from proof.tmpl.bend (both beside this script).

The template is PROOF.bend with every 32-bit pattern written as {U32:x}:
this script expands each into U32{WCon{x0, WCon{x1, ... WCon{x31, WNil{}}}}},
the deep pattern that splits a U32 into its 32 bits (the proofs compute on
symbolic bits). Output is written with LF line endings.
"""
import os, re

here = os.path.dirname(os.path.abspath(__file__))

def u32(p):
    s = "WNil{}"
    for i in reversed(range(32)):
        s = "WCon{%s%d, %s}" % (p, i, s)
    return "U32{" + s + "}"

with open(os.path.join(here, "proof.tmpl.bend"), encoding="utf-8", newline="") as f:
    src = f.read()
out = re.sub(r"\{U32:(\w+)\}", lambda m: u32(m.group(1)), src)
with open(os.path.join(here, "..", "PROOF.bend"), "w", encoding="utf-8", newline="\n") as f:
    f.write(out)
