"""The tables of SM3's specification, as data, for the generators.

Each table is transcribed from the document cited beside it; gen/rounds.py
writes the Bend code from them, and ref/model.py's own implementation of
the algorithm reads the same tables (so a wrong table would show up only
in the specification's vectors, which ref/model.py checks first, not in the
differential test against it; hashlib checks SM3 independently of
these tables).
"""
# ------------------------------------------------------------------ SM3
# GB/T 32905-2016 (draft-shen-sm3-hash, sections 3.1 to 3.3): IV and T_j
SM3_IV = [0x7380166F, 0x4914B2B9, 0x172442D7, 0xDA8A0600, 0xA96F30BC, 0x163138AA, 0xE38DEE4D, 0xB0FB0E4E]
SM3_T = [0x79CC4519] * 16 + [0x7A879D8A] * 48
