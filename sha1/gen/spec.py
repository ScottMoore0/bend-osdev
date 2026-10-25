"""The tables of SHA-1's specification, as data, for the generators.

Each table is transcribed from the document cited beside it; gen/rounds.py
writes the Bend code from them, and ref/model.py's own implementation of
the algorithm reads the same tables (so a wrong table would show up only
in the specification's vectors, which ref/model.py checks first, not in the
differential test against it; hashlib checks SHA-1 independently of
these tables).
"""
# ------------------------------------------------------------------ SHA-1
# FIPS 180-4, sections 4.2.1 and 5.3.1
SHA1_IV = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
SHA1_K = [0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xCA62C1D6]
