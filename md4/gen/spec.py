"""The tables of MD4's specification, as data, for the generators.

Each table is transcribed from the document cited beside it; gen/rounds.py
writes the Bend code from them, and ref/model.py's own implementation of
the algorithm reads the same tables (so a wrong table would show up only
in the specification's vectors, which ref/model.py checks first, not in the
differential test against it).
"""
# ------------------------------------------------------------------ MD4
# RFC 1320, section 3.4: the three rounds' shifts, word orders and constants
MD4_IV = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476]
MD4_S = [[3, 7, 11, 19], [3, 5, 9, 13], [3, 9, 11, 15]]
MD4_X = [list(range(16)),
         [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15],
         [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]]
MD4_K = [0, 0x5A827999, 0x6ED9EBA1]
