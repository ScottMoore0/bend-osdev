"""The tables of MD5's specification, as data, for the generators.

Each table is transcribed from the document cited beside it; gen/rounds.py
writes the Bend code from them, and ref/model.py's own implementation of
the algorithm reads the same tables (so a wrong table would show up only
in the specification's vectors, which ref/model.py checks first, not in the
differential test against it; hashlib checks MD5 independently of
these tables).
"""
import math

M32 = 0xFFFFFFFF

# ------------------------------------------------------------------ MD5
# RFC 1321, section 3.4: T[i] = floor(4294967296 * abs(sin(i))), the shifts
# and the word order k of each step
MD5_IV = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476]  # section 3.3 (MD4's, RFC 1320)
MD5_T = [int(4294967296 * abs(math.sin(i))) & M32 for i in range(1, 65)]
assert MD5_T[0] == 0xD76AA478 and MD5_T[63] == 0xEB86D391
MD5_S = [[7, 12, 17, 22], [5, 9, 14, 20], [4, 11, 16, 23], [6, 10, 15, 21]]
MD5_X = [[i for i in range(16)],
         [(1 + 5 * i) % 16 for i in range(16)],
         [(5 + 3 * i) % 16 for i in range(16)],
         [(7 * i) % 16 for i in range(16)]]
