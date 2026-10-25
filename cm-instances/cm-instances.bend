# bend-osdev-cm-instances: cipher-modes' modes over each 128-bit block cipher
# of bend-osdev, with cipher-modes' round-trip laws written out per cipher
# (LAWS.bend, by gen/instances.py).
#
# Each cipher plugs into cipher-modes as its template arguments, unchanged:
#   SM4        ~LcSm4Key, ~LcSm4.encrypt, ~LcSm4.decrypt            (sm4/sm4.bend)
#   Camellia   ~LcCamelliaKey, ~LcCamellia.encrypt, ~LcCamellia.decrypt
#   Serpent    ~LcSerpentKey, ~LcSerpent.encrypt, ~LcSerpent.decrypt
#   Twofish    ~LcTwofishKey, ~LcTwofish.encrypt, ~LcTwofish.decrypt
#   ARIA       ~LcAriaKey, ~LcAria.encrypt, ~LcAria.decrypt
#   CAST-256   ~LcCast6Key, ~LcCast6.encrypt, ~LcCast6.decrypt
# for instance CB.Cbc.encrypt(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, k, iv, m)
# with CB = cipher-modes/cbc.bend. This package adds no code to them: its
# content is the laws, which hold of exactly those calls.
#
# The laws are in a package of their own because their proofs take in both
# cipher-modes' proofs and the ciphers' own (sm4, camellia, serpent, twofish,
# aria, cast6), and a package that imports the ciphers' proofs (crypto does)
# need not carry cipher-modes' too.
import Base
