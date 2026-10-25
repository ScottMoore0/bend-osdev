# bend-osdev-cm-instances: the 128-bit modes over each 128-bit block cipher
# of bend-osdev, with the modes' round-trip laws written out per cipher
# (LAWS.bend, by gen/instances.py).
#
# Each cipher plugs into the modes as their template arguments, unchanged:
#   SM4        ~LcSm4Key, ~LcSm4.encrypt, ~LcSm4.decrypt            (sm4/sm4.bend)
#   Camellia   ~LcCamelliaKey, ~LcCamellia.encrypt, ~LcCamellia.decrypt
#   Serpent    ~LcSerpentKey, ~LcSerpent.encrypt, ~LcSerpent.decrypt
#   Twofish    ~LcTwofishKey, ~LcTwofish.encrypt, ~LcTwofish.decrypt
#   ARIA       ~LcAriaKey, ~LcAria.encrypt, ~LcAria.decrypt
#   CAST-256   ~LcCast6Key, ~LcCast6.encrypt, ~LcCast6.decrypt
# for instance CB.Cbc.encrypt(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, k, iv, m)
# with CB = cbc/cbc.bend. This package adds no code to them: its
# content is the laws, which hold of exactly those calls.
#
# The laws are in a package of their own because their proofs take in both
# the modes' proofs and the ciphers' own (sm4, camellia, serpent, twofish,
# aria, cast6), and a package that imports the ciphers' proofs (crypto does)
# need not carry the modes' too.
import Base
