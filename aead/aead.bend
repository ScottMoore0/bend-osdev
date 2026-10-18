# bend-osdev-aead: authenticated encryption with associated data, as
# instances of bend-osdev-crypto's AEAD interface (crypto/aead.bend, the
# shape of RFC 5116): AEGIS-128 (aegis128.bend), encrypt-then-MAC over any
# cipher and any MAC (authenc.bend), and the IV generators ESSIV
# (essiv.bend), seqiv (seqiv.bend) and echainiv (echainiv.bend), which turn
# one AEAD (or, for ESSIV, one cipher with an IV) into another.
#
# This file holds what they share: a ciphertext with its tag appended, and
# split again. Bend imports do not re-export: import the files you use.
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr

# A ciphertext and its tag, split from the bytes of both (the tag the last
# tlen bytes; CrTooShort for fewer than tlen bytes)
type AdSplit is Data:
  AdSplit{c: B.Octets, t: B.Octets}

def ad.split.pick(short: Bool, +tlen: Nat, +o: B.Octets) -> Result<&2, &2, Cr.CrError, AdSplit>:
  match short:
    case True{}:
      Fail{Cr.CrTooShort{B.Octets.len(o)}}
    case False{}:
      +n = Nat.sub(B.Octets.len(o), tlen)
      Done{AdSplit{B.Octets.take(n, o), B.Octets.drop(n, o)}}

def AdTag.split(+tlen: Nat, +o: B.Octets) -> Result<&2, &2, Cr.CrError, AdSplit>:
  ad.split.pick(Nat.is_lt(B.Octets.len(o), tlen), tlen, o)

# the ciphertext with its tag appended
def AdTag.join(c: B.Octets, t: B.Octets) -> B.Octets:
  B.Octets.append(c, t)

# Whether two tags are equal, every byte compared (no early exit)
def AdTag.is_eq(a: B.Octets, b: B.Octets) -> Bool:
  B.Octets.is_eq(a, b)
