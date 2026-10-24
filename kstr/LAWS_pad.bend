# bend-osdev-kstr's padding rules (format.bend), for every input: a field
# width w pads the unpadded form u (the same conversion and sign flags, no
# width) to max(w, len(u)) bytes (pad_len); left-justified, the first
# len(u) bytes are u (pad_left), with spaces after; right-justified with
# spaces, dropping the first w - len(u) bytes leaves u (pad_right). Proved
# in PROOF_pad.bend.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./format.bend as F

law pad_len:
  for +c: F.KConv
  for +w: Nat
  for +z: Bool
  for +l: Bool
  for +p: Bool
  for +s: Bool
  for +v: W.W64
  {B.Octets.len(F.KStr.format(F.KFmt{c, w, z, l, p, s}, v)) == Nat.max(w, B.Octets.len(F.KStr.format(F.KFmt{c, 0n, False{}, False{}, p, s}, v))) : Nat}

law pad_left:
  for +c: F.KConv
  for +w: Nat
  for +z: Bool
  for +p: Bool
  for +s: Bool
  for +v: W.W64
  {B.Octets.take(B.Octets.len(F.KStr.format(F.KFmt{c, 0n, False{}, False{}, p, s}, v)), F.KStr.format(F.KFmt{c, w, z, True{}, p, s}, v)) == F.KStr.format(F.KFmt{c, 0n, False{}, False{}, p, s}, v) : B.Octets}

law pad_right:
  for +c: F.KConv
  for +w: Nat
  for +p: Bool
  for +s: Bool
  for +v: W.W64
  {B.Octets.drop(Nat.sub(w, B.Octets.len(F.KStr.format(F.KFmt{c, 0n, False{}, False{}, p, s}, v))), F.KStr.format(F.KFmt{c, w, False{}, False{}, p, s}, v)) == F.KStr.format(F.KFmt{c, 0n, False{}, False{}, p, s}, v) : B.Octets}
