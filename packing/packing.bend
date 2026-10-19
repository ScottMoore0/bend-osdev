# bend-osdev-packing: bit fields at any bit positions of a byte buffer,
# packed and unpacked, the counterpart of Linux's lib/packing (packing(),
# pack(), unpack()).
#
# A field is given by its first and last bit, start >= end, numbered from
# bit 0 of the buffer as view.bend lays the buffer out under the quirks (a
# parameter, PkQuirks; packing.quirks_none() is the plain big-endian layout).
# The field's value is a W64, so a field is at most 64 bits wide; bit end of
# the buffer is bit 0 of the value.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./view.bend as V
import ./field.bend as F

type PkError is Data:
  PkBadRange{}
  PkTooWide{}
  PkOutOfBuffer{}
  PkBadLength{}
  PkOverflow{}

# the width of the field from end to start
def packing.width(+start: Nat, end: Nat) -> Nat:
  Nat.sub(1n+start, end)

def packing.check.len(bad: Bool) -> Maybe<&2, PkError>:
  match bad:
    case True{}:
      Some{PkBadLength{}}
    case False{}:
      None{}

def packing.check.buf(bad: Bool, +q: V.PkQuirks, +l: Nat) -> Maybe<&2, PkError>:
  match bad:
    case True{}:
      Some{PkOutOfBuffer{}}
    case False{}:
      packing.check.len(Bool.and(V.packing.wordwise(q), Bool.not(Nat.is_eq(Nat.mod(l, 4n), 0n))))

def packing.check.wide(bad: Bool, +q: V.PkQuirks, +l: Nat, +start: Nat) -> Maybe<&2, PkError>:
  match bad:
    case True{}:
      Some{PkTooWide{}}
    case False{}:
      packing.check.buf(Nat.is_le(Nat.mul(l, 8n), start), q, l)

def packing.check.range(bad: Bool, +q: V.PkQuirks, +l: Nat, +start: Nat, +end: Nat) -> Maybe<&2, PkError>:
  match bad:
    case True{}:
      Some{PkBadRange{}}
    case False{}:
      packing.check.wide(Nat.is_lt(64n, packing.width(start, end)), q, l, start)

# why a field cannot be used on a buffer of l bytes, if it cannot:
# PkBadRange (start < end), PkTooWide (more than 64 bits), PkOutOfBuffer
# (start past the buffer's last bit), PkBadLength (a wordwise quirk on a
# buffer whose length is not a multiple of 4)
def packing.check(+q: V.PkQuirks, +l: Nat, +start: Nat, +end: Nat) -> Maybe<&2, PkError>:
  packing.check.range(Nat.is_lt(start, end), q, l, start, end)

def packing.unpack.go(m: Maybe<&2, PkError>, +q: V.PkQuirks, xs: List<&2, U32>, +end: Nat, +w: Nat) -> Result<&2, &2, PkError, W.W64>:
  match m:
    case None{}:
      Done{F.packing.bits_w64(F.packing.slice(V.packing.view(q, xs), end, w))}
    case Some{e}:
      Fail{e}

# the field from bit end to bit start of buf (unpack)
def packing.unpack(+q: V.PkQuirks, buf: B.Octets, +start: Nat, +end: Nat) -> Result<&2, &2, PkError, W.W64>:
  +xs = B.Octets.to_list(buf)
  packing.unpack.go(packing.check(q, List.length(&2, U32, xs), start, end), q, xs, end, packing.width(start, end))

# buf with the field from bit end to bit start set to v's low w bits
def packing.put(+q: V.PkQuirks, xs: List<&2, U32>, +end: Nat, +w: Nat, +v: W.W64) -> B.Octets:
  B.Octets.of_list(V.packing.unview(q, F.packing.splice(V.packing.view(q, xs), end, List.take(&2, Bool, F.packing.w64_bits(v), w))))

def packing.pack.go(m: Maybe<&2, PkError>, ok: Bool, +q: V.PkQuirks, xs: List<&2, U32>, +end: Nat, +w: Nat, +v: W.W64) -> Result<&2, &2, PkError, B.Octets>:
  match m ok:
    case None{} True{}:
      Done{packing.put(q, xs, end, w, v)}
    case None{} False{}:
      Fail{PkOverflow{}}
    case Some{e} _:
      Fail{e}

# buf with the field from bit end to bit start set to v; PkOverflow if v
# does not fit in the field (pack)
def packing.pack(+q: V.PkQuirks, buf: B.Octets, +start: Nat, +end: Nat, +v: W.W64) -> Result<&2, &2, PkError, B.Octets>:
  +xs = B.Octets.to_list(buf)
  +w = packing.width(start, end)
  packing.pack.go(packing.check(q, List.length(&2, U32, xs), start, end), F.packing.fits(v, w), q, xs, end, w, v)

# the same, with v cut to the field's width instead of refused
def packing.pack_masked(+q: V.PkQuirks, buf: B.Octets, +start: Nat, +end: Nat, +v: W.W64) -> Result<&2, &2, PkError, B.Octets>:
  +xs = B.Octets.to_list(buf)
  packing.pack.go(packing.check(q, List.length(&2, U32, xs), start, end), True{}, q, xs, end, packing.width(start, end), v)

# bit k of buf, as the quirks number the bits (False past the end)
def packing.bit(+q: V.PkQuirks, buf: B.Octets, k: Nat) -> Bool:
  F.packing.nth(V.packing.view(q, B.Octets.to_list(buf)), k)
