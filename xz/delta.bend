# bend-osdev-xz: the delta filter's decoder ("The .xz File Format", 5.3.3).
#
# The encoder stores each byte less the byte `distance` places before it
# (modulo 256, with zeros before the start); the decoder adds it back. The
# distance is 1 to 256, and the filter's one properties byte is distance - 1.
# The decoder keeps the last 256 bytes it wrote, so it decodes in pieces.
import Base
import ../bytes/bytes.bend as B

# the last 256 bytes written (position i at i mod 256), the position, and the
# distance
type XzDelta is Type:
  XzDelta{hist: Array<U32>, pos: U32, dist: U32}

# what update answers: the decoder, and the decoded bytes
type XzDeltaOut is Type:
  XzDeltaOut{dec: XzDelta, out: B.Octets}

# a decoder for the distance dist (1 to 256)
def XzDelta.start(dist: U32) -> XzDelta:
  XzDelta{Array.new(U32, 8n, 0), 0, dist}

# r holds the history and the byte dist places before position pos
def XzDelta.go(xs: List<&2, U32>, r: Array<U32> & U32, +pos: U32, +dist: U32, acc: List<&2, U32>) -> XzDeltaOut:
  match xs:
    case Nil{}:
      (hist, v) = r
      XzDeltaOut{XzDelta{hist, pos, dist}, B.Octets.of_list(List.reverse(&2, U32, acc))}
    case Con{h, t}:
      (hist, +v) = r
      +b = U32.and(U32.add(h, v), 255)
      +next = U32.add(pos, 1)
      XzDelta.go(t, Array.get(U32, Array.set(U32, hist, pos, b), U32.sub(next, dist)), next, dist, Con{b, acc})

# the next piece of data
def XzDelta.update(d: XzDelta, o: B.Octets) -> XzDeltaOut:
  XzDelta{hist, +pos, +dist} = d
  XzDelta.go(B.Octets.to_list(o), Array.get(U32, hist, U32.sub(pos, dist)), pos, dist, Nil{})

def XzDelta.decode.fin(r: XzDeltaOut) -> B.Octets:
  XzDeltaOut{d, out} = r
  out

# one-shot: o decoded with the distance dist
def XzDelta.decode(dist: U32, o: B.Octets) -> B.Octets:
  XzDelta.decode.fin(XzDelta.update(XzDelta.start(dist), o))
