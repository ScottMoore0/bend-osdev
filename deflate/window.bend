# bend-osdev-deflate: the inflater's window, the last 32768 bytes of output.
#
# RFC 1951, section 2: a match may refer to "a duplicated string occurring
# in a previous block, up to 32K input bytes before"; the distance codes
# (3.2.5) reach at most 32768 back. The window holds that many bytes, keyed
# by their position modulo 32768, in a 15-level trie (table.bend), so a
# match costs a few steps per byte however far back it reads.
#
# count is how many bytes are behind the next one, up to 32768: a distance
# above it reaches before the start of the output (and of the dictionary).
import Base
import ./table.bend as T

type DflWin is Data:
  DflWin{tab: T.DflTab, pos: U32, count: U32}

def win.empty() -> DflWin:
  DflWin{T.DflTNil{}, 0, 0}

def win.bump(full: Bool, c: U32) -> U32:
  match full:
    case True{}:
      c
    case False{}:
      U32.add(c, 1)

# the window after one more byte
def win.put(w: DflWin, v: U32) -> DflWin:
  match w:
    case DflWin{tab, +pos, +count}:
      DflWin{T.tab.set15(pos, tab, v), U32.add(pos, 1), win.bump(U32.is_le(32768, count), count)}

# the byte d back (d from 1 to the count)
def win.get(w: DflWin, d: U32) -> U32:
  match w:
    case DflWin{tab, pos, count}:
      T.tab.get15(U32.sub(pos, d), tab)

# how many bytes a distance may reach back (at most 32768)
def win.count(w: DflWin) -> U32:
  match w:
    case DflWin{tab, pos, count}:
      count

# the window after the bytes xs, in order
def win.push(xs: List<&2, U32>, w: DflWin) -> DflWin:
  match xs:
    case Nil{}:
      w
    case Con{h, t}:
      win.push(t, win.put(w, h))

# the window holding a preset dictionary (RFC 1950, 2.2: FDICT; only its
# last 32768 bytes can be reached)
def win.of(xs: List<&2, U32>) -> DflWin:
  win.push(xs, win.empty())
