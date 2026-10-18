# bend-osdev-lzo, the decoder's window: random access to the last 65536
# bytes of output.
#
# An LZO1X match reads back at most 49151 bytes (the largest M4 distance).
# The decoder keeps its recent output in this window as well as in its output
# list, so a match costs a few steps per byte however far back it reads: a
# binary trie keyed by a byte's position modulo 65536 (the low 16 bits of the
# position, low bit first). Its depth is 16, whatever the input.
#
# Nothing in the package's laws depends on what the window answers (they
# follow lengths, literals and failures, not the bytes a match copies), so
# any structure that answers the byte at a distance can replace this one.
import Base

type LzoTree is Data:
  LzoTNil{}
  LzoTLeaf{v: U32}
  LzoTNode{lo: LzoTree, hi: LzoTree}

# the byte with key k (m bits of it left to walk), 0 if there is none
def win.tget(m: Nat, n: Nat, k: Word(Nat.add(m, n)), t: LzoTree) -> U32:
  match m:
    case 0n:
      match t:
        case LzoTLeaf{v}:
          v
        case _:
          0
    case 1n+p:
      match k:
        case WCon{b, r}:
          match b:
            case True{}:
              match t:
                case LzoTNode{lo, hi}:
                  win.tget(p, n, r, hi)
                case _:
                  0
            case False{}:
              match t:
                case LzoTNode{lo, hi}:
                  win.tget(p, n, r, lo)
                case _:
                  0

# the trie with v at key k
def win.tset(m: Nat, n: Nat, k: Word(Nat.add(m, n)), t: LzoTree, v: U32) -> LzoTree:
  match m:
    case 0n:
      LzoTLeaf{v}
    case 1n+p:
      match k:
        case WCon{b, r}:
          match b:
            case True{}:
              match t:
                case LzoTNode{lo, hi}:
                  LzoTNode{lo, win.tset(p, n, r, hi, v)}
                case _:
                  LzoTNode{LzoTNil{}, win.tset(p, n, r, LzoTNil{}, v)}
            case False{}:
              match t:
                case LzoTNode{lo, hi}:
                  LzoTNode{win.tset(p, n, r, lo, v), hi}
                case _:
                  LzoTNode{win.tset(p, n, r, LzoTNil{}, v), LzoTNil{}}

# the trie's 16 levels: the low 16 bits of the position, low bit first
def win.at(i: U32, t: LzoTree) -> U32:
  match i:
    case U32{w}:
      win.tget(16n, 16n, w, t)

def win.store(i: U32, t: LzoTree, v: U32) -> LzoTree:
  match i:
    case U32{w}:
      win.tset(16n, 16n, w, t, v)

# tree: the bytes by position; pos: the next byte's position (mod 2^32);
# count: how many bytes have been written
type LzoWin is Data:
  LzoWin{tree: LzoTree, pos: U32, count: Nat}

# The public interface of this file (the decoder's, and a replacement's)

# no bytes yet
def win.empty() -> LzoWin:
  LzoWin{LzoTNil{}, 0, 0n}

# the window after one more byte
def win.put(w: LzoWin, v: U32) -> LzoWin:
  match w:
    case LzoWin{tree, +pos, count}:
      LzoWin{win.store(pos, tree, v), U32.add(pos, 1), 1n+count}

# the byte o + 1 back (o below 65536)
def win.get(w: LzoWin, o: Nat) -> U32:
  match w:
    case LzoWin{tree, pos, count}:
      win.at(U32.sub(pos, U32.add(U32.from_nat(o), 1)), tree)

# how many bytes have been written
def win.count(w: LzoWin) -> Nat:
  match w:
    case LzoWin{tree, pos, count}:
      count
