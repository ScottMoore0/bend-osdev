# bend-osdev-c842, the window: random access to the last 4096 bytes of a
# byte stream, by absolute position.
#
# 842's pointers read the 2 KB histories the paper describes (Blaner et
# al. 2013): an index names a position in a ring of 2048 bytes (P8, P4) or
# 512 bytes (P2). The position a pointer reads lies at most 2055 bytes back,
# since it is taken below the output length rounded down to 8
# (ref/OBSERVATIONS.md, E6). So a window over the last 4096 bytes answers
# every pointer. The decoder keeps its output here as well as in its output
# list, and the matcher keeps the input it has passed.
#
# The window is a binary trie keyed by the low 12 bits of a byte's position,
# low bit first, so every access takes 12 steps whatever the stream's
# length. Nothing in the package's laws depends on what the window answers
# (they follow literals, lengths and failures), so any structure that answers
# the byte at a position can replace this one behind the three defs at the
# end.
import Base

type C842Tree is Data:
  C842TNil{}
  C842TLeaf{v: U32}
  C842TNode{lo: C842Tree, hi: C842Tree}

# the byte with key k (m bits of it left to walk), 0 if there is none
def c842.win.tget(m: Nat, n: Nat, k: Word(Nat.add(m, n)), t: C842Tree) -> U32:
  match m:
    case 0n:
      match t:
        case C842TLeaf{v}:
          v
        case _:
          0
    case 1n+p:
      match k:
        case WCon{b, r}:
          match b:
            case True{}:
              match t:
                case C842TNode{lo, hi}:
                  c842.win.tget(p, n, r, hi)
                case _:
                  0
            case False{}:
              match t:
                case C842TNode{lo, hi}:
                  c842.win.tget(p, n, r, lo)
                case _:
                  0

# the trie with v at key k
def c842.win.tset(m: Nat, n: Nat, k: Word(Nat.add(m, n)), t: C842Tree, v: U32) -> C842Tree:
  match m:
    case 0n:
      C842TLeaf{v}
    case 1n+p:
      match k:
        case WCon{b, r}:
          match b:
            case True{}:
              match t:
                case C842TNode{lo, hi}:
                  C842TNode{lo, c842.win.tset(p, n, r, hi, v)}
                case _:
                  C842TNode{C842TNil{}, c842.win.tset(p, n, r, C842TNil{}, v)}
            case False{}:
              match t:
                case C842TNode{lo, hi}:
                  C842TNode{c842.win.tset(p, n, r, lo, v), hi}
                case _:
                  C842TNode{c842.win.tset(p, n, r, C842TNil{}, v), C842TNil{}}

type C842Win is Data:
  C842Win{tree: C842Tree}

# The public interface of this file (the decoder's and the matcher's, and a
# replacement's)

# no bytes yet
def c842.win.empty() -> C842Win:
  C842Win{C842TNil{}}

# the window with byte v at position pos
def c842.win.put(w: C842Win, pos: U32, v: U32) -> C842Win:
  match w pos:
    case C842Win{tree} U32{k}:
      C842Win{c842.win.tset(12n, 20n, k, tree, v)}

# the byte at position pos (one of the last 4096 put), 0 if there is none
def c842.win.get(w: C842Win, pos: U32) -> U32:
  match w pos:
    case C842Win{tree} U32{k}:
      c842.win.tget(12n, 20n, k, tree)
