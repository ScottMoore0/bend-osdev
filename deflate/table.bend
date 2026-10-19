# bend-osdev-deflate, internal: a table of U32 values keyed by the low bits
# of a U32, as a binary trie (the key's low bit first). Its depth is the
# number of key bits, so a lookup costs that many steps whatever the table
# holds. The window (32 KB of output) and the encoder's code tables use it.
import Base

type DflTab is Data:
  DflTNil{}
  DflTLeaf{v: U32}
  DflTNode{lo: DflTab, hi: DflTab}

# the value at key k (m key bits left to walk), 0 if there is none
def tab.tget(m: Nat, n: Nat, k: Word(Nat.add(m, n)), t: DflTab) -> U32:
  match m:
    case 0n:
      match t:
        case DflTLeaf{v}:
          v
        case _:
          0
    case 1n+p:
      match k:
        case WCon{b, r}:
          match b:
            case True{}:
              match t:
                case DflTNode{lo, hi}:
                  tab.tget(p, n, r, hi)
                case _:
                  0
            case False{}:
              match t:
                case DflTNode{lo, hi}:
                  tab.tget(p, n, r, lo)
                case _:
                  0

# the table with v at key k
def tab.tset(m: Nat, n: Nat, k: Word(Nat.add(m, n)), t: DflTab, v: U32) -> DflTab:
  match m:
    case 0n:
      DflTLeaf{v}
    case 1n+p:
      match k:
        case WCon{b, r}:
          match b:
            case True{}:
              match t:
                case DflTNode{lo, hi}:
                  DflTNode{lo, tab.tset(p, n, r, hi, v)}
                case _:
                  DflTNode{DflTNil{}, tab.tset(p, n, r, DflTNil{}, v)}
            case False{}:
              match t:
                case DflTNode{lo, hi}:
                  DflTNode{tab.tset(p, n, r, lo, v), hi}
                case _:
                  DflTNode{tab.tset(p, n, r, DflTNil{}, v), DflTNil{}}

# 15 key bits: the window's 32768 positions
def tab.get15(i: U32, t: DflTab) -> U32:
  match i:
    case U32{w}:
      tab.tget(15n, 17n, w, t)

def tab.set15(i: U32, t: DflTab, v: U32) -> DflTab:
  match i:
    case U32{w}:
      tab.tset(15n, 17n, w, t, v)

# 9 key bits: the 288 literal/length symbols (and the 32 distance symbols)
def tab.get9(i: U32, t: DflTab) -> U32:
  match i:
    case U32{w}:
      tab.tget(9n, 23n, w, t)

def tab.set9(i: U32, t: DflTab, v: U32) -> DflTab:
  match i:
    case U32{w}:
      tab.tset(9n, 23n, w, t, v)
