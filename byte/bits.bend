# Splitting a word into its low and high bits, and joining them back: the
# low m bits of a Word(m + n), its high n bits, and the Word(m + n) of a
# Word(m) below a Word(n). Bits are least significant first, as in Base's
# Word.
import Base

def ByteBits.lo(m: Nat, n: Nat, w: Word(Nat.add(m, n))) -> Word(m):
  match m:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{h, t}:
          WCon{h, ByteBits.lo(p, n, t)}

def ByteBits.hi(m: Nat, n: Nat, w: Word(Nat.add(m, n))) -> Word(n):
  match m:
    case 0n:
      w
    case 1n+p:
      match w:
        case WCon{h, t}:
          ByteBits.hi(p, n, t)

def ByteBits.cat(m: Nat, n: Nat, a: Word(m), b: Word(n)) -> Word(Nat.add(m, n)):
  match m:
    case 0n:
      b
    case 1n+p:
      match a:
        case WCon{h, t}:
          WCon{h, ByteBits.cat(p, n, t, b)}
