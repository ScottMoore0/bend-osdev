# bend-osdev-fdt, layout.bend: sizes, padding, alignment and byte-list
# scanning shared by the block readers and writers. Internal: nothing here is
# public interface, and any of it may change.
import Base

# Numbers: a length as a 32-bit field

def fdt.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+fdt.half(q)

def fdt.odd(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match p:
        case 0n:
          True{}
        case 1n+q:
          fdt.odd(q)

# the low k bits of n
def fdt.nbits(k: Nat, +n: Nat) -> Word(k):
  match k:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{fdt.odd(n), fdt.nbits(p, fdt.half(n))}

# n with its low k bits dropped: n / 2^k
def fdt.high(k: Nat, n: Nat) -> Nat:
  match k:
    case 0n:
      n
    case 1n+p:
      fdt.high(p, fdt.half(n))

# n modulo 2^32
def fdt.u32n(n: Nat) -> U32:
  U32{fdt.nbits(32n, n)}

# n / 2^32: zero exactly when n fits in a 32-bit field
def fdt.over(n: Nat) -> Nat:
  fdt.high(32n, n)

def fdt.is_zero(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

# n fits in a 32-bit field
def fdt.fits(n: Nat) -> Bool:
  fdt.is_zero(fdt.over(n))

# a is at most b
def fdt.le(a: Nat, b: Nat) -> Bool:
  fdt.is_zero(Nat.sub(a, b))

# Padding and alignment

# the padding that takes a length of n bytes to a multiple of four
def fdt.pad4(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+a:
      match a:
        case 0n:
          3n
        case 1n+b:
          match b:
            case 0n:
              2n
            case 1n+c:
              match c:
                case 0n:
                  1n
                case 1n+d:
                  fdt.pad4(d)

# n is a multiple of four
def fdt.al4(n: Nat) -> Bool:
  fdt.is_zero(fdt.pad4(n))

# n is a multiple of eight
def fdt.al8(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+a:
      match a:
        case 0n:
          False{}
        case 1n+b:
          match b:
            case 0n:
              False{}
            case 1n+c:
              match c:
                case 0n:
                  False{}
                case 1n+d:
                  match d:
                    case 0n:
                      False{}
                    case 1n+e:
                      match e:
                        case 0n:
                          False{}
                        case 1n+f:
                          match f:
                            case 0n:
                              False{}
                            case 1n+g:
                              match g:
                                case 0n:
                                  False{}
                                case 1n+h:
                                  fdt.al8(h)

# Byte lists

# no byte of xs is NUL
def fdt.nonul(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Bool.not(U32.is_eq(h, 0)), fdt.nonul(t))

# a byte list cut in two
type FdtCut is Data:
  FdtCut{head: List<&2, U32>, rest: List<&2, U32>}

# Scanning for a NUL: the bytes before it (kept reversed while scanning),
# then, once it is found, the bytes after it
type FdtScan is Data:
  FdtScanning{acc: List<&2, U32>}
  FdtFound{acc: List<&2, U32>}

def fdt.scan.pick(nul: Bool, acc: List<&2, U32>, h: U32) -> FdtScan:
  match nul:
    case True{}:
      FdtFound{acc}
    case False{}:
      FdtScanning{Con{h, acc}}

def fdt.scan.step(acc: List<&2, U32>, +h: U32) -> FdtScan:
  fdt.scan.pick(U32.is_eq(h, 0), acc, h)

def fdt.scan.go(xs: List<&2, U32>, st: FdtScan) -> Maybe<&2, FdtCut>:
  match xs st:
    case Nil{} FdtFound{acc}:
      Some{FdtCut{List.reverse(&2, U32, acc), Nil{}}}
    case Con{h, t} FdtFound{acc}:
      Some{FdtCut{List.reverse(&2, U32, acc), Con{h, t}}}
    case Nil{} FdtScanning{acc}:
      None{}
    case Con{h, t} FdtScanning{acc}:
      fdt.scan.go(t, fdt.scan.step(acc, h))

# the bytes of xs before its first NUL, and the bytes after that NUL; None if
# xs has no NUL
def fdt.cstr(xs: List<&2, U32>) -> Maybe<&2, FdtCut>:
  fdt.scan.go(xs, FdtScanning{Nil{}})
