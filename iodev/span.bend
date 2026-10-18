# bend-osdev-iodev: block arithmetic. A byte range (off, len) on a device
# of bs-byte blocks lies in the blocks first to first + count - 1: it starts
# skip bytes into block first and ends slack bytes before the end of the
# last block. Pure and device-free, so any helper (pure, owned or IO) that
# splits a range into blocks can share it, and the laws pin it down:
#
#   first * bs + skip == off          skip < bs
#   count * bs == skip + len + slack  slack < bs
#
# (for bs > 0; a zero block size gives a span of zero blocks).
import Base

type IOSpan is Data:
  IOSpan{first: Nat, skip: Nat, count: Nat, slack: Nat}

# the span of len bytes from byte offset off, on bs-byte blocks
def IOSpan.of(+bs: Nat, +off: Nat, +len: Nat) -> IOSpan:
  +skip = Nat.mod(off, bs)
  +total = Nat.add(Nat.add(skip, len), Nat.sub(bs, 1n))
  IOSpan{Nat.div(off, bs), skip, Nat.div(total, bs), Nat.sub(Nat.sub(bs, 1n), Nat.mod(total, bs))}

def IOSpan.first(s: IOSpan) -> Nat:
  match s:
    case IOSpan{f, k, c, l}:
      f

def IOSpan.skip(s: IOSpan) -> Nat:
  match s:
    case IOSpan{f, k, c, l}:
      k

def IOSpan.count(s: IOSpan) -> Nat:
  match s:
    case IOSpan{f, k, c, l}:
      c

def IOSpan.slack(s: IOSpan) -> Nat:
  match s:
    case IOSpan{f, k, c, l}:
      l

# the byte offset of block n
def IOSpan.offset(bs: Nat, n: Nat) -> Nat:
  Nat.mul(n, bs)

# the number of bs-byte blocks that hold size bytes (a final partial block
# counts as one)
def IOSpan.blocks(+bs: Nat, size: Nat) -> Nat:
  Nat.div(Nat.add(size, Nat.sub(bs, 1n)), bs)
