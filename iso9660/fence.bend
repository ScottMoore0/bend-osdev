# bend-osdev-iso9660, fence.bend: a fenced device. An in-memory device
# (blockdev's MemDev) that answers only the blocks from first to
# first + count - 1, and refuses every other read (DevOutOfRange). The laws
# use it to say what a reader may read: a walk or a stream on the fenced
# device gives what it gives on the whole device. A caller can use it the
# same way, to keep a reader to a region of a device.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as BD

type IsoFence is Data:
  IsoFence{dev: BD.MemDev, first: Nat, count: Nat}

def IsoFence.block_size(f: IsoFence) -> Nat:
  match f:
    case IsoFence{d, a, n}:
      BD.MemDev.block_size(d)

def iso.fence.pick(ok: Bool, d: BD.MemDev, +n: Nat) -> Result<&2, &2, BD.DevError, B.Octets>:
  match ok:
    case True{}:
      BD.MemDev.read_block(d, n)
    case False{}:
      Fail{BD.DevOutOfRange{n}}

def iso.fence.read(f: IsoFence, +n: Nat) -> Result<&2, &2, BD.DevError, B.Octets>:
  match f:
    case IsoFence{d, +a, c}:
      iso.fence.pick(Bool.and(Nat.is_le(a, n), Nat.is_lt(n, Nat.add(a, c))), d, n)

# block n, if it is inside the fence (plain parameters, to fit the device
# interface's template type)
def IsoFence.read_block(f: IsoFence, n: Nat) -> Result<&2, &2, BD.DevError, B.Octets>:
  iso.fence.read(f, n)
