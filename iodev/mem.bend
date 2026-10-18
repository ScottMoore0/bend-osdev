# bend-osdev-iodev: blockdev's devices on the IO interface. IOMem runs a
# MemDev (pure) and IOImg an ImgDev (owned) through iodev's helpers; they
# perform no effect, so a component written against the IO interface runs
# on them unchanged (and the laws tie IOMem's answers to blockdev's pure
# helpers).
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../blockdev/imgdev.bend as I
import ./iodev.bend as V

def IOMem.block_size(d: D.MemDev) -> IO(D.MemDev & Nat):
  V.IODev.of_pure_size(~D.MemDev, ~D.MemDev.block_size, d)

def IOMem.block_count(+d: D.MemDev) -> IO(D.MemDev & Nat):
  IO.pure(D.MemDev & Nat, (d, D.MemDev.block_count(d)))

def IOMem.read_block(d: D.MemDev, n: Nat) -> IO(D.MemDev & Result<&2, &2, D.DevError, B.Octets>):
  V.IODev.of_pure_read(~D.MemDev, ~D.MemDev.read_block, d, n)

def IOMem.write_block(d: D.MemDev, n: Nat, data: B.Octets) -> IO(D.MemDev & Result<&2, &2, D.DevError, Unit>):
  V.IODev.of_own_write(~D.MemDev, ~D.MemDev.own_write_block, d, n, data)

def IOImg.block_size(img: I.ImgDev) -> IO(I.ImgDev & Nat):
  V.IODev.of_own_size(~I.ImgDev, ~I.ImgDev.block_size, img)

def IOImg.block_count(img: I.ImgDev) -> IO(I.ImgDev & Nat):
  V.IODev.of_own_size(~I.ImgDev, ~I.ImgDev.block_count, img)

def IOImg.read_block(img: I.ImgDev, n: Nat) -> IO(I.ImgDev & Result<&2, &2, D.DevError, B.Octets>):
  V.IODev.of_own_read(~I.ImgDev, ~I.ImgDev.read_block, img, n)

def IOImg.write_block(img: I.ImgDev, n: Nat, data: B.Octets) -> IO(I.ImgDev & Result<&2, &2, D.DevError, Unit>):
  V.IODev.of_own_write(~I.ImgDev, ~I.ImgDev.write_block, img, n, data)
