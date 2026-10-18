# DRAFT: not yet reviewed by the maintainer
#
# Block arithmetic, for every block size, offset and length: a range's
# span starts at its offset, covers it exactly (with skip bytes before and
# slack bytes after, each less than a block), and an offset inside block n
# lies in block n.
#
# The adapters, for every pure device, continuation and range: the IO
# helpers on a pure device (through IODev.of_pure_*) perform no effect,
# hand back the device unchanged, and answer what blockdev's pure helpers
# answer; a good write through IOMem is MemDev.update.
#
# The overlay, for every device below it: reading a block after a write
# that succeeded gives what was written, without reading the device below;
# on a pure device below, a write leaves the reads of every other block
# unchanged, and an overlay with nothing written reads the device.
#
# Vectors: spans, the helpers on IOMem and IOImg, write_bytes, the overlay.
#
# A law about an IO action states what it gives a continuation k: the
# action run as m(R, k). IO effects themselves (FileDev) are tested, not
# proved (ref/).
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../blockdev/imgdev.bend as I
import ./span.bend as S
import ./iodev.bend as V
import ./mem.bend as M
import ./overlay.bend as O

# Block arithmetic (a block of 1 + bp bytes)

law span_start:
  for +bp: Nat
  for +off: Nat
  for +len: Nat
  {Nat.add(Nat.mul(S.IOSpan.first(S.IOSpan.of(1n+bp, off, len)), 1n+bp), S.IOSpan.skip(S.IOSpan.of(1n+bp, off, len))) == off : Nat}

law span_skip:
  for +bp: Nat
  for +off: Nat
  for +len: Nat
  {Nat.is_lt(S.IOSpan.skip(S.IOSpan.of(1n+bp, off, len)), 1n+bp) == True{} : Bool}

law span_cover:
  for +bp: Nat
  for +off: Nat
  for +len: Nat
  {Nat.mul(S.IOSpan.count(S.IOSpan.of(1n+bp, off, len)), 1n+bp) == Nat.add(Nat.add(S.IOSpan.skip(S.IOSpan.of(1n+bp, off, len)), len), S.IOSpan.slack(S.IOSpan.of(1n+bp, off, len))) : Nat}

law span_slack:
  for +bp: Nat
  for +off: Nat
  for +len: Nat
  {Nat.is_lt(S.IOSpan.slack(S.IOSpan.of(1n+bp, off, len)), 1n+bp) == True{} : Bool}

law span_in_block:
  for +bp: Nat
  for +n: Nat
  for +i: Nat
  for +len: Nat
  for h: {Nat.is_lt(i, 1n+bp) == True{} : Bool}
  {(S.IOSpan.first(S.IOSpan.of(1n+bp, Nat.add(S.IOSpan.offset(1n+bp, n), i), len)), S.IOSpan.skip(S.IOSpan.of(1n+bp, Nat.add(S.IOSpan.offset(1n+bp, n), i), len))) == (n, i) : Nat & Nat}

law blocks_cover:
  for +bp: Nat
  for +size: Nat
  {Nat.mul(S.IOSpan.blocks(1n+bp, size), 1n+bp) == Nat.add(size, S.IOSpan.slack(S.IOSpan.of(1n+bp, 0n, size))) : Nat}

# The adapters

law io_read_blocks:
  for ~D: Data
  for ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>
  for -R: Type
  for -k: (D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>
  for d: D
  for count: Nat
  for first: Nat
  {V.IODev.read_blocks(~D, ~V.IODev.of_pure_read(~D, ~read_block), count, d, first)(R, k) == k((d, D.Dev.read_blocks(~D, ~read_block, d, count, first))) : IO.OP<R>}

law io_read_bytes:
  for ~D: Data
  for ~block_size: D -> Nat
  for ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>
  for -R: Type
  for -k: (D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>
  for d: D
  for off: Nat
  for len: Nat
  {V.IODev.read_bytes(~D, ~V.IODev.of_pure_size(~D, ~block_size), ~V.IODev.of_pure_read(~D, ~read_block), d, off, len)(R, k) == k((d, D.Dev.read_bytes(~D, ~block_size, ~read_block, d, off, len))) : IO.OP<R>}

law io_mem_write_ok:
  for -R: Type
  for -k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>
  for +d: D.MemDev
  for +n: Nat
  for +data: B.Octets
  for len_ok: {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool}
  for in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}
  {M.IOMem.write_block(d, n, data)(R, k) == k((D.MemDev.update(d, n, data), Done{Unit{}})) : IO.OP<R>}

# The overlay

law ov_read_put:
  for ~D: Type
  for ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>)
  for -R: Type
  for -k: (O.IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>
  for o: O.IOOverlay<D>
  for +n: Nat
  for +data: B.Octets
  for ok: {Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put(~D, o, n, data)) == Done{Unit{}} : Result<&2, &2, D.DevError, Unit>}
  {O.IOOverlay.read_block(~D, ~read_block, Pair.fst(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put(~D, o, n, data)), n)(R, k) == k((Pair.fst(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put(~D, o, n, data)), Done{data})) : IO.OP<R>}

law ov_put_other:
  for ~D: Data
  for ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>
  for -R: Type
  for -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>
  for o: O.IOOverlay<D>
  for +n: Nat
  for +m: Nat
  for +data: B.Octets
  for diff: {U32.is_eq(U32.from_nat(n), U32.from_nat(m)) == False{} : Bool}
  {O.IOOverlay.read_block(~D, ~V.IODev.of_pure_read(~D, ~read_block), Pair.fst(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put(~D, o, n, data)), m)(R, x => k(Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, B.Octets>, x))) == O.IOOverlay.read_block(~D, ~V.IODev.of_pure_read(~D, ~read_block), o, m)(R, x => k(Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, B.Octets>, x))) : IO.OP<R>}

law ov_read_fresh:
  for ~D: Data
  for ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>
  for -R: Type
  for -k: (O.IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>
  for d: D
  for bs: Nat
  for count: Nat
  for n: Nat
  {O.IOOverlay.read_block(~D, ~V.IODev.of_pure_read(~D, ~read_block), O.IOOverlay.of(~D, d, bs, count), n)(R, k) == k((O.IOOverlay.of(~D, d, bs, count), read_block(d, n))) : IO.OP<R>}

# Vectors: a 3-block device of 4-byte blocks holding "abcdefghij" (padded)

def dev() -> D.MemDev:
  D.MemDev.of_octets(4n, B.Octets.of_string("abcdefghij"))

def text(r: Result<&2, &2, D.DevError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      "error"

def run_mem(m: IO(D.MemDev & Result<&2, &2, D.DevError, B.Octets>)) -> IO.OP<String>:
  m(String, x => Emit{text(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, x))})

def run_img(m: IO(I.ImgDev & Result<&2, &2, D.DevError, B.Octets>)) -> IO.OP<String>:
  m(String, x => Emit{text(Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, x))})

def mem_then(m: IO(D.MemDev & Result<&2, &2, D.DevError, Unit>), k: D.MemDev -> IO(D.MemDev & Result<&2, &2, D.DevError, B.Octets>)) -> IO(D.MemDev & Result<&2, &2, D.DevError, B.Octets>):
  IO.bind(D.MemDev & Result<&2, &2, D.DevError, Unit>, D.MemDev & Result<&2, &2, D.DevError, B.Octets>, m, x => k(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x)))

law vector_span:
  {S.IOSpan.of(4n, 6n, 7n) == S.IOSpan{1n, 2n, 3n, 3n} : S.IOSpan}

law vector_blocks:
  {S.IOSpan.blocks(4n, 10n) == 3n : Nat}

law vector_io_bytes:
  {run_mem(V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, dev(), 2n, 7n)) == Emit{"cdefghi"} : IO.OP<String>}

law vector_io_past_end:
  {run_mem(V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, dev(), 10n, 4n)) == Emit{"error"} : IO.OP<String>}

law vector_io_img:
  {run_img(V.IODev.read_bytes(~I.ImgDev, ~M.IOImg.block_size, ~M.IOImg.read_block, I.ImgDev.of_octets(1n, B.Octets.of_string("abcdefghij")), 3n, 6n)) == Emit{"defghi"} : IO.OP<String>}

law vector_write_bytes:
  {run_mem(mem_then(V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, dev(), 3n, B.Octets.of_string("XYZW")), d => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, 0n, 10n))) == Emit{"abcXYZWhij"} : IO.OP<String>}

# the same device under an overlay: a write lands in the overlay, reads see
# it, and the device below keeps its blocks

def ov_dev() -> O.IOOverlay<D.MemDev>:
  O.IOOverlay.of(~D.MemDev, dev(), 4n, 3n)

def ov_then(m: IO(O.IOOverlay<D.MemDev> & Result<&2, &2, D.DevError, Unit>), k: O.IOOverlay<D.MemDev> -> IO(O.IOOverlay<D.MemDev> & Result<&2, &2, D.DevError, B.Octets>)) -> IO(O.IOOverlay<D.MemDev> & Result<&2, &2, D.DevError, B.Octets>):
  IO.bind(O.IOOverlay<D.MemDev> & Result<&2, &2, D.DevError, Unit>, O.IOOverlay<D.MemDev> & Result<&2, &2, D.DevError, B.Octets>, m, x => k(Pair.fst(O.IOOverlay<D.MemDev>, Result<&2, &2, D.DevError, Unit>, x)))

def ov_write() -> IO(O.IOOverlay<D.MemDev> & Result<&2, &2, D.DevError, Unit>):
  V.IODev.write_bytes(~O.IOOverlay<D.MemDev>, ~O.IOOverlay.block_size(~D.MemDev), ~O.IOOverlay.read_block(~D.MemDev, ~M.IOMem.read_block), ~O.IOOverlay.write_block(~D.MemDev), ov_dev(), 3n, B.Octets.of_string("XYZW"))

def run_ov(m: IO(O.IOOverlay<D.MemDev> & Result<&2, &2, D.DevError, B.Octets>)) -> IO.OP<String>:
  m(String, x => Emit{text(Pair.snd(O.IOOverlay<D.MemDev>, Result<&2, &2, D.DevError, B.Octets>, x))})

def run_base(m: IO(O.IOOverlay<D.MemDev> & Result<&2, &2, D.DevError, Unit>)) -> IO.OP<String>:
  m(String, x => Emit{B.Octets.to_string(B.Octets.take(10n, D.MemDev.to_octets(O.IOOverlay.base(~D.MemDev, Pair.fst(O.IOOverlay<D.MemDev>, Result<&2, &2, D.DevError, Unit>, x)))))})

law vector_overlay:
  {run_ov(ov_then(ov_write(), o => V.IODev.read_bytes(~O.IOOverlay<D.MemDev>, ~O.IOOverlay.block_size(~D.MemDev), ~O.IOOverlay.read_block(~D.MemDev, ~M.IOMem.read_block), o, 0n, 10n))) == Emit{"abcXYZWhij"} : IO.OP<String>}

law vector_overlay_base:
  {run_base(ov_write()) == Emit{"abcdefghij"} : IO.OP<String>}
