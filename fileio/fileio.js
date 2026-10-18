// bend-osdev-fileio: the JavaScript side of the library effects in
// fileio.bend, on Base's File handle (a file descriptor). MIT; see LICENSE.
//
// Shaped as Base's own file effects (bend2/effs/file_*.js): each takes the
// handle first and answers it beside a Result, Fail carrying the errno.
// A 64-bit offset crosses as two U32 halves, high then low, and is used as
// a BigInt position, so offsets past 2^53 stay exact; a 64-bit size comes
// back the same way, as a pair.

function bosd_fileio_fail(e) {
  return io_fail(Math.abs(e.errno ?? 5));
}

function bosd_fileio_off(hi, lo) {
  return (BigInt(hi >>> 0) << 32n) | BigInt(lo >>> 0);
}

// O_RDWR, never O_TRUNC; O_CREAT (mode 0644) only when create is not 0.
function bosd_fileio_open(path, create) {
  const fs = require("fs");
  const name = io_bytes(path);
  if (name.includes(0)) {
    return io_fail(process.platform === "darwin" ? 92 : 84);
  }
  const flags = fs.constants.O_RDWR | (create !== 0 ? fs.constants.O_CREAT : 0);
  try {
    return io_done(fs.openSync(name.length > 0 ? Buffer.from(name) : "",
      flags, 0o644));
  } catch (e) {
    return bosd_fileio_fail(e);
  }
}

// Up to max bytes at the offset; an offset of 2^63 or more fails (EINVAL),
// as pread does in C.
function bosd_fileio_read_at(file, hi, lo, max) {
  const fs = require("fs");
  const off = bosd_fileio_off(hi, lo);
  if (off >= 1n << 63n) {
    return io_tup(file, io_fail(22));
  }
  const len = Math.min(max, 2147483647);
  const b = new Uint8Array(Math.max(len, 1));
  try {
    const n = fs.readSync(file, b, 0, len, off);
    return io_tup(file, io_done(io_list(b, n)));
  } catch (e) {
    return io_tup(file, bosd_fileio_fail(e));
  }
}

// Every byte at the offset, looping on short writes; no progress fails
// with EIO, as Base's File.write does (#1445); a value past 255 fails with
// EINVAL before any byte is written, and so does a byte at 2^63 or more.
function bosd_fileio_write_at(file, hi, lo, data) {
  const fs = require("fs");
  const b = io_unlist(data);
  if (b === null) {
    return io_tup(file, io_fail(22));
  }
  const off = bosd_fileio_off(hi, lo);
  let at = 0;
  try {
    while (at < b.length) {
      if (off + BigInt(at) >= 1n << 63n) {
        return io_tup(file, io_fail(22));
      }
      const n = fs.writeSync(file, b, at, b.length - at, off + BigInt(at));
      if (n === 0) {
        return io_tup(file, io_fail(5));
      }
      at += n;
    }
    return io_tup(file, io_done({ $: CID(Unit) }));
  } catch (e) {
    return io_tup(file, bosd_fileio_fail(e));
  }
}

// The size in bytes, as its high and low halves.
function bosd_fileio_size(file) {
  try {
    const s = require("fs").fstatSync(file, { bigint: true }).size;
    return io_tup(file, io_done(io_tup(Number(s >> 32n),
      Number(s & 4294967295n))));
  } catch (e) {
    return io_tup(file, bosd_fileio_fail(e));
  }
}

function bosd_fileio_sync(file) {
  try {
    require("fs").fsyncSync(file);
    return io_tup(file, io_done({ $: CID(Unit) }));
  } catch (e) {
    return io_tup(file, bosd_fileio_fail(e));
  }
}

io_eff(CID(FileIO.eff.open), bosd_fileio_open);
io_eff(CID(FileIO.eff.read_at), bosd_fileio_read_at);
io_eff(CID(FileIO.eff.write_at), bosd_fileio_write_at);
io_eff(CID(FileIO.eff.size), bosd_fileio_size);
io_eff(CID(FileIO.eff.sync), bosd_fileio_sync);
