// bend-osdev-fileio: the C side of the library effects in fileio.bend, on
// Base's File handle (a file descriptor). MIT; see LICENSE.
//
// Shaped as Base's own file effects (bend2/effs/file_*.c): each request
// takes the handle first and runs its system call on a helper thread
// (io_work); the answer is the handle beside a Result, Fail carrying the
// errno. A 64-bit offset crosses as two U32 halves, high then low, and a
// 64-bit size comes back the same way, as a pair.

#include <sys/stat.h>

static u64 bosd_fileio_off(Term hi, Term lo) {
  return ((u64)(u32)hi << 32) | (u64)(u32)lo;
}

static Term bosd_fileio_unit_pack(Env e, IoWork* w) {
  return io_tup(e, io_hand(w->hand), io_res(e, w, term_pak(CID(Unit), 0)));
}

#ifdef CID(FileIO.eff.open)

// O_RDWR, never O_TRUNC; O_CREAT (mode 0644) only when create is not 0.
static void bosd_fileio_open_call(IoWork* w) {
  w->made = (intptr_t)io_sys_end(w, open(w->data, (int)w->word, 0644));
}

static Term bosd_fileio_open_pack(Env e, IoWork* w) {
  free(w->data);
  return io_res(e, w, io_hand(w->made));
}

static Term bosd_fileio_open_run(Env e, Term* f, IoWork* w) {
  w->data = io_cstr(e, f[0], &w->size);
  w->word = (u32)(O_RDWR | ((u32)f[1] != 0 ? O_CREAT : 0));
  if (io_nul(w->data, w->size)) {
    w->code = EILSEQ;
    return bosd_fileio_open_pack(e, w);
  }
  return io_work(w, bosd_fileio_open_call, bosd_fileio_open_pack);
}

static void __attribute__((constructor)) bosd_fileio_open_use(void) {
  io_eff(CID(FileIO.eff.open), bosd_fileio_open_run);
}

#endif

#ifdef CID(FileIO.eff.read_at)

// Up to max bytes at the offset (pread), as File.read_at gives them; the
// position of the file does not move. An offset of 2^63 or more fails
// (EINVAL, from pread).
static void bosd_fileio_read_at_call(IoWork* w) {
  w->size = io_sys_end(w,
    pread((int)w->hand, w->data, w->word, (off_t)w->made));
}

static Term bosd_fileio_read_at_pack(Env e, IoWork* w) {
  Term r = io_res(e, w, io_list(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

static Term bosd_fileio_read_at_run(Env e, Term* f, IoWork* w) {
  u64 max = (u32)f[3];
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->made = (intptr_t)bosd_fileio_off(f[1], f[2]);
  w->word = max < INT32_MAX ? (u32)max : INT32_MAX;
  w->data = io_mem(malloc(w->word + 1));
  return io_work(w, bosd_fileio_read_at_call, bosd_fileio_read_at_pack);
}

static void __attribute__((constructor)) bosd_fileio_read_at_use(void) {
  io_eff(CID(FileIO.eff.read_at), bosd_fileio_read_at_run);
}

#endif

#ifdef CID(FileIO.eff.write_at)

// Every byte at the offset (pwrite), looping on short writes; the position
// of the file does not move. A write that makes no progress fails with
// EIO, as Base's File.write does (#1445); a value past 255 fails with
// EINVAL before any byte is written.
static void bosd_fileio_write_at_call(IoWork* w) {
  int     fd = (int)w->hand;
  ssize_t n  = 0;
  for (u64 at = 0; n >= 0 && at < w->size; at += (u64)n) {
    n = pwrite(fd, w->data + at, w->size - at, (off_t)((u64)w->made + at));
    if (n == 0) {
      w->code = EIO;
      return;
    }
  }
  io_sys_end(w, n);
}

static Term bosd_fileio_write_at_pack(Env e, IoWork* w) {
  free(w->data);
  return bosd_fileio_unit_pack(e, w);
}

static Term bosd_fileio_write_at_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->made = (intptr_t)bosd_fileio_off(f[1], f[2]);
  w->data = io_cbuf(e, f[3], &w->size, CID(Con));
  w->code = w->data == NULL ? EINVAL : 0;
  return w->code ? bosd_fileio_write_at_pack(e, w)
    : io_work(w, bosd_fileio_write_at_call, bosd_fileio_write_at_pack);
}

static void __attribute__((constructor)) bosd_fileio_write_at_use(void) {
  io_eff(CID(FileIO.eff.write_at), bosd_fileio_write_at_run);
}

#endif

#ifdef CID(FileIO.eff.size)

// The size in bytes (fstat), as its high and low halves.
static void bosd_fileio_size_call(IoWork* w) {
  struct stat st;
  int n = fstat((int)w->hand, &st);
  io_sys_end(w, n);
  w->size = n == 0 ? (u64)st.st_size : 0;
}

static Term bosd_fileio_size_pack(Env e, IoWork* w) {
  return io_tup(e, io_hand(w->hand),
    io_res(e, w, io_tup(e, (u32)(w->size >> 32), (u32)w->size)));
}

static Term bosd_fileio_size_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  return io_work(w, bosd_fileio_size_call, bosd_fileio_size_pack);
}

static void __attribute__((constructor)) bosd_fileio_size_use(void) {
  io_eff(CID(FileIO.eff.size), bosd_fileio_size_run);
}

#endif

#ifdef CID(FileIO.eff.sync)

// fsync: the data and metadata of the file reach the device.
static void bosd_fileio_sync_call(IoWork* w) {
  io_sys_end(w, fsync((int)w->hand));
}

static Term bosd_fileio_sync_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  return io_work(w, bosd_fileio_sync_call, bosd_fileio_unit_pack);
}

static void __attribute__((constructor)) bosd_fileio_sync_use(void) {
  io_eff(CID(FileIO.eff.sync), bosd_fileio_sync_run);
}

#endif
