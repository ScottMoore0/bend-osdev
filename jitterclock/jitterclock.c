// bend-osdev-jitterclock: the C side of the clock effect in
// jitterclock.bend. MIT; see LICENSE.
//
// JClock.eff.now reads CLOCK_MONOTONIC with clock_gettime (POSIX) and
// answers the nanoseconds as two U32 halves, high then low. Its argument
// is not used: it is there so that the read depends on a value the caller
// computed first, which orders the read after that computation. The read
// runs on the calling thread (it does not block), as Base's IO.now does.

#include <time.h>

#ifdef CID(JClock.eff.now)

static Term bosd_jclock_now_run(Env e, Term* f, IoWork* w) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  u64 ns = (u64)ts.tv_sec * 1000000000ull + (u64)ts.tv_nsec;
  return io_tup(e, (u32)(ns >> 32), (u32)ns);
}

static void __attribute__((constructor)) bosd_jclock_now_use(void) {
  io_eff(CID(JClock.eff.now), bosd_jclock_now_run);
}

#endif
