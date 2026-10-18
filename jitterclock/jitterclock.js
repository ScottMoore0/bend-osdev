// bend-osdev-jitterclock: the JavaScript side of the clock effect in
// jitterclock.bend. MIT; see LICENSE.
//
// JClock.eff.now reads process.hrtime.bigint() (a monotonic clock in
// nanoseconds) and answers it as two U32 halves, high then low. Its
// argument is not used: it orders the read after the value the caller
// computed for it.

function bosd_jclock_now(dep) {
  const t = process.hrtime.bigint();
  return io_tup(Number((t >> 32n) & 4294967295n), Number(t & 4294967295n));
}

io_eff(CID(JClock.eff.now), bosd_jclock_now);
