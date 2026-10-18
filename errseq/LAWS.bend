# Properties, for every state, cursor and error:
#
# * a fresh observer (the default sample) sees no error until one is
#   recorded, and then sees it: it learns only of errors after it sampled;
# * an observer whose cursor belongs to the state learns of a newly
#   recorded error, the latest one;
# * a check-and-advance that reports an error leaves the observer with
#   nothing more to learn: checking again reports nothing, and changes
#   nothing, until another error is recorded; so each error is learned of
#   exactly once by each observer;
# * with no new error there is no report, and error 0 records nothing;
# * cursors stay valid: sampling and advancing give valid cursors, and
#   recording errors and other observers' advances keep a cursor valid and
#   leave what it would learn unchanged;
# * the kernel option: a fresh observer sampling while the latest error is
#   unseen learns of it, but not once some observer has seen it.
import Base
import ./errseq.bend as E

# A fresh observer

law errseq_fresh_quiet:
  for s: E.Errseq
  {E.Errseq.check(s, E.Errseq.sample(E.ErrseqOptions.default(), s)) == None{} : Maybe<&2, U32>}

law errseq_fresh_sees_next:
  for s: E.Errseq
  for +e: U32
  for h: {U32.is_zero(e) == False{} : Bool}
  {E.Errseq.check(E.Errseq.set(s, e), E.Errseq.sample(E.ErrseqOptions.default(), s)) == Some{e} : Maybe<&2, U32>}

# Every observer learns of a new error

law errseq_new_error_seen:
  for s: E.Errseq
  for c: E.ErrseqCursor
  for +e: U32
  for v: {E.Errseq.cursor_valid(s, c) == True{} : Bool}
  for h: {U32.is_zero(e) == False{} : Bool}
  {E.Errseq.check(E.Errseq.set(s, e), c) == Some{e} : Maybe<&2, U32>}

law errseq_advance_reports_check:
  for s: E.Errseq
  for c: E.ErrseqCursor
  {E.ErrseqCheck.error(E.Errseq.check_and_advance(s, c)) == E.Errseq.check(s, c) : Maybe<&2, U32>}

# Exactly once: after an advance there is nothing more to learn

law errseq_advance_then_quiet:
  for s: E.Errseq
  for c: E.ErrseqCursor
  {E.Errseq.check(E.ErrseqCheck.state(E.Errseq.check_and_advance(s, c)), E.ErrseqCheck.cursor(E.Errseq.check_and_advance(s, c))) == None{} : Maybe<&2, U32>}

law errseq_advance_twice:
  for s: E.Errseq
  for c: E.ErrseqCursor
  {E.Errseq.check_and_advance(E.ErrseqCheck.state(E.Errseq.check_and_advance(s, c)), E.ErrseqCheck.cursor(E.Errseq.check_and_advance(s, c))) == E.ErrseqCheck{E.ErrseqCheck.state(E.Errseq.check_and_advance(s, c)), E.ErrseqCheck.cursor(E.Errseq.check_and_advance(s, c)), None{}} : E.ErrseqCheck}

# No new error, no report

law errseq_quiet_unchanged:
  for s: E.Errseq
  for c: E.ErrseqCursor
  for q: {E.Errseq.check(s, c) == None{} : Maybe<&2, U32>}
  {E.Errseq.check_and_advance(s, c) == E.ErrseqCheck{s, c, None{}} : E.ErrseqCheck}

law errseq_set_zero:
  for s: E.Errseq
  {E.Errseq.set(s, 0) == s : E.Errseq}

law errseq_new_quiet:
  for c: E.ErrseqCursor
  for v: {E.Errseq.cursor_valid(E.Errseq.new(), c) == True{} : Bool}
  {E.Errseq.check(E.Errseq.new(), c) == None{} : Maybe<&2, U32>}

# Cursors stay valid, and other observers are left alone

law errseq_sample_valid:
  for o: E.ErrseqOptions
  for s: E.Errseq
  {E.Errseq.cursor_valid(s, E.Errseq.sample(o, s)) == True{} : Bool}

law errseq_advance_valid:
  for s: E.Errseq
  for c: E.ErrseqCursor
  for v: {E.Errseq.cursor_valid(s, c) == True{} : Bool}
  {E.Errseq.cursor_valid(E.ErrseqCheck.state(E.Errseq.check_and_advance(s, c)), E.ErrseqCheck.cursor(E.Errseq.check_and_advance(s, c))) == True{} : Bool}

law errseq_set_keeps_valid:
  for s: E.Errseq
  for c: E.ErrseqCursor
  for +e: U32
  for v: {E.Errseq.cursor_valid(s, c) == True{} : Bool}
  {E.Errseq.cursor_valid(E.Errseq.set(s, e), c) == True{} : Bool}

law errseq_advance_keeps_other_valid:
  for s: E.Errseq
  for c: E.ErrseqCursor
  for d: E.ErrseqCursor
  {E.Errseq.cursor_valid(E.ErrseqCheck.state(E.Errseq.check_and_advance(s, c)), d) == E.Errseq.cursor_valid(s, d) : Bool}

law errseq_advance_other_check:
  for s: E.Errseq
  for c: E.ErrseqCursor
  for d: E.ErrseqCursor
  {E.Errseq.check(E.ErrseqCheck.state(E.Errseq.check_and_advance(s, c)), d) == E.Errseq.check(s, d) : Maybe<&2, U32>}

# The kernel option

law errseq_kernel_unseen:
  for s: E.Errseq
  for +e: U32
  for h: {U32.is_zero(e) == False{} : Bool}
  {E.Errseq.check(E.Errseq.set(s, e), E.Errseq.sample(E.ErrseqOptions.kernel(), E.Errseq.set(s, e))) == Some{e} : Maybe<&2, U32>}

law errseq_kernel_seen_quiet:
  for s: E.Errseq
  for c: E.ErrseqCursor
  for +e: U32
  for v: {E.Errseq.cursor_valid(s, c) == True{} : Bool}
  for h: {U32.is_zero(e) == False{} : Bool}
  {E.Errseq.check(E.ErrseqCheck.state(E.Errseq.check_and_advance(E.Errseq.set(s, e), c)), E.Errseq.sample(E.ErrseqOptions.kernel(), E.ErrseqCheck.state(E.Errseq.check_and_advance(E.Errseq.set(s, e), c)))) == None{} : Maybe<&2, U32>}

law errseq_kernel_quiet_when_seen:
  for s: E.Errseq
  for h: {E.Errseq.seen(s) == True{} : Bool}
  {E.Errseq.sample(E.ErrseqOptions.kernel(), s) == E.Errseq.sample(E.ErrseqOptions.default(), s) : E.ErrseqCursor}

# Witnesses: each hypothesis above can hold

law errseq_wit:
  {(U32.is_zero(5), E.Errseq.cursor_valid(E.Errseq.new(), E.Errseq.sample(E.ErrseqOptions.default(), E.Errseq.new())), E.Errseq.check(E.Errseq.new(), E.Errseq.sample(E.ErrseqOptions.default(), E.Errseq.new())), E.Errseq.seen(E.Errseq.new())) == (False{}, True{}, None{}, True{}) : Bool & Bool & Maybe<&2, U32> & Bool}

# Vectors: two observers, A sampled before the first error, B after it

law errseq_vec_two_observers:
  {(E.Errseq.check(E.Errseq.set(E.Errseq.set(E.Errseq.new(), 5), 28), E.Errseq.sample(E.ErrseqOptions.default(), E.Errseq.new())), E.Errseq.check(E.Errseq.set(E.Errseq.set(E.Errseq.new(), 5), 28), E.Errseq.sample(E.ErrseqOptions.default(), E.Errseq.set(E.Errseq.new(), 5))), E.Errseq.check(E.Errseq.set(E.Errseq.new(), 5), E.Errseq.sample(E.ErrseqOptions.default(), E.Errseq.set(E.Errseq.new(), 5)))) == (Some{28}, Some{28}, None{}) : Maybe<&2, U32> & Maybe<&2, U32> & Maybe<&2, U32>}
