# bend-osdev-errseq: error sequence counters, as a pure state machine.
#
# A writer records errors in an Errseq; any number of observers each hold a
# cursor, and each learns of an error it has not seen exactly once. The
# state counts the errors recorded (seq), keeps the latest (err), and
# remembers whether any observer has been told of the latest (seen). A
# cursor is the count its observer last saw: an observer whose cursor is
# behind the count has an error to learn of, the latest one.
#
# Nothing here reads a clock or shared memory: every operation takes the
# state and answers the new one, so the caller decides where the state lives
# and how it is shared.
import Base

# The one behavioural choice. report_unseen: whether a fresh observer's
# sample is set one error back when nobody has been told of the latest
# error yet, so that the first observer to check learns of it (as the
# kernel's errseq_sample does). Off by default: a fresh observer learns
# only of errors recorded after it sampled.
type ErrseqOptions is Data:
  ErrseqOptions{report_unseen: Bool}

def ErrseqOptions.default() -> ErrseqOptions:
  ErrseqOptions{False{}}

def ErrseqOptions.kernel() -> ErrseqOptions:
  ErrseqOptions{True{}}

# seq: the number of errors recorded; err: the latest (0 before any);
# seen: some observer has been told of the latest (True before any)
type Errseq is Data:
  Errseq{seq: Nat, err: U32, seen: Bool}

# an observer's position: the count of errors it has accounted for
type ErrseqCursor is Data:
  ErrseqCursor{seq: Nat}

# what a check-and-advance answers: the state (the latest error marked
# seen if it was reported), the observer's new cursor, and the error
# reported, if any
type ErrseqCheck is Data:
  ErrseqCheck{state: Errseq, cursor: ErrseqCursor, error: Maybe<&2, U32>}

def Errseq.new() -> Errseq:
  Errseq{0n, 0, True{}}

def Errseq.seq(s: Errseq) -> Nat:
  match s:
    case Errseq{n, e, f}:
      n

def Errseq.error(s: Errseq) -> U32:
  match s:
    case Errseq{n, e, f}:
      e

def Errseq.seen(s: Errseq) -> Bool:
  match s:
    case Errseq{n, e, f}:
      f

def ErrseqCursor.seq(c: ErrseqCursor) -> Nat:
  match c:
    case ErrseqCursor{n}:
      n

def ErrseqCheck.state(r: ErrseqCheck) -> Errseq:
  match r:
    case ErrseqCheck{s, c, e}:
      s

def ErrseqCheck.cursor(r: ErrseqCheck) -> ErrseqCursor:
  match r:
    case ErrseqCheck{s, c, e}:
      c

def ErrseqCheck.error(r: ErrseqCheck) -> Maybe<&2, U32>:
  match r:
    case ErrseqCheck{s, c, e}:
      e

# Recording an error (errseq_set). Error 0 means "no error" and records
# nothing.

def Errseq.set.go(zero: Bool, s: Errseq, e: U32) -> Errseq:
  match zero:
    case True{}:
      s
    case False{}:
      match s:
        case Errseq{n, old, f}:
          Errseq{1n+n, e, False{}}

def Errseq.set(s: Errseq, +e: U32) -> Errseq:
  Errseq.set.go(U32.is_zero(e), s, e)

# Sampling (errseq_sample): a new observer's cursor

def Errseq.sample.back(unseen: Bool, +n: Nat) -> Nat:
  match unseen:
    case True{}:
      Nat.sub(n, 1n)
    case False{}:
      n

def Errseq.sample(o: ErrseqOptions, s: Errseq) -> ErrseqCursor:
  match o s:
    case ErrseqOptions{ru} Errseq{n, e, f}:
      ErrseqCursor{Errseq.sample.back(Bool.and(ru, Bool.not(f)), n)}

# Checking (errseq_check): the latest error if the observer is behind,
# None if it has seen everything recorded

def Errseq.check.go(same: Bool, e: U32) -> Maybe<&2, U32>:
  match same:
    case True{}:
      None{}
    case False{}:
      Some{e}

def Errseq.check(s: Errseq, c: ErrseqCursor) -> Maybe<&2, U32>:
  match s c:
    case Errseq{n, e, f} ErrseqCursor{k}:
      Errseq.check.go(Nat.is_eq(k, n), e)

# Checking and advancing (errseq_check_and_advance): as check, and the
# observer's cursor moves to the count, and the latest error is marked seen

def Errseq.advance.go(same: Bool, +n: Nat, +e: U32, f: Bool, +k: Nat) -> ErrseqCheck:
  match same:
    case True{}:
      ErrseqCheck{Errseq{n, e, f}, ErrseqCursor{k}, None{}}
    case False{}:
      ErrseqCheck{Errseq{n, e, True{}}, ErrseqCursor{n}, Some{e}}

def Errseq.check_and_advance(s: Errseq, c: ErrseqCursor) -> ErrseqCheck:
  match s c:
    case Errseq{+n, e, f} ErrseqCursor{+k}:
      Errseq.advance.go(Nat.is_eq(k, n), n, e, f, k)

# Whether a cursor belongs to this state: it is at most the count. Every
# cursor from sample and check_and_advance is, and recording errors and
# other observers' advances keep it so (see LAWS.bend).
def Errseq.cursor_valid(s: Errseq, c: ErrseqCursor) -> Bool:
  match s c:
    case Errseq{n, e, f} ErrseqCursor{k}:
      Nat.is_le(k, n)
