import Base
import ./errseq.bend as E

def show(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{e}:
      "error " ++ U32.show(e)

def seen(r: E.ErrseqCheck) -> String:
  show(E.ErrseqCheck.error(r))

# a file's writeback errors, watched by two open files: A opened before
# any error, B after the first
def main() -> IO(Unit):
  +o = E.ErrseqOptions.default()
  +s0 = E.Errseq.new()
  +a0 = E.Errseq.sample(o, s0)
  +s1 = E.Errseq.set(s0, 5)
  +b0 = E.Errseq.sample(o, s1)
  +ra = E.Errseq.check_and_advance(s1, a0)
  +s2 = E.ErrseqCheck.state(ra)
  +a1 = E.ErrseqCheck.cursor(ra)
  +ra2 = E.Errseq.check_and_advance(s2, a1)
  +s3 = E.Errseq.set(E.Errseq.set(s2, 28), 5)
  +rb = E.Errseq.check_and_advance(s3, b0)
  +s4 = E.Errseq.set(E.Errseq.new(), 5)
  do IO<Unit>:
    IO.print("A after the first error: " ++ seen(ra))
    IO.print("A again: " ++ seen(ra2))
    IO.print("B, sampled after it: " ++ show(E.Errseq.check(s1, b0)))
    IO.print("B after two more: " ++ seen(rb))
    IO.print("A after two more: " ++ show(E.Errseq.check(s3, a1)))
    IO.print("B again: " ++ seen(E.Errseq.check_and_advance(E.ErrseqCheck.state(rb), E.ErrseqCheck.cursor(rb))))
    IO.print("error 0 records nothing: " ++ show(E.Errseq.check(E.Errseq.set(s2, 0), a1)))
    IO.print("unseen, default sample: " ++ show(E.Errseq.check(s4, E.Errseq.sample(o, s4))))
    IO.print("unseen, kernel sample: " ++ show(E.Errseq.check(s4, E.Errseq.sample(E.ErrseqOptions.kernel(), s4))))
    IO.print("seen, kernel sample: " ++ show(E.Errseq.check(s2, E.Errseq.sample(E.ErrseqOptions.kernel(), s2))))

#|A after the first error: error 5
#|A again: none
#|B, sampled after it: none
#|B after two more: error 5
#|A after two more: error 5
#|B again: none
#|error 0 records nothing: none
#|unseen, default sample: none
#|unseen, kernel sample: error 5
#|seen, kernel sample: none
