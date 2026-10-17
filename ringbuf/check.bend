import Base
import ./ringbuf.bend as R

def show_list(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      "-"
    case Con{x, Nil{}}:
      U32.show(x)
    case Con{x, t}:
      U32.show(x) ++ "," ++ show_list(t)

def show_res(res: Result<&2, &2, R.RingError, U32>) -> String:
  match res:
    case Done{x}:
      U32.show(x)
    case Fail{R.RingFull{}}:
      "RingFull"
    case Fail{R.RingEmpty{}}:
      "RingEmpty"

def show_push(res: Result<&2, &2, R.RingError, Unit>) -> String:
  match res:
    case Done{u}:
      "ok"
    case Fail{R.RingFull{}}:
      "RingFull"
    case Fail{R.RingEmpty{}}:
      "RingEmpty"

def ring_of(p: R.RingBuf & Nat) -> R.RingBuf:
  (r, n) = p
  r

def ring_out(p: R.RingBuf & List<&2, U32>) -> R.RingBuf:
  (r, xs) = p
  r

def count(p: R.RingBuf & Nat) -> String:
  (r, n) = p
  Nat.show(n)

def got(p: R.RingBuf & List<&2, U32>) -> String:
  (r, xs) = p
  show_list(xs)

def popped(p: R.RingBuf & Result<&2, &2, R.RingError, U32>) -> String:
  (r, res) = p
  show_res(res)

def pushed(p: R.RingBuf & Result<&2, &2, R.RingError, Unit>) -> String:
  (r, res) = p
  show_push(res)

def len(p: R.RingBuf & Nat) -> String:
  (r, n) = p
  Nat.show(n)

# a ring of 4 slots holding 3, 4, 5, 6 after 1, 2 went through: its
# counters have passed the end of the slots
def four() -> R.RingBuf:
  ring_of(R.ring.push_list(ring_out(R.ring.pop_list(ring_of(R.ring.push_list(R.ring.new(2n), [1, 2])), 2n)), [3, 4, 5, 6]))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(count(R.ring.capacity(R.ring.new_default())))
    IO.print(count(R.ring.push_list(R.ring.new(2n), [1, 2, 3, 4, 5, 6])))
    IO.print(got(R.ring.pop_list(four(), 9n)))
    IO.print(pushed(R.ring.push(four(), 7)))
    IO.print(popped(R.ring.peek(four())) ++ " " ++ len(R.ring.len(four())))
    IO.print(popped(R.ring.pop(R.ring.new(3n))))
    IO.print(got(R.ring.pop_list(ring_of(R.ring.push_list(ring_out(R.ring.pop_list(four(), 3n)), [7, 8, 9])), 9n)))
    IO.print(len(R.ring.avail(ring_out(R.ring.pop_list(four(), 1n)))))

#|256
#|4
#|3,4,5,6
#|RingFull
#|3 4
#|RingEmpty
#|6,7,8,9
#|1
