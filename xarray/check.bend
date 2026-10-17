import Base
import ./xarray.bend as X

def show_index(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{k}:
      U32.show(k)

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def show_entries(xs: List<&2, X.XEntry<U32>>) -> String:
  match xs:
    case Nil{}:
      "."
    case Con{h, t}:
      match h:
        case X.XEntry{k, v}:
          U32.show(k) ++ "=" ++ U32.show(v) ++ " " ++ show_entries(t)

def show_insert(r: Result<&2, &2, X.XArrayError, X.XArray<U32>>) -> String:
  match r:
    case Fail{e}:
      match e:
        case X.XArrayBusy{}:
          "busy"
    case Done{t}:
      show_entries(X.XArray.range(U32, t, 0, 4294967295))

# entries at 0, 5, 6, 2^31 and 2^32 - 1
def sample() -> X.XArray<U32>:
  X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.store(U32, X.XArray.empty(U32), 5, 50), 4294967295, 9), 6, 60), 0, 1), 2147483648, 2)

def marked() -> X.XArray<U32>:
  X.XArray.set_mark(U32, X.XArray.set_mark(U32, X.XArray.set_mark(U32, sample(), 6, X.XMark0{}), 2147483648, X.XMark0{}), 7, X.XMark0{})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show_bool(X.XArray.is_empty(U32, X.XArray.empty(U32))))
    IO.print(show_bool(X.XArray.is_empty(U32, sample())))
    IO.print(show_index(X.XArray.load(U32, sample(), 6)))
    IO.print(show_index(X.XArray.load(U32, sample(), 7)))
    IO.print(show_index(X.XArray.load(U32, X.XArray.erase(U32, sample(), 6), 6)))
    IO.print(show_index(X.XArray.find(U32, sample(), 1)))
    IO.print(show_index(X.XArray.find(U32, sample(), 7)))
    IO.print(show_index(X.XArray.find(U32, X.XArray.erase(U32, sample(), 4294967295), 2147483649)))
    IO.print(show_index(X.XArray.find_last(U32, sample(), 2147483647)))
    IO.print(show_index(X.XArray.find_last(U32, X.XArray.erase(U32, sample(), 0), 4)))
    IO.print(show_entries(X.XArray.range(U32, sample(), 0, 4294967295)))
    IO.print(show_entries(X.XArray.range(U32, sample(), 5, 2147483648)))
    IO.print(show_entries(X.XArray.range(U32, sample(), 7, 100)))
    IO.print(show_bool(X.XArray.get_mark(U32, marked(), 6, X.XMark0{})))
    IO.print(show_bool(X.XArray.get_mark(U32, marked(), 6, X.XMark1{})))
    IO.print(show_bool(X.XArray.get_mark(U32, marked(), 7, X.XMark0{})))
    IO.print(show_index(X.XArray.find_marked(U32, marked(), 0, X.XMark0{})))
    IO.print(show_index(X.XArray.find_marked(U32, marked(), 7, X.XMark0{})))
    IO.print(show_index(X.XArray.find_marked(U32, X.XArray.erase(U32, marked(), 2147483648), 7, X.XMark0{})))
    IO.print(show_index(X.XArray.find_marked(U32, X.XArray.clear_mark(U32, marked(), 6, X.XMark0{}), 0, X.XMark0{})))
    IO.print(show_bool(X.XArray.get_mark(U32, X.XArray.store(U32, marked(), 6, 61), 6, X.XMark0{})))
    IO.print(show_bool(X.XArray.is_empty(U32, X.XArray.erase(U32, X.XArray.erase(U32, X.XArray.erase(U32, X.XArray.erase(U32, X.XArray.erase(U32, sample(), 0), 5), 6), 2147483648), 4294967295))))
    IO.print(show_insert(X.XArray.insert(U32, sample(), 6, 1)))
    IO.print(show_insert(X.XArray.insert(U32, sample(), 7, 70)))

#|true
#|false
#|60
#|none
#|none
#|5
#|2147483648
#|none
#|6
#|none
#|0=1 5=50 6=60 2147483648=2 4294967295=9 .
#|5=50 6=60 2147483648=2 .
#|.
#|true
#|false
#|false
#|6
#|2147483648
#|none
#|2147483648
#|true
#|true
#|busy
#|0=1 5=50 6=60 7=70 2147483648=2 4294967295=9 .
