# Examples, then exhaustive comparisons with the reference on small
# alphabets: every pattern and text up to a length, the text whole, split
# in two at every offset, and one byte per chunk. Each count line is the
# number of disagreements, then the number of comparisons.
import Base
import ../bytes/bytes.bend as B
import ./textsearch.bend as T
import ./naive.bend as V
import ./kmp.bend as K
import ./bm.bend as M
import ./fsm.bend as F

def show_ns(ms: List<&2, Nat>) -> String:
  match ms:
    case Nil{}:
      "-"
    case Con{m, Nil{}}:
      Nat.show(m)
    case Con{m, t}:
      Nat.show(m) ++ " " ++ show_ns(t)

def show_m(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{n}:
      Nat.show(n)

def str(s: String) -> List<&2, U32>:
  B.Octets.to_list(B.Octets.of_string(s))

def oct(s: String) -> B.Octets:
  B.Octets.of_string(s)

def nat_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, at} Con{b, bt}:
      Bool.and(Nat.is_eq(a, b), nat_eq(at, bt))
    case _ _:
      False{}

# Enumerating words

def prepend(+c: U32, ws: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, t}:
      Con{Con{c, w}, prepend(c, t)}

def words.go(as: List<&2, U32>, +ws: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match as:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      List.append(&2, List<&2, U32>, prepend(a, ws), words.go(t, ws))

# the words of exactly n letters
def words(+as: List<&2, U32>, n: Nat) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      [Nil{}]
    case 1n+k:
      words.go(as, words(as, k))

# the words of lo to hi letters
def upto(k: Nat, +as: List<&2, U32>, +lo: Nat) -> List<&2, List<&2, U32>>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      List.append(&2, List<&2, U32>, words(as, lo), upto(r, as, 1n+lo))

# a text split in two at every offset, and as one chunk per byte
def splits.go(k: Nat, +xs: List<&2, U32>, +i: Nat) -> List<&2, List<&2, List<&2, U32>>>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      Con{[List.take(&2, U32, xs, i), List.drop(&2, U32, xs, i)], splits.go(r, xs, 1n+i)}

def singles(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{[c], singles(t)}

def splits(+xs: List<&2, U32>) -> List<&2, List<&2, List<&2, U32>>>:
  Con{[xs], Con{singles(xs), splits.go(1n+List.length(&2, U32, xs), xs, 0n)}}

# Counting disagreements

type Tally is Data:
  Tally{bad: Nat, all: Nat}

def tally.add(t: Tally, ok: Bool) -> Tally:
  match t ok:
    case Tally{b, a} True{}:
      Tally{b, 1n+a}
    case Tally{b, a} False{}:
      Tally{1n+b, 1n+a}

def show_t(name: String, t: Tally) -> String:
  match t:
    case Tally{b, a}:
      name ++ " " ++ Nat.show(b) ++ " of " ++ Nat.show(a)

# a search over chunks, against the expected ends
def by_splits(+icase: Bool, +p: List<&2, U32>, +want: List<&2, Nat>, ss: List<&2, List<&2, List<&2, U32>>>, t: Tally) -> Tally:
  match ss:
    case Nil{}:
      t
    case Con{+cs, r}:
      +ok = Bool.and(nat_eq(K.ts.kmp.search(icase, p, cs), want), Bool.and(nat_eq(M.ts.bm.search(icase, M.TsGoodSuffix{}, p, cs), want), nat_eq(M.ts.bm.search(icase, M.TsHorspool{}, p, cs), want)))
      by_splits(icase, p, want, r, tally.add(t, ok))

def by_texts(+icase: Bool, +p: List<&2, U32>, xs: List<&2, List<&2, U32>>, t: Tally) -> Tally:
  match xs:
    case Nil{}:
      t
    case Con{+x, r}:
      by_texts(icase, p, r, by_splits(icase, p, V.ts.naive.ends(icase, p, x), splits(x), t))

def by_pats(+icase: Bool, ps: List<&2, List<&2, U32>>, +xs: List<&2, List<&2, U32>>, t: Tally) -> Tally:
  match ps:
    case Nil{}:
      t
    case Con{+p, r}:
      by_pats(icase, r, xs, by_texts(icase, p, xs, t))

# the token automaton against its reference
def fsm_splits(+tks: List<&2, F.TsToken>, +want: List<&2, Nat>, ss: List<&2, List<&2, List<&2, U32>>>, t: Tally) -> Tally:
  match ss:
    case Nil{}:
      t
    case Con{+cs, r}:
      fsm_splits(tks, want, r, tally.add(t, nat_eq(F.ts.fsm.search(tks, cs), want)))

def fsm_texts(+tks: List<&2, F.TsToken>, xs: List<&2, List<&2, U32>>, t: Tally) -> Tally:
  match xs:
    case Nil{}:
      t
    case Con{+x, r}:
      fsm_texts(tks, r, fsm_splits(tks, F.ts.fsm.naive(tks, x), splits(x), t))

def fsm_pats(ps: List<&2, List<&2, F.TsToken>>, +xs: List<&2, List<&2, U32>>, t: Tally) -> Tally:
  match ps:
    case Nil{}:
      t
    case Con{+p, r}:
      fsm_pats(r, xs, fsm_texts(p, xs, t))

# literal tokens against the plain reference
def lit_texts(+p: List<&2, U32>, xs: List<&2, List<&2, U32>>, t: Tally) -> Tally:
  match xs:
    case Nil{}:
      t
    case Con{+x, r}:
      lit_texts(p, r, tally.add(t, nat_eq(F.ts.fsm.ends(F.ts.fsm.literal(p), x), V.ts.naive.ends(False{}, p, x))))

def lit_pats(ps: List<&2, List<&2, U32>>, +xs: List<&2, List<&2, U32>>, t: Tally) -> Tally:
  match ps:
    case Nil{}:
      t
    case Con{+p, r}:
      lit_pats(r, xs, lit_texts(p, xs, t))

def classes() -> List<&2, F.TsClass>:
  [F.TsIs{97}, F.TsIs{98}, F.TsAnyByte{}]

def recurs() -> List<&2, F.TsRecur>:
  [F.TsOne{}, F.TsPerhaps{}, F.TsStar{}, F.TsPlus{}]

def tokens.go(+cl: F.TsClass, rs: List<&2, F.TsRecur>) -> List<&2, F.TsToken>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{F.TsToken{cl, r}, tokens.go(cl, t)}

def tokens(cs: List<&2, F.TsClass>) -> List<&2, F.TsToken>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      List.append(&2, F.TsToken, tokens.go(c, recurs()), tokens(t))

def pairs.go(+a: F.TsToken, bs: List<&2, F.TsToken>) -> List<&2, List<&2, F.TsToken>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{[a, b], pairs.go(a, t)}

def pairs(as: List<&2, F.TsToken>, +bs: List<&2, F.TsToken>) -> List<&2, List<&2, F.TsToken>>:
  match as:
    case Nil{}:
      Nil{}
    case Con{+a, t}:
      List.append(&2, List<&2, F.TsToken>, pairs.go(a, bs), pairs(t, bs))

def singles_t(ts: List<&2, F.TsToken>) -> List<&2, List<&2, F.TsToken>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{[a], singles_t(t)}

def token_pats() -> List<&2, List<&2, F.TsToken>>:
  +ts = tokens(classes())
  List.append(&2, List<&2, F.TsToken>, singles_t(ts), pairs(ts, ts))

def ab() -> List<&2, U32>:
  [97, 98]

def zero() -> Tally:
  Tally{0n, 0n}

# Examples

def kmp(s: String) -> K.TsKmp:
  K.ts.kmp.start(T.ts.exact(), str(s))

def text() -> List<&2, B.Octets>:
  [oct("the quick bro"), oct("wn fox, the qu"), oct("ick brown dog")]

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show_ns(T.ts.find_all(~K.TsKmp, ~K.ts.kmp.feed, kmp("quick"), text())))
    IO.print(show_ns(T.ts.starts(5n, T.ts.find_all(~K.TsKmp, ~K.ts.kmp.feed, kmp("brown"), text()))))
    IO.print(show_m(T.ts.find(~M.TsBm, ~M.ts.bm.feed, M.ts.bm.start(T.ts.exact(), M.ts.bm.rule_default(), str("fox")), text())))
    IO.print(show_ns(T.ts.find_all(~M.TsBm, ~M.ts.bm.feed, M.ts.bm.start(True{}, M.TsHorspool{}, str("THE")), text())))
    IO.print(show_ns(K.ts.kmp.ends(True{}, str("ABA"), str("abababa"))))
    IO.print(show_ns(M.ts.bm.ends(False{}, M.TsGoodSuffix{}, str("aaa"), str("aaaaaa"))))
    IO.print(show_ns(F.ts.fsm.search([F.TsToken{F.TsIs{120}, F.TsOne{}}, F.TsToken{F.ts.fsm.digit(), F.TsPlus{}}, F.TsToken{F.TsIs{121}, F.TsPerhaps{}}], [str("ax12y x"), str("3 x yx9")])))
    IO.print(show_ns(F.ts.fsm.ends([F.TsToken{F.TsAnyByte{}, F.TsStar{}}, F.TsToken{F.TsIs{98}, F.TsOne{}}], str("abcab"))))
    IO.print(show_ns(K.ts.kmp.ends(False{}, Nil{}, str("abc"))))
    IO.print(show_t("plain", by_pats(False{}, upto(5n, ab(), 1n), upto(11n, ab(), 0n), zero())))
    IO.print(show_t("abc", by_pats(False{}, upto(3n, [97, 98, 99], 1n), upto(7n, [97, 98, 99], 0n), zero())))
    IO.print(show_t("icase", by_pats(True{}, upto(2n, [65, 97, 98], 1n), upto(6n, [65, 97, 98], 0n), zero())))
    IO.print(show_t("literal", lit_pats(upto(4n, ab(), 1n), upto(9n, ab(), 0n), zero())))
    IO.print(show_t("tokens", fsm_pats(token_pats(), upto(8n, ab(), 0n), zero())))

#|9 30
#|10 31
#|19
#|3 24
#|3 5 7
#|3 4 5 6
#|3 4 5 8 14
#|2 5
#|-
#|plain 0 of 1523650
#|abc 0 of 362466
#|icase 0 of 32796
#|literal 0 of 15330
#|tokens 0 of 359268
