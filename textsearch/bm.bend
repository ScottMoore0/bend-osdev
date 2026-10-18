# bend-osdev-textsearch, Boyer-Moore (the kernel's ts_bm): the pattern is
# laid against the text and compared from its last byte back; on a mismatch
# or a match it moves right by a shift the pattern alone determines. Two
# shift rules, a parameter:
#
# * TsHorspool: Horspool's bad-character rule, by the text byte under the
#   pattern's last byte: the distance from that byte's last occurrence in
#   the pattern (before its last position) to the end, else the pattern's
#   length;
# * TsGoodSuffix (the default): the larger of Horspool's shift and the
#   strong good-suffix shift: the least shift that lines the matched suffix
#   up with an equal run of the pattern and puts a different byte under the
#   mismatched one (computed from that definition).
#
# Across chunks the search keeps the last m - 1 bytes it has seen (fewer at
# the start): every match ending in a new chunk starts within them or the
# chunk, and none fits in them alone.
import Base
import ./textsearch.bend as T

type TsBmRule is Data:
  TsHorspool{}
  TsGoodSuffix{}

# the pattern (case-folded when icase), its length, the good-suffix shift
# for a mismatch at each position, and the shift after a match
type TsBmConf is Data:
  TsBmConf{icase: Bool, rule: TsBmRule, pat: List<&2, U32>, m: Nat, gs: List<&2, Nat>, gsm: Nat}

# the configuration and the bytes kept from earlier chunks
type TsBm is Data:
  TsBm{conf: TsBmConf, carry: List<&2, U32>}

def ts.bm.rule_default() -> TsBmRule:
  TsGoodSuffix{}

def ts.bm.at(xs: List<&2, U32>, k: Nat) -> U32:
  match xs k:
    case Nil{} _:
      0
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      ts.bm.at(t, j)

def ts.bm.nat_at(xs: List<&2, Nat>, k: Nat) -> Nat:
  match xs k:
    case Nil{} _:
      0n
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      ts.bm.nat_at(t, j)

def ts.bm.pick(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# Horspool's shift for byte b under the pattern's last byte: xs is the
# pattern before its last byte, from position j
def ts.bm.hs.go(xs: List<&2, U32>, +b: U32, +m: Nat, +j: Nat, +r: Nat) -> Nat:
  match xs:
    case Nil{}:
      r
    case Con{x, t}:
      ts.bm.hs.go(t, b, m, 1n+j, ts.bm.pick(U32.is_eq(x, b), Nat.sub(Nat.sub(m, 1n), j), r))

def ts.bm.hs(+pat: List<&2, U32>, +m: Nat, +b: U32) -> Nat:
  ts.bm.hs.go(List.take(&2, U32, pat, Nat.sub(m, 1n)), b, m, 0n, m)

# whether the pattern shifted right by s agrees with itself at positions
# i, i + 1, ... (n of them), where both are defined
def ts.bm.agree.go(n: Nat, +pat: List<&2, U32>, +s: Nat, +i: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+k:
      Bool.and(Bool.or(Nat.is_lt(i, s), U32.is_eq(ts.bm.at(pat, Nat.sub(i, s)), ts.bm.at(pat, i))), ts.bm.agree.go(k, pat, s, 1n+i))

def ts.bm.agree(+pat: List<&2, U32>, +m: Nat, +s: Nat, +lo: Nat) -> Bool:
  ts.bm.agree.go(Nat.sub(m, lo), pat, s, lo)

# whether shift s is consistent with a mismatch at position j: the matched
# suffix after j agrees, and a different byte comes under position j
def ts.bm.gs.ok(+pat: List<&2, U32>, +m: Nat, +j: Nat, +s: Nat) -> Bool:
  Bool.and(ts.bm.agree(pat, m, s, 1n+j), Bool.or(Nat.is_lt(j, s), Bool.not(U32.is_eq(ts.bm.at(pat, Nat.sub(j, s)), ts.bm.at(pat, j)))))

def ts.bm.gs.least(fuel: Nat, +pat: List<&2, U32>, +m: Nat, +j: Nat, +s: Nat) -> Nat:
  match fuel:
    case 0n:
      m
    case 1n+f:
      ts.bm.pick(ts.bm.gs.ok(pat, m, j, s), s, ts.bm.gs.least(f, pat, m, j, 1n+s))

def ts.bm.gs.table(n: Nat, +pat: List<&2, U32>, +m: Nat, +j: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{ts.bm.gs.least(m, pat, m, j, 1n), ts.bm.gs.table(k, pat, m, 1n+j)}

# the least shift after a match: the pattern's period
def ts.bm.gs.period(fuel: Nat, +pat: List<&2, U32>, +m: Nat, +s: Nat) -> Nat:
  match fuel:
    case 0n:
      m
    case 1n+f:
      ts.bm.pick(ts.bm.agree(pat, m, s, 0n), s, ts.bm.gs.period(f, pat, m, 1n+s))

def ts.bm.conf(+icase: Bool, rule: TsBmRule, p: List<&2, U32>) -> TsBmConf:
  +fp = T.ts.fold_all(icase, p)
  +m = List.length(&2, U32, fp)
  TsBmConf{icase, rule, fp, m, ts.bm.gs.table(m, fp, m, 0n), ts.bm.gs.period(m, fp, m, 1n)}

# the state before any text
def ts.bm.start(+icase: Bool, rule: TsBmRule, p: List<&2, U32>) -> TsBm:
  TsBm{ts.bm.conf(icase, rule, p), Nil{}}

# One window

# how many bytes match from the front of two lists (the pattern and the
# window, both reversed)
def ts.bm.common(+icase: Bool, xs: List<&2, U32>, ys: List<&2, U32>) -> Nat:
  match xs ys:
    case Nil{} _:
      0n
    case Con{a, at} Nil{}:
      0n
    case Con{a, at} Con{b, bt}:
      ts.bm.pick(U32.is_eq(a, T.ts.fold(icase, b)), 1n+ts.bm.common(icase, at, bt), 0n)

# the outcome of a window: whether the pattern is there, and the shift
type TsBmLook is Data:
  TsBmLook{hit: Bool, shift: Nat}

def ts.bm.shift(rule: TsBmRule, +h: Nat, +g: Nat) -> Nat:
  match rule:
    case TsHorspool{}:
      h
    case TsGoodSuffix{}:
      Nat.max(h, g)

def ts.bm.look(c: TsBmConf, +win: List<&2, U32>) -> TsBmLook:
  match c:
    case TsBmConf{+icase, rule, +pat, +m, gs, +gsm}:
      +k = ts.bm.common(icase, List.reverse(&2, U32, pat), List.reverse(&2, U32, win))
      +full = Bool.and(Nat.is_eq(List.length(&2, U32, win), m), Nat.is_eq(k, m))
      +h = ts.bm.hs(pat, m, T.ts.fold(icase, ts.bm.at(win, Nat.sub(m, 1n))))
      TsBmLook{full, ts.bm.shift(rule, h, ts.bm.pick(full, gsm, ts.bm.nat_at(gs, Nat.sub(Nat.sub(m, 1n), k))))}

def ts.bm.hit(l: TsBmLook) -> Bool:
  match l:
    case TsBmLook{h, s}:
      h

def ts.bm.step(l: TsBmLook) -> Nat:
  match l:
    case TsBmLook{h, s}:
      Nat.max(s, 1n)

def ts.bm.m(c: TsBmConf) -> Nat:
  match c:
    case TsBmConf{i, r, p, m, g, gm}:
      m

def ts.bm.emit(hit: Bool, +e: Nat, ms: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      Con{e, ms}
    case False{}:
      ms

# the ends of the matches in w, its first byte at offset off; fuel bounds
# the windows (each moves right at least one byte)
def ts.bm.scan(fuel: Nat, +c: TsBmConf, w: List<&2, U32>, +off: Nat) -> List<&2, Nat>:
  match fuel w:
    case 0n _:
      Nil{}
    case 1n+f Nil{}:
      Nil{}
    case 1n+f Con{+x, +t}:
      +l = ts.bm.look(c, List.take(&2, U32, Con{x, t}, ts.bm.m(c)))
      +s = ts.bm.step(l)
      ts.bm.emit(ts.bm.hit(l), Nat.add(off, ts.bm.m(c)), ts.bm.scan(f, c, List.drop(&2, U32, Con{x, t}, s), Nat.add(off, s)))

# The textsearch interface

def ts.bm.feed.go(+c: TsBmConf, +m: Nat, +buf: List<&2, U32>, +base: Nat) -> TsBm & List<&2, Nat>:
  match m:
    case 0n:
      (TsBm{c, Nil{}}, Nil{})
    case 1n+k:
      +n = List.length(&2, U32, buf)
      (TsBm{c, List.drop(&2, U32, buf, Nat.sub(n, k))}, ts.bm.scan(1n+n, c, buf, base))

# a chunk of bytes, the first at offset pos: searched after the kept bytes
def ts.bm.feed(s: TsBm, pos: Nat, xs: List<&2, U32>) -> TsBm & List<&2, Nat>:
  match s:
    case TsBm{+c, +carry}:
      ts.bm.feed.go(c, ts.bm.m(c), List.append(&2, U32, carry, xs), Nat.sub(pos, List.length(&2, U32, carry)))

def ts.bm.snd(r: TsBm & List<&2, Nat>) -> List<&2, Nat>:
  match r:
    case (s, ms):
      ms

# the ends of the occurrences of p in the text xs
def ts.bm.ends(+icase: Bool, rule: TsBmRule, p: List<&2, U32>, xs: List<&2, U32>) -> List<&2, Nat>:
  ts.bm.snd(ts.bm.feed(ts.bm.start(icase, rule, p), 0n, xs))

# the ends of the occurrences of p in the text arriving as the chunks cs
def ts.bm.search(+icase: Bool, rule: TsBmRule, p: List<&2, U32>, cs: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  T.ts.run(~TsBm, ~ts.bm.feed, ts.bm.start(icase, rule, p), 0n, cs)
