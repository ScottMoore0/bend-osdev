# bend-osdev-kstr, option parsing in the manner of the kernel's match_token
# and its match_int, match_uint, match_octal and match_hex helpers (as their
# documentation describes): an option string is split at commas (empty
# pieces skipped), and each piece is matched against a table of patterns;
# the first pattern that matches the whole piece wins, with its arguments.
#
# In a pattern, a byte matches itself, and a conversion matches an argument:
# %d an optional '-' and decimal digits, %u decimal digits, %o octal digits,
# %x hex digits (each at least one digit, taken greedily), %s the rest of
# the piece (at least one byte, so %s ends a pattern), %% a percent sign.
import Base
import ../bytes/bytes.bend as B
import ./kstr.bend as K

type KStrPattern is Data:
  KStrPattern{token: U32, pattern: B.Octets}

type KStrMatch is Data:
  KStrMatch{token: U32, args: List<&2, B.Octets>}

# A pattern, read once into items

type KOptItem is Data:
  KOLit{c: U32}
  KOSigned{}
  KODec{}
  KOOct{}
  KOHex{}
  KOStr{}
  KOBad{}

def kopt.conv.pick(d: Bool, u: Bool, o: Bool, x: Bool, s: Bool, p: Bool) -> KOptItem:
  match d u o x s p:
    case True{} _ _ _ _ _:
      KOSigned{}
    case False{} True{} _ _ _ _:
      KODec{}
    case False{} False{} True{} _ _ _:
      KOOct{}
    case False{} False{} False{} True{} _ _:
      KOHex{}
    case False{} False{} False{} False{} True{} _:
      KOStr{}
    case False{} False{} False{} False{} False{} True{}:
      KOLit{37}
    case False{} False{} False{} False{} False{} False{}:
      KOBad{}

def kopt.conv(+c: U32) -> KOptItem:
  kopt.conv.pick(U32.is_eq(c, 100), U32.is_eq(c, 117), U32.is_eq(c, 111), U32.is_eq(c, 120), U32.is_eq(c, 115), U32.is_eq(c, 37))

def kopt.head_is(+c: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      U32.is_eq(h, c)

# the pattern's items (pct: the head is '%')
def kopt.items(xs: List<&2, U32>, pct: Bool) -> List<&2, KOptItem>:
  match xs pct:
    case Nil{} _:
      Nil{}
    case Con{c, Nil{}} True{}:
      [KOBad{}]
    case Con{c, Con{d, +t}} True{}:
      Con{kopt.conv(d), kopt.items(t, kopt.head_is(37, t))}
    case Con{c, +t} False{}:
      Con{KOLit{c}, kopt.items(t, kopt.head_is(37, t))}

# Classes of bytes: 0 decimal, 1 octal, 2 hex

def kopt.in.pick(dec: Bool, oct: Bool, +c: U32) -> Bool:
  match dec oct:
    case True{} _:
      Bool.and(U32.is_le(48, c), U32.is_le(c, 57))
    case False{} True{}:
      Bool.and(U32.is_le(48, c), U32.is_le(c, 55))
    case False{} False{}:
      Bool.or(Bool.and(U32.is_le(48, c), U32.is_le(c, 57)), Bool.or(Bool.and(U32.is_le(97, c), U32.is_le(c, 102)), Bool.and(U32.is_le(65, c), U32.is_le(c, 70))))

def kopt.in(+cls: U32, +c: U32) -> Bool:
  kopt.in.pick(U32.is_eq(cls, 0), U32.is_eq(cls, 1), c)

def kopt.head_in(+cls: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{c, t}:
      kopt.in(cls, c)

# how many bytes from the front of xs are in the class (ok: the head is)
def kopt.span(xs: List<&2, U32>, ok: Bool, +cls: U32, n: Nat) -> Nat:
  match xs ok:
    case Con{c, +t} True{}:
      kopt.span(t, kopt.head_in(cls, t), cls, 1n+n)
    case _ _:
      n

def kopt.span_of(+cls: U32, +xs: List<&2, U32>) -> Nat:
  kopt.span(xs, kopt.head_in(cls, xs), cls, 0n)

def kopt.minus.pick(m: Bool) -> Nat:
  match m:
    case True{}:
      1n
    case False{}:
      0n

def kopt.minus(xs: List<&2, U32>) -> Nat:
  kopt.minus.pick(kopt.head_is(45, xs))

# the state: the rest of the piece, the arguments so far (reversed), and
# whether the match has failed
type KOptSt is Data:
  KOptSt{s: List<&2, U32>, args: List<&2, B.Octets>, bad: Bool}

# n bytes as an argument (none, or extra set, is a failure)
def kopt.take(+n: Nat, extra: Bool, st: KOptSt) -> KOptSt:
  match st:
    case KOptSt{+s, args, bad}:
      KOptSt{B.drop(n, s), Con{B.Octets.of_list(B.take(n, s)), args}, Bool.or(bad, Bool.or(Nat.is_eq(n, 0n), extra))}

def kopt.signed(+m: Nat, st: KOptSt) -> KOptSt:
  match st:
    case KOptSt{+s, args, bad}:
      +d = kopt.span_of(0, B.drop(m, s))
      kopt.take(Nat.add(m, d), Nat.is_eq(d, 0n), KOptSt{s, args, bad})

def kopt.item.go(i: KOptItem, +s: List<&2, U32>, args: List<&2, B.Octets>, bad: Bool) -> KOptSt:
  match i:
    case KOLit{+c}:
      KOptSt{B.drop(1n, s), args, Bool.or(bad, Bool.not(kopt.head_is(c, s)))}
    case KOSigned{}:
      kopt.signed(kopt.minus(s), KOptSt{s, args, bad})
    case KODec{}:
      kopt.take(kopt.span_of(0, s), False{}, KOptSt{s, args, bad})
    case KOOct{}:
      kopt.take(kopt.span_of(1, s), False{}, KOptSt{s, args, bad})
    case KOHex{}:
      kopt.take(kopt.span_of(2, s), False{}, KOptSt{s, args, bad})
    case KOStr{}:
      kopt.take(B.len(s), False{}, KOptSt{s, args, bad})
    case KOBad{}:
      KOptSt{s, args, True{}}

def kopt.item(i: KOptItem, st: KOptSt) -> KOptSt:
  match st:
    case KOptSt{+s, args, bad}:
      kopt.item.go(i, s, args, bad)

def kopt.run(its: List<&2, KOptItem>, st: KOptSt) -> KOptSt:
  match its:
    case Nil{}:
      st
    case Con{i, rest}:
      kopt.run(rest, kopt.item(i, st))

def kopt.rev(xs: List<&2, B.Octets>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      kopt.rev(t, Con{h, acc})

def kopt.done.pick(ok: Bool, +token: U32, args: List<&2, B.Octets>) -> Maybe<&2, KStrMatch>:
  match ok:
    case True{}:
      Some{KStrMatch{token, kopt.rev(args, Nil{})}}
    case False{}:
      None{}

def kopt.done(+token: U32, st: KOptSt) -> Maybe<&2, KStrMatch>:
  match st:
    case KOptSt{s, args, bad}:
      kopt.done.pick(Bool.and(Bool.not(bad), B.list_eq(s, Nil{})), token, args)

# whether the piece s matches the pattern p, with its arguments
def KStr.match_one(p: KStrPattern, s: B.Octets) -> Maybe<&2, KStrMatch>:
  match p:
    case KStrPattern{+token, pat}:
      +xs = B.Octets.to_list(pat)
      kopt.done(token, kopt.run(kopt.items(xs, kopt.head_is(37, xs)), KOptSt{B.Octets.to_list(s), Nil{}, False{}}))

def kopt.or(a: Maybe<&2, KStrMatch>, b: Maybe<&2, KStrMatch>) -> Maybe<&2, KStrMatch>:
  match a:
    case Some{m}:
      Some{m}
    case None{}:
      b

# the first pattern of the table that matches s (match_token)
def KStr.match_token(+s: B.Octets, table: List<&2, KStrPattern>) -> Maybe<&2, KStrMatch>:
  match table:
    case Nil{}:
      None{}
    case Con{p, rest}:
      kopt.or(KStr.match_one(p, s), KStr.match_token(s, rest))

# an argument as a number: match_int (signed) and match_uint in base 0,
# match_octal in base 8, match_hex in base 16
def KStr.match_int(o: B.Octets) -> Result<&2, &2, K.KStrError, U32>:
  K.KStr.to_s32(o, 0)

def KStr.match_uint(o: B.Octets) -> Result<&2, &2, K.KStrError, U32>:
  K.KStr.to_u32(o, 0)

def KStr.match_octal(o: B.Octets) -> Result<&2, &2, K.KStrError, U32>:
  K.KStr.to_u32(o, 8)

def KStr.match_hex(o: B.Octets) -> Result<&2, &2, K.KStrError, U32>:
  K.KStr.to_u32(o, 16)

# Splitting at commas, skipping empty pieces (comma: the head is a comma)

def kopt.push.pick(empty: Bool, cur: List<&2, U32>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match empty:
    case True{}:
      acc
    case False{}:
      Con{B.Octets.of_list(B.rev(cur)), acc}

def kopt.push(+cur: List<&2, U32>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  kopt.push.pick(B.list_eq(cur, Nil{}), cur, acc)

def kopt.split(xs: List<&2, U32>, comma: Bool, +cur: List<&2, U32>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs comma:
    case Nil{} _:
      kopt.rev(kopt.push(cur, acc), Nil{})
    case Con{c, +t} True{}:
      kopt.split(t, kopt.head_is(44, t), Nil{}, kopt.push(cur, acc))
    case Con{c, +t} False{}:
      kopt.split(t, kopt.head_is(44, t), Con{c, cur}, acc)

# the pieces of an option string, split at commas, empty ones skipped
def KStr.split_options(o: B.Octets) -> List<&2, B.Octets>:
  +xs = B.Octets.to_list(o)
  kopt.split(xs, kopt.head_is(44, xs), Nil{}, Nil{})
