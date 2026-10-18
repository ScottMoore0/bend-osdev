# bend-osdev-apparmor: the profile language's tokens (apparmor.d(5),
# "FORMAT"), and the terms a rule is written in.
#
# Tokens: words, quoted strings, { } ( ) and the comma that ends a rule. '#'
# at the start of a token begins a comment to the end of the line, except
# "#include". Inside a word a '{' ... '}' group is part of the word (a glob),
# so are ',' inside it and a ',' followed by a word character; a word ends
# at white space, a '"', a ',' before white space, the end, '}', ')', '#' or
# ',', a '(' after '=', a ')' inside parentheses, and a '}' outside a group.
#
# Terms: a rule's tokens read as words, quoted strings, parenthesised lists,
# conditions key=value and the arrow ->.
import Base
import ./text.bend as X

type AaTok is Data:
  AaTWord{text: List<&2, U32>, line: U32}
  AaTQuoted{text: List<&2, U32>, line: U32}
  AaTOpen{line: U32}
  AaTClose{line: U32}
  AaTLParen{line: U32}
  AaTRParen{line: U32}
  AaTComma{line: U32}

def AaTok.line(t: AaTok) -> U32:
  match t:
    case AaTWord{x, l}:
      l
    case AaTQuoted{x, l}:
      l
    case AaTOpen{l}:
      l
    case AaTClose{l}:
      l
    case AaTLParen{l}:
      l
    case AaTRParen{l}:
      l
    case AaTComma{l}:
      l

# the token is the word s
def AaTok.is(t: AaTok, s: String) -> Bool:
  match t:
    case AaTWord{x, l}:
      X.AaText.is(x, s)
    case AaTQuoted{x, l}:
      False{}
    case AaTOpen{l}:
      False{}
    case AaTClose{l}:
      False{}
    case AaTLParen{l}:
      False{}
    case AaTRParen{l}:
      False{}
    case AaTComma{l}:
      False{}

# The lexer

type AaLxMode is Data:
  AaLxSpace{}
  AaLxWord{acc: List<&2, U32>, depth: Nat}
  AaLxQuote{acc: List<&2, U32>, esc: Bool}
  AaLxHash{n: Nat}
  AaLxComment{}

# mode, current line, parenthesis depth, tokens (last first), still well
# formed, and the line of the first fault
type AaLex is Data:
  AaLex{mode: AaLxMode, line: U32, pdepth: Nat, out: List<&2, AaTok>, ok: Bool, bad: U32}

type AaLxCh is Data:
  AaLxCWs{}
  AaLxCNl{}
  AaLxCHash{}
  AaLxCOpen{}
  AaLxCClose{}
  AaLxCLP{}
  AaLxCRP{}
  AaLxCComma{}
  AaLxCQuote{}
  AaLxCOther{}

def AaLxCh.ws(+h: U32) -> Bool:
  Bool.or(U32.is_eq(h, 32), Bool.or(U32.is_eq(h, 9), Bool.or(U32.is_eq(h, 13), Bool.or(U32.is_eq(h, 11), U32.is_eq(h, 12)))))

def AaLxCh.of(+h: U32) -> AaLxCh:
  Bool.pick(AaLxCh, AaLxCh.ws(h), AaLxCWs{}, Bool.pick(AaLxCh, U32.is_eq(h, 10), AaLxCNl{}, Bool.pick(AaLxCh, U32.is_eq(h, 35), AaLxCHash{}, Bool.pick(AaLxCh, U32.is_eq(h, 123), AaLxCOpen{}, Bool.pick(AaLxCh, U32.is_eq(h, 125), AaLxCClose{}, Bool.pick(AaLxCh, U32.is_eq(h, 40), AaLxCLP{}, Bool.pick(AaLxCh, U32.is_eq(h, 41), AaLxCRP{}, Bool.pick(AaLxCh, U32.is_eq(h, 44), AaLxCComma{}, Bool.pick(AaLxCh, U32.is_eq(h, 34), AaLxCQuote{}, AaLxCOther{})))))))))

# a character after which a ',' ends a word: white space, the end, '}', ')', '#', ','
def AaLxCh.ends(+n: U32) -> Bool:
  Bool.or(AaLxCh.ws(n), Bool.or(U32.is_eq(n, 10), Bool.or(U32.is_eq(n, 0), Bool.or(U32.is_eq(n, 125), Bool.or(U32.is_eq(n, 41), Bool.or(U32.is_eq(n, 35), U32.is_eq(n, 44)))))))

def AaLex.fail(st: AaLex) -> AaLex:
  match st:
    case AaLex{m, +l, p, out, +ok, bad}:
      AaLex{AaLxSpace{}, l, p, out, False{}, Bool.pick(U32, ok, l, bad)}

def AaLex.mode(st: AaLex, m: AaLxMode) -> AaLex:
  match st:
    case AaLex{m0, l, p, out, ok, bad}:
      AaLex{m, l, p, out, ok, bad}

def AaLex.push(st: AaLex, t: AaTok) -> AaLex:
  match st:
    case AaLex{m, l, p, out, ok, bad}:
      AaLex{AaLxSpace{}, l, p, Con{t, out}, ok, bad}

def AaLex.line(st: AaLex) -> U32:
  match st:
    case AaLex{m, l, p, out, ok, bad}:
      l

def AaLex.pdepth(st: AaLex) -> Nat:
  match st:
    case AaLex{m, l, p, out, ok, bad}:
      p

# one more line, the mode unchanged
def AaLex.bump(st: AaLex) -> AaLex:
  match st:
    case AaLex{m, l, p, out, ok, bad}:
      AaLex{m, U32.add(l, 1), p, out, ok, bad}

def AaLex.newline(st: AaLex) -> AaLex:
  AaLex.mode(AaLex.bump(st), AaLxSpace{})

def AaLex.open_paren(st: AaLex) -> AaLex:
  match st:
    case AaLex{m, +l, p, out, ok, bad}:
      AaLex{AaLxSpace{}, l, 1n+p, Con{AaTLParen{l}, out}, ok, bad}

def AaLex.close_paren.go(p: Nat, st: AaLex) -> AaLex:
  match p:
    case 0n:
      AaLex.fail(st)
    case 1n+q:
      match st:
        case AaLex{m, +l, p0, out, ok, bad}:
          AaLex{AaLxSpace{}, l, q, Con{AaTRParen{l}, out}, ok, bad}

def AaLex.close_paren(+st: AaLex) -> AaLex:
  AaLex.close_paren.go(AaLex.pdepth(st), st)

# the last token is the word "->": a '{' after it starts a pattern
# (change_profile -> {a,b}), not a block
def AaLex.after_arrow(st: AaLex) -> Bool:
  match st:
    case AaLex{m, l, p, out, ok, bad}:
      match out:
        case Nil{}:
          False{}
        case Con{t, rest}:
          AaTok.is(t, "->")

def AaLex.open(+st: AaLex) -> AaLex:
  Bool.pick(AaLex, AaLex.after_arrow(st), AaLex.mode(st, AaLxWord{[123], 1n}), AaLex.push(st, AaTOpen{AaLex.line(st)}))

# a character between tokens
def AaLex.space.go(k: AaLxCh, +st: AaLex, h: U32) -> AaLex:
  match k:
    case AaLxCOther{}:
      AaLex.mode(st, AaLxWord{[h], 0n})
    case AaLxCWs{}:
      st
    case AaLxCNl{}:
      AaLex.newline(st)
    case AaLxCHash{}:
      AaLex.mode(st, AaLxHash{0n})
    case AaLxCOpen{}:
      AaLex.open(st)
    case AaLxCClose{}:
      AaLex.push(st, AaTClose{AaLex.line(st)})
    case AaLxCLP{}:
      AaLex.open_paren(st)
    case AaLxCRP{}:
      AaLex.close_paren(st)
    case AaLxCComma{}:
      AaLex.push(st, AaTComma{AaLex.line(st)})
    case AaLxCQuote{}:
      AaLex.mode(st, AaLxQuote{Nil{}, False{}})

def AaLex.space(st: AaLex, +h: U32) -> AaLex:
  AaLex.space.go(AaLxCh.of(h), st, h)

# the word in acc (last character first) ends
def AaLex.word_end(+st: AaLex, acc: List<&2, U32>) -> AaLex:
  AaLex.push(st, AaTWord{X.AaText.rev(acc), AaLex.line(st)})

def AaLex.keep(st: AaLex, acc: List<&2, U32>, depth: Nat, h: U32) -> AaLex:
  AaLex.mode(st, AaLxWord{Con{h, acc}, depth})

def AaLex.word.comma(keep: Bool, +st: AaLex, acc: List<&2, U32>, depth: Nat, h: U32) -> AaLex:
  match keep:
    case True{}:
      AaLex.keep(st, acc, depth, h)
    case False{}:
      +st2 = AaLex.word_end(st, acc)
      AaLex.push(st2, AaTComma{AaLex.line(st2)})

def AaLex.word.lp(split: Bool, st: AaLex, acc: List<&2, U32>, depth: Nat, h: U32) -> AaLex:
  match split:
    case True{}:
      AaLex.open_paren(AaLex.word_end(st, acc))
    case False{}:
      AaLex.keep(st, acc, depth, h)

def AaLex.word.rp(split: Bool, st: AaLex, acc: List<&2, U32>, depth: Nat, h: U32) -> AaLex:
  match split:
    case True{}:
      AaLex.close_paren(AaLex.word_end(st, acc))
    case False{}:
      AaLex.keep(st, acc, depth, h)

def AaLex.word.close(depth: Nat, st: AaLex, acc: List<&2, U32>, h: U32) -> AaLex:
  match depth:
    case 0n:
      +st2 = AaLex.word_end(st, acc)
      AaLex.push(st2, AaTClose{AaLex.line(st2)})
    case 1n+d:
      AaLex.keep(st, acc, d, h)

def AaLex.word.go(k: AaLxCh, +st: AaLex, +acc: List<&2, U32>, +depth: Nat, +h: U32, +next: U32) -> AaLex:
  match k:
    case AaLxCWs{}:
      AaLex.space(AaLex.word_end(st, acc), h)
    case AaLxCNl{}:
      AaLex.space(AaLex.word_end(st, acc), h)
    case AaLxCComma{}:
      AaLex.word.comma(Bool.or(Nat.is_gt(depth, 0n), Bool.not(Bool.or(Nat.is_gt(AaLex.pdepth(st), 0n), AaLxCh.ends(next)))), st, acc, depth, h)
    case AaLxCLP{}:
      AaLex.word.lp(Bool.and(Nat.is_eq(depth, 0n), U32.is_eq(X.AaText.head(acc), 61)), st, acc, depth, h)
    case AaLxCRP{}:
      AaLex.word.rp(Bool.and(Nat.is_eq(depth, 0n), Nat.is_gt(AaLex.pdepth(st), 0n)), st, acc, depth, h)
    case AaLxCOpen{}:
      AaLex.keep(st, acc, 1n+depth, h)
    case AaLxCClose{}:
      AaLex.word.close(depth, st, acc, h)
    case AaLxCQuote{}:
      AaLex.mode(AaLex.word_end(st, acc), AaLxQuote{Nil{}, False{}})
    case AaLxCHash{}:
      AaLex.keep(st, acc, depth, h)
    case AaLxCOther{}:
      AaLex.keep(st, acc, depth, h)

def AaLex.quote.go(esc: Bool, +st: AaLex, +acc: List<&2, U32>, +h: U32) -> AaLex:
  match esc:
    case True{}:
      AaLex.mode(st, AaLxQuote{Con{h, acc}, False{}})
    case False{}:
      Bool.pick(AaLex, U32.is_eq(h, 92), AaLex.mode(st, AaLxQuote{Con{h, acc}, True{}}), Bool.pick(AaLex, U32.is_eq(h, 34), AaLex.push(st, AaTQuoted{X.AaText.rev(acc), AaLex.line(st)}), Bool.pick(AaLex, U32.is_eq(h, 10), AaLex.mode(AaLex.bump(st), AaLxQuote{Con{h, acc}, False{}}), AaLex.mode(st, AaLxQuote{Con{h, acc}, False{}}))))

# the letters of "include"
def AaLex.inc(n: Nat) -> U32:
  match n:
    case 0n:
      105
    case 1n+a:
      match a:
        case 0n:
          110
        case 1n+b:
          match b:
            case 0n:
              99
            case 1n+c:
              match c:
                case 0n:
                  108
                case 1n+d:
                  match d:
                    case 0n:
                      117
                    case 1n+e:
                      match e:
                        case 0n:
                          100
                        case 1n+f:
                          101

def AaLex.comment(+st: AaLex, +h: U32) -> AaLex:
  Bool.pick(AaLex, U32.is_eq(h, 10), AaLex.newline(st), AaLex.mode(st, AaLxComment{}))

def AaLex.hash.go(more: Bool, +st: AaLex, +n: Nat, +h: U32) -> AaLex:
  match more:
    case True{}:
      Bool.pick(AaLex, U32.is_eq(h, AaLex.inc(n)), AaLex.mode(st, AaLxHash{1n+n}), AaLex.comment(st, h))
    case False{}:
      Bool.pick(AaLex, Bool.or(AaLxCh.ws(h), Bool.or(U32.is_eq(h, 10), Bool.or(U32.is_eq(h, 60), U32.is_eq(h, 34)))), AaLex.space(AaLex.push(st, AaTWord{X.AaText.of_string("#include"), AaLex.line(st)}), h), AaLex.comment(st, h))

def AaLex.step.mode(m: AaLxMode, +st: AaLex, +h: U32, +next: U32) -> AaLex:
  match m:
    case AaLxSpace{}:
      AaLex.space(st, h)
    case AaLxWord{acc, depth}:
      AaLex.word.go(AaLxCh.of(h), st, acc, depth, h, next)
    case AaLxQuote{acc, esc}:
      AaLex.quote.go(esc, st, acc, h)
    case AaLxHash{+n}:
      AaLex.hash.go(Nat.is_lt(n, 7n), st, n, h)
    case AaLxComment{}:
      AaLex.comment(st, h)

def AaLex.step(st: AaLex, +h: U32, +next: U32) -> AaLex:
  match st:
    case AaLex{m, l, p, out, ok, bad}:
      AaLex.step.mode(m, AaLex{AaLxSpace{}, l, p, out, ok, bad}, h, next)

def AaLex.finish.go(m: AaLxMode, +st: AaLex) -> AaLex:
  match m:
    case AaLxSpace{}:
      st
    case AaLxWord{acc, depth}:
      AaLex.word_end(st, acc)
    case AaLxQuote{acc, esc}:
      AaLex.fail(st)
    case AaLxHash{n}:
      Bool.pick(AaLex, Nat.is_eq(n, 7n), AaLex.push(st, AaTWord{X.AaText.of_string("#include"), AaLex.line(st)}), st)
    case AaLxComment{}:
      st

def AaLex.finish.paren(p: Nat, st: AaLex) -> AaLex:
  match p:
    case 0n:
      st
    case 1n+q:
      AaLex.fail(st)

def AaLex.finish(st: AaLex) -> AaLex:
  match st:
    case AaLex{m, l, p, out, ok, bad}:
      +st2 = AaLex.finish.go(m, AaLex{AaLxSpace{}, l, p, out, ok, bad})
      AaLex.finish.paren(AaLex.pdepth(st2), st2)

def AaLex.run(xs: List<&2, U32>, st: AaLex) -> AaLex:
  match xs:
    case Nil{}:
      AaLex.finish(st)
    case Con{+h, +t}:
      AaLex.run(t, AaLex.step(st, h, X.AaText.head(t)))

def AaTok.rev_onto(xs: List<&2, AaTok>, acc: List<&2, AaTok>) -> List<&2, AaTok>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      AaTok.rev_onto(t, Con{h, acc})

def AaLex.result(st: AaLex) -> Result<&2, &2, U32, List<&2, AaTok>>:
  match st:
    case AaLex{m, l, p, out, ok, bad}:
      match ok:
        case True{}:
          Done{AaTok.rev_onto(out, Nil{})}
        case False{}:
          Fail{bad}

# the tokens of a text, or the line of its first fault
def AaTok.lex(xs: List<&2, U32>) -> Result<&2, &2, U32, List<&2, AaTok>>:
  AaLex.result(AaLex.run(xs, AaLex{AaLxSpace{}, 1, 0n, Nil{}, True{}, 0}))

# Terms

type AaTerm is Data:
  AaTmWord{text: List<&2, U32>}
  AaTmQuoted{text: List<&2, U32>}
  AaTmList{items: List<&2, AaTerm>}
  AaTmCond{key: List<&2, U32>, value: AaTerm}
  AaTmArrow{}

# a character of a condition's key: a letter, a digit, '_' or '.'
def AaTerm.key_char(+c: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)), Bool.or(Bool.and(U32.is_ge(c, 65), U32.is_le(c, 90)), Bool.or(Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), Bool.or(U32.is_eq(c, 95), U32.is_eq(c, 46)))))

def AaTerm.letter(+c: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)), Bool.and(U32.is_ge(c, 65), U32.is_le(c, 90)))

# a condition's key and the text after its '='
type AaKV is Data:
  AaKV{key: List<&2, U32>, rest: List<&2, U32>}

# key=rest: the key (last character first) read so far
def AaTerm.split.go(xs: List<&2, U32>, +acc: List<&2, U32>) -> Maybe<&2, AaKV>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, +t}:
      Bool.pick(Maybe<&2, AaKV>, U32.is_eq(h, 61), Some{AaKV{X.AaText.rev(acc), t}}, Bool.pick(Maybe<&2, AaKV>, AaTerm.key_char(h), AaTerm.split.go(t, Con{h, acc}), None{}))

# a word key=rest, split, when the key is a letter then key characters
def AaTerm.split(xs: List<&2, U32>) -> Maybe<&2, AaKV>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Bool.pick(Maybe<&2, AaKV>, AaTerm.letter(h), AaTerm.split.go(Con{h, t}, Nil{}), None{})

# the builder: a stack of open lists (innermost first), each its terms (last
# first) and a key waiting for its value
type AaTmFrame is Data:
  AaTmFrame{acc: List<&2, AaTerm>, key: Maybe<&2, List<&2, U32>>}

type AaTmB is Data:
  AaTmB{frames: List<&2, AaTmFrame>, ok: Bool}

def AaTmB.fail(b: AaTmB) -> AaTmB:
  match b:
    case AaTmB{fs, ok}:
      AaTmB{fs, False{}}

def AaTmFrame.add(f: AaTmFrame, t: AaTerm) -> AaTmFrame:
  match f:
    case AaTmFrame{acc, key}:
      match key:
        case None{}:
          AaTmFrame{Con{t, acc}, None{}}
        case Some{k}:
          AaTmFrame{Con{AaTmCond{k, t}, acc}, None{}}

def AaTmB.add(b: AaTmB, t: AaTerm) -> AaTmB:
  match b:
    case AaTmB{fs, ok}:
      match fs:
        case Nil{}:
          AaTmB{Nil{}, False{}}
        case Con{f, rest}:
          AaTmB{Con{AaTmFrame.add(f, t), rest}, ok}

def AaTmFrame.set_key(f: AaTmFrame, k: List<&2, U32>) -> Maybe<&2, AaTmFrame>:
  match f:
    case AaTmFrame{acc, key}:
      match key:
        case None{}:
          Some{AaTmFrame{acc, Some{k}}}
        case Some{k0}:
          None{}

def AaTmB.key.go(m: Maybe<&2, AaTmFrame>, rest: List<&2, AaTmFrame>, ok: Bool) -> AaTmB:
  match m:
    case None{}:
      AaTmB{rest, False{}}
    case Some{f}:
      AaTmB{Con{f, rest}, ok}

def AaTmB.key(b: AaTmB, k: List<&2, U32>) -> AaTmB:
  match b:
    case AaTmB{fs, ok}:
      match fs:
        case Nil{}:
          AaTmB{Nil{}, False{}}
        case Con{f, rest}:
          AaTmB.key.go(AaTmFrame.set_key(f, k), rest, ok)

def AaTmB.cond.go(r: List<&2, U32>, b: AaTmB, k: List<&2, U32>) -> AaTmB:
  match r:
    case Nil{}:
      AaTmB.key(b, k)
    case Con{h, t}:
      AaTmB.add(b, AaTmCond{k, AaTmWord{Con{h, t}}})

def AaTmB.cond(m: Maybe<&2, AaKV>, b: AaTmB, w: List<&2, U32>) -> AaTmB:
  match m:
    case None{}:
      AaTmB.add(b, AaTmWord{w})
    case Some{kr}:
      match kr:
        case AaKV{k, r}:
          AaTmB.cond.go(r, b, k)

def AaTmB.word(+b: AaTmB, +w: List<&2, U32>) -> AaTmB:
  Bool.pick(AaTmB, X.AaText.is(w, "->"), AaTmB.add(b, AaTmArrow{}), AaTmB.cond(AaTerm.split(w), b, w))

def AaTmB.open(b: AaTmB) -> AaTmB:
  match b:
    case AaTmB{fs, ok}:
      AaTmB{Con{AaTmFrame{Nil{}, None{}}, fs}, ok}

def AaTerm.rev_onto(xs: List<&2, AaTerm>, acc: List<&2, AaTerm>) -> List<&2, AaTerm>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      AaTerm.rev_onto(t, Con{h, acc})

def AaTmB.close(b: AaTmB) -> AaTmB:
  match b:
    case AaTmB{fs, ok}:
      match fs:
        case Nil{}:
          AaTmB{Nil{}, False{}}
        case Con{f, rest}:
          match f:
            case AaTmFrame{acc, key}:
              match key:
                case None{}:
                  AaTmB.add(AaTmB{rest, ok}, AaTmList{AaTerm.rev_onto(acc, Nil{})})
                case Some{k}:
                  AaTmB{rest, False{}}

# inside parentheses a comma separates; elsewhere it is out of place
def AaTmB.comma(b: AaTmB) -> AaTmB:
  match b:
    case AaTmB{fs, ok}:
      match fs:
        case Nil{}:
          AaTmB{Nil{}, False{}}
        case Con{f, rest}:
          match rest:
            case Nil{}:
              AaTmB{Con{f, Nil{}}, False{}}
            case Con{g, more}:
              AaTmB{Con{f, Con{g, more}}, ok}

def AaTmB.step(b: AaTmB, t: AaTok) -> AaTmB:
  match t:
    case AaTWord{w, l}:
      AaTmB.word(b, w)
    case AaTQuoted{q, l}:
      AaTmB.add(b, AaTmQuoted{q})
    case AaTOpen{l}:
      AaTmB.fail(b)
    case AaTClose{l}:
      AaTmB.fail(b)
    case AaTLParen{l}:
      AaTmB.open(b)
    case AaTRParen{l}:
      AaTmB.close(b)
    case AaTComma{l}:
      AaTmB.comma(b)

def AaTmB.run(ts: List<&2, AaTok>, b: AaTmB) -> AaTmB:
  match ts:
    case Nil{}:
      b
    case Con{t, rest}:
      AaTmB.run(rest, AaTmB.step(b, t))

def AaTmB.result(b: AaTmB) -> Maybe<&2, List<&2, AaTerm>>:
  match b:
    case AaTmB{fs, ok}:
      match fs:
        case Nil{}:
          None{}
        case Con{f, rest}:
          match f:
            case AaTmFrame{acc, key}:
              match key:
                case None{}:
                  match rest:
                    case Nil{}:
                      match ok:
                        case True{}:
                          Some{AaTerm.rev_onto(acc, Nil{})}
                        case False{}:
                          None{}
                    case Con{g, more}:
                      None{}
                case Some{k}:
                  None{}

# a statement's tokens as terms, or None if its parentheses or conditions are malformed
def AaTerm.of_toks(ts: List<&2, AaTok>) -> Maybe<&2, List<&2, AaTerm>>:
  AaTmB.result(AaTmB.run(ts, AaTmB{[AaTmFrame{Nil{}, None{}}], True{}}))

# Reading terms

def AaTerm.is(t: AaTerm, s: String) -> Bool:
  match t:
    case AaTmWord{w}:
      X.AaText.is(w, s)
    case AaTmQuoted{q}:
      False{}
    case AaTmList{xs}:
      False{}
    case AaTmCond{k, v}:
      False{}
    case AaTmArrow{}:
      False{}

def AaTerm.is_one_of(t: AaTerm, ns: List<&2, String>) -> Bool:
  match t:
    case AaTmWord{w}:
      X.AaText.one_of(ns, w)
    case AaTmQuoted{q}:
      False{}
    case AaTmList{xs}:
      False{}
    case AaTmCond{k, v}:
      False{}
    case AaTmArrow{}:
      False{}

# a word or quoted string's text
def AaTerm.text(t: AaTerm) -> Maybe<&2, List<&2, U32>>:
  match t:
    case AaTmWord{w}:
      Some{w}
    case AaTmQuoted{q}:
      Some{q}
    case AaTmList{xs}:
      None{}
    case AaTmCond{k, v}:
      None{}
    case AaTmArrow{}:
      None{}

# the texts of a value: one word or string, or the words and strings of a list
def AaTerm.texts.cons(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match a:
    case None{}:
      None{}
    case Some{x}:
      match b:
        case None{}:
          None{}
        case Some{xs}:
          Some{Con{x, xs}}

def AaTerm.texts.go(xs: List<&2, AaTerm>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{x, rest}:
      AaTerm.texts.cons(AaTerm.text(x), AaTerm.texts.go(rest))

def AaTerm.texts(t: AaTerm) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match t:
    case AaTmWord{w}:
      Some{[w]}
    case AaTmQuoted{q}:
      Some{[q]}
    case AaTmList{xs}:
      AaTerm.texts.go(xs)
    case AaTmCond{k, v}:
      None{}
    case AaTmArrow{}:
      None{}

def AaTerm.is_arrow(t: AaTerm) -> Bool:
  match t:
    case AaTmArrow{}:
      True{}
    case _:
      False{}
