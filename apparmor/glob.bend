# bend-osdev-apparmor: AppArmor globs (AARE), as an explicit matcher.
#
# apparmor.d(5), "Globbing (AARE)": * any run of characters except '/', **
# any run including '/', ? one character except '/', [abc] [a-c] [^a-c] one
# character in (or not in) a set, {ab,cd} alternatives. Where the page is
# silent, the choices follow what apparmor_parser 4.0.1 compiles a pattern to
# (its --dump=rule-exprs output; see the README, "Experiments"):
#   * a * that is a whole path segment ('/' before it, '/' or the end after
#     it) matches one or more characters, so /tmp/* does not match /tmp/;
#     a ** after a '/' and before a '/', a '*' or the end matches one or
#     more characters, the first not '/'. Both are a ? followed by the star;
#   * a negated class may match '/';
#   * runs of '/' collapse to one, except a leading "//";
#   * \c is the character c; a class may not hold '\', start with ']' or
#     end with '-'; a {...} group needs at least two alternatives.
#
# A pattern is brace-expanded when it is parsed: AaGlob holds its
# alternatives, each a sequence of AaGTok. Three matchers, tied by laws for
# every sequence and path:
#   AaGSeq.model, the list model: every way to cut the path into one piece
#     per token (AaGCuts.all), each piece checked against its token;
#   AaGSeq.matches, the reference: a backtracking walk over the sequence and
#     the path (exponential in the stars, since Bend evaluates every
#     argument);
#   AaGSeq.run, what AaGlob.matches uses: the set of active positions in the
#     sequence moved along the path a byte at a time, stopping when none is
#     left (linear in the path, times the sequence's length).
import Base
import ./text.bend as X

type AaGRange is Data:
  AaGRange{lo: U32, hi: U32}

type AaGTok is Data:
  AaGChar{c: U32}
  AaGAny{}
  AaGClass{neg: Bool, ranges: List<&2, AaGRange>}
  AaGStar{}
  AaGStar2{}

type AaGlob is Data:
  AaGlob{alts: List<&2, List<&2, AaGTok>>, literal: Bool}

# Character classes

def AaGRange.has(r: AaGRange, +c: U32) -> Bool:
  match r:
    case AaGRange{lo, hi}:
      Bool.and(U32.is_le(lo, c), U32.is_le(c, hi))

def AaGClass.any(rs: List<&2, AaGRange>, +c: U32) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{r, t}:
      Bool.or(AaGRange.has(r, c), AaGClass.any(t, c))

def AaGClass.has(neg: Bool, rs: List<&2, AaGRange>, +c: U32) -> Bool:
  match neg:
    case True{}:
      Bool.not(AaGClass.any(rs, c))
    case False{}:
      AaGClass.any(rs, c)

# The matcher

def AaGSeq.matches(+seq: List<&2, AaGTok>, s: List<&2, U32>) -> Bool:
  match seq:
    case Nil{}:
      X.AaText.is_nil(s)
    case Con{AaGChar{c}, r}:
      match s:
        case Nil{}:
          False{}
        case Con{h, t}:
          Bool.and(U32.is_eq(h, c), AaGSeq.matches(r, t))
    case Con{AaGAny{}, r}:
      match s:
        case Nil{}:
          False{}
        case Con{h, t}:
          Bool.and(U32.is_ne(h, 47), AaGSeq.matches(r, t))
    case Con{AaGClass{neg, rs}, r}:
      match s:
        case Nil{}:
          False{}
        case Con{h, t}:
          Bool.and(AaGClass.has(neg, rs, h), AaGSeq.matches(r, t))
    case Con{AaGStar{}, r}:
      match s:
        case Nil{}:
          AaGSeq.matches(r, Nil{})
        case Con{+h, +t}:
          Bool.or(AaGSeq.matches(r, Con{h, t}), Bool.and(U32.is_ne(h, 47), AaGSeq.matches(seq, t)))
    case Con{AaGStar2{}, r}:
      match s:
        case Nil{}:
          AaGSeq.matches(r, Nil{})
        case Con{+h, +t}:
          Bool.or(AaGSeq.matches(r, Con{h, t}), AaGSeq.matches(seq, t))

# The fast matcher: the set of active positions in the sequence, one bit
# per suffix (the sequence itself, its tail, ..., the empty suffix), moved
# along the path a byte at a time. Bend evaluates every argument, so the
# backtracking matcher above explores every branch; this one does a fixed
# amount of work per byte and position. A law proves it equal to the
# backtracking matcher for every sequence, path and set of positions.

def AaGNfa.hd(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b, t}:
      b

def AaGNfa.tl(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      t

# a star stays on a byte (* on anything but '/', ** on anything)
def AaGNfa.stay(tok: AaGTok, +h: U32) -> Bool:
  match tok:
    case AaGStar{}:
      U32.is_ne(h, 47)
    case AaGStar2{}:
      True{}
    case _:
      False{}

# a single-byte token moves past a byte it takes
def AaGNfa.adv(tok: AaGTok, +h: U32) -> Bool:
  match tok:
    case AaGChar{c}:
      U32.is_eq(h, c)
    case AaGAny{}:
      U32.is_ne(h, 47)
    case AaGClass{n, rs}:
      AaGClass.has(n, rs, h)
    case _:
      False{}

# a star may match nothing: the position after it is active too
def AaGNfa.isstar(tok: AaGTok) -> Bool:
  match tok:
    case AaGStar{}:
      True{}
    case AaGStar2{}:
      True{}
    case _:
      False{}

# the positions active after the byte h: cin, the position is reached
# without a byte (after a star); ain, the previous position moved here
def AaGNfa.next(+seq: List<&2, AaGTok>, +bs: List<&2, Bool>, +cin: Bool, +ain: Bool, +h: U32) -> List<&2, Bool>:
  match seq:
    case Nil{}:
      [ain]
    case Con{+tok, r}:
      Con{Bool.or(Bool.and(Bool.or(AaGNfa.hd(bs), cin), AaGNfa.stay(tok, h)), ain), AaGNfa.next(r, AaGNfa.tl(bs), Bool.and(Bool.or(AaGNfa.hd(bs), cin), AaGNfa.isstar(tok)), Bool.and(Bool.or(AaGNfa.hd(bs), cin), AaGNfa.adv(tok, h)), h)}

# what a set of positions accepts: some active position's suffix matches s
def AaGNfa.sem(+seq: List<&2, AaGTok>, +bs: List<&2, Bool>, +s: List<&2, U32>) -> Bool:
  match seq:
    case Nil{}:
      Bool.and(AaGNfa.hd(bs), X.AaText.is_nil(s))
    case Con{tok, r}:
      Bool.or(Bool.and(AaGNfa.hd(bs), AaGSeq.matches(Con{tok, r}, s)), AaGNfa.sem(r, AaGNfa.tl(bs), s))

# some position is active
def AaGNfa.alive(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b, t}:
      Bool.or(b, AaGNfa.alive(t))

# the positions moved along the path; at its end, the active positions
# whose suffixes match the empty string accept. alive: some position is
# active (computed by the caller); when none is, the path cannot match.
def AaGNfa.run(s: List<&2, U32>, alive: Bool, +seq: List<&2, AaGTok>, bs: List<&2, Bool>) -> Bool:
  match s:
    case Nil{}:
      AaGNfa.sem(seq, bs, Nil{})
    case Con{h, t}:
      match alive:
        case False{}:
          False{}
        case True{}:
          +n = AaGNfa.next(seq, bs, False{}, False{}, h)
          AaGNfa.run(t, AaGNfa.alive(n), seq, n)

def AaGNfa.falses(seq: List<&2, AaGTok>) -> List<&2, Bool>:
  match seq:
    case Nil{}:
      [False{}]
    case Con{t, r}:
      Con{False{}, AaGNfa.falses(r)}

# only the first position (the whole sequence) is active
def AaGNfa.start(seq: List<&2, AaGTok>) -> List<&2, Bool>:
  match seq:
    case Nil{}:
      [True{}]
    case Con{t, r}:
      Con{True{}, AaGNfa.falses(r)}

# the matcher evaluation uses
def AaGSeq.run(+seq: List<&2, AaGTok>, s: List<&2, U32>) -> Bool:
  AaGNfa.run(s, True{}, seq, AaGNfa.start(seq))

# The list model: a path matches a sequence of n tokens when it can be cut
# into n pieces, in order, each matching its token

# no byte of p is '/'
def AaGPiece.no_slash(p: List<&2, U32>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(U32.is_ne(h, 47), AaGPiece.no_slash(t))

# the piece p is one byte b for which ok holds
def AaGPiece.one(ok: Bool, p: List<&2, U32>) -> Bool:
  match p:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.and(ok, X.AaText.is_nil(t))

def AaGPiece.first(p: List<&2, U32>) -> U32:
  match p:
    case Nil{}:
      0
    case Con{h, t}:
      h

# the piece p matches the token
def AaGTok.piece(tok: AaGTok, +p: List<&2, U32>) -> Bool:
  match tok:
    case AaGChar{c}:
      AaGPiece.one(U32.is_eq(AaGPiece.first(p), c), p)
    case AaGAny{}:
      AaGPiece.one(U32.is_ne(AaGPiece.first(p), 47), p)
    case AaGClass{neg, rs}:
      AaGPiece.one(AaGClass.has(neg, rs, AaGPiece.first(p)), p)
    case AaGStar{}:
      AaGPiece.no_slash(p)
    case AaGStar2{}:
      True{}

# the cuts with an empty first piece
def AaGCuts.empty_first(ds: List<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, List<&2, U32>>>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{Con{Nil{}, d}, AaGCuts.empty_first(t)}

# the cuts with h put in front of the first piece
def AaGCuts.grow(+h: U32, ds: List<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, List<&2, U32>>>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case Nil{}:
          AaGCuts.grow(h, t)
        case Con{p, ps}:
          Con{Con{Con{h, p}, ps}, AaGCuts.grow(h, t)}

def AaGCuts.append(xs: List<&2, List<&2, List<&2, U32>>>, ys: List<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, List<&2, U32>>>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaGCuts.append(t, ys)}

# every way to cut s into n pieces
def AaGCuts.all(+n: Nat, s: List<&2, U32>) -> List<&2, List<&2, List<&2, U32>>>:
  match n:
    case 0n:
      match s:
        case Nil{}:
          [Nil{}]
        case Con{h, t}:
          Nil{}
    case 1n+p:
      match s:
        case Nil{}:
          AaGCuts.empty_first(AaGCuts.all(p, Nil{}))
        case Con{+h, +t}:
          AaGCuts.append(AaGCuts.empty_first(AaGCuts.all(p, Con{h, t})), AaGCuts.grow(h, AaGCuts.all(n, t)))

# the pieces d match the tokens one to one
def AaGSeq.fits(+seq: List<&2, AaGTok>, d: List<&2, List<&2, U32>>) -> Bool:
  match seq:
    case Nil{}:
      match d:
        case Nil{}:
          True{}
        case Con{p, ps}:
          False{}
    case Con{tok, r}:
      match d:
        case Nil{}:
          False{}
        case Con{p, ps}:
          Bool.and(AaGTok.piece(tok, p), AaGSeq.fits(r, ps))

def AaGSeq.fits_any(+seq: List<&2, AaGTok>, ds: List<&2, List<&2, List<&2, U32>>>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      Bool.or(AaGSeq.fits(seq, d), AaGSeq.fits_any(seq, t))

def AaGSeq.len(seq: List<&2, AaGTok>) -> Nat:
  match seq:
    case Nil{}:
      0n
    case Con{t, r}:
      1n+AaGSeq.len(r)

def AaGSeq.model(+seq: List<&2, AaGTok>, s: List<&2, U32>) -> Bool:
  AaGSeq.fits_any(seq, AaGCuts.all(AaGSeq.len(seq), s))

# A whole pattern: some alternative matches

def AaGlob.matches.go(alts: List<&2, List<&2, AaGTok>>, +s: List<&2, U32>) -> Bool:
  match alts:
    case Nil{}:
      False{}
    case Con{a, t}:
      Bool.or(AaGSeq.run(a, s), AaGlob.matches.go(t, s))

# the same with the backtracking matcher (the reference)
def AaGlob.matches_ref.go(alts: List<&2, List<&2, AaGTok>>, +s: List<&2, U32>) -> Bool:
  match alts:
    case Nil{}:
      False{}
    case Con{a, t}:
      Bool.or(AaGSeq.matches(a, s), AaGlob.matches_ref.go(t, s))

def AaGlob.matches_ref(g: AaGlob, +s: List<&2, U32>) -> Bool:
  match g:
    case AaGlob{alts, literal}:
      AaGlob.matches_ref.go(alts, s)

def AaGlob.matches(g: AaGlob, +s: List<&2, U32>) -> Bool:
  match g:
    case AaGlob{alts, literal}:
      AaGlob.matches.go(alts, s)

def AaGlob.model.go(alts: List<&2, List<&2, AaGTok>>, +s: List<&2, U32>) -> Bool:
  match alts:
    case Nil{}:
      False{}
    case Con{a, t}:
      Bool.or(AaGSeq.model(a, s), AaGlob.model.go(t, s))

def AaGlob.model(g: AaGlob, +s: List<&2, U32>) -> Bool:
  match g:
    case AaGlob{alts, literal}:
      AaGlob.model.go(alts, s)

def AaGlob.is_literal(g: AaGlob) -> Bool:
  match g:
    case AaGlob{alts, literal}:
      literal

# How specific a match is, for choosing between attachments: a literal
# pattern ranks above every other; otherwise the longest run of literal
# bytes before the first wildcard, over the alternatives that match.

def AaGSeq.prefix(seq: List<&2, AaGTok>) -> U32:
  match seq:
    case Nil{}:
      0
    case Con{t, r}:
      match t:
        case AaGChar{c}:
          U32.add(1, AaGSeq.prefix(r))
        case AaGAny{}:
          0
        case AaGClass{n, rs}:
          0
        case AaGStar{}:
          0
        case AaGStar2{}:
          0

def AaGlob.rank.max(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), b, a)

def AaGlob.rank.go(alts: List<&2, List<&2, AaGTok>>, +s: List<&2, U32>, +best: U32) -> U32:
  match alts:
    case Nil{}:
      best
    case Con{+a, t}:
      AaGlob.rank.go(t, s, Bool.pick(U32, AaGSeq.run(a, s), AaGlob.rank.max(best, U32.add(AaGSeq.prefix(a), 1)), best))

# 0: no match; 1 + prefix length for a pattern; 1000000 for a literal match
def AaGlob.rank(g: AaGlob, +s: List<&2, U32>) -> U32:
  match g:
    case AaGlob{alts, literal}:
      match literal:
        case True{}:
          Bool.pick(U32, AaGlob.matches.go(alts, s), 1000000, 0)
        case False{}:
          AaGlob.rank.go(alts, s, 0)

# Parsing a pattern's text (after variable expansion and unquoting)

type AaGFlat is Data:
  AaGFTok{t: AaGTok}
  AaGFOpen{}
  AaGFSep{}
  AaGFClose{}

type AaGMode is Data:
  AaGMNorm{}
  AaGMEsc{}
  AaGMStar{}
  AaGMClass{neg: Bool, first: Bool, rs: List<&2, AaGRange>, pend: Maybe<&2, U32>, dash: Bool}

# the lexer's state: the mode, the character before the current one, whether
# the last thing emitted is a '/' that a following '/' collapses into,
# whether nothing has been emitted yet, the brace depth, the flat tokens
# (last first), and whether the text is still well formed
type AaGLex is Data:
  AaGLex{mode: AaGMode, prev: U32, slash: Bool, start: Bool, depth: Nat, out: List<&2, AaGFlat>, ok: Bool}

def AaGLex.fail(st: AaGLex) -> AaGLex:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      AaGLex{AaGMNorm{}, p, sl, st0, d, out, False{}}

def AaGLex.emit(st: AaGLex, f: AaGFlat, prev: U32) -> AaGLex:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      AaGLex{AaGMNorm{}, prev, False{}, False{}, d, Con{f, out}, ok}

def AaGLex.slash.go(sl: Bool, st: AaGLex) -> AaGLex:
  match sl:
    case True{}:
      match st:
        case AaGLex{m, p, sl2, st0, d, out, ok}:
          AaGLex{AaGMNorm{}, 47, True{}, False{}, d, out, ok}
    case False{}:
      match st:
        case AaGLex{m, p, sl2, +st0, d, out, ok}:
          AaGLex{AaGMNorm{}, 47, Bool.not(st0), False{}, d, Con{AaGFTok{AaGChar{47}}, out}, ok}

def AaGLex.slash(st: AaGLex) -> AaGLex:
  match st:
    case AaGLex{m, p, +sl, st0, d, out, ok}:
      AaGLex.slash.go(sl, AaGLex{m, p, sl, st0, d, out, ok})

def AaGLex.depth(st: AaGLex) -> Nat:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      d

def AaGLex.prev(st: AaGLex) -> U32:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      p

def AaGLex.set_mode(st: AaGLex, m: AaGMode) -> AaGLex:
  match st:
    case AaGLex{m0, p, sl, st0, d, out, ok}:
      AaGLex{m, p, sl, st0, d, out, ok}

def AaGLex.open(st: AaGLex) -> AaGLex:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      AaGLex{AaGMNorm{}, 123, False{}, False{}, 1n+d, Con{AaGFOpen{}, out}, ok}

def AaGLex.close.go(d: Nat, out: List<&2, AaGFlat>, ok: Bool, p: U32) -> AaGLex:
  match d:
    case 0n:
      AaGLex{AaGMNorm{}, 125, False{}, False{}, 0n, out, False{}}
    case 1n+e:
      AaGLex{AaGMNorm{}, 125, False{}, False{}, e, Con{AaGFClose{}, out}, ok}

def AaGLex.close(st: AaGLex) -> AaGLex:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      AaGLex.close.go(d, out, ok, p)

def AaGLex.comma.go(d: Nat, st: AaGLex) -> AaGLex:
  match d:
    case 0n:
      AaGLex.emit(st, AaGFTok{AaGChar{44}}, 44)
    case 1n+e:
      AaGLex.emit(st, AaGFSep{}, 44)

def AaGLex.comma(+st: AaGLex) -> AaGLex:
  AaGLex.comma.go(AaGLex.depth(st), st)

# a star or double star: after a '/', and before what `next` says, it stands
# for one or more characters (a ? in front of it)
def AaGLex.star.go(seg: Bool, st: AaGLex, t: AaGTok) -> AaGLex:
  match seg:
    case True{}:
      AaGLex.emit(AaGLex.emit(st, AaGFTok{AaGAny{}}, 42), AaGFTok{t}, 42)
    case False{}:
      AaGLex.emit(st, AaGFTok{t}, 42)

def AaGLex.star(+st: AaGLex, next: Bool) -> AaGLex:
  AaGLex.star.go(Bool.and(U32.is_eq(AaGLex.prev(st), 47), next), st, AaGStar{})

def AaGLex.star2(+st: AaGLex, next: Bool) -> AaGLex:
  AaGLex.star.go(Bool.and(U32.is_eq(AaGLex.prev(st), 47), next), st, AaGStar2{})

# what a character means in normal mode
type AaGCh is Data:
  AaGCLit{}
  AaGCEsc{}
  AaGCStar{}
  AaGCAny{}
  AaGCClass{}
  AaGCOpen{}
  AaGCComma{}
  AaGCClose{}
  AaGCBad{}
  AaGCSlash{}

def AaGCh.of(+h: U32) -> AaGCh:
  Bool.pick(AaGCh, U32.is_eq(h, 92), AaGCEsc{}, Bool.pick(AaGCh, U32.is_eq(h, 42), AaGCStar{}, Bool.pick(AaGCh, U32.is_eq(h, 63), AaGCAny{}, Bool.pick(AaGCh, U32.is_eq(h, 91), AaGCClass{}, Bool.pick(AaGCh, U32.is_eq(h, 123), AaGCOpen{}, Bool.pick(AaGCh, U32.is_eq(h, 44), AaGCComma{}, Bool.pick(AaGCh, U32.is_eq(h, 125), AaGCClose{}, Bool.pick(AaGCh, U32.is_eq(h, 93), AaGCBad{}, Bool.pick(AaGCh, U32.is_eq(h, 47), AaGCSlash{}, AaGCLit{})))))))))

def AaGLex.norm(k: AaGCh, +h: U32, st: AaGLex) -> AaGLex:
  match k:
    case AaGCLit{}:
      AaGLex.emit(st, AaGFTok{AaGChar{h}}, h)
    case AaGCEsc{}:
      AaGLex.set_mode(st, AaGMEsc{})
    case AaGCStar{}:
      AaGLex.set_mode(st, AaGMStar{})
    case AaGCAny{}:
      AaGLex.emit(st, AaGFTok{AaGAny{}}, 63)
    case AaGCClass{}:
      AaGLex.set_mode(st, AaGMClass{False{}, True{}, Nil{}, None{}, False{}})
    case AaGCOpen{}:
      AaGLex.open(st)
    case AaGCComma{}:
      AaGLex.comma(st)
    case AaGCClose{}:
      AaGLex.close(st)
    case AaGCBad{}:
      AaGLex.fail(st)
    case AaGCSlash{}:
      AaGLex.slash(st)

# Character classes: what a character means inside [...]
type AaGK is Data:
  AaGKClose{}
  AaGKCaret{}
  AaGKDash{}
  AaGKBack{}
  AaGKOther{}

def AaGK.of(+h: U32) -> AaGK:
  Bool.pick(AaGK, U32.is_eq(h, 93), AaGKClose{}, Bool.pick(AaGK, U32.is_eq(h, 94), AaGKCaret{}, Bool.pick(AaGK, U32.is_eq(h, 45), AaGKDash{}, Bool.pick(AaGK, U32.is_eq(h, 92), AaGKBack{}, AaGKOther{}))))

def AaGClass.flush(rs: List<&2, AaGRange>, pend: Maybe<&2, U32>) -> List<&2, AaGRange>:
  match pend:
    case None{}:
      rs
    case Some{+c}:
      Con{AaGRange{c, c}, rs}

# a range lo-h, the dash seen: lo is pending
def AaGClass.range(pend: Maybe<&2, U32>, h: U32, rs: List<&2, AaGRange>, st: AaGLex, neg: Bool) -> AaGLex:
  match pend:
    case None{}:
      AaGLex.fail(st)
    case Some{lo}:
      AaGLex.set_mode(st, AaGMClass{neg, False{}, Con{AaGRange{lo, h}, rs}, None{}, False{}})

def AaGClass.close.go(bad: Bool, st: AaGLex, neg: Bool, rs: List<&2, AaGRange>) -> AaGLex:
  match bad:
    case True{}:
      AaGLex.fail(st)
    case False{}:
      AaGLex.emit(st, AaGFTok{AaGClass{neg, rs}}, 93)

def AaGClass.other(dash: Bool, st: AaGLex, neg: Bool, rs: List<&2, AaGRange>, pend: Maybe<&2, U32>, h: U32) -> AaGLex:
  match dash:
    case True{}:
      AaGClass.range(pend, h, rs, st, neg)
    case False{}:
      AaGLex.set_mode(st, AaGMClass{neg, False{}, AaGClass.flush(rs, pend), Some{h}, False{}})

def AaGClass.caret.go(lit: Bool, st: AaGLex, neg: Bool, rs: List<&2, AaGRange>, pend: Maybe<&2, U32>, dash: Bool) -> AaGLex:
  match lit:
    case True{}:
      AaGClass.other(dash, st, neg, rs, pend, 94)
    case False{}:
      AaGLex.set_mode(st, AaGMClass{True{}, True{}, rs, pend, dash})

# k: 0 a literal '-' (first, or nothing pending), 1 the dash of a range, 2 a second dash
def AaGClass.dash.go(k: Nat, st: AaGLex, neg: Bool, rs: List<&2, AaGRange>, pend: Maybe<&2, U32>) -> AaGLex:
  match k:
    case 0n:
      AaGLex.set_mode(st, AaGMClass{neg, False{}, AaGClass.flush(rs, pend), Some{45}, False{}})
    case 1n+j:
      match j:
        case 0n:
          AaGLex.set_mode(st, AaGMClass{neg, False{}, rs, pend, True{}})
        case 1n+i:
          AaGLex.fail(st)

def AaGClass.dash.kind(first: Bool, dash: Bool, pend: Maybe<&2, U32>) -> Nat:
  match first:
    case True{}:
      0n
    case False{}:
      match dash:
        case True{}:
          2n
        case False{}:
          match pend:
            case None{}:
              0n
            case Some{c}:
              1n

def AaGClass.step(k: AaGK, +h: U32, st: AaGLex, +neg: Bool, +first: Bool, +rs: List<&2, AaGRange>, +pend: Maybe<&2, U32>, +dash: Bool) -> AaGLex:
  match k:
    case AaGKClose{}:
      AaGClass.close.go(Bool.or(first, dash), st, neg, AaGClass.flush(rs, pend))
    case AaGKCaret{}:
      AaGClass.caret.go(Bool.or(neg, Bool.not(first)), st, neg, rs, pend, dash)
    case AaGKDash{}:
      AaGClass.dash.go(AaGClass.dash.kind(first, dash, pend), st, neg, rs, pend)
    case AaGKBack{}:
      AaGLex.fail(st)
    case AaGKOther{}:
      AaGClass.other(dash, st, neg, rs, pend, h)

def AaGLex.step.star(two: Bool, st: AaGLex, +h: U32, +next: U32) -> AaGLex:
  match two:
    case True{}:
      AaGLex.star2(st, Bool.or(U32.is_eq(next, 47), Bool.or(U32.is_eq(next, 42), U32.is_eq(next, 0))))
    case False{}:
      AaGLex.norm(AaGCh.of(h), h, AaGLex.star(st, U32.is_eq(h, 47)))

# one character, in the current mode; next is the character after it (0 at the end)
def AaGLex.step.mode(m: AaGMode, st: AaGLex, +h: U32, +next: U32) -> AaGLex:
  match m:
    case AaGMNorm{}:
      AaGLex.norm(AaGCh.of(h), h, st)
    case AaGMEsc{}:
      AaGLex.emit(st, AaGFTok{AaGChar{h}}, h)
    case AaGMStar{}:
      AaGLex.step.star(U32.is_eq(h, 42), st, h, next)
    case AaGMClass{neg, first, rs, pend, dash}:
      AaGClass.step(AaGK.of(h), h, st, neg, first, rs, pend, dash)

def AaGLex.step(st: AaGLex, +h: U32, +next: U32) -> AaGLex:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      AaGLex.step.mode(m, AaGLex{AaGMNorm{}, p, sl, st0, d, out, ok}, h, next)

def AaGLex.finish(st: AaGLex) -> AaGLex:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      match m:
        case AaGMNorm{}:
          AaGLex{AaGMNorm{}, p, sl, st0, d, out, ok}
        case AaGMEsc{}:
          AaGLex{AaGMNorm{}, p, sl, st0, d, out, False{}}
        case AaGMStar{}:
          AaGLex.star(AaGLex{AaGMNorm{}, p, sl, st0, d, out, ok}, True{})
        case AaGMClass{n, f, rs, pe, da}:
          AaGLex{AaGMNorm{}, p, sl, st0, d, out, False{}}

def AaGLex.run(xs: List<&2, U32>, st: AaGLex) -> AaGLex:
  match xs:
    case Nil{}:
      AaGLex.finish(st)
    case Con{+h, +t}:
      AaGLex.run(t, AaGLex.step(st, h, X.AaText.head(t)))

# Brace expansion of the flat tokens. Sequences are built last token first.

type AaGFrame is Data:
  AaGFrame{outer: List<&2, List<&2, AaGTok>>, done: List<&2, List<&2, AaGTok>>, n: Nat}

type AaGExp is Data:
  AaGExp{cur: List<&2, List<&2, AaGTok>>, frames: List<&2, AaGFrame>, ok: Bool}

def AaGSeqs.cons(+t: AaGTok, xs: List<&2, List<&2, AaGTok>>) -> List<&2, List<&2, AaGTok>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, r}:
      Con{Con{t, h}, AaGSeqs.cons(t, r)}

def AaGSeqs.append(xs: List<&2, List<&2, AaGTok>>, ys: List<&2, List<&2, AaGTok>>) -> List<&2, List<&2, AaGTok>>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaGSeqs.append(t, ys)}

def AaGSeq.append(xs: List<&2, AaGTok>, ys: List<&2, AaGTok>) -> List<&2, AaGTok>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaGSeq.append(t, ys)}

def AaGSeq.rev_onto(xs: List<&2, AaGTok>, acc: List<&2, AaGTok>) -> List<&2, AaGTok>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      AaGSeq.rev_onto(t, Con{h, acc})

def AaGSeqs.rev(xs: List<&2, List<&2, AaGTok>>) -> List<&2, List<&2, AaGTok>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{AaGSeq.rev_onto(h, Nil{}), AaGSeqs.rev(t)}

# every a ++ o, a an alternative and o an outer prefix (both last token first)
def AaGSeqs.after(+a: List<&2, AaGTok>, os: List<&2, List<&2, AaGTok>>) -> List<&2, List<&2, AaGTok>>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{AaGSeq.append(a, o), AaGSeqs.after(a, t)}

def AaGSeqs.product(alts: List<&2, List<&2, AaGTok>>, +os: List<&2, List<&2, AaGTok>>) -> List<&2, List<&2, AaGTok>>:
  match alts:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      AaGSeqs.append(AaGSeqs.after(a, os), AaGSeqs.product(t, os))

def AaGExp.sep(fs: List<&2, AaGFrame>, cur: List<&2, List<&2, AaGTok>>, ok: Bool) -> AaGExp:
  match fs:
    case Nil{}:
      AaGExp{cur, Nil{}, False{}}
    case Con{f, rest}:
      match f:
        case AaGFrame{o, d, n}:
          AaGExp{[Nil{}], Con{AaGFrame{o, AaGSeqs.append(d, cur), 1n+n}, rest}, ok}

def AaGExp.close.go(n: Nat, o: List<&2, List<&2, AaGTok>>, alts: List<&2, List<&2, AaGTok>>, rest: List<&2, AaGFrame>, ok: Bool) -> AaGExp:
  match n:
    case 0n:
      AaGExp{o, rest, False{}}
    case 1n+m:
      AaGExp{AaGSeqs.product(alts, o), rest, ok}

def AaGExp.close(fs: List<&2, AaGFrame>, cur: List<&2, List<&2, AaGTok>>, ok: Bool) -> AaGExp:
  match fs:
    case Nil{}:
      AaGExp{cur, Nil{}, False{}}
    case Con{f, rest}:
      match f:
        case AaGFrame{o, d, n}:
          AaGExp.close.go(n, o, AaGSeqs.append(d, cur), rest, ok)

def AaGExp.step(e: AaGExp, f: AaGFlat) -> AaGExp:
  match e:
    case AaGExp{cur, fs, ok}:
      match f:
        case AaGFTok{t}:
          AaGExp{AaGSeqs.cons(t, cur), fs, ok}
        case AaGFOpen{}:
          AaGExp{[Nil{}], Con{AaGFrame{cur, Nil{}, 0n}, fs}, ok}
        case AaGFSep{}:
          AaGExp.sep(fs, cur, ok)
        case AaGFClose{}:
          AaGExp.close(fs, cur, ok)

def AaGExp.run(xs: List<&2, AaGFlat>, e: AaGExp) -> AaGExp:
  match xs:
    case Nil{}:
      e
    case Con{f, t}:
      AaGExp.run(t, AaGExp.step(e, f))

def AaGFlat.rev_onto(xs: List<&2, AaGFlat>, acc: List<&2, AaGFlat>) -> List<&2, AaGFlat>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      AaGFlat.rev_onto(t, Con{h, acc})

def AaGTok.is_char(t: AaGTok) -> Bool:
  match t:
    case AaGChar{c}:
      True{}
    case AaGAny{}:
      False{}
    case AaGClass{n, rs}:
      False{}
    case AaGStar{}:
      False{}
    case AaGStar2{}:
      False{}

# every flat token is a literal character
def AaGFlat.literal(xs: List<&2, AaGFlat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{f, t}:
      match f:
        case AaGFTok{tok}:
          Bool.and(AaGTok.is_char(tok), AaGFlat.literal(t))
        case AaGFOpen{}:
          False{}
        case AaGFSep{}:
          False{}
        case AaGFClose{}:
          False{}

def AaGlob.of_exp.go(ok: Bool, cur: List<&2, List<&2, AaGTok>>, lit: Bool) -> Maybe<&2, AaGlob>:
  match ok:
    case True{}:
      Some{AaGlob{AaGSeqs.rev(cur), lit}}
    case False{}:
      None{}

def AaGlob.of_exp(e: AaGExp, lit: Bool) -> Maybe<&2, AaGlob>:
  match e:
    case AaGExp{cur, fs, ok}:
      match fs:
        case Nil{}:
          AaGlob.of_exp.go(ok, cur, lit)
        case Con{f, r}:
          None{}

def AaGlob.of_flat(+flat: List<&2, AaGFlat>) -> Maybe<&2, AaGlob>:
  AaGlob.of_exp(AaGExp.run(flat, AaGExp{[Nil{}], Nil{}, True{}}), AaGFlat.literal(flat))

def AaGlob.of_lex(st: AaGLex) -> Maybe<&2, AaGlob>:
  match st:
    case AaGLex{m, p, sl, st0, d, out, ok}:
      match d:
        case 0n:
          match ok:
            case True{}:
              AaGlob.of_flat(AaGFlat.rev_onto(out, Nil{}))
            case False{}:
              None{}
        case 1n+e:
          None{}

# the pattern written as the text xs, or None if it is malformed
def AaGlob.parse(xs: List<&2, U32>) -> Maybe<&2, AaGlob>:
  AaGlob.of_lex(AaGLex.run(xs, AaGLex{AaGMNorm{}, 0, False{}, True{}, 0n, Nil{}, True{}}))

# a pattern matching exactly the bytes xs (no wildcards)
def AaGSeq.literal(xs: List<&2, U32>) -> List<&2, AaGTok>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{AaGChar{h}, AaGSeq.literal(t)}

def AaGlob.literal(xs: List<&2, U32>) -> AaGlob:
  AaGlob{[AaGSeq.literal(xs)], True{}}

# the pattern that matches every string
def AaGlob.all() -> AaGlob:
  AaGlob{[[AaGStar2{}]], False{}}

def AaGlob.match_text.go(m: Maybe<&2, AaGlob>, +s: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{g}:
      AaGlob.matches(g, s)

# the pattern written as p (False if it is malformed) matches s
def AaGlob.match_text(p: List<&2, U32>, +s: List<&2, U32>) -> Bool:
  AaGlob.match_text.go(AaGlob.parse(p), s)
