# bend-osdev-fdt, structure.bend: the tokens of the structure block
# (Devicetree Specification v0.4, section 5.4), and a streaming lexer that
# reads them from the block's bytes.
#
# Each token is a big-endian 32-bit tag, 4-aligned:
#   FDT_BEGIN_NODE (1): the node's name, a NUL, zero padding to 4 bytes
#   FDT_END_NODE (2)
#   FDT_PROP (3): len and nameoff (32 bits each), then len bytes of value,
#     zero padding to 4 bytes; nameoff is an offset into the strings block
#   FDT_NOP (4)
#   FDT_END (9): the end of the block
#
# The lexer is a byte-at-a-time state machine (FdtLexer.start / feed /
# finish), so a block can be fed in pieces: feeding a then b is feeding
# a ++ b. It checks the tokens' shapes, not their nesting: tree.bend builds
# the tree and checks that.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./layout.bend as L

# A token, without FDT_END (the end of a token list stands for it)
type FdtToken is Data:
  FdtTokBegin{name: B.Octets}
  FdtTokEnd{}
  FdtTokProp{nameoff: U32, value: B.Octets}
  FdtTokNop{}

# Writing

def tok.begin(+nb: List<&2, U32>) -> List<&2, U32>:
  B.append(B.be32(1), B.append(nb, Con{0, B.zeros(L.fdt.pad4(1n+B.len(nb)))}))

def tok.prop(off: U32, +vb: List<&2, U32>) -> List<&2, U32>:
  B.append(B.be32(3), B.append(B.be32(L.fdt.u32n(B.len(vb))), B.append(B.be32(off), B.append(vb, B.zeros(L.fdt.pad4(B.len(vb)))))))

def tok.list(t: FdtToken) -> List<&2, U32>:
  match t:
    case FdtTokBegin{name}:
      tok.begin(B.Octets.to_list(name))
    case FdtTokEnd{}:
      B.be32(2)
    case FdtTokProp{off, v}:
      tok.prop(off, B.Octets.to_list(v))
    case FdtTokNop{}:
      B.be32(4)

# the tokens, then FDT_END
def toks.list(ts: List<&2, FdtToken>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      B.be32(9)
    case Con{t, r}:
      B.append(tok.list(t), toks.list(r))

# the structure block holding these tokens, then FDT_END
def FdtToken.encode_all(ts: List<&2, FdtToken>) -> B.Octets:
  B.Octets.of_list(toks.list(ts))

# a token its encoding can carry: a name without a NUL; a value shorter than
# 2^32 bytes
def FdtToken.valid(t: FdtToken) -> Bool:
  match t:
    case FdtTokBegin{name}:
      L.fdt.nonul(B.Octets.to_list(name))
    case FdtTokEnd{}:
      True{}
    case FdtTokProp{off, v}:
      L.fdt.fits(B.len(B.Octets.to_list(v)))
    case FdtTokNop{}:
      True{}

def FdtToken.valid_all(ts: List<&2, FdtToken>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, r}:
      Bool.and(FdtToken.valid(t), FdtToken.valid_all(r))

# The lexer

# what a 32-bit word being read is for
type LxPurpose is Data:
  LxTag{}
  LxLen{}
  LxOff{len: Nat}

type LxMode is Data:
  # a word, with the bytes read so far (reversed, at most 3)
  LxWord{purpose: LxPurpose, got: List<&2, U32>}
  # a node's name, the bytes so far reversed
  LxName{acc: List<&2, U32>}
  # padding bytes still to skip (at least 1)
  LxPad{left: Nat}
  # a value: bytes still to read (at least 1), its length, the bytes so far
  # reversed
  LxValue{nameoff: U32, left: Nat, total: Nat, acc: List<&2, U32>}
  # after FDT_END; extra: bytes followed it
  LxEnd{extra: Bool}
  LxFail{error: E.FdtError}

# the lexer's state: the mode, and the tokens so far, reversed
type FdtLexer is Data:
  FdtLexer{mode: LxMode, toks: List<&2, FdtToken>}

def lx.tagword() -> LxMode:
  LxWord{LxTag{}, Nil{}}

# skip p padding bytes, then read a tag
def lx.padded(p: Nat) -> LxMode:
  match p:
    case 0n:
      lx.tagword()
    case 1n+q:
      LxPad{1n+q}

def lx.w32(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{v}:
      v
    case None{}:
      0

def lx.tag9(is9: Bool, v: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match is9:
    case True{}:
      FdtLexer{LxEnd{False{}}, toks}
    case False{}:
      FdtLexer{LxFail{E.FdtBadToken{v}}, toks}

def lx.tag4(is4: Bool, +v: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match is4:
    case True{}:
      FdtLexer{lx.tagword(), Con{FdtTokNop{}, toks}}
    case False{}:
      lx.tag9(U32.is_eq(v, 9), v, toks)

def lx.tag3(is3: Bool, +v: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match is3:
    case True{}:
      FdtLexer{LxWord{LxLen{}, Nil{}}, toks}
    case False{}:
      lx.tag4(U32.is_eq(v, 4), v, toks)

def lx.tag2(is2: Bool, +v: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match is2:
    case True{}:
      FdtLexer{lx.tagword(), Con{FdtTokEnd{}, toks}}
    case False{}:
      lx.tag3(U32.is_eq(v, 3), v, toks)

def lx.tag1(is1: Bool, +v: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match is1:
    case True{}:
      FdtLexer{LxName{Nil{}}, toks}
    case False{}:
      lx.tag2(U32.is_eq(v, 2), v, toks)

def lx.value_start(+len: Nat, off: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match len:
    case 0n:
      FdtLexer{lx.tagword(), Con{FdtTokProp{off, B.Octets.of_list(Nil{})}, toks}}
    case 1n+p:
      FdtLexer{LxValue{off, 1n+p, 1n+p, Nil{}}, toks}

# a word read in full
def lx.word_done(p: LxPurpose, +v: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match p:
    case LxTag{}:
      lx.tag1(U32.is_eq(v, 1), v, toks)
    case LxLen{}:
      FdtLexer{LxWord{LxOff{U32.to_nat(v)}, Nil{}}, toks}
    case LxOff{len}:
      lx.value_start(len, v, toks)

def lx.word(p: LxPurpose, got: List<&2, U32>, h: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match got:
    case Nil{}:
      FdtLexer{LxWord{p, Con{h, Nil{}}}, toks}
    case Con{a, Nil{}}:
      FdtLexer{LxWord{p, Con{h, Con{a, Nil{}}}}, toks}
    case Con{b, Con{a, Nil{}}}:
      FdtLexer{LxWord{p, Con{h, Con{b, Con{a, Nil{}}}}}, toks}
    case Con{c, Con{b, Con{a, rest}}}:
      lx.word_done(p, lx.w32(B.be32_at([a, b, c, h], 0n)), toks)

def lx.name_end(+nb: List<&2, U32>, toks: List<&2, FdtToken>) -> FdtLexer:
  FdtLexer{lx.padded(L.fdt.pad4(1n+B.len(nb))), Con{FdtTokBegin{B.Octets.of_list(nb)}, toks}}

def lx.name(nul: Bool, h: U32, acc: List<&2, U32>, toks: List<&2, FdtToken>) -> FdtLexer:
  match nul:
    case True{}:
      lx.name_end(List.reverse(&2, U32, acc), toks)
    case False{}:
      FdtLexer{LxName{Con{h, acc}}, toks}

# a value byte read; left: the bytes still to read after it
def lx.value(left: Nat, off: U32, +total: Nat, acc: List<&2, U32>, toks: List<&2, FdtToken>) -> FdtLexer:
  match left:
    case 0n:
      FdtLexer{lx.padded(L.fdt.pad4(total)), Con{FdtTokProp{off, B.Octets.of_list(List.reverse(&2, U32, acc))}, toks}}
    case 1n+r:
      FdtLexer{LxValue{off, 1n+r, total, acc}, toks}

def lx.step.mode(mode: LxMode, +h: U32, toks: List<&2, FdtToken>) -> FdtLexer:
  match mode:
    case LxWord{p, got}:
      lx.word(p, got, h, toks)
    case LxName{acc}:
      lx.name(U32.is_eq(h, 0), h, acc, toks)
    case LxPad{left}:
      match left:
        case 0n:
          lx.word(LxTag{}, Nil{}, h, toks)
        case 1n+q:
          FdtLexer{lx.padded(q), toks}
    case LxValue{off, left, total, acc}:
      match left:
        case 0n:
          FdtLexer{LxFail{E.FdtTruncated{}}, toks}
        case 1n+q:
          lx.value(q, off, total, Con{h, acc}, toks)
    case LxEnd{extra}:
      FdtLexer{LxEnd{True{}}, toks}
    case LxFail{e}:
      FdtLexer{LxFail{e}, toks}

# one byte
def lx.step(st: FdtLexer, h: U32) -> FdtLexer:
  match st:
    case FdtLexer{mode, toks}:
      lx.step.mode(mode, h, toks)

def lx.go(xs: List<&2, U32>, st: FdtLexer) -> FdtLexer:
  match xs:
    case Nil{}:
      st
    case Con{h, t}:
      lx.go(t, lx.step(st, h))

# a lexer at the start of a structure block
def FdtLexer.start() -> FdtLexer:
  FdtLexer{lx.tagword(), Nil{}}

# the lexer after the bytes o
def FdtLexer.feed(st: FdtLexer, o: B.Octets) -> FdtLexer:
  lx.go(B.Octets.to_list(o), st)

def lx.fin_end(bad: Bool, toks: List<&2, FdtToken>) -> Result<&2, &2, E.FdtError, List<&2, FdtToken>>:
  match bad:
    case True{}:
      Fail{E.FdtAfterEnd{}}
    case False{}:
      Done{List.reverse(&2, FdtToken, toks)}

def lx.fin(mode: LxMode, strict: Bool, toks: List<&2, FdtToken>) -> Result<&2, &2, E.FdtError, List<&2, FdtToken>>:
  match mode:
    case LxEnd{extra}:
      lx.fin_end(Bool.and(extra, strict), toks)
    case LxFail{e}:
      Fail{e}
    case LxWord{p, got}:
      Fail{E.FdtTruncated{}}
    case LxName{acc}:
      Fail{E.FdtTruncated{}}
    case LxPad{left}:
      Fail{E.FdtTruncated{}}
    case LxValue{off, left, total, acc}:
      Fail{E.FdtTruncated{}}

# the tokens read, once the block has ended: FdtTruncated if it stopped
# before FDT_END; with strict, FdtAfterEnd if bytes followed FDT_END
def FdtLexer.finish(strict: Bool, st: FdtLexer) -> Result<&2, &2, E.FdtError, List<&2, FdtToken>>:
  match st:
    case FdtLexer{mode, toks}:
      lx.fin(mode, strict, toks)

# the tokens of a whole structure block, which must end with FDT_END
def FdtToken.decode_all(o: B.Octets) -> Result<&2, &2, E.FdtError, List<&2, FdtToken>>:
  FdtLexer.finish(True{}, FdtLexer.feed(FdtLexer.start(), o))
