#!/usr/bin/env python3
"""Differential test cases for bend-osdev-textsearch.

The references are Python's own: bytes.find for plain patterns (with
bytes.lower for ignoring case), and the re module for token patterns (each
token a character class with no suffix, ?, * or +; a match is a non-empty
run of bytes that re.fullmatch accepts). Each case is a random pattern and
text, cut into random chunks; the package's KMP, Boyer-Moore (both shift
rules) and token automaton must report the same match ends.

Writes ref/cases.bend and ref/expected.txt; prints how many cases.
"""
import os, random, re, sys
sys.dont_write_bytecode = True

def ends(p, t, icase):
    if icase:
        p, t = p.lower(), t.lower()
    out, i = [], t.find(p)
    while i >= 0 and p:
        out.append(i + len(p))
        i = t.find(p, i + 1)
    return out

def regex(tokens):
    out = b""
    for (kind, arg, recur) in tokens:
        if kind == "is":
            cls = re.escape(bytes([arg]))
        elif kind == "range":
            cls = b"[" + re.escape(bytes([arg[0]])) + b"-" + re.escape(bytes([arg[1]])) + b"]"
        elif kind == "oneof":
            cls = b"[" + b"".join(re.escape(bytes([b])) for b in arg) + b"]"
        else:
            cls = b"."
        out += cls + {"one": b"", "perhaps": b"?", "star": b"*", "plus": b"+"}[recur]
    return re.compile(out, re.S)

def token_ends(tokens, t):
    rx = regex(tokens)
    return [i for i in range(1, len(t) + 1) if any(rx.fullmatch(t, j, i) for j in range(i))]

def chunks(rng, t):
    cuts = sorted(rng.sample(range(len(t) + 1), min(len(t) + 1, rng.randrange(0, 6))))
    out, last = [], 0
    for c in cuts + [len(t)]:
        out.append(t[last:c])
        last = c
    return out

def bend_list(b):
    return "[%s]" % ", ".join(str(x) for x in b)

def bend_chunks(cs):
    return "[%s]" % ", ".join(bend_list(c) for c in cs)

def bend_token(tok):
    kind, arg, recur = tok
    if kind == "is":
        cls = "F.TsIs{%d}" % arg
    elif kind == "range":
        cls = "F.TsRange{%d, %d}" % arg
    elif kind == "oneof":
        cls = "F.TsOneOf{%s}" % bend_list(arg)
    else:
        cls = "F.TsAnyByte{}"
    rec = {"one": "F.TsOne{}", "perhaps": "F.TsPerhaps{}", "star": "F.TsStar{}", "plus": "F.TsPlus{}"}[recur]
    return "F.TsToken{%s, %s}" % (cls, rec)

def show(ms):
    return " ".join(str(m) for m in ms) if ms else "-"

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, expect = [], []
    def case(body, exp):
        defs.append("def c%d() -> String:\n  %s\n" % (len(defs), body))
        expect.append(exp)
    alphabets = [b"ab", b"abcd", b"aAbB", bytes(range(256))]
    # plain patterns: KMP and both Boyer-Moore rules, chunked
    for _ in range(120):
        alpha = rng.choice(alphabets)
        p = bytes(rng.choice(alpha) for _ in range(rng.randrange(1, 9)))
        t = bytearray(rng.choice(alpha) for _ in range(rng.randrange(0, 160)))
        for _ in range(rng.randrange(0, 4)):
            if len(t) >= len(p):
                i = rng.randrange(len(t) - len(p) + 1)
                t[i:i + len(p)] = p
        t = bytes(t)
        icase = rng.random() < 0.3
        cs = chunks(rng, t)
        ic = "True{}" if icase else "False{}"
        case("plain(%s, %s, %s)" % (ic, bend_list(p), bend_chunks(cs)), " | ".join([show(ends(p, t, icase))] * 3))
    # token patterns
    for _ in range(80):
        alpha = rng.choice([b"ab", b"abc1", b"a1 9"])
        tokens = []
        for _ in range(rng.randrange(1, 5)):
            kind = rng.choice(["is", "is", "range", "oneof", "any"])
            if kind == "is":
                arg = rng.choice(alpha)
            elif kind == "range":
                lo = rng.choice(alpha)
                arg = (lo, rng.randrange(lo, 256) if rng.random() < 0.3 else max(lo, rng.choice(alpha)))
            elif kind == "oneof":
                arg = bytes(rng.sample(alpha, rng.randrange(1, len(alpha) + 1)))
            else:
                arg = None
            tokens.append((kind, arg, rng.choice(["one", "one", "perhaps", "star", "plus"])))
        t = bytes(rng.choice(alpha) for _ in range(rng.randrange(0, 40)))
        cs = chunks(rng, t)
        case("tokens([%s], %s)" % (", ".join(bend_token(k) for k in tokens), bend_chunks(cs)), show(token_ends(tokens, t)))
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PRELUDE)
        f.write("\n".join(defs) + "\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    IO.print(c%d())" % i for i in range(len(defs))) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(defs), "cases")

PRELUDE = '''import Base
import ../kmp.bend as K
import ../bm.bend as M
import ../fsm.bend as F

def show(ms: List<&2, Nat>) -> String:
  match ms:
    case Nil{}:
      "-"
    case Con{m, Nil{}}:
      Nat.show(m)
    case Con{m, t}:
      Nat.show(m) ++ " " ++ show(t)

def plain(+icase: Bool, +p: List<&2, U32>, +cs: List<&2, List<&2, U32>>) -> String:
  show(K.ts.kmp.search(icase, p, cs)) ++ " | " ++ show(M.ts.bm.search(icase, M.TsGoodSuffix{}, p, cs)) ++ " | " ++ show(M.ts.bm.search(icase, M.TsHorspool{}, p, cs))

def tokens(tks: List<&2, F.TsToken>, cs: List<&2, List<&2, U32>>) -> String:
  show(F.ts.fsm.search(tks, cs))

'''

if __name__ == "__main__":
    main()
