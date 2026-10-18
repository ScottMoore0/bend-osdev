#!/usr/bin/env python3
"""Writes the generated lemmas of xz/PROOF.bend (the .lzma header laws): the
case splits that are too long to write by hand. Run it from xz/ and it
replaces the block between the BEGIN and END marker lines in PROOF.bend.

  * al_props: for every lc, lp and pb with lc + lp <= 4 and pb <= 4, the
    header parser reads the properties byte back (one case for each of the
    75, and the impossible ones refuted);
  * al_fields, al_drop: the dictionary size and the two halves of the
    uncompressed size, split into bits, are read back, and the 13 header
    bytes are skipped exactly;
  * al_short, al_has5: lists of fewer than 12 (and 5) bytes, case by case.
"""
import os, sys

R_HDR = "Result<&2, &2, E.XzError, A.XzAloneHeader>"

def succs(k, var):
    t = var
    for _ in range(k):
        t = "1n+(%s)" % t
    return t

def ind(n):
    return "  " * n

def props_lemma():
    lines = []
    head = ("def al_props(+lc: Nat, +lp: Nat, +pb: Nat, +ys: List<&2, U32>, e1: {Nat.is_le(Nat.add(lc, lp), 4n) == True{} : Bool}, "
            "e2: {Nat.is_le(pb, 4n) == True{} : Bool}) -> {%s : %s}:")
    goal = lambda a, b, c: ("A.XzAl.parse.fields(%s, %s, %s, ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(%s, %s, %s))), "
                            "B.byte(A.XzAlone.props(%s, %s, %s)), ys)" % (a, b, c, a, b, c, a, b, c))
    lines.append(head % (goal("lc", "lp", "pb"), R_HDR))

    def split(var, depth, limit, leaf, refute, k=0, cur=None):
        # match var against 0 .. limit; past it, refute
        cur = cur or var
        out = []
        out.append(ind(depth) + "match %s:" % cur)
        out.append(ind(depth + 1) + "case 0n:")
        out += leaf(k, depth + 2)
        nxt = "%s%d" % (var, k)
        out.append(ind(depth + 1) + "case 1n+%s:" % nxt)
        if k == limit:
            out += refute(succs(k + 1, nxt), depth + 2)
        else:
            out += split(var, depth + 2, limit, leaf, refute, k + 1, nxt)
        return out

    def lc_leaf(c, d):
        def lp_leaf(l, d2):
            def pb_leaf(b, d3):
                return [ind(d3) + "{==}"]
            def pb_refute(t, d3):
                return [ind(d3) + "absurd({%s : %s}, false_not_true(e2))" % (goal("%dn" % c, "%dn" % l, t), R_HDR)]
            return split("pb", d2, 4, pb_leaf, pb_refute)
        def lp_refute(t, d2):
            return [ind(d2) + "absurd({%s : %s}, false_not_true(e1))" % (goal("%dn" % c, t, "pb"), R_HDR)]
        return split("lp", d, 4 - c, lp_leaf, lp_refute)
    def lc_refute(t, d):
        return [ind(d) + "absurd({%s : %s}, false_not_true(e1))" % (goal(t, "lp", "pb"), R_HDR)]
    lines += split("lc", 1, 4, lc_leaf, lc_refute)
    return "\n".join(lines) + "\n"

def bits(p):
    t = "WNil{}"
    for i in reversed(range(32)):
        t = "WCon{%s%d, %s}" % (p, i, t)
    return "U32{%s}" % t

def fields_lemma():
    l = ("A.XzAl.parse.got(lc, lp, pb, Some{d}, Some{W.W64.from_parts(y, x)}) == A.XzAl.parse.fields(lc, lp, pb, "
         "B.append(B.mask(B.append(B.le32(d), B.append(B.le32(x), B.le32(y)))), r))")
    out = ["def al_fields(+lc: Nat, +lp: Nat, +pb: Nat, +d: U32, +x: U32, +y: U32, +r: List<&2, U32>) -> {%s : %s}:" % (l, R_HDR)]
    out.append("  match d x y:")
    out.append("    case %s %s %s:" % (bits("a"), bits("b"), bits("c")))
    out.append("      {==}")
    return "\n".join(out) + "\n"

def drop_lemma():
    l = "r == B.drop(13n, B.append(B.mask(Con{q, B.append(B.le32(d), B.append(B.le32(x), B.le32(y)))}), r))"
    out = ["def al_drop(+q: U32, +d: U32, +x: U32, +y: U32, +r: List<&2, U32>) -> {%s : List<&2, U32>}:" % l]
    out.append("  match d x y:")
    out.append("    case %s %s %s:" % (bits("a"), bits("b"), bits("c")))
    out.append("      {==}")
    return "\n".join(out) + "\n"

def list_lemma(name, n, stmt, ty, extra):
    """a lemma about every list xs of fewer than n elements, by cases"""
    out = ["def %s(%sxs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), %dn) == True{} : Bool}) -> {%s : %s}:" % (name, extra, n, stmt("xs"), ty)]
    def go(k, cur, depth, prefix):
        o = [ind(depth) + "match %s:" % cur, ind(depth + 1) + "case Nil{}:", ind(depth + 2) + "{==}"]
        h, t = "x%d" % k, "t%d" % k
        o.append(ind(depth + 1) + "case Con{%s, %s}:" % (h, t))
        whole = prefix(t)
        if k == n - 1:
            # the length is n + the rest's: split the rest once more, so the
            # hypothesis computes to False
            o.append(ind(depth + 2) + "match %s:" % t)
            for case, rest in [("Nil{}", "Nil{}"), ("Con{y, z}", "Con{y, z}")]:
                o.append(ind(depth + 3) + "case %s:" % case)
                o.append(ind(depth + 4) + "absurd({%s : %s}, false_not_true(e))" % (stmt(prefix(rest)), ty))
        else:
            o += go(k + 1, t, depth + 2, lambda z, h=h, prefix=prefix: prefix("Con{%s, %s}" % ("x%d" % (k + 1), z)))
        return o
    out += go(0, "xs", 1, lambda z: "Con{x0, %s}" % z)
    return "\n".join(out) + "\n"

def short_lemma():
    return list_lemma("al_short", 12, lambda xs: "Fail{E.XzTruncated{}} == A.XzAl.parse.fields(lc, lp, pb, B.mask(%s))" % xs, R_HDR,
                      "+lc: Nat, +lp: Nat, +pb: Nat, ")

def has5_lemma():
    return list_lemma("al_has5", 5, lambda xs: "False{} == A.XzAl.has(5n, B.mask(%s))" % xs, "Bool", "")

BEGIN = "# BEGIN generated by gen/proofs.py: do not edit by hand"
END = "# END generated by gen/proofs.py"

def main():
    block = "\n".join([BEGIN, "", props_lemma(), fields_lemma(), drop_lemma(), short_lemma(), has5_lemma(), END])
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "PROOF.bend")
    s = open(p, newline="").read()
    a, b = s.index(BEGIN), s.index(END) + len(END)
    open(p, "w", newline="").write(s[:a] + block + s[b:])

main()
