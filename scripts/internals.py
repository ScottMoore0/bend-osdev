#!/usr/bin/env python3
"""List the uses, in each package, of another package's defs that the other
package's README does not list as public.

scripts/internals.py [--all] [package...]

A def or type of package Q is public when its README names it in backticks
(a table cell like `X509Cert.tbs`, `.sig_alg` names X509Cert.sig_alg too).
For each file of a package P that imports one of Q's files (`import
../q/f.bend as A`), each `A.name` it uses is looked up in f.bend's defs and
types; a name f.bend defines that Q's README does not name is reported.
Imports of Q's LAWS*, PROOF* and proof_* files are law and lemma uses, not
code: they are skipped unless --all is given. Exit status 1 if any use is
reported.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORT = re.compile(r"^import \.\./([^/\s]+)/(\S+\.bend) as (\w+)\s*$", re.M)
DEF = re.compile(r"^(?:def|type|law|axiom|trait)\s+([A-Za-z_][\w.]*)", re.M)
CTOR = re.compile(r"^\s+([A-Z]\w*)\s*(?:\{|$|:)", re.M)
TICK = re.compile(r"`([^`]+)`")
NAME = re.compile(r"\.?[A-Za-z_][\w.]*")


RANGE = re.compile(r"`([A-Za-z_][\w.]*?)\.[a-z]+\d+([\w.]*)` (?:to|\.\.) `[A-Za-z_][\w.]*?\.[a-z]+\d+[\w.]*`")
ETC = re.compile(r"`([A-Za-z_]\w*)\.[\w.]*`,? \.\.\.")


def public(pkg):
    """The names pkg's README lists: a bare `add` is any type's .add, and
    `T.le16` to `T.be64` is every T.<letters><digits> with that suffix,
    `T.f`, ... and `T.x_*` are every T.* and T.x_*, `T{a, b}` names T.a
    and T.b, and `T.TYPE_A/B()` names T.TYPE_A and T.TYPE_B"""
    path = os.path.join(ROOT, pkg, "README.md")
    names = set()
    if not os.path.exists(path):
        return names
    last = None
    for line in open(path, encoding="utf-8"):
        # a `.f` continues the last `T.g` of its paragraph or table row
        if line.strip() == "" or line.startswith("|"):
            last = None
        # "Defs named `x5.*` are internal." names what is not public
        if "internal" in line:
            continue
        row = re.search(r"`([A-Z]\w*)[.{]", line)
        if row and line.startswith("|") and re.search(r"\baccessors\b", line):
            names.add(("prefix", row.group(1) + "."))
        if row and re.search(r"`[A-Z0-9_]+\(\)` (?:…|\.\.\.?) `[A-Z0-9_]+\(\)`", line):
            names.add(("caps", row.group(1)))
        for t, suffix in RANGE.findall(line):
            names.add(("range", t, suffix))
        for t in ETC.findall(line):
            names.add(("prefix", t + "."))
        for span in TICK.findall(line):
            for t, fields in re.findall(r"([A-Za-z_]\w*)\{([^{}]*)\}", span):
                names.update(t + "." + f for f in re.findall(r"\w+", fields))
                last = t + "."
            for head, rest in re.findall(r"([\w.]*_[A-Z0-9]+)((?:/[A-Z0-9]+)+)", span):
                stem = head[:head.rindex("_") + 1]
                names.add(head)
                names.update(stem + x for x in rest.split("/") if x)
            # arguments and fields name no defs: `f(a, b)`, `T{x, y}`
            span = re.sub(r"\([^()]*\)|\{[^{}]*\}", " ", span)
            for w in re.findall(r"[\w.]+\*", span):
                names.add(("prefix", w.rstrip("*")))
            for n in NAME.findall(span):
                n = n.rstrip(".")
                if n.startswith("."):
                    if last is None:
                        continue
                    n = last.split(".")[0] + n
                elif n.startswith("X."):
                    # `X.norm(h)`: every header type X's norm
                    n = n[2:]
                elif "." in n:
                    # `T.f`, `.g` names T.g; a bare `U` does not change T
                    last = n
                names.add(n)
    return names


def defined(pkg, f):
    path = os.path.join(ROOT, pkg, f)
    if not os.path.exists(path):
        return set()
    text = open(path, encoding="utf-8").read()
    return set(DEF.findall(text)) | set(CTOR.findall(text))


def is_public(n, pub):
    # a name is public if it, or a def it is a field or method of, is named
    if n in pub:
        return True
    parts = n.split(".")
    if len(parts) > 1 and ".".join(parts[1:]) in pub:
        return True
    for x in pub:
        if isinstance(x, tuple) and x[0] == "prefix" and (
                n.startswith(x[1]) or ".".join(parts[1:]).startswith(x[1])):
            return True
    if len(parts) == 2 and ("caps", parts[0]) in pub and re.fullmatch(r"[A-Z0-9_]+", parts[1]):
        return True
    m = re.fullmatch(r"(.+?)\.[a-z]+\d+([\w.]*)", n)
    return m is not None and ("range", m.group(1), m.group(2)) in pub


def audit(pkgs, everything):
    found = []
    cache = {}
    for p in pkgs:
        d = os.path.join(ROOT, p)
        for f in sorted(os.listdir(d)):
            if not f.endswith(".bend"):
                continue
            text = open(os.path.join(d, f), encoding="utf-8").read()
            for q, qf, alias in IMPORT.findall(text):
                if q == p:
                    continue
                if not everything and re.match(r"(LAWS|PROOF|proof_)", qf):
                    continue
                if q not in cache:
                    cache[q] = public(q)
                defs = defined(q, qf)
                for n in sorted(set(re.findall(r"\b" + alias + r"\.([A-Za-z_][\w.]*)", text))):
                    n = n.rstrip(".")
                    # the longest prefix f.bend defines is the def used
                    parts = n.split(".")
                    hit = next((".".join(parts[:i]) for i in range(len(parts), 0, -1)
                                if ".".join(parts[:i]) in defs), None)
                    if hit is None or is_public(hit, cache[q]):
                        continue
                    found.append((p, f, q, qf, hit))
    return found


def main():
    args = sys.argv[1:]
    everything = "--all" in args
    args = [a for a in args if a != "--all"]
    pkgs = args or sorted(x for x in os.listdir(ROOT)
                          if os.path.exists(os.path.join(ROOT, x, "DEPS")))
    found = audit(pkgs, everything)
    for p, f, q, qf, n in found:
        print(f"{p}/{f}: {q}/{qf} {n}")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
