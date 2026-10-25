#!/usr/bin/env python3
"""Publish bend-osdev packages on BendHub, dependencies first.

  scripts/publish.py [--dry-run | --check] [--bend CMD] [pkg...]

Each package x is published as bend-osdev-x@<x/VERSION> (CONVENTIONS.md).
Its files are staged in a temporary directory first:

  * every top-level .bend file of x/ (the code, LAWS.bend, PROOF.bend and
    check.bend), any file of x/ they import (a foreign def's C and
    JavaScript sides too, `import "./x.c"`), and its LICENSE; the rest of
    ref/ and gen/ stays out;
  * each import of a sibling package, `import ../y/f.bend as Y`, becomes the
    hub import `import bend-osdev-y@<y/VERSION>/f.bend as Y`;
  * a - in a file's path becomes a _ (mode-core.bend is staged as
    mode_core.bend), in the file's name and in every import of it, since
    the hub refuses a path segment that is not letters, digits and _;
  * a generated entry, package.bend, imports every staged file, because
    `bend --publish` sends the file it is given and what that file imports,
    and a package's entry file does not import all of its concerns.

The staged files are what the hub holds; the repository is unchanged. With no
packages named, every package is published; naming some publishes those, in
dependency order. A package whose name and version are already on the hub is
skipped. --dry-run stages each package and prints its files and imports,
publishing nothing. --check publishes nothing either: it stages each package
into a local stand-in for the hub (a library directory holding the staged
packages; the rest of the hub is fetched as usual) and runs `--check-only` on
it, so the hub imports resolve and every staged file checks before anything
is published. CMD (default: $BEND, else `bend`) runs the Bend CLI; the
hub needs a login first (`bend login`).
"""
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import hashlib
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORT = re.compile(r"^(import\s+)(\S+\.bend)(\s+as\s+\S+)", re.M)
# a foreign def's sources, in its body: import "./effs/x.c"
FOREIGN = re.compile(r'^\s+import\s+"([^"]+\.(?:c|js))"', re.M)
# the verdict on a file that type-checks but relies on foreign code: Bend
# 2.0.37 lists the defs one per line ("- name"); 2.0.39 lists them on one
# "defs that depend on foreign effects:" line and may add a "Hint:" line
FOREIGN_VERDICT = re.compile(r"SOME PROOFS FAIL\nError: (\d+) defs? rel(?:y|ies) on unsafe or foreign code:\n"
                             r"(?:(?:- \S+\n)+|defs that depend on foreign effects: [^\n]+\n(?:Hint: [^\n]*\n)?)\s*$")
HUB = os.environ.get("BEND_HUB", "https://hub.bend-lang.com")


def packages():
    return sorted(d for d in os.listdir(ROOT) if os.path.isfile(os.path.join(ROOT, d, "DEPS")))


def version(p):
    return open(os.path.join(ROOT, p, "VERSION"), encoding="utf-8").read().strip()


def hub_name(p):
    return "bend-osdev-%s@%s" % (p, version(p))


def top_files(p):
    return sorted(f for f in os.listdir(os.path.join(ROOT, p)) if f.endswith(".bend"))


def sibling(p, f, target):
    """the sibling package and its file that file f of p imports as target,
    or None for a file of p itself or a hub import"""
    if "@" in target.split("/")[0]:
        return None
    parts = os.path.normpath(os.path.join(p, os.path.dirname(f), target)).replace("\\", "/").split("/")
    if parts[0] == p or parts[0] == ".." or len(parts) < 2:
        return None
    return parts[0], "/".join(parts[1:])


def imports(p, f):
    if not f.endswith(".bend"):
        return []
    return IMPORT.findall(open(os.path.join(ROOT, p, f), encoding="utf-8").read())


def foreign(p, f):
    """the C and JavaScript files of p that file f's foreign defs import"""
    if not f.endswith(".bend"):
        return []
    text = open(os.path.join(ROOT, p, f), encoding="utf-8").read()
    return [os.path.normpath(os.path.join(os.path.dirname(f), t)).replace("\\", "/")
            for t in FOREIGN.findall(text)]


def files(p):
    """the files of p that are published: its top-level .bend files and the
    files of p they import (check.bend may import one under ref/, say)"""
    seen, todo = set(), list(top_files(p))
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        for _, target, _ in imports(p, f):
            if "@" in target.split("/")[0] or sibling(p, f, target) is not None:
                continue
            g = os.path.normpath(os.path.join(os.path.dirname(f), target)).replace("\\", "/")
            if g != "Base" and not g.startswith(".."):
                todo.append(g)
        todo += [g for g in foreign(p, f) if not g.startswith("..")]
    return sorted(seen)


def deps(p):
    out = set()
    for f in files(p):
        for _, target, _ in imports(p, f):
            s = sibling(p, f, target)
            if s is not None:
                out.add(s[0])
    return out


def order(want):
    """want and everything it imports, dependencies first"""
    seen, out = set(), []

    def visit(p, path):
        if p in path:
            sys.exit("an import cycle: " + " -> ".join(path + [p]))
        if p in seen:
            return
        for d in sorted(deps(p)):
            visit(d, path + [p])
        seen.add(p)
        out.append(p)

    for p in want:
        visit(p, [])
    return out


def hub_path(path):
    """a file path as the hub accepts it: the hub refuses a path segment that
    is not letters, digits and _ (mode-core.bend), so a - becomes a _ in
    every segment; . and .. are kept"""
    return "/".join(s if s in (".", "..") else s.replace("-", "_") for s in path.split("/"))


def stage(p, into):
    """the staged files of p in the directory into; returns the hub imports"""
    hub = set()
    os.makedirs(into)
    for f in files(p):
        def rewrite(m):
            s = sibling(p, f, m.group(2))
            if s is None:
                if "@" in m.group(2).split("/")[0]:
                    return m.group(0)
                return m.group(1) + hub_path(m.group(2)) + m.group(3)
            hub.add(hub_name(s[0]))
            return m.group(1) + hub_name(s[0]) + "/" + hub_path(s[1]) + m.group(3)
        text = open(os.path.join(ROOT, p, f), encoding="utf-8").read()
        out = os.path.join(into, hub_path(f))
        os.makedirs(os.path.dirname(out), exist_ok=True)
        with open(out, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(IMPORT.sub(rewrite, text))
    shutil.copy(os.path.join(ROOT, p, "LICENSE"), os.path.join(into, "LICENSE"))
    lines = ["# bend-osdev-%s: every file of the package, so that bend --publish sends" % p,
             "# them all (written by scripts/publish.py; not in the repository)",
             "import Base"]
    lines += ["import ./%s as F%d" % (hub_path(f), k) for k, f in enumerate(top_files(p))]
    with open(os.path.join(into, "package.bend"), "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(lines) + "\n")
    return sorted(hub)


def on_hub(name):
    """whether name@version already names a package on the hub"""
    try:
        with urllib.request.urlopen("%s/name/%s" % (HUB, name), timeout=30) as r:
            return re.fullmatch(r"0x[0-9a-f]{32}", r.read().decode().strip()) is not None
    except Exception:
        return False


def fake_lib(tmp):
    """an empty library directory: what the stand-in hub does not hold, the
    checker fetches from the hub, as it does when publishing"""
    lib = os.path.join(tmp, "lib")
    os.makedirs(os.path.join(lib, "names"))
    return lib


def fake_publish(lib, name, into):
    """name, in the stand-in library, naming the staged files in into"""
    h = "0x" + hashlib.sha256(("bend-osdev-publish-check " + name).encode()).hexdigest()[:32]
    shutil.copytree(into, os.path.join(lib, h))
    with open(os.path.join(lib, "names", name), "w") as fh:
        fh.write(h + "\n")


def main(args):
    dry = "--dry-run" in args
    check = "--check" in args
    bend = shlex.split(os.environ.get("BEND", "bend"))
    rest = [a for a in args if a not in ("--dry-run", "--check")]
    if "--bend" in rest:
        k = rest.index("--bend")
        bend = shlex.split(rest[k + 1])
        rest = rest[:k] + rest[k + 2:]
    known = packages()
    for p in rest:
        if p not in known:
            sys.exit("no package " + p)
    todo = order(rest or known)
    if rest:
        todo = [p for p in todo if p in rest or not on_hub(hub_name(p))]
    tmp = tempfile.mkdtemp(prefix="bend-osdev-publish-")
    lib = fake_lib(tmp) if check else None
    failed = []
    for p in todo:
        name = hub_name(p)
        into = os.path.join(tmp, p)
        hub = stage(p, into)
        print("== %s: %d files, imports %s" % (name, len(files(p)) + 2, ", ".join(hub) or "none"), flush=True)
        if dry:
            continue
        if check:
            env = dict(os.environ, BEND_LIB=lib)
            r = subprocess.run(bend + [os.path.join(into, "package.bend"), "--check-only"], env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            ok = r.returncode == 0 and "ALL PROOFS CHECK" in r.stdout
            note = ""
            # a package with foreign defs (library effects) type-checks, but
            # the verdict then names every def that relies on them, as it
            # does for @unsafe: the checker reads an effect's type, never
            # its code
            m = FOREIGN_VERDICT.match(r.stdout)
            if not ok and m and any(f.endswith((".c", ".js")) for f in files(p)):
                ok, note = True, " (%s defs rely on its foreign effects, as expected)" % m.group(1)
            print("   " + ("ok" + note if ok else "FAIL\n" + r.stdout[-3000:]), flush=True)
            if not ok:
                failed.append(p)
            fake_publish(lib, name, into)
            continue
        if on_hub(name):
            print("   already on the hub", flush=True)
            continue
        r = subprocess.run(bend + [os.path.join(into, "package.bend"), "--publish", name])
        if r.returncode != 0:
            failed.append(p)
            print("   FAILED; stopping (its dependants would fail too)", flush=True)
            break
    shutil.rmtree(tmp, ignore_errors=True)
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main(sys.argv[1:])
