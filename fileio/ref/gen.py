#!/usr/bin/env python3
"""Differential test cases for bend-osdev-fileio: random files read and
written in place by cases.bend through the effects, against Python doing
the same to a copy of each file with its own open, seek, read and write.

Every file is made twice in the work directory: a.N, which cases.bend
opens with FileIO.open and changes, and b.N, the copy Python changes as it
generates the cases (opened "r+b", or created when the case asks for it).
Python's answers to its own reads and sizes are the expected output, and
after the run every a.N must equal its b.N byte for byte.

One file is over 4 GiB: a sparse file (truncate), written and read past
the 4 GiB mark and across it, and grown past its end. If the file system
does not keep it sparse, that file is left out and the count says so.
Sparse files are compared over the union of their data extents
(SEEK_DATA, SEEK_HOLE): outside them both read as zeros.

  gen.py [seed] dir        writes the files, dir/ops.bin and
                           dir/expected.txt; prints the count
  gen.py --compare dir     compares every a.N with its b.N
"""
import os, random, struct, sys

GiB = 1 << 30
BIG = 5 * GiB + 1234


def words(*xs):
    return b"".join(struct.pack("<I", x) for x in xs)


def blob(bs):
    return words(len(bs)) + bs


def off_words(off):
    return words(off >> 32, off & 0xFFFFFFFF)


def regions(path):
    """the data extents of the file, or the whole file if the file system
    cannot say"""
    size = os.path.getsize(path)
    out = []
    with open(path, "rb") as f:
        fd = f.fileno()
        at = 0
        try:
            while at < size:
                d = os.lseek(fd, at, os.SEEK_DATA)
                h = os.lseek(fd, d, os.SEEK_HOLE)
                out.append((d, h))
                at = h
        except OSError as e:
            if e.errno == 6:  # ENXIO: no data past at
                return out
            return [(0, size)]
    return out


def same(a, b):
    sa, sb = os.path.getsize(a), os.path.getsize(b)
    if sa != sb:
        return "sizes %d and %d" % (sa, sb)
    spans = sorted(regions(a) + regions(b))
    with open(a, "rb") as fa, open(b, "rb") as fb:
        for lo, hi in spans:
            at = lo
            while at < hi:
                n = min(hi - at, 1 << 20)
                fa.seek(at)
                fb.seek(at)
                if fa.read(n) != fb.read(n):
                    return "bytes differ in %d..%d" % (at, at + n)
                at += n
    return None


def compare(work):
    names = sorted(f[2:] for f in os.listdir(work) if f.startswith("b."))
    for n in names:
        a, b = os.path.join(work, "a." + n), os.path.join(work, "b." + n)
        if not os.path.exists(a):
            print("a.%s missing" % n)
            return 1
        why = same(a, b)
        if why:
            print("a.%s differs from b.%s: %s" % (n, n, why))
            return 1
    return 0


def sparse_ok(path):
    st = os.stat(path)
    return st.st_blocks * 512 < 64 * 1024 * 1024


def case_ops(rng, b, big):
    """random operations on the open file b (Python's copy); returns the
    encoded operations and their expected lines"""
    ops, lines = [], []

    def read(off, n):
        ops.append(words(0) + off_words(off) + words(n))
        b.seek(off)
        lines.append("r ok " + b.read(n).hex())

    def write(off, data):
        ops.append(words(1) + off_words(off) + words(len(data)) + data)
        b.seek(off)
        b.write(data)
        b.flush()
        lines.append("w ok")

    def size():
        ops.append(words(2))
        lines.append("s %d" % os.fstat(b.fileno()).st_size)

    def rand(n):
        return bytes(rng.randrange(256) for _ in range(n))

    marks = [0]
    if big:
        # across the 4 GiB mark, past it, and past the end (the file grows,
        # once over a hole)
        four = 1 << 32
        size()
        read(four - 4, 8)
        write(four - 1, rand(3))
        read(four - 4, 8)
        write(four + 4097, rand(300))
        read(four + 4000, 600)
        write(BIG - 10, rand(30))
        size()
        read(BIG - 20, 50)
        write(2 * four + 7, rand(5))
        size()
        read(2 * four, 20)
        marks = [four - 3, four, four + 4097, BIG - 10, 2 * four + 7]
    for _ in range(rng.randrange(1, 30)):
        r = rng.random()
        end = os.fstat(b.fileno()).st_size
        if big:
            off = rng.choice([rng.choice(marks) + rng.randrange(-50, 50),
                              rng.randrange(1 << 32, end + 1), end + rng.randrange(0, 20)])
        else:
            off = rng.choice([rng.randrange(0, end + 1), rng.randrange(0, end + 200), 0, end])
        off = max(off, 0)
        if r < 0.45:
            read(off, rng.choice([0, 1, rng.randrange(0, 300)]))
        elif r < 0.85:
            write(off, rand(rng.choice([0, 1, rng.randrange(0, 300)])))
            marks.append(off)
        elif r < 0.95:
            size()
        else:
            ops.append(words(3))
            lines.append("y ok")
    return ops, lines


def main():
    if sys.argv[1] == "--compare":
        sys.exit(compare(sys.argv[2]))
    seed = int(sys.argv[1]) if len(sys.argv) > 2 else 2026
    work = sys.argv[-1]
    rng = random.Random(seed)
    sections, expect = [], []
    nops, nfiles = 0, 0
    # the big sparse file first, then 30 small ones
    plan = [("big", None)] + [("small", k) for k in range(30)]
    big_note = "1 sparse file of %d bytes" % BIG
    for kind, k in plan:
        name = "big" if kind == "big" else "f%d" % k
        a, b = os.path.join(work, "a." + name), os.path.join(work, "b." + name)
        create = 0
        if kind == "big":
            for p in (a, b):
                with open(p, "wb") as f:
                    f.truncate(BIG)
            if not (sparse_ok(a) and sparse_ok(b)):
                os.remove(a)
                os.remove(b)
                big_note = "no sparse files here: the file over 4 GiB was left out"
                continue
            # a few bytes before, at and past the 4 GiB mark
            for p in (a, b):
                with open(p, "r+b") as f:
                    f.seek((1 << 32) - 2)
                    f.write(b"\x11\x22\x33\x44")
        else:
            how = rng.random()
            raw = bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, rng.randrange(0, 5000)])))
            if how < 0.8:
                for p in (a, b):
                    with open(p, "wb") as f:
                        f.write(raw)
            elif how < 0.9:
                create = 1  # missing, created by the open
            else:
                create = 0  # missing: the open fails
        expect.append("file " + a)
        if not os.path.exists(b) and create == 0:
            expect.append("open failed 2")
            sections.append(blob(a.encode()) + words(create, 0))
            nfiles += 1
            continue
        if not os.path.exists(b):
            open(b, "wb").close()
        expect.append("open ok")
        with open(b, "r+b") as f:
            ops, lines = case_ops(rng, f, kind == "big")
        expect += lines
        nops += len(ops)
        nfiles += 1
        sections.append(blob(a.encode()) + words(create, len(ops)) + b"".join(ops))
    with open(os.path.join(work, "ops.bin"), "wb") as f:
        f.write(words(len(sections)) + b"".join(sections))
    with open(os.path.join(work, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d operations on %d files (%s)" % (nops, nfiles, big_note))


main()
