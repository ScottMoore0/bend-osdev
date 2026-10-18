#!/usr/bin/env python3
"""Differential test cases for bend-osdev-iodev: random image files, read
and written through FileDev (under an overlay), MemDev, ImgDev and, on a
copy of the file, FileRW on bend-osdev-fileio's effects (written in
place), by cases.bend, against Python reading the same files itself.

The model: an image is its file padded with zeros to whole blocks; a read
of zero bytes succeeds; a read past the last block fails with the first
missing block's number; a write reads its first and last blocks before it
writes, so a write past the end fails with the first of those that is
missing and changes nothing; a save writes the padded image with every
write so far. The expected answers come from Python's own reads of the
generated files (open, seek, read), so a FileDev read is checked against
an independent reader of the same bytes. FileRW writes its copy in place;
Python makes its own copy and does each write that succeeds to it with
seek and write (a write that reaches a final partial block also pads that
block with zeros, as FileRW writes whole blocks), and the two copies must
be equal byte for byte at the end.

  gen.py [seed]    writes work/ (the images, their copies and ops.bin),
                   expected.txt and saves.txt (each saved or written file,
                   and its expected copy), prints the count

Over 4 GiB (big.bend): a sparse image of 5 GiB + 1234 bytes in 1000-byte
blocks (so one block holds the 4 GiB mark) and Python's own copy, both
made with truncate; reads and writes before, across and past the mark and
into the final partial block, then random ones near them, answered by the
same model from Python's copy. The two files are compared over the union
of their data extents (SEEK_DATA, SEEK_HOLE): outside them both are zeros.

  gen.py --big [seed] dir    writes dir/big.img, dir/big.twin,
                             dir/big-ops.bin and dir/big-expected.txt;
                             exits 77 if the file system keeps no sparse
                             files
  gen.py --same a b          compares two files
"""
import os, random, struct, sys

here = os.path.dirname(os.path.abspath(__file__))
work = os.path.join(here, "work")

def words(*xs):
    return b"".join(struct.pack("<I", x) for x in xs)

def blob(bs):
    return words(len(bs)) + bs

def read_model(img, bs, off, n):
    count = (len(img) + bs - 1) // bs
    if n == 0:
        return "ok "
    first, last = off // bs, (off + n - 1) // bs
    if last >= count:
        return "out of range %d" % max(first, count)
    return "ok " + bytes(img[off:off + n]).hex()

def write_model(img, bs, off, data):
    count = (len(img) + bs - 1) // bs
    if len(data) == 0:
        return "ok"
    first, last = off // bs, (off + len(data) - 1) // bs
    if first >= count:
        return "out of range %d" % first
    if last >= count:
        return "out of range %d" % last
    img[off:off + len(data)] = data
    return "ok"

def twin_write(path, bs, off, data):
    """Python's own write of data at off to its copy of the image; the last
    block of the span is padded to a whole block, as FileRW writes it"""
    end = ((off + len(data) - 1) // bs + 1) * bs
    with open(path, "r+b") as f:
        f.seek(off)
        f.write(data)
        if os.fstat(f.fileno()).st_size < end:
            f.truncate(end)

def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    os.makedirs(work, exist_ok=True)
    for f in os.listdir(work):
        os.remove(os.path.join(work, f))
    sections, expect, saves = [], [], []
    ncases = 0
    for k in range(40):
        bs = rng.choice([1, 2, 3, 4, 7, 8, 16, 60, 64, 512, 1000, 4096])
        size = rng.choice([0, bs, 3 * bs, rng.randrange(0, 6000), rng.randrange(0, 300)])
        raw = bytes(rng.randrange(256) for _ in range(size))
        name = "work/img%d.bin" % k
        rw, twin = "work/rw%d.bin" % k, "work/rw%d.expect" % k
        for p in (name, rw, twin):
            with open(os.path.join(here, p), "wb") as f:
                f.write(raw)
        saves.append((rw, twin))
        # the model reads the file back itself, with seek and read
        count = (size + bs - 1) // bs
        img = bytearray()
        with open(os.path.join(here, name), "rb") as f:
            for b in range(count):
                f.seek(b * bs)
                blk = f.read(bs)
                img += blk + bytes(bs - len(blk))
        use_img = 1 if bs % 4 == 0 else 0
        tags = ["f", "m"] + (["i"] if use_img else []) + ["w"]
        expect.append("image %s %d" % (name, bs))
        ops = []
        for _ in range(rng.randrange(1, 25)):
            r = rng.random()
            total = count * bs
            if r < 0.6:
                off = rng.randrange(0, total + 2 * bs + 2)
                n = rng.choice([0, 1, rng.randrange(0, 3 * bs + 2), rng.randrange(0, 200)])
                if rng.random() < 0.7 and total > 0:
                    off = rng.randrange(0, total)
                    n = rng.randrange(0, total - off + 1)
                ops.append(words(0, off, n))
                ans = read_model(img, bs, off, n)
                expect += ["%s %s" % (t, ans) for t in tags]
            elif r < 0.93:
                off = rng.randrange(0, total + 2 * bs + 2)
                n = rng.choice([0, 1, rng.randrange(0, 3 * bs + 2), rng.randrange(0, 100)])
                if rng.random() < 0.8 and total > 0:
                    off = rng.randrange(0, total)
                    n = rng.randrange(0, min(total - off, 300) + 1)
                data = bytes(rng.randrange(256) for _ in range(n))
                ops.append(words(1, off, n) + data)
                ans = write_model(img, bs, off, data)
                expect += ["%s %s" % (t, ans) for t in tags]
                if ans == "ok" and data:
                    twin_write(os.path.join(here, twin), bs, off, data)
            else:
                out = "work/save%d_%d.bin" % (k, len(saves))
                ops.append(words(2) + blob(out.encode()))
                expect.append("s ok")
                exp = "work/save%d_%d.expect" % (k, len(saves))
                with open(os.path.join(here, exp), "wb") as f:
                    f.write(bytes(img))
                saves.append((out, exp))
            ncases += 1
        sections.append(blob(name.encode()) + blob(rw.encode()) + words(bs, use_img, len(ops)) + b"".join(ops))
    with open(os.path.join(work, "ops.bin"), "wb") as f:
        f.write(words(len(sections)) + b"".join(sections))
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    with open(os.path.join(here, "saves.txt"), "w") as f:
        f.write("".join("%s %s\n" % s for s in saves))
    print("%d operations on 40 image files (%d saves, 40 files written in place)" % (ncases, len(saves) - 40))

BIG = 5 * (1 << 30) + 1234
BIG_BS = 1000


def regions(path):
    """the data extents of the file, or the whole file if the file system
    cannot say"""
    size = os.path.getsize(path)
    out = []
    with open(path, "rb") as f:
        at = 0
        try:
            while at < size:
                d = os.lseek(f.fileno(), at, os.SEEK_DATA)
                h = os.lseek(f.fileno(), d, os.SEEK_HOLE)
                out.append((d, h))
                at = h
        except OSError as e:
            return out if e.errno == 6 else [(0, size)]  # ENXIO: no more data
    return out


def same(a, b):
    sa, sb = os.path.getsize(a), os.path.getsize(b)
    if sa != sb:
        return "sizes %d and %d" % (sa, sb)
    with open(a, "rb") as fa, open(b, "rb") as fb:
        for lo, hi in sorted(regions(a) + regions(b)):
            for at in range(lo, hi, 1 << 20):
                n = min(hi - at, 1 << 20)
                fa.seek(at)
                fb.seek(at)
                if fa.read(n) != fb.read(n):
                    return "bytes differ in %d..%d" % (at, at + n)
    return None


def big(seed, out):
    rng = random.Random(seed)
    img, twin = os.path.join(out, "big.img"), os.path.join(out, "big.twin")
    for p in (img, twin):
        with open(p, "wb") as f:
            f.truncate(BIG)
            f.seek((1 << 32) - 2)
            f.write(bytes([17, 34, 51, 68]))
    if any(os.stat(p).st_blocks * 512 > 64 << 20 for p in (img, twin)):
        os.remove(img)
        os.remove(twin)
        print("the file system here keeps no sparse files")
        sys.exit(77)
    bs, count = BIG_BS, (BIG + BIG_BS - 1) // BIG_BS
    ops, expect = [], ["w count %d" % count]

    def read(off, n):
        ops.append(words(0, off >> 32, off & 0xFFFFFFFF, n))
        if n == 0:
            expect.append("w ok ")
            return
        first, last = off // bs, (off + n - 1) // bs
        if last >= count:
            expect.append("w out of range %d" % max(first, count))
            return
        with open(twin, "rb") as f:
            f.seek(off)
            got = f.read(n)
        expect.append("w ok " + (got + bytes(n - len(got))).hex())

    def write(off, data):
        ops.append(words(1, off >> 32, off & 0xFFFFFFFF, len(data)) + data)
        if not data:
            expect.append("w ok")
            return
        first, last = off // bs, (off + len(data) - 1) // bs
        if first >= count:
            expect.append("w out of range %d" % first)
        elif last >= count:
            expect.append("w out of range %d" % last)
        else:
            twin_write(twin, bs, off, data)
            expect.append("w ok")

    def rand(n):
        return bytes(rng.randrange(256) for _ in range(n))

    four, end = 1 << 32, count * bs
    read(four - 10, 20)
    write(four - 3, rand(7))
    read(four - 1000, 2000)
    write(four + 5000, rand(3000))
    read(four + 4000, 5000)
    write(BIG - 5, rand(3))
    read(BIG - 100, 200)
    read(end - 10, 20)
    write(end, rand(1))
    marks = [four - 3, four + 5000, BIG - 5, 3 * (1 << 30), 100]
    for _ in range(20):
        off = max(0, min(rng.choice(marks) + rng.randrange(-2000, 2000), end + 10))
        n = rng.choice([0, 1, rng.randrange(0, 3000)])
        if rng.random() < 0.5:
            read(off, n)
        else:
            write(off, rand(n))
            marks.append(off)
    path = img.encode()
    with open(os.path.join(out, "big-ops.bin"), "wb") as f:
        f.write(blob(path) + words(bs, len(ops)) + b"".join(ops))
    with open(os.path.join(out, "big-expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d operations on a sparse image of %d bytes" % (len(ops), BIG))


if len(sys.argv) > 1 and sys.argv[1] == "--big":
    big(int(sys.argv[2]) if len(sys.argv) > 3 else 2026, sys.argv[-1])
elif len(sys.argv) > 1 and sys.argv[1] == "--same":
    why = same(sys.argv[2], sys.argv[3])
    if why:
        print("%s differs from %s: %s" % (sys.argv[2], sys.argv[3], why))
        sys.exit(1)
else:
    main()
