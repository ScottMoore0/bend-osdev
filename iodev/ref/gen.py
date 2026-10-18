#!/usr/bin/env python3
"""Differential test cases for bend-osdev-iodev: random image files, read
and written through FileDev (under an overlay), MemDev and ImgDev by
cases.bend, against Python reading the same files itself.

The model: an image is its file padded with zeros to whole blocks; a read
of zero bytes succeeds; a read past the last block fails with the first
missing block's number; a write reads its first and last blocks before it
writes, so a write past the end fails with the first of those that is
missing and changes nothing; a save writes the padded image with every
write so far. The expected answers come from Python's own reads of the
generated files (open, seek, read), so a FileDev read is checked against
an independent reader of the same bytes.

  gen.py [seed]    writes work/ (the images and ops.bin), expected.txt and
                   saves.txt (saved file, expected copy), prints the count
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
        with open(os.path.join(here, name), "wb") as f:
            f.write(raw)
        # the model reads the file back itself, with seek and read
        count = (size + bs - 1) // bs
        img = bytearray()
        with open(os.path.join(here, name), "rb") as f:
            for b in range(count):
                f.seek(b * bs)
                blk = f.read(bs)
                img += blk + bytes(bs - len(blk))
        use_img = 1 if bs % 4 == 0 else 0
        tags = ["f", "m"] + (["i"] if use_img else [])
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
            else:
                out = "work/save%d_%d.bin" % (k, len(saves))
                ops.append(words(2) + blob(out.encode()))
                expect.append("s ok")
                exp = "work/save%d_%d.expect" % (k, len(saves))
                with open(os.path.join(here, exp), "wb") as f:
                    f.write(bytes(img))
                saves.append((out, exp))
            ncases += 1
        sections.append(blob(name.encode()) + words(bs, use_img, len(ops)) + b"".join(ops))
    with open(os.path.join(work, "ops.bin"), "wb") as f:
        f.write(words(len(sections)) + b"".join(sections))
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    with open(os.path.join(here, "saves.txt"), "w") as f:
        f.write("".join("%s %s\n" % s for s in saves))
    print("%d operations on 40 image files (%d saves)" % (ncases, len(saves)))

main()
