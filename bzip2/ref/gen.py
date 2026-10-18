#!/usr/bin/env python3
"""Differential test cases for bend-osdev-bzip2.

  gen.py SEED          writes the case files into ref/work/, the runner's
                       arguments (args.txt) and the expected output
                       (expected.txt); prints the number of cases
  gen.py verify        checks the streams the package compressed (work/*.bz2
                       named in args.txt) decode back to their input, with
                       Python's bz2 module and, when installed, the bzip2 tool

Decoding: streams made by Python's bz2 module (libbzip2) and, when installed,
by the bzip2 tool, at every level 1 to 9: empty, one byte, text, runs of
every length around RLE1's limits (4, 5, 255, 256), random bytes, all 256
byte values, several blocks, several streams, streams with trailing bytes,
and copies with a byte changed, a bit flipped, bytes deleted or the end cut
off. The expected answer is the bzip2 tool's when it is installed (an error,
or the same output: its length and zlib CRC-32), else Python's; Python is
lenient about a damaged second stream (it keeps the first and stops), so
damaged copies are made of single streams only.

BZIP2_TOOL=none runs without the tool, as on a machine that lacks it.

Encoding: the package compresses inputs at levels 1, 2, 5 and 9 (some
through the streaming writer), and each stream must decode back to its
input with Python's bz2 module and with bzip2 -d.
"""
import bz2, binascii, os, random, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.join(HERE, "work")
TOOL = None if os.environ.get("BZIP2_TOOL") == "none" else shutil.which("bzip2")


def tool_compress(data, level):
    return subprocess.run([TOOL, "-%d" % level, "-c"], input=data, capture_output=True, check=True).stdout


def judge(stream):
    """The expected runner line's tail: 'LEN CRC' or 'error'."""
    if TOOL:
        p = subprocess.run([TOOL, "-dc"], input=stream, capture_output=True)
        if p.returncode != 0:
            return "error"
        out = p.stdout
    else:
        try:
            out = bz2.decompress(stream)
        except Exception:
            return "error"
    return "%d %d" % (len(out), binascii.crc32(out))


def inputs(rng):
    words = [b"block ", b"sorting ", b"huffman, ", b"burrows ", b"wheeler ", b"move-to-front ", b"run\n", b"bzip2 "]
    text = lambda n: b"".join(rng.choice(words) for _ in range(n))
    runs = b"".join(bytes([rng.randrange(256)]) * k for k in [1, 2, 3, 4, 5, 6, 254, 255, 256, 257, 259, 300, 509, 510, 511, 600])
    out = [
        ("empty", b""),
        ("one", b"x"),
        ("hello", b"hello, hello, hello, bzip2!\n"),
        ("text", text(400)),
        ("runs", runs),
        ("zeros", bytes(3000)),
        ("random", bytes(rng.randrange(256) for _ in range(3000))),
        ("all256", bytes(range(256)) * 3),
        ("twobytes", bytes(rng.choice(b"ab") for _ in range(2000))),
        ("mixed", text(100) + bytes(rng.randrange(256) for _ in range(500)) + bytes(700) + text(100)),
    ]
    return out


def main(seed):
    rng = random.Random(seed)
    os.makedirs(WORK, exist_ok=True)
    for f in os.listdir(WORK):
        os.remove(os.path.join(WORK, f))
    args, expect = [], []

    def dec(name, stream, want=None):
        path = os.path.join("work", name + ".in")
        with open(os.path.join(HERE, path), "wb") as f:
            f.write(stream)
        args.extend(["d", path, name])
        expect.append(name + " " + (want or judge(stream)))

    singles = []
    for k, (name, data) in enumerate(inputs(rng)):
        for level in range(1, 10):
            if level not in (1, 9) and (k + level) % 3:
                continue  # every level for some inputs, 1 and 9 for all
            s = bz2.compress(data, level)
            dec("py_%s_%d" % (name, level), s)
            singles.append(s)
            if TOOL and level in (1, 6, 9):
                t = tool_compress(data, level)
                if t != s:
                    dec("tool_%s_%d" % (name, level), t)
    # several blocks: level 1 holds 100,000 bytes a block
    big = b"".join(bytes([rng.randrange(256)]) * rng.randrange(1, 9) for _ in range(60000))
    dec("py_blocks_1", bz2.compress(big, 1))
    dec("py_blocks_2", bz2.compress(big[:150000], 2))
    # several streams, and trailing bytes after the last
    two = bz2.compress(b"first stream, ", 9) + bz2.compress(b"", 3) + bz2.compress(b"third", 1)
    dec("multi", two)
    dec("multi_garbage", two + b"garbage")
    dec("multi_zeros", two + bytes(5))
    dec("multi_bz", two + b"BZ")
    dec("multi_bzh9", two + b"BZh9")
    dec("not_bzip2", b"hello, world")
    # a padding bit after the stream's end, flipped (the tool accepts it)
    pad = bytearray(bz2.compress(b"hello", 9))
    pad[-1] ^= 1
    dec("padding_bit", bytes(pad))
    # the empty input is not a stream (the bzip2 tool's answer; Python's bz2
    # answers no bytes)
    dec("empty_input", b"", "error")
    # damaged copies of single streams
    pool = [s for s in singles if len(s) > 14]
    for i in range(60):
        s = bytearray(rng.choice(pool))
        kind = i % 4
        if kind == 0:
            p = rng.randrange(len(s))
            s[p] = rng.randrange(256)
        elif kind == 1:
            p = rng.randrange(len(s))
            s[p] ^= 1 << rng.randrange(8)
        elif kind == 2:
            p = rng.randrange(len(s))
            del s[p:p + rng.randrange(1, 4)]
        else:
            s = s[:rng.randrange(len(s))]
        dec("bad_%02d" % i, bytes(s))
    # encoding
    for k, (name, data) in enumerate(inputs(rng) + [("blocks", big[:250000])]):
        for level in (1, 2, 5, 9):
            if name == "blocks" and level > 2:
                continue
            path = os.path.join("work", "c_%s_%d.raw" % (name, level))
            with open(os.path.join(HERE, path), "wb") as f:
                f.write(data)
            act = ("s%d" if (k + level) % 4 == 0 else "c%d") % level
            out = os.path.join("work", "c_%s_%d" % (name, level))
            args.extend([act, path, out])
            expect.append(out + " written")
    with open(os.path.join(HERE, "args.txt"), "w") as f:
        f.write("\n".join(args) + "\n")
    with open(os.path.join(HERE, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect))


def verify():
    args = open(os.path.join(HERE, "args.txt")).read().split()
    n, bad = 0, []
    for act, path, name in zip(args[0::3], args[1::3], args[2::3]):
        if act == "d":
            continue
        raw = open(os.path.join(HERE, path), "rb").read()
        s = open(os.path.join(HERE, name + ".bz2"), "rb").read()
        ok = bz2.decompress(s) == raw
        if TOOL:
            p = subprocess.run([TOOL, "-dc"], input=s, capture_output=True)
            ok = ok and p.returncode == 0 and p.stdout == raw
        if not ok:
            bad.append(name)
        n += 1
    if bad:
        print("compressed streams that do not decode back:", " ".join(bad))
        sys.exit(1)
    print("%d compressed streams decode back (%s)" % (n, "bz2 and bzip2 -d" if TOOL else "bz2 only; bzip2 tool missing"))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "verify":
        verify()
    else:
        main(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
