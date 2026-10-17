#!/usr/bin/env python3
"""Writes ../sample.bend: the small ext4 image check.bend reads.

  sample.py WORKDIR

The image is made by mke2fs 1.47.0 from a fixed tree, with a fixed UUID,
hash seed and clock (E2FSPROGS_FAKE_TIME; the inodes' change times still
come from the real clock, so checksums differ from run to run). sample.bend
holds only the non-zero runs of the blocks the package reads (the bitmaps
are left out: a reader never needs them). Run it again only to change the
sample; check.bend's expected lines then change too.
"""
import os, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))

def tree(root):
    os.makedirs(os.path.join(root, "docs"))
    with open(os.path.join(root, "hello.txt"), "wb") as f:
        f.write(b"Hello, ext4!\n")
    with open(os.path.join(root, "docs", "notes.txt"), "wb") as f:
        f.write(bytes((i * 7 + 3) % 251 for i in range(5000)))
    open(os.path.join(root, "docs", "empty"), "wb").close()
    with open(os.path.join(root, "sparse"), "wb") as f:
        f.write(b"head" * 25)
        f.seek(20000)
        f.write(b"tail" * 25)
    os.symlink("hello.txt", os.path.join(root, "link"))
    os.symlink("../" * 25 + "hello.txt", os.path.join(root, "docs", "long-link"))
    os.symlink("docs", os.path.join(root, "up"))
    for p, ds, fs in os.walk(root):
        for n in fs + ds + [p]:
            q = os.path.join(p, n) if n != p else p
            os.utime(q, (1700000000, 1700000000), follow_symlinks=False)

def main():
    work = sys.argv[1]
    root = os.path.join(work, "sample.tree")
    shutil.rmtree(root, ignore_errors=True)
    tree(root)
    img = os.path.join(work, "sample.img")
    with open(img, "wb") as f:
        f.truncate(256 * 1024)
    env = dict(os.environ, E2FSPROGS_FAKE_TIME="1700000000")
    subprocess.run(["mke2fs", "-q", "-F", "-t", "ext4", "-b", "1024", "-N", "32", "-L", "sample",
                    "-U", "0b5e1f2a-3c4d-4e5f-8a6b-7c8d9e0f1a2b", "-E", "hash_seed=1a2b3c4d-5e6f-4a1b-8c2d-3e4f5a6b7c8d,root_owner=0:0",
                    "-d", root, img], check=True, env=env)
    data = open(img, "rb").read()
    out = subprocess.run(["dumpe2fs", img], capture_output=True, text=True).stdout
    skip = set()
    for line in out.splitlines():
        line = line.strip()
        for key in ("Block bitmap at ", "Inode bitmap at "):
            if line.startswith(key):
                skip.add(int(line[len(key):].split()[0].split(",")[0]))
    blocks = []
    for n in range(len(data) // 1024):
        blk = data[n * 1024:(n + 1) * 1024]
        if n in skip or not any(blk):
            continue
        runs, i = [], 0
        while i < 1024:
            if blk[i] == 0:
                i += 1
                continue
            j = i
            while j < 1024 and (any(blk[j:j + 8])):
                j += 1
            runs.append((i, blk[i:j]))
            i = j
        blocks.append((n, runs))
    lines = []
    for n, runs in blocks:
        rs = ", ".join("Ext2SampleRun{%dn, [%s]}" % (off, ", ".join(map(str, b))) for off, b in runs)
        lines.append("    Ext2SampleBlock{%dn, [%s]}" % (n, rs))
    with open(os.path.join(HERE, "..", "sample.bend"), "w") as f:
        f.write('''# bend-osdev-ext2: the sample image check.bend reads (a test fixture, not
# part of the interface). Written by ref/sample.py from a small tree with
# mke2fs 1.47.0: ext4, 1 KiB blocks, 256 blocks, 32 inodes, metadata_csum,
# label "sample". Only the non-zero runs of the blocks a reader needs are
# kept; every other byte is zero.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D

type Ext2SampleRun is Data:
  Ext2SampleRun{offset: Nat, bytes: List<&2, U32>}

type Ext2SampleBlock is Data:
  Ext2SampleBlock{block: Nat, runs: List<&2, Ext2SampleRun>}

def Ext2Sample.fill(runs: List<&2, Ext2SampleRun>, +pos: Nat) -> B.Octets:
  match runs:
    case Nil{}:
      B.Octets.zeros(Nat.sub(1024n, pos))
    case Con{Ext2SampleRun{+off, xs}, t}:
      +o = B.Octets.of_list(xs)
      B.Octets.append(B.Octets.zeros(Nat.sub(off, pos)), B.Octets.append(o, Ext2Sample.fill(t, Nat.add(off, B.Octets.len(o)))))

def Ext2Sample.write(bs: List<&2, Ext2SampleBlock>, d: D.MemDev) -> D.MemDev:
  match bs:
    case Nil{}:
      d
    case Con{Ext2SampleBlock{n, runs}, t}:
      Ext2Sample.write(t, D.MemDev.update(d, n, Ext2Sample.fill(runs, 0n)))

def Ext2Sample.blocks() -> List<&2, Ext2SampleBlock>:
  [
''' + ",\n".join(lines) + '''
  ]

# the sample image, as an in-memory device of 256 blocks of 1 KiB
def Ext2Sample.dev() -> D.MemDev:
  Ext2Sample.write(Ext2Sample.blocks(), D.MemDev.blank(1024n, 256n))
''')
    print(len(blocks), "blocks,", sum(len(b) for _, r in blocks for _, b in r), "bytes")
    print(subprocess.run(["debugfs", "-R", "ls -l /", img], capture_output=True, text=True).stdout)

main()
