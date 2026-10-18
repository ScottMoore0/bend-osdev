#!/usr/bin/env python3
"""Writes ../jsample.bend: the small image with a journal that check.bend
writes through the journal.

  jsample.py WORKDIR

mke2fs 1.47.0 makes the image from a fixed tree, with a fixed UUID and
clock (E2FSPROGS_FAKE_TIME): ext4 (extents, 64bit, flex_bg,
metadata_csum), 1 KiB blocks, 4096 blocks, 32 inodes, a journal of 1024
blocks, no resize inode; the journal's superblock is then given csum_v3
(crc32c), so the transactions check.bend writes carry checksums.
jsample.bend keeps the non-zero runs of every non-zero block (a writer
needs the bitmaps too). Run it again only to change the sample;
check.bend's expected lines then change too.
"""
import os, shutil, struct, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import model

UUID = "7b2f5011-1c6f-4f20-8d3e-4f5061728394"

def run(cmd, **kw):
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **kw)

def main():
    work = sys.argv[1]
    root = os.path.join(work, "jsample.tree")
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(os.path.join(root, "dir"))
    with open(os.path.join(root, "a"), "wb") as f:
        f.write(b"the first file\n")
    with open(os.path.join(root, "dir", "b"), "wb") as f:
        f.write(bytes((i * 5 + 1) % 251 for i in range(2000)))
    for p, ds, fs in os.walk(root):
        for n in fs + ds + [p]:
            q = os.path.join(p, n) if n != p else p
            os.utime(q, (1700000000, 1700000000), follow_symlinks=False)
    img = os.path.join(work, "jsample.img")
    with open(img, "wb") as f:
        f.truncate(4096 * 1024)
    env = dict(os.environ, E2FSPROGS_FAKE_TIME="1700000000")
    run(["mke2fs", "-q", "-F", "-t", "ext4", "-b", "1024", "-N", "32", "-L", "jsample", "-J", "size=1",
         "-O", "^resize_inode", "-U", UUID, "-E", "root_owner=0:0,lazy_itable_init=0", "-d", root, img], env=env)
    # the journal's superblock with csum_v3 (crc32c), resealed
    jb = [int(x) for x in subprocess.run(["debugfs", "-R", "blocks <8>", img], capture_output=True, text=True).stdout.split()]
    data = bytearray(open(img, "rb").read())
    raw = bytearray(data[jb[0] * 1024:(jb[0] + 1) * 1024])
    struct.pack_into(">I", raw, 0x28, (struct.unpack_from(">I", raw, 0x28)[0] & ~0x18) | 16)
    raw[0x50] = 4
    data[jb[0] * 1024:(jb[0] + 1) * 1024] = model.jsb_with(bytes(raw), 0, struct.unpack_from(">I", raw, 0x18)[0])
    open(img, "wb").write(data)
    if subprocess.run(["e2fsck", "-fn", img], capture_output=True).returncode != 0:
        raise SystemExit("e2fsck rejects the sample")
    blocks = []
    for n in range(len(data) // 1024):
        blk = bytes(data[n * 1024:(n + 1) * 1024])
        if not any(blk):
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
    with open(os.path.join(HERE, "..", "jsample.bend"), "w") as f:
        f.write("# bend-osdev-ext4: the image with a journal check.bend writes through the\n")
        f.write("# journal (a test fixture, not part of the interface). Written by\n")
        f.write("# ref/jsample.py with mke2fs 1.47.0: ext4, 1 KiB blocks, 4096 blocks, 32\n")
        f.write("# inodes, a 1024-block journal given csum_v3, files /a and /dir/b. Every\n")
        f.write("# non-zero block is kept, as its non-zero runs.\n")
        f.write("import Base\nimport ../bytes/bytes.bend as B\nimport ../blockdev/blockdev.bend as D\nimport ./sample.bend as SM\n\n")
        names = []
        for k in range(0, len(blocks), 20):
            name = "Ext4JSample.blocks%d" % (k // 20)
            names.append(name)
            f.write("def %s() -> List<&2, SM.Ext4SampleBlock>:\n  [\n" % name)
            items = []
            for n, runs in blocks[k:k + 20]:
                rs = ", ".join("SM.Ext4SampleRun{%dn, [%s]}" % (o, ", ".join(str(b) for b in bs)) for o, bs in runs)
                items.append("    SM.Ext4SampleBlock{%dn, [%s]}" % (n, rs))
            f.write(",\n".join(items) + "\n  ]\n\n")
        f.write("# the image as a device of 1 KiB blocks\n")
        f.write("def Ext4JSample.device() -> D.MemDev:\n")
        expr = "D.MemDev.blank(1024n, 4096n)"
        for name in names:
            expr = "SM.Ext4Sample.write(%s(), %s)" % (name, expr)
        f.write("  %s\n" % expr)
    print(len(blocks), "blocks")

main()
