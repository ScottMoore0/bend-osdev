#!/usr/bin/env python3
"""Writes ../sample.bend: the small ext4 image check.bend reads.

  sample.py WORKDIR

mke2fs 1.47.0 makes the image from a fixed tree, with a fixed UUID, hash
seed and clock (E2FSPROGS_FAKE_TIME): ext4, 1 KiB blocks, 2048 blocks, 64
inodes, features dir_index, has_journal, inline_data, ea_inode,
metadata_csum. e2fsck -fD indexes /big (150 hard links to /target);
debugfs adds extended attributes
(one in an EA inode) and three journal transactions (blocks 1900 to 1902,
1900 revoked). sample.bend keeps only the non-zero runs of the blocks the
package reads (the bitmaps are left out). Run it again only to change the
sample; check.bend's expected lines then change too.
"""
import os, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
UUID = "6a1e4f00-0b5e-4e1f-9c2d-3e4f5a6b7c8d"
SEED = "0c1d2e3f-4a5b-4c6d-8e7f-90a1b2c3d4e5"

def tree(root):
    os.makedirs(os.path.join(root, "big"))
    with open(os.path.join(root, "target"), "wb") as f:
        f.write(b"one inode, many names")
    for i in range(150):
        os.link(os.path.join(root, "target"), os.path.join(root, "big", "f_%d" % i))
    os.makedirs(os.path.join(root, "small"))
    with open(os.path.join(root, "small", "a"), "wb") as f:
        f.write(b"hi\n")
    with open(os.path.join(root, "inl"), "wb") as f:
        f.write(b"x" * 50)
    with open(os.path.join(root, "inl2"), "wb") as f:
        f.write(bytes(range(32, 132)))
    with open(os.path.join(root, "file"), "wb") as f:
        f.write(bytes((i * 7 + 3) % 251 for i in range(1500)))
    for p, ds, fs in os.walk(root):
        for n in fs + ds + [p]:
            q = os.path.join(p, n) if n != p else p
            os.utime(q, (1700000000, 1700000000), follow_symlinks=False)

def run(cmd, **kw):
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **kw)

def block(byte, n=1024, head=b""):
    return head + bytes([byte]) * (n - len(head))

def main():
    work = sys.argv[1]
    root = os.path.join(work, "sample.tree")
    shutil.rmtree(root, ignore_errors=True)
    tree(root)
    img = os.path.join(work, "sample.img")
    with open(img, "wb") as f:
        f.truncate(2048 * 1024)
    env = dict(os.environ, E2FSPROGS_FAKE_TIME="1700000000")
    run(["mke2fs", "-q", "-F", "-t", "ext4", "-b", "1024", "-N", "64", "-L", "sample",
         "-O", "dir_index,has_journal,inline_data,ea_inode,metadata_csum",
         "-U", UUID, "-E", "hash_seed=%s,root_owner=0:0" % SEED, "-d", root, img], env=env)
    subprocess.run(["e2fsck", "-fyD", img], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
    big = os.path.join(work, "ea.val")
    with open(big, "wb") as f:
        f.write(bytes((i * 13 + 5) % 256 for i in range(1100)))
    mid = os.path.join(work, "ea.mid")
    with open(mid, "wb") as f:
        f.write(bytes((i * 3 + 1) % 256 for i in range(300)))
    cmds = os.path.join(work, "ea.cmds")
    with open(cmds, "w") as f:
        f.write("ea_set /file user.short hello\n")
        f.write("ea_set -f %s /file user.mid\n" % mid)
        f.write("ea_set -f %s /file user.huge\n" % big)
    run(["debugfs", "-w", "-f", cmds, img], env=env)
    # debugfs's ea_set leaves i_blocks short; e2fsck puts it right
    subprocess.run(["e2fsck", "-fy", img], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
    d1 = os.path.join(work, "j.d1")
    with open(d1, "wb") as f:
        f.write(block(0, head=b"first journalled block") + block(0, head=b"second journalled block"))
    d2 = os.path.join(work, "j.d2")
    with open(d2, "wb") as f:
        f.write(block(0, head=bytes([192, 59, 57, 152]) + b" starts with the magic number"))
    with open(cmds, "w") as f:
        f.write("jo -c\njw -b 1900,1901 %s\njw -r 1900\njw -b 1902 %s\njc\n" % (d1, d2))
    run(["debugfs", "-w", "-f", cmds, img], env=env)
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
    with open(os.path.join(HERE, "..", "sample.bend"), "w") as f:
        f.write("# bend-osdev-ext4: the sample image check.bend reads (a test fixture, not\n")
        f.write("# part of the interface). Written by ref/sample.py with mke2fs 1.47.0:\n")
        f.write("# ext4, 1 KiB blocks, 2048 blocks, 64 inodes, dir_index, has_journal,\n")
        f.write("# inline_data, ea_inode, metadata_csum; /big indexed by e2fsck -D;\n")
        f.write("# attributes and three journal transactions added by debugfs. Only the\n")
        f.write("# non-zero runs of the blocks a reader needs are kept.\n")
        f.write("import Base\nimport ../bytes/bytes.bend as B\nimport ../blockdev/blockdev.bend as D\n\n")
        f.write("type Ext4SampleRun is Data:\n  Ext4SampleRun{offset: Nat, bytes: List<&2, U32>}\n\n")
        f.write("type Ext4SampleBlock is Data:\n  Ext4SampleBlock{block: Nat, runs: List<&2, Ext4SampleRun>}\n\n")
        f.write("def Ext4Sample.fill(runs: List<&2, Ext4SampleRun>, +pos: Nat) -> B.Octets:\n")
        f.write("  match runs:\n    case Nil{}:\n      B.Octets.zeros(Nat.sub(1024n, pos))\n")
        f.write("    case Con{Ext4SampleRun{+off, xs}, t}:\n      +o = B.Octets.of_list(xs)\n")
        f.write("      B.Octets.append(B.Octets.zeros(Nat.sub(off, pos)), B.Octets.append(o, Ext4Sample.fill(t, Nat.add(off, B.Octets.len(o)))))\n\n")
        f.write("def Ext4Sample.write(bs: List<&2, Ext4SampleBlock>, d: D.MemDev) -> D.MemDev:\n")
        f.write("  match bs:\n    case Nil{}:\n      d\n    case Con{Ext4SampleBlock{n, runs}, t}:\n")
        f.write("      Ext4Sample.write(t, D.MemDev.update(d, n, Ext4Sample.fill(runs, 0n)))\n\n")
        # the block list in pieces of at most 20 blocks, so no literal is long
        names = []
        for k in range(0, len(blocks), 20):
            name = "Ext4Sample.blocks%d" % (k // 20)
            names.append(name)
            f.write("def %s() -> List<&2, Ext4SampleBlock>:\n  [\n" % name)
            items = []
            for n, runs in blocks[k:k + 20]:
                rs = ", ".join("Ext4SampleRun{%dn, [%s]}" % (o, ", ".join(str(b) for b in bs)) for o, bs in runs)
                items.append("    Ext4SampleBlock{%dn, [%s]}" % (n, rs))
            f.write(",\n".join(items) + "\n  ]\n\n")
        f.write("# the image as a device of 1 KiB blocks\n")
        f.write("def Ext4Sample.device() -> D.MemDev:\n")
        expr = "D.MemDev.blank(1024n, 2048n)"
        for name in names:
            expr = "Ext4Sample.write(%s(), %s)" % (name, expr)
        f.write("  %s\n" % expr)
    print(len(blocks), "blocks")

main()
