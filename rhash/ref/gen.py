#!/usr/bin/env python3
"""Differential test cases for bend-osdev-rhash.

Writes ref/cases.bend (a Bend program that runs random sequences of
inserts, removes, explicit migration steps and explicit resizes on tables,
and prints every key's lookup and the size after each batch) and
ref/expected.txt (the same from a Python dict, which never resizes).

Each scenario mixes the operations with migrations under way: the policies
move one or four old buckets per operation, so a resize spans many
operations, and explicit steps and resizes land at random points in it.
Three key setups: U32 keys under the default hash (khash's jhash2), U32
keys under a hash that sends every key to bucket 0 (a table must stay
right whatever its hash does), and word-list keys of one to three words.
"""
import os, random, sys

SCEN = [
    # name, params (Bend expression), hash, key kind, key range, ops
    ("default", "R.RhParams.default()", "~R.RHash.jhash2", "u32", 300, 1200),
    ("shrink-1step", "R.RhParams{70n, 30n, True{}, 2n, 31n, 2n, 1n, 7, 2654435769}", "~R.RHash.jhash2", "u32", 200, 1200),
    ("one-bucket", "R.RhParams{70n, 30n, True{}, 1n, 6n, 1n, 1n, 0, 1}", "~flat", "u32", 60, 500),
    ("words", "R.RhParams{60n, 20n, True{}, 2n, 31n, 3n, 2n, 123, 99}", "~R.RHash.jhash2", "words", 120, 900),
]
BATCH = 100


def key_bend(kind, k):
    if kind == "u32":
        return str(k)
    return "[" + ", ".join(str(x) for x in k) + "]"


def key_types(kind):
    if kind == "u32":
        return "U32", "~R.RHash.key_u32"
    return "List<&2, U32>", "~R.RHash.key_words"


def keys_of(kind, rng, n):
    if kind == "u32":
        return list(rng.sample(range(0, 4000000000), n))
    out = set()
    while len(out) < n:
        out.add(tuple(rng.randrange(0, 5) for _ in range(rng.randrange(1, 4))))
    return sorted(out)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    here = os.path.dirname(os.path.abspath(__file__))
    defs, mains, expect = [], [], []
    for si, (name, params, hsh, kind, nkeys, nops) in enumerate(SCEN):
        K, enc = key_types(kind)
        A = f"~{K}, ~U32, {enc}, {hsh}"
        keys = keys_of(kind, rng, nkeys)
        model = {}
        ops = []
        for _ in range(nops):
            r = rng.random()
            k = rng.choice(keys)
            if r < 0.55:
                v = rng.randrange(0, 1 << 32)
                ops.append(f"R.RhIns{{{key_bend(kind, k)}, {v}}}")
                model[k] = v
            elif r < 0.85:
                ops.append(f"R.RhDel{{{key_bend(kind, k)}}}")
                model.pop(k, None)
            elif r < 0.95:
                ops.append("R.RhStep{}")
            else:
                ops.append(f"R.RhResize{{{rng.randrange(0, 9)}n, {rng.randrange(0, 1 << 32)}}}")
            if len(ops) % BATCH == 0:
                b = len(ops) // BATCH - 1
                defs.append(f"def s{si}.ops{b}() -> List<&2, R.RhOp<{K}, U32>>:\n  [" + ", ".join(ops[-BATCH:]) + "]\n")
                expect.append(f"{name} {b}: size {len(model)} " + " ".join(
                    "-" if k not in model else str(model[k]) for k in keys))
        nb = len(ops) // BATCH
        defs.append(f"def s{si}.keys() -> List<&2, {K}>:\n  [" + ", ".join(key_bend(kind, k) for k in keys) + "]\n")
        defs.append(
            f"def s{si}.look(+t: R.RHash<{K}, U32>, ks: List<&2, {K}>) -> String:\n"
            f"  match ks:\n    case Nil{{}}:\n      \"\"\n    case Con{{k, rest}}:\n"
            f"      \" \" ++ show(R.RHash.lookup({A}, t, k)) ++ s{si}.look(t, rest)\n")
        defs.append(
            f"def s{si}.report(b: Nat, +t: R.RHash<{K}, U32>) -> String:\n"
            f"  \"{name} \" ++ Nat.show(b) ++ \": size \" ++ Nat.show(R.RHash.size(~{K}, ~U32, t)) ++ s{si}.look(t, s{si}.keys())\n")
        body = [f"def s{si}.run() -> IO(Unit):", f"  +t0 = R.RHash.new(~{K}, ~U32, {params})"]
        for b in range(nb):
            body.append(f"  +t{b + 1} = R.RHash.run({A}, t{b}, s{si}.ops{b}())")
        body.append("  do IO<Unit>:")
        for b in range(nb):
            body.append(f"    IO.print(s{si}.report({b}n, t{b + 1}))")
        defs.append("\n".join(body) + "\n")
        mains.append(f"    s{si}.run()")
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write("import Base\nimport ../rhash.bend as R\n\n")
        f.write("# every key to bucket 0\ndef flat(seed: U32, ws: List<&2, U32>) -> U32:\n  0\n\n")
        f.write("def show(m: Maybe<&2, U32>) -> String:\n  match m:\n    case None{}:\n      \"-\"\n    case Some{v}:\n      U32.show(v)\n\n")
        f.write("\n".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(mains) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(sum(n for *_, n in SCEN), "operations,", len(expect), "batches")


if __name__ == "__main__":
    main()
