#!/usr/bin/env python3
"""Differential test for bend-osdev-ebpf.

Writes ref/cases.bend (a Bend program that runs each generated eBPF program
in this package's interpreter and prints R0) and ref/expected.txt (R0 from an
independent eBPF interpreter written here from RFC 9669, "BPF Instruction Set
Architecture (ISA)"). The two interpreters share an author (see the README),
so this is a cross-check of one reading of the specification against another,
not an independent oracle.

clang's BPF target was not available in this environment (`clang -target bpf`
reported "No available targets are compatible with triple bpf", both for the
bundled clang behind $HOME/bend-audit/cc-wrap and for the system clang), and
the WSL2 kernel has unprivileged BPF disabled (kernel.unprivileged_bpf_
disabled = 2), so neither clang-compiled objects nor BPF_PROG_TEST_RUN could
be used; the independent Python model stands in. run.sh exits 77 when it
cannot run (no python3).

The generated programs are straight-line and forward-branching register
arithmetic (ALU/ALU64, moves, sign extension, byte swaps, conditional and
unconditional jumps, exit) over registers seeded with constants, with no
memory access, so both interpreters compute a defined R0 for the empty
context. Memory, the stack, helpers and the verifier are covered by
check.bend and LAWS.bend.
"""
import os, random, sys

M64 = (1 << 64) - 1
M32 = (1 << 32) - 1

def u64(x): return x & M64
def u32(x): return x & M32

def s64(x):
    x &= M64
    return x - (1 << 64) if x >> 63 else x

def s32(x):
    x &= M32
    return x - (1 << 32) if x >> 31 else x

def sext32(v):
    v &= M32
    return u64(v - (1 << 32) if v >> 31 else v)

def abs64(x): return u64(-x) if (x >> 63) else x
def abs32(x): return u32(-x) if (x >> 31) else x

# --- the reference ALU, matching alu.bend ---

def alu64(op, a, b):
    a &= M64; b &= M64
    if op == "add": return u64(a + b)
    if op == "sub": return u64(a - b)
    if op == "mul": return u64(a * b)
    if op == "or":  return a | b
    if op == "and": return a & b
    if op == "xor": return a ^ b
    if op == "lsh": return u64(a << (b & 63))
    if op == "rsh": return a >> (b & 63)
    if op == "mov": return b
    if op == "arsh": return u64(s64(a) >> (b & 63))
    if op == "div": return 0 if b == 0 else a // b
    if op == "mod": return a if b == 0 else a % b
    if op == "sdiv":
        if b == 0: return 0
        q = abs64(a) // abs64(b)
        return u64(-q) if ((a >> 63) ^ (b >> 63)) else q
    if op == "smod":
        if b == 0: return a
        r = abs64(a) % abs64(b)
        return u64(-r) if (a >> 63) else r
    raise ValueError(op)

def alu32(op, a, b):
    a &= M32; b &= M32
    if op == "add": return u32(a + b)
    if op == "sub": return u32(a - b)
    if op == "mul": return u32(a * b)
    if op == "or":  return a | b
    if op == "and": return a & b
    if op == "xor": return a ^ b
    if op == "lsh": return u32(a << (b & 31))
    if op == "rsh": return a >> (b & 31)
    if op == "mov": return b
    if op == "arsh": return u32(s32(a) >> (b & 31))
    if op == "div": return 0 if b == 0 else a // b
    if op == "mod": return a if b == 0 else a % b
    if op == "sdiv":
        if b == 0: return 0
        q = abs32(a) // abs32(b)
        return u32(-q) if ((a >> 31) ^ (b >> 31)) else q
    if op == "smod":
        if b == 0: return a
        r = abs32(a) % abs32(b)
        return u32(-r) if (a >> 31) else r
    raise ValueError(op)

def do_alu(width, op, a, b):
    if width == 64:
        return alu64(op, a, b)
    return u64(alu32(op, u32(a), u32(b)))  # 32-bit result zero-extended

def bswap(v, bits):
    v &= (1 << bits) - 1
    out = 0
    for i in range(bits // 8):
        out = (out << 8) | ((v >> (8 * i)) & 0xFF)
    return out

def cond(width, c, a, b):
    if width == 64:
        ua, ub, sa, sb = u64(a), u64(b), s64(a), s64(b)
    else:
        ua, ub, sa, sb = u32(a), u32(b), s32(a), s32(b)
    return {
        "jeq": ua == ub, "jne": ua != ub,
        "jgt": ua > ub, "jge": ua >= ub, "jlt": ua < ub, "jle": ua <= ub,
        "jsgt": sa > sb, "jsge": sa >= sb, "jslt": sa < sb, "jsle": sa <= sb,
        "jset": (ua & ub) != 0,
    }[c]

# --- an instruction is a dict; run a program, return R0 ---

def run(prog, steps=10000):
    regs = [0] * 11
    pc = 0
    while steps > 0:
        steps -= 1
        if pc < 0 or pc >= len(prog):
            return None
        i = prog[pc]
        k = i["k"]
        if k == "alu":
            b = i["imm"] if i["src"] == "K" else regs[i["sreg"]]
            if i["width"] == 64 and i["src"] == "K":
                b = sext32(i["imm"])
            regs[i["dreg"]] = do_alu(i["width"], i["op"], regs[i["dreg"]], b)
            pc += 1
        elif k == "neg":
            regs[i["dreg"]] = alu64("sub", 0, regs[i["dreg"]]) if i["width"] == 64 else u64(alu32("sub", 0, u32(regs[i["dreg"]])))
            pc += 1
        elif k == "end":
            regs[i["dreg"]] = bswap(regs[i["dreg"]], i["bits"]) if i["swap"] else (regs[i["dreg"]] & ((1 << i["bits"]) - 1))
            pc += 1
        elif k == "lddw":
            regs[i["dreg"]] = i["imm64"]
            pc += 1
        elif k == "ja":
            pc += 1 + i["off"]
        elif k == "jmp":
            b = sext32(i["imm"]) if i["src"] == "K" and i["width"] == 64 else (i["imm"] if i["src"] == "K" else regs[i["sreg"]])
            pc += 1 + (i["off"] if cond(i["width"], i["op"], regs[i["dreg"]], b) else 0)
        elif k == "exit":
            return regs[0]
    return None

# --- generate a random program and its Bend expression ---

ALU_OPS = ["add","sub","mul","div","sdiv","or","and","lsh","rsh","mod","smod","xor","mov","arsh"]
BEND_ALU = {"add":"EbpfAdd","sub":"EbpfSub","mul":"EbpfMul","div":"EbpfDiv","sdiv":"EbpfSdiv","or":"EbpfOr","and":"EbpfAnd","lsh":"EbpfLsh","rsh":"EbpfRsh","mod":"EbpfMod","smod":"EbpfSmod","xor":"EbpfXor","mov":"EbpfMov","arsh":"EbpfArsh"}
CONDS = ["jeq","jne","jgt","jge","jlt","jle","jsgt","jsge","jslt","jsle","jset"]
BEND_COND = {"jeq":"EbpfJeq","jne":"EbpfJne","jgt":"EbpfJgt","jge":"EbpfJge","jlt":"EbpfJlt","jle":"EbpfJle","jsgt":"EbpfJsgt","jsge":"EbpfJsge","jslt":"EbpfJslt","jsle":"EbpfJsle","jset":"EbpfJset"}

def reg(n): return "I.EbpfR%d{}" % n
def width_bend(w): return "I.EbpfBits64{}" if w == 64 else "I.EbpfBits32{}"
def src_bend(i):
    return "I.EbpfK{%d}" % i["imm"] if i["src"] == "K" else "I.EbpfX{%s}" % reg(i["sreg"])

def bend_insn(i):
    k = i["k"]
    if k == "alu":
        return "I.EbpfAlu{%s, I.%s{}, %s, %s}" % (width_bend(i["width"]), BEND_ALU[i["op"]], reg(i["dreg"]), src_bend(i))
    if k == "neg":
        return "I.EbpfNeg{%s, %s}" % (width_bend(i["width"]), reg(i["dreg"]))
    if k == "end":
        kind = {("le"):"EbpfToLe","be":"EbpfToBe","bswap":"EbpfBswap"}[i["kind"]]
        bits = {16:"EbpfE16",32:"EbpfE32",64:"EbpfE64"}[i["bits"]]
        return "I.EbpfEnd{I.%s{}, I.%s{}, %s}" % (kind, bits, reg(i["dreg"]))
    if k == "lddw":
        lo = i["imm64"] & M32
        hi = (i["imm64"] >> 32) & M32
        return "I.EbpfLddw{I.EbpfLdImm64{}, %s, %d, %d}" % (reg(i["dreg"]), lo, hi)
    if k == "ja":
        return "I.EbpfJa{%d}" % i["off"]
    if k == "jmp":
        src = "I.EbpfK{%d}" % i["imm"] if i["src"] == "K" else "I.EbpfX{%s}" % reg(i["sreg"])
        return "I.EbpfJmp{%s, I.%s{}, %s, %s, %d}" % (width_bend(i["width"]), BEND_COND[i["op"]], reg(i["dreg"]), src, i["off"])
    if k == "exit":
        return "I.EbpfExit{}"

def gen_program(rng):
    prog = []
    # seed R0..R5 with constants
    for r in range(6):
        prog.append({"k": "lddw", "dreg": r, "imm64": rng.getrandbits(64)})
    nbody = rng.randint(3, 14)
    for _ in range(nbody):
        choice = rng.random()
        if choice < 0.62:
            w = rng.choice([32, 64])
            op = rng.choice(ALU_OPS)
            if rng.random() < 0.5:
                prog.append({"k":"alu","width":w,"op":op,"dreg":rng.randint(0,5),"src":"K","imm":rng.getrandbits(32)})
            else:
                prog.append({"k":"alu","width":w,"op":op,"dreg":rng.randint(0,5),"src":"X","sreg":rng.randint(0,5)})
        elif choice < 0.70:
            prog.append({"k":"neg","width":rng.choice([32,64]),"dreg":rng.randint(0,5)})
        elif choice < 0.80:
            bits = rng.choice([16,32,64])
            kind = rng.choice(["le","be"]) if bits != 64 else rng.choice(["le","be","bswap"])
            if kind == "bswap" and bits == 64:
                prog.append({"k":"end","kind":"bswap","bits":64,"swap":True,"dreg":rng.randint(0,5)})
            else:
                prog.append({"k":"end","kind":kind,"bits":bits,"swap":(kind=="be"),"dreg":rng.randint(0,5)})
        else:
            # a forward conditional jump skipping 1..2 of the following body
            off = rng.randint(1, 2)
            w = rng.choice([32, 64])
            op = rng.choice(CONDS)
            if rng.random() < 0.5:
                prog.append({"k":"jmp","width":w,"op":op,"dreg":rng.randint(0,5),"src":"K","imm":rng.getrandbits(32),"off":off})
            else:
                prog.append({"k":"jmp","width":w,"op":op,"dreg":rng.randint(0,5),"src":"X","sreg":rng.randint(0,5),"off":off})
            # pad so the jump never lands past exit
            for _ in range(off):
                prog.append({"k":"alu","width":64,"op":"add","dreg":rng.randint(0,5),"src":"K","imm":rng.getrandbits(16)})
    prog.append({"k":"alu","width":64,"op":"mov","dreg":0,"src":"X","sreg":rng.randint(0,5)})
    prog.append({"k":"exit"})
    return prog

def fix_end_swap(i, host_le=True):
    # TO_LE swaps on a big-endian host only; here the host is little-endian
    pass

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    n = 240
    lines, expect = [], []
    for idx in range(n):
        prog = gen_program(rng)
        r0 = run(prog)
        if r0 is None:
            continue
        exprs = ", ".join(bend_insn(i) for i in prog)
        lines.append('    IO.print("p%d " ++ outp(R.ebpf_run([%s], mem)))' % (idx, exprs))
        expect.append("p%d ok %d" % (idx, u64(r0)))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\n")
        f.write("import ../../word64/word64.bend as W\n")
        f.write("import ../../bytes/bytes.bend as B\n")
        f.write("import ../../bpf/insn.bend as C\n")
        f.write("import ../insn.bend as I\n")
        f.write("import ../memory.bend as M\n")
        f.write("import ../interp.bend as R\n\n")
        f.write("def outp(o: R.EbpfOutcome) -> String:\n")
        f.write("  match o:\n")
        f.write("    case R.EbpfOk{v}:\n      \"ok \" ++ W.W64.show(v)\n")
        f.write("    case R.EbpfErr{e}:\n      \"err\"\n\n")
        f.write("def mem() -> M.EbpfMem:\n  M.EbpfMem.new(C.BpfLittle{}, B.Octets.empty(), B.Octets.empty(), Nil{})\n\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
