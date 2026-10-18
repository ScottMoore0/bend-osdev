#!/usr/bin/env python3
"""Differential test cases for bend-osdev-tcpip's TCP connection.

Writes ref/cases.bend (a Bend program that runs random event scripts through
sim.bend's two-endpoint network and prints each trace) and ref/expected.txt
(the same traces from model.py, an independent model of the connection
written from RFC 9293, 6298 and 5681 and the README's stated choices).

The scripts open connections (one side active and one passive, both active
at once, or one active with nothing listening), send data of random sizes,
deliver, lose and hold segments, let time pass (so that retransmission, zero
window probes, TIME-WAIT and giving up happen), read, close and abort.
"""
import os, random, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model as M

def bend_bool(b):
    return "True{}" if b else "False{}"

def bend_event(ev):
    if ev[0] == "open":
        return "T.TcpCallOpen{%s}" % bend_bool(ev[1])
    if ev[0] == "send":
        return "T.TcpCallSend{text(%dn, %d)}" % (len(ev[1]), ev[2])
    if ev[0] == "read":
        return "T.TcpCallRead{%d}" % ev[1]
    if ev[0] == "close":
        return "T.TcpCallClose{}"
    return "T.TcpCallAbort{}"

def bend_cmd(c):
    if c[0] == "call":
        return "M.TcpSimCall{%s, %s}" % (bend_bool(c[1]), bend_event(c[2]))
    if c[0] == "deliver":
        return "M.TcpSimDeliver{%s}" % bend_bool(c[1])
    if c[0] == "drop":
        return "M.TcpSimDrop{%s}" % bend_bool(c[1])
    if c[0] == "tick":
        return "M.TcpSimTick{%d}" % c[1]
    return "M.TcpSimFlush{}"

# n letters from a linear congruential generator seeded with s; cases.bend's
# text(n, s) makes the same, so the data need not be written out
def text(n, s):
    out = []
    for _ in range(n):
        s = (s * 1103515245 + 12345) & 0xFFFFFFFF
        out.append(97 + (s >> 16) % 26)
    return bytes(out)

def data(rng):
    n = rng.choice([0, 1, 5, 40, 300, 900, 2000, 5000])
    s = rng.randrange(2 ** 32)
    return text(n, s), s

def options(rng):
    return M.Options(
        mss=rng.choice([1460, 536, 100]),
        rcv_buf=rng.choice([65535, 65535, 4000, 1000]),
        snd_buf=rng.choice([65535, 65535, 3000]),
        nagle=rng.random() < 0.7,
        app_reads=rng.random() < 0.3,
        retries=rng.choice([8, 3]),
        syn_retries=rng.choice([7, 2]),
        msl=rng.choice([120000, 1000]),
        ooo_limit=rng.choice([64, 2]),
    )

def script(rng):
    cs = []
    kind = rng.random()
    if kind < 0.75:
        cs += [("call", False, ("open", False)), ("call", True, ("open", True))]
    elif kind < 0.9:
        cs += [("call", True, ("open", True)), ("call", False, ("open", True))]
    else:
        cs += [("call", True, ("open", True))]
    for _ in range(rng.randrange(10, 50)):
        r = rng.random()
        side = rng.random() < 0.5
        if r < 0.22:
            cs.append(("deliver", side))
        elif r < 0.30:
            cs.append(("drop", side))
        elif r < 0.45:
            cs.append(("flush",))
        elif r < 0.60:
            cs.append(("tick", rng.choice([0, 10, 200, 1000, 1500, 3000, 7000, 30000])))
        elif r < 0.80:
            d, s = data(rng)
            cs.append(("call", side, ("send", d, s)))
        elif r < 0.86:
            cs.append(("call", side, ("read", rng.choice([1, 100, 5000]))))
        elif r < 0.95:
            cs.append(("call", side, ("close",)))
        elif r < 0.97:
            cs.append(("call", side, ("abort",)))
        else:
            cs.append(("call", side, ("open", rng.random() < 0.5)))
    cs += [("flush",), ("tick", 1000), ("flush",), ("tick", 300000), ("flush",)]
    return cs

TEXT = """# n letters from a linear congruential generator seeded with s (gen.py's
# text)
def text.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+m:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      text.go(m, s2, Con{U32.add(97, U32.mod(U32.shrn(s2, 16n), 26)), acc})

def text(n: Nat, s: U32) -> B.Octets:
  B.Octets.of_list(text.go(n, s, Nil{}))

"""

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    progs, expect = [], []
    for k in range(count):
        oa, ob = options(rng), options(rng)
        ia, ib = rng.randrange(2 ** 32), rng.randrange(2 ** 32)
        if k % 10 == 0:
            ia = 2 ** 32 - rng.randrange(1, 3000)   # sequence numbers that wrap
        cs = script(rng)
        sim = M.Sim(oa, ia, ob, ib)
        for c in cs:
            sim.cmd(c)
        expect.append("== case %d" % k)
        expect.append(sim.trace())
        expect.append("")
        progs.append('    IO.print("== case %d")\n    IO.print(M.TcpSim.trace(CC.RenoState, M.TcpSim.run(~CC.RenoState, ~CC.Reno.cc(), [%s], M.TcpSim.new(~CC.RenoState, ~CC.Reno.cc(), %s, %d, %s, %d))))' % (
            k, ", ".join(bend_cmd(c) for c in cs), oa.bend(), ia, ob.bend(), ib))
    with open(os.path.join(here, "cases.bend"), "w", newline=chr(10)) as f:
        f.write("import Base\nimport ../../bytes/bytes.bend as B\nimport ../tcp.bend as T\nimport ../rto.bend as R\nimport ../cc.bend as CC\nimport ../sim.bend as M\n\n")
        f.write(TEXT)
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(progs) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline=chr(10)) as f:
        f.write("\n".join(expect) + "\n")
    print(count, "cases,", sum(len(e.split("\n")) for e in expect[1::3]), "trace lines")

main()
