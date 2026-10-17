# bend-osdev-fdt, example.bend: a sample devicetree, modelled on the example
# in the Devicetree Specification v0.4, chapter 2 (a board with two CPUs,
# memory, a serial port, /chosen and /aliases), with one memory reservation.
# check.bend and LAWS.bend use it; it is public so that users can try the
# package on a known tree.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./rsvmap.bend as R
import ./tree.bend as T
import ./props.bend as P

def ex.s(x: String) -> B.Octets:
  B.Octets.of_string(x)

def ex.text(k: String, v: String) -> T.FdtProp:
  T.FdtProp{ex.s(k), P.FdtProp.of_text(v)}

def ex.u32(k: String, v: U32) -> T.FdtProp:
  T.FdtProp{ex.s(k), P.FdtProp.of_u32(v)}

def ex.cells(k: String, v: List<&2, U32>) -> T.FdtProp:
  T.FdtProp{ex.s(k), P.FdtProp.of_cells(v)}

def ex.cpu(name: String, +reg: U32) -> T.FdtNode:
  T.FdtNode{ex.s(name), [ex.text("device_type", "cpu"), ex.u32("reg", reg), ex.u32("timebase-frequency", 825000000), ex.u32("clock-frequency", 825000000)], []}

# 0xfe001000 = 4261416960, 0x20000000 = 536870912
def FdtExample.tree() -> T.FdtNode:
  T.FdtNode{ex.s(""), [ex.text("model", "fsl,mpc8572ds"), ex.text("compatible", "fsl,mpc8572ds"), ex.u32("#address-cells", 1), ex.u32("#size-cells", 1)], [T.FdtNode{ex.s("cpus"), [ex.u32("#address-cells", 1), ex.u32("#size-cells", 0)], [ex.cpu("cpu@0", 0), ex.cpu("cpu@1", 1)]}, T.FdtNode{ex.s("memory@0"), [ex.text("device_type", "memory"), ex.cells("reg", [0, 536870912])], []}, T.FdtNode{ex.s("uart@fe001000"), [ex.text("compatible", "ns16550"), ex.cells("reg", [4261416960, 256])], []}, T.FdtNode{ex.s("chosen"), [ex.text("bootargs", "root=/dev/sda2")], []}, T.FdtNode{ex.s("aliases"), [ex.text("serial0", "/uart@fe001000")], []}]}

# one reservation: 64 KiB at 0x10000000 (268435456)
def FdtExample.rsv() -> List<&2, R.FdtRsv>:
  [R.FdtRsv{W.W64.from_u32(268435456), W.W64.from_u32(65536)}]
