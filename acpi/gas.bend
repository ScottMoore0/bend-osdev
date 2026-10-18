# bend-osdev-acpi, gas.bend: the Generic Address Structure (ACPI 6.5,
# section 5.2.3.2), 12 bytes:
#
#   offset  size  field
#        0     1  Address Space ID (0 system memory, 1 system I/O, 2 PCI
#                 configuration space, 3 embedded controller, 4 SMBus,
#                 5 CMOS, 6 PCI BAR target, 7 IPMI, 8 GPIO, 9 generic
#                 serial bus, 10 PCC, 11 PRM, 0x7F functional fixed hardware)
#        1     1  Register Bit Width
#        2     1  Register Bit Offset
#        3     1  Access Size (0 undefined, 1 byte, 2 word, 3 dword, 4 qword)
#        4     8  Address
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./fields.bend as F

type AcpiGas is Data:
  AcpiGas{space: U32, bit_width: U32, bit_offset: U32, access_size: U32, address: W.W64}

def AcpiGas.space_memory() -> U32:
  0

def AcpiGas.space_io() -> U32:
  1

def AcpiGas.space_pci_config() -> U32:
  2

def AcpiGas.space_ec() -> U32:
  3

def AcpiGas.space_ffixedhw() -> U32:
  127

def AcpiGas.size() -> Nat:
  12n

# the structure at offset i of o
def AcpiGas.at(+o: B.Octets, +i: Nat) -> AcpiGas:
  AcpiGas{F.AcpiF.u8(o, i), F.AcpiF.u8(o, Nat.add(i, 1n)), F.AcpiF.u8(o, Nat.add(i, 2n)), F.AcpiF.u8(o, Nat.add(i, 3n)), F.AcpiF.u64(o, Nat.add(i, 4n))}

def AcpiGas.encode(g: AcpiGas) -> B.Octets:
  match g:
    case AcpiGas{s, w, off, a, addr}:
      B.Octets.append(B.Octets.of_list([s, w, off, a]), B.Octets.le64(addr))

def AcpiGas.zero() -> AcpiGas:
  AcpiGas{0, 0, 0, 0, W.W64.zero()}

def AcpiGas.address(g: AcpiGas) -> W.W64:
  match g:
    case AcpiGas{s, w, off, a, addr}:
      addr

def AcpiGas.space(g: AcpiGas) -> U32:
  match g:
    case AcpiGas{s, w, off, a, addr}:
      s

# no register: the address is zero
def AcpiGas.is_null(g: AcpiGas) -> Bool:
  W.W64.is_zero(AcpiGas.address(g))

# a system I/O register block at a 32-bit port address, n bytes long (how
# the FADT's ACPI 1.0 block fields are read as Generic Addresses)
def AcpiGas.io_block(port: U32, n: U32) -> AcpiGas:
  AcpiGas{1, U32.and(255, U32.mul(n, 8)), 0, 0, W.W64.from_u32(port)}

def AcpiGas.show(g: AcpiGas) -> String:
  match g:
    case AcpiGas{s, w, off, a, addr}:
      "{" ++ U32.show(s) ++ " " ++ U32.show(w) ++ " " ++ U32.show(off) ++ " " ++ U32.show(a) ++ " " ++ W.W64.show_hex(addr) ++ "}"
