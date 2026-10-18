# bend-osdev-acpi, error.bend: why a table, an AML definition block or an
# AML evaluation was refused. One constructor per failure, so a caller can
# tell them apart.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

type AcpiError is Data:
  # Tables

  # fewer bytes than the structure needs: need, got
  AcpiTooShort{need: Nat, got: Nat}
  # the signature is not the one the parser reads
  AcpiBadSignature{got: B.Octets}
  # a table's length field below its header, or past the bytes given
  AcpiBadLength{length: U32}
  # the bytes of a table do not sum to 0 mod 256 (the sum, mod 256)
  AcpiBadChecksum{sum: U32}
  # the RSDP's first 20 bytes do not sum to 0 mod 256
  AcpiRsdpBadChecksum{sum: U32}
  # the RSDP (revision 2 or later) does not sum to 0 mod 256 over its length
  AcpiRsdpBadExtChecksum{sum: U32}
  # a revision this parser does not read
  AcpiBadRevision{revision: U32}
  # a sub-structure (MADT, SRAT entry) at this offset in the table's body is
  # shorter than 2 bytes, shorter than its type needs, or runs past the table
  AcpiBadEntry{offset: Nat, kind: U32}
  # a table's body does not hold what its fields say (an SLIT matrix that
  # does not fit, an RSDT/XSDT body that is not a whole number of entries)
  AcpiBadSize{size: Nat}
  # the memory reader has no bytes at this physical address
  AcpiNotMapped{address: W.W64}
  # no table with this signature
  AcpiTableMissing{signature: B.Octets}

  # AML

  # the definition block or a package ends inside a term
  AcpiAmlTruncated{}
  # an opcode this interpreter does not know (extended opcodes: 0x5B00 + op)
  AcpiAmlBadOpcode{opcode: U32}
  # a PkgLength with reserved bits set, or longer than its enclosing package
  AcpiAmlBadPkgLength{}
  # a NameString that is not well-formed
  AcpiAmlBadName{}
  # a name that does not resolve
  AcpiAmlUndefined{path: String}
  # a name defined twice in one scope
  AcpiAmlDuplicate{path: String}
  # an operand of the wrong kind (a statement where a value is needed, a
  # value that cannot be converted, a reference where none can be taken)
  AcpiAmlBadOperand{opcode: U32}
  # an operation on an object of a type it does not take
  AcpiAmlBadType{what: String}
  # Index past the end of a buffer, string or package; a field outside its
  # region or buffer
  AcpiAmlRange{}
  # Divide or Mod by zero
  AcpiAmlDivZero{}
  # Break or Continue outside While, Return outside a method
  AcpiAmlBadControl{}
  # a Fatal operator: type, code, argument
  AcpiAmlFatal{kind: U32, code: U32, arg: W.W64}
  # a construct this interpreter does not support (named in README.md)
  AcpiAmlUnsupported{what: String}
  # the step bound ran out before the evaluation finished
  AcpiAmlStepLimit{}
  # the operation-region host refused an access (its own code)
  AcpiAmlHost{code: U32}
