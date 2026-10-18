# bend-osdev-acpi, dsdt.bend: the Differentiated and Secondary System
# Description Tables, "DSDT" and "SSDT" (ACPI 6.5, sections 5.2.11.1 and
# 5.2.11.2): a header, then a definition block of AML byte code (chapter
# 20), kept here as its bytes; aml_*.bend read and run it. A definition
# block whose header revision is below 2 uses 32-bit integers (chapter 19,
# DefinitionBlock: ComplianceRevision), 64-bit otherwise.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H

type AcpiAml is Data:
  AcpiAml{header: H.AcpiHeader, aml: B.Octets}

def AcpiAml.header(t: AcpiAml) -> H.AcpiHeader:
  match t:
    case AcpiAml{h, a}:
      h

def AcpiAml.aml(t: AcpiAml) -> B.Octets:
  match t:
    case AcpiAml{h, a}:
      a

# true when the block's integers are 64 bits wide
def AcpiAml.wide(t: AcpiAml) -> Bool:
  U32.is_le(2, H.AcpiHeader.revision(AcpiAml.header(t)))

def AcpiAml.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiAml>:
  match t:
    case H.AcpiSdt{h, body}:
      Done{AcpiAml{h, body}}

def aml.parse(r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiAml>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      AcpiAml.of_sdt(t)

# a DSDT or SSDT at the front of o (checked; either signature)
def AcpiAml.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiAml>:
  aml.parse(H.AcpiSdt.parse(o))

def AcpiAml.parse_dsdt(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiAml>:
  aml.parse(H.AcpiSdt.parse_sig(B.Octets.of_string("DSDT"), o))

# the table: the header's signature as given (DSDT or SSDT), length and
# checksum computed
def AcpiAml.build(t: AcpiAml) -> B.Octets:
  match t:
    case AcpiAml{h, a}:
      H.AcpiSdt.build(h, a)
