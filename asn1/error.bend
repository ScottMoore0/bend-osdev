# bend-osdev-asn1, errors: why bytes were refused as BER or DER, why a value
# could not be encoded, and why a typed reader or a schema refused an
# element. Each names one failure; README.md says which clause of ITU-T
# X.690 (02/2021) or X.680 (02/2021) each enforces.
import Base

type Asn1Error is Data:
  Asn1Truncated{}
  Asn1BadTag{}
  Asn1ReservedTag{}
  Asn1BadLength{}
  Asn1NonMinimalLength{}
  Asn1Indefinite{}
  Asn1PrimIndefinite{}
  Asn1NoEoc{}
  Asn1BadEoc{}
  Asn1BadForm{}
  Asn1SetOrder{}
  Asn1Trailing{}
  Asn1Exhausted{}
  Asn1TooLong{}
  Asn1Unexpected{}
  Asn1BadValue{}
  Asn1BadInteger{}
  Asn1Negative{}
  Asn1BadBits{}
  Asn1BadOid{}
  Asn1BadString{}
  Asn1BadTime{}
  Asn1SchemaMismatch{}
  Asn1SchemaExtra{}
  Asn1SchemaMissing{}
  Asn1SchemaDefault{}

# the error's name, for messages and tests
def Asn1Error.name(e: Asn1Error) -> String:
  match e:
    case Asn1Truncated{}:
      "Asn1Truncated"
    case Asn1BadTag{}:
      "Asn1BadTag"
    case Asn1ReservedTag{}:
      "Asn1ReservedTag"
    case Asn1BadLength{}:
      "Asn1BadLength"
    case Asn1NonMinimalLength{}:
      "Asn1NonMinimalLength"
    case Asn1Indefinite{}:
      "Asn1Indefinite"
    case Asn1PrimIndefinite{}:
      "Asn1PrimIndefinite"
    case Asn1NoEoc{}:
      "Asn1NoEoc"
    case Asn1BadEoc{}:
      "Asn1BadEoc"
    case Asn1BadForm{}:
      "Asn1BadForm"
    case Asn1SetOrder{}:
      "Asn1SetOrder"
    case Asn1Trailing{}:
      "Asn1Trailing"
    case Asn1Exhausted{}:
      "Asn1Exhausted"
    case Asn1TooLong{}:
      "Asn1TooLong"
    case Asn1Unexpected{}:
      "Asn1Unexpected"
    case Asn1BadValue{}:
      "Asn1BadValue"
    case Asn1BadInteger{}:
      "Asn1BadInteger"
    case Asn1Negative{}:
      "Asn1Negative"
    case Asn1BadBits{}:
      "Asn1BadBits"
    case Asn1BadOid{}:
      "Asn1BadOid"
    case Asn1BadString{}:
      "Asn1BadString"
    case Asn1BadTime{}:
      "Asn1BadTime"
    case Asn1SchemaMismatch{}:
      "Asn1SchemaMismatch"
    case Asn1SchemaExtra{}:
      "Asn1SchemaExtra"
    case Asn1SchemaMissing{}:
      "Asn1SchemaMissing"
    case Asn1SchemaDefault{}:
      "Asn1SchemaDefault"
