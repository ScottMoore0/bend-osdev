# The text round trip from the text: every string parse accepts is written
# back by show as that string in lower case (dashes and decimal digits as
# they are, hex letters in lower case). With text_round_trip and
# text_upper_round_trip (LAWS.bend), parse and show are inverse on the
# lower-case text form, and parse reads a UUID in either case.
import Base
import ./uuid.bend as U

law text_parse_show:
  for +s: String
  for u: U.Uuid
  for e: {U.Uuid.parse(s) == Done{u} : Result<&2, &2, U.UuidError, U.Uuid>}
  {U.Uuid.show(u) == String.to_lower(s) : String}
