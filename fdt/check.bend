import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./rsvmap.bend as R
import ./structure.bend as S
import ./tree.bend as T
import ./props.bend as P
import ./path.bend as Pa
import ./fdt.bend as F
import ./example.bend as X

def blob() -> B.Octets:
  F.Fdt.build_with(T.FdtStringsDedup{}, X.FdtExample.tree(), X.FdtExample.rsv(), 0)

def err(e: E.FdtError) -> String:
  match e:
    case E.FdtBadToken{t}:
      "bad token " ++ U32.show(t)
    case E.FdtTooShort{}:
      "too short"
    case E.FdtBadMagic{}:
      "bad magic"
    case E.FdtBadVersion{}:
      "bad version"
    case E.FdtTruncated{}:
      "truncated"
    case E.FdtBadTotalSize{}:
      "totalsize past the end of the blob"
    case _:
      "another error"

def show(r: Result<&2, &2, E.FdtError, F.FdtBlob>) -> String:
  match r:
    case Done{b}:
      match b:
        case F.FdtBlob{v, boot, rs, root}:
          "version " ++ U32.show(v) ++ ", " ++ Nat.show(List.length(&2, R.FdtRsv, rs)) ++ " reservation(s): " ++ T.FdtNode.dump(root)
    case Fail{e}:
      "error: " ++ err(e)

def text.r(r: Result<&2, &2, E.FdtError, String>) -> String:
  match r:
    case Done{s}:
      s
    case Fail{e}:
      "not a string"

def text(m: Maybe<&2, B.Octets>) -> String:
  match m:
    case Some{v}:
      text.r(P.FdtProp.text(v))
    case None{}:
      "none"

def ntoks(r: Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>) -> String:
  match r:
    case Done{ts}:
      Nat.show(List.length(&2, S.FdtToken, ts)) ++ " tokens"
    case Fail{e}:
      "error: " ++ err(e)

def regs(m: Maybe<&2, Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>>) -> String:
  match m:
    case Some{r}:
      match r:
        case Done{l}:
          match l:
            case Con{g, t}:
              match g:
                case P.FdtReg{a, s}:
                  W.W64.show_hex(a) ++ " " ++ W.W64.show_hex(s)
            case Nil{}:
              "no reg"
        case Fail{e}:
          "error: " ++ err(e)
    case None{}:
      "none"

# names that share bytes: a tail of an earlier name, a repeat, the empty
# name, and a name with a NUL inside (the deduplicating writer searches the
# block for that one; the reader reads it up to its NUL)
def nprop(k: B.Octets) -> T.FdtProp:
  T.FdtProp{k, B.Octets.of_list([])}

def names() -> T.FdtNode:
  T.FdtNode{B.Octets.of_string(""), [nprop(B.Octets.of_string("linux,phandle")), nprop(B.Octets.of_string("phandle")), nprop(B.Octets.of_string("le")), nprop(B.Octets.of_string("status")), nprop(B.Octets.of_string("phandle")), nprop(B.Octets.of_string("x")), nprop(B.Octets.of_list([108, 101, 0, 120])), nprop(B.Octets.of_string(""))], []}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(B.Octets.len(blob())) ++ " bytes: " ++ B.Octets.hex(B.Octets.take(48n, blob())))
    IO.print(show(F.Fdt.parse(F.FdtOptions.default(), blob())))
    IO.print(text(Pa.FdtNode.find_prop(X.FdtExample.tree(), "/chosen", "bootargs")))
    IO.print(text(Pa.FdtNode.find_prop(X.FdtExample.tree(), "serial0", "compatible")))
    IO.print(regs(Pa.FdtNode.find_reg(X.FdtExample.tree(), "/memory@0")))
    IO.print(ntoks(S.FdtLexer.finish(True{}, S.FdtLexer.feed(S.FdtLexer.feed(S.FdtLexer.start(), B.Octets.slice(72n, 100n, blob())), B.Octets.slice(172n, 424n, blob())))))
    IO.print(show(F.Fdt.parse(F.FdtOptions.default(), B.Octets.take(300n, blob()))))
    IO.print(show(F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_string("not a devicetree blob"))))
    IO.print(B.Octets.hex(F.Fdt.build_with(T.FdtStringsDedup{}, names(), [], 0)))
    IO.print(show(F.Fdt.parse(F.FdtOptions.default(), F.Fdt.build_with(T.FdtStringsDedup{}, names(), [], 0))))

#|708 bytes: d00dfeed000002c4000000480000025400000028000000110000001000000000000000700000020c0000000010000000
#|version 17, 1 reservation(s): {model=66736c2c6d706338353732647300;compatible=66736c2c6d706338353732647300;#address-cells=00000001;#size-cells=00000001;cpus{#address-cells=00000001;#size-cells=00000000;cpu@0{device_type=63707500;reg=00000000;timebase-frequency=312c8040;clock-frequency=312c8040;}cpu@1{device_type=63707500;reg=00000001;timebase-frequency=312c8040;clock-frequency=312c8040;}}memory@0{device_type=6d656d6f727900;reg=0000000020000000;}uart@fe001000{compatible=6e73313635353000;reg=fe00100000000100;}chosen{bootargs=726f6f743d2f6465762f7364613200;}aliases{serial0=2f7561727440666530303130303000;}}
#|root=/dev/sda2
#|ns16550
#|0000000000000000 0000000020000000
#|36 tokens
#|error: totalsize past the end of the blob
#|error: bad magic
#|d00dfeed000000c400000038000000a8000000280000001100000010000000000000001c0000007000000000000000000000000000000000000000010000000000000003000000000000000000000003000000000000000600000003000000000000000b00000003000000000000000e00000003000000000000000600000003000000000000001500000003000000000000001700000003000000000000000d00000002000000096c696e75782c7068616e646c65007374617475730078006c65007800
#|version 17, 0 reservation(s): {linux,phandle=;phandle=;le=;status=;phandle=;x=;le=;=;}
