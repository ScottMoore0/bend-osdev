import Base
import bend-kit-int@0.2.0.0/int.bend as Int
import ./word64.bend as W
import ./LAWS.bend as Laws

def Laws.add_wraps():
  {==}

def Laws.sub_wraps():
  {==}

def Laws.hi_of_parts():
  {==}

def Laws.lo_of_parts():
  {==}

def Laws.shl_crosses_halves():
  {==}

def Laws.shr_crosses_halves():
  {==}

def Laws.mul_of_max_halves():
  {==}

def Laws.show_max():
  {==}

def Laws.show_hex_parts():
  {==}

def Laws.show_hex_zero():
  {==}

def Laws.lo_from_u32(a):
  match a:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.hi_from_parts(h, l):
  match h l:
    case U32{WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.lo_from_parts(h, l):
  match h l:
    case U32{WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.parts_of(v):
  match v:
    case W.W64{Int.U64{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WCon{b32, WCon{b33, WCon{b34, WCon{b35, WCon{b36, WCon{b37, WCon{b38, WCon{b39, WCon{b40, WCon{b41, WCon{b42, WCon{b43, WCon{b44, WCon{b45, WCon{b46, WCon{b47, WCon{b48, WCon{b49, WCon{b50, WCon{b51, WCon{b52, WCon{b53, WCon{b54, WCon{b55, WCon{b56, WCon{b57, WCon{b58, WCon{b59, WCon{b60, WCon{b61, WCon{b62, WCon{b63, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}
