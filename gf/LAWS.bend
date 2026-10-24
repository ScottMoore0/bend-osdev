# GF(2^8) (gf.bend). For every reduction polynomial (every Gf8Field) and
# every input, multiplication is commutative and associative, distributes
# over addition, has 1 as its identity and 0 as its zero; addition is
# commutative and associative, with 0 as its identity and every element its
# own negative; xtime is multiplication by x; and powers add. (These are the
# laws of the ring GF(2)[x] modulo the polynomial, which hold whether or not
# the polynomial is irreducible.)
#
# For the named fields (AES's 0x11B and Reed-Solomon's 0x11D, both
# irreducible): every nonzero element has an inverse, and is a power of the
# field's generator, its logarithm (checked for all 255 nonzero bytes).
#
# Vectors: FIPS 197's worked products (section 4.2), the AES inverse of
# 0x53 (0xCA), and the Reed-Solomon powers of x. The tables (tables.bend),
# GF(2^128) (gf128.bend) and GF(2^m) (gfm.bend) laws follow.
import Base
import ../bytes/bytes.bend as B
import ./gf.bend as G
import ./tables.bend as T
import ./gf128.bend as H
import ./gfm.bend as M

# Multiplication: a commutative ring with identity, for every polynomial

law mul_comm:
  for +f: G.Gf8Field
  for +a: U32
  for +b: U32
  {G.Gf8.mul(f, a, b) == G.Gf8.mul(f, b, a) : U32}

law mul_assoc:
  for +f: G.Gf8Field
  for +a: U32
  for +b: U32
  for +c: U32
  {G.Gf8.mul(f, G.Gf8.mul(f, a, b), c) == G.Gf8.mul(f, a, G.Gf8.mul(f, b, c)) : U32}

law mul_distrib:
  for +f: G.Gf8Field
  for +a: U32
  for +b: U32
  for +c: U32
  {G.Gf8.mul(f, a, G.Gf8.add(b, c)) == G.Gf8.add(G.Gf8.mul(f, a, b), G.Gf8.mul(f, a, c)) : U32}

law mul_one:
  for +f: G.Gf8Field
  for +a: U32
  {G.Gf8.mul(f, 1, a) == G.Gf8.elt(a) : U32}

law mul_zero:
  for +f: G.Gf8Field
  for +a: U32
  {G.Gf8.mul(f, 0, a) == 0 : U32}

law xtime_mul_x:
  for +f: G.Gf8Field
  for +a: U32
  {G.Gf8.xtime(f, a) == G.Gf8.mul(f, 2, a) : U32}

# Addition: XOR, a group in which every element is its own negative

law add_comm:
  for +a: U32
  for +b: U32
  {G.Gf8.add(a, b) == G.Gf8.add(b, a) : U32}

law add_assoc:
  for +a: U32
  for +b: U32
  for +c: U32
  {G.Gf8.add(G.Gf8.add(a, b), c) == G.Gf8.add(a, G.Gf8.add(b, c)) : U32}

law add_zero:
  for +a: U32
  {G.Gf8.add(a, 0) == G.Gf8.elt(a) : U32}

law add_self:
  for +a: U32
  {G.Gf8.add(a, a) == 0 : U32}

# Powers: a^(m + n) = a^m * a^n

law pow_add:
  for +f: G.Gf8Field
  for +a: U32
  for +m: Nat
  for +n: Nat
  {G.Gf8.pow(f, a, Nat.add(m, n)) == G.Gf8.mul(f, G.Gf8.pow(f, a, m), G.Gf8.pow(f, a, n)) : U32}

# Inverses and logarithms in the named fields, for every nonzero element

law mul_inv_aes:
  for +a: U32
  for nz: {G.Gf8.is_zero(a) == False{} : Bool}
  {G.Gf8.mul(G.Gf8.aes(), a, G.Gf8.inv(G.Gf8.aes(), a)) == 1 : U32}

law mul_inv_rs:
  for +a: U32
  for nz: {G.Gf8.is_zero(a) == False{} : Bool}
  {G.Gf8.mul(G.Gf8.rs(), a, G.Gf8.inv(G.Gf8.rs(), a)) == 1 : U32}

law exp_log_aes:
  for +a: U32
  for nz: {G.Gf8.is_zero(a) == False{} : Bool}
  {G.Gf8.exp(G.Gf8.aes(), G.Gf8.log(G.Gf8.aes(), a)) == G.Gf8.elt(a) : U32}

law exp_log_rs:
  for +a: U32
  for nz: {G.Gf8.is_zero(a) == False{} : Bool}
  {G.Gf8.exp(G.Gf8.rs(), G.Gf8.log(G.Gf8.rs(), a)) == G.Gf8.elt(a) : U32}

law inv_zero:
  for +f: G.Gf8Field
  {G.Gf8.inv(f, 0) == 0 : U32}

# Vectors: FIPS 197, section 4.2: {57} * {83} = {c1}, {57} * {13} = {fe},
# and xtime: {57} * {02} = {ae}, {57} * {04} = {47}, {57} * {08} = {8e},
# {57} * {10} = {07}

law v_aes_mul:
  {G.Gf8.mul(G.Gf8.aes(), 87, 131) == 193 : U32}

law v_aes_mul13:
  {G.Gf8.mul(G.Gf8.aes(), 87, 19) == 254 : U32}

law v_aes_xtime:
  {[G.Gf8.xtime(G.Gf8.aes(), 87), G.Gf8.mul(G.Gf8.aes(), 87, 4), G.Gf8.mul(G.Gf8.aes(), 87, 8), G.Gf8.mul(G.Gf8.aes(), 87, 16)] == [174, 71, 142, 7] : List<&2, U32>}

# the inverse of {53} is {ca} (the AES S-box's first step)
law v_aes_inv:
  {G.Gf8.inv(G.Gf8.aes(), 83) == 202 : U32}

# in the Reed-Solomon field x^8 = x^4 + x^3 + x^2 + 1 = 0x1D, and x has
# order 255 (x^255 = 1): x generates the field
law v_rs_x8:
  {G.Gf8.exp(G.Gf8.rs(), 8n) == 29 : U32}

law v_rs_order:
  {G.Gf8.exp(G.Gf8.rs(), 255n) == 1 : U32}

law v_div:
  {G.Gf8.mul(G.Gf8.aes(), G.Gf8.div(G.Gf8.aes(), 87, 131), 131) == 87 : U32}

# The tables (tables.bend), for the named fields and every input: the
# table built by Gf8Tab.new is handed back unchanged beside each result, and
# the result is the reference's: a product is Gf8.mul, a logarithm Gf8.log,
# and the exponential of i (below 510) is Gf8.exp. They also give the
# reference's results on these vectors.

law tab_mul_aes:
  for +a: U32
  for +b: U32
  {T.Gf8Tab.mul(T.Gf8Tab.new(G.Gf8.aes()), a, b) == (T.Gf8Tab.new(G.Gf8.aes()), G.Gf8.mul(G.Gf8.aes(), a, b)) : T.Gf8Tab & U32}

law tab_mul_rs:
  for +a: U32
  for +b: U32
  {T.Gf8Tab.mul(T.Gf8Tab.new(G.Gf8.rs()), a, b) == (T.Gf8Tab.new(G.Gf8.rs()), G.Gf8.mul(G.Gf8.rs(), a, b)) : T.Gf8Tab & U32}

law tab_log_aes:
  for +a: U32
  {T.Gf8Tab.log(T.Gf8Tab.new(G.Gf8.aes()), a) == (T.Gf8Tab.new(G.Gf8.aes()), U32.from_nat(G.Gf8.log(G.Gf8.aes(), a))) : T.Gf8Tab & U32}

law tab_log_rs:
  for +a: U32
  {T.Gf8Tab.log(T.Gf8Tab.new(G.Gf8.rs()), a) == (T.Gf8Tab.new(G.Gf8.rs()), U32.from_nat(G.Gf8.log(G.Gf8.rs(), a))) : T.Gf8Tab & U32}

law tab_exp_aes:
  for +i: U32
  for +hi: {Nat.is_lt(U32.to_nat(i), 510n) == True{} : Bool}
  {T.Gf8Tab.exp(T.Gf8Tab.new(G.Gf8.aes()), i) == (T.Gf8Tab.new(G.Gf8.aes()), G.Gf8.exp(G.Gf8.aes(), U32.to_nat(i))) : T.Gf8Tab & U32}

law tab_exp_rs:
  for +i: U32
  for +hi: {Nat.is_lt(U32.to_nat(i), 510n) == True{} : Bool}
  {T.Gf8Tab.exp(T.Gf8Tab.new(G.Gf8.rs()), i) == (T.Gf8Tab.new(G.Gf8.rs()), G.Gf8.exp(G.Gf8.rs(), U32.to_nat(i))) : T.Gf8Tab & U32}

# a witness for tab_exp's hypothesis: the last entry, 509
law witness_tab_exp:
  {Nat.is_lt(U32.to_nat(509), 510n) == True{} : Bool}

law v_tab_mul_aes:
  {Pair.snd(T.Gf8Tab, U32, T.Gf8Tab.mul(T.Gf8Tab.new(G.Gf8.aes()), 87, 131)) == 193 : U32}

law v_tab_inv_aes:
  {Pair.snd(T.Gf8Tab, U32, T.Gf8Tab.inv(T.Gf8Tab.new(G.Gf8.aes()), 83)) == 202 : U32}

law v_tab_mul_rs:
  {Pair.snd(T.Gf8Tab, U32, T.Gf8Tab.mul(T.Gf8Tab.new(G.Gf8.rs()), 200, 77)) == G.Gf8.mul(G.Gf8.rs(), 200, 77) : U32}

law v_tab_zero:
  {Pair.snd(T.Gf8Tab, U32, T.Gf8Tab.mul(T.Gf8Tab.new(G.Gf8.rs()), 0, 77)) == 0 : U32}

# GF(2^128) (gf128.bend): vectors only. GCM: Test Case 2 of the GCM
# specification (McGrew and Viega; H = AES-128 of the zero block under the
# zero key): X1 = C * H, and GHASH(H, C || lengths). CMAC: the subkeys of
# SP 800-38B D.1 / RFC 4493 (L = AES-128(K, 0), K1 = 2L, K2 = 4L). The
# others pin the bit orders against each other. Laws for every input would
# compute on 128 symbolic bits through 128 rounds; ref/run.sh checks every
# function against independent implementations instead (see the README).
# H = 66e94bd4ef8a2c3b884cfa59ca342b2e, C = 0388dace60b6a392f328c2b971b2fe78,
# and a = 0123456789abcdeffedcba9876543210.

# 5e2ec746917062882c85b0685353deb7
law v_gcm_x1:
  {H.Gf128.mul_gcm(H.Gf128.of_words(59300558, 1622582162, 4079534777, 1907555960), H.Gf128.of_words(1726565332, 4018809915, 2286746201, 3392416558)) == H.Gf128.of_words(1580123974, 2440061576, 746958952, 1398005431) : H.Gf128}

# f38cbb1ad69223dcc3457ae5b6b0f885 (one block of C, then the lengths: 0 bits
# of A, 128 of C)
law v_gcm_ghash:
  {H.Gf128.ghash(H.Gf128.of_words(1726565332, 4018809915, 2286746201, 3392416558), [H.Gf128.of_words(59300558, 1622582162, 4079534777, 1907555960), H.Gf128.of_words(0, 0, 0, 128)]) == H.Gf128.of_words(4086086426, 3599901660, 3276110565, 3065051269) : H.Gf128}

# L = 7df76b0c1ab899b33e42f047b91b546f, K1 = fbeed618357133667c85e08f7236a8de,
# K2 = f7ddac306ae266ccf90bc11ee46d513b
law v_cmac_k1:
  {H.Gf128.double_be(H.Gf128.of_words(2113366796, 448305587, 1044574279, 3105576047)) == H.Gf128.of_words(4226733592, 896611174, 2089148559, 1916184798) : H.Gf128}

law v_cmac_k2:
  {H.Gf128.double_be(H.Gf128.of_words(4226733592, 896611174, 2089148559, 1916184798)) == H.Gf128.of_words(4158499888, 1793222348, 4178297118, 3832369467) : H.Gf128}

# GCM's x is the block 0x40 00 .. 00: mul_x_gcm is multiplication by it
law v_gcm_mul_x:
  {H.Gf128.mul_gcm(H.Gf128.of_words(19088743, 2309737967, 4275878552, 1985229328), H.Gf128.of_words(1073741824, 0, 0, 0)) == H.Gf128.mul_x_gcm(H.Gf128.of_words(19088743, 2309737967, 4275878552, 1985229328)) : H.Gf128}

law v_gcm_mul_x_value:
  {H.Gf128.mul_x_gcm(H.Gf128.of_words(19088743, 2309737967, 4275878552, 1985229328)) == H.Gf128.of_words(9544371, 3302352631, 4285422924, 992614664) : H.Gf128}

# in big-endian order x is the number 2: double_be is multiplication by it
law v_be_mul_x:
  {H.Gf128.mul_be(H.Gf128.of_words(19088743, 2309737967, 4275878552, 1985229328), H.Gf128.of_words(0, 0, 0, 2)) == H.Gf128.double_be(H.Gf128.of_words(19088743, 2309737967, 4275878552, 1985229328)) : H.Gf128}

law v_be_mul:
  {H.Gf128.mul_be(H.Gf128.of_words(19088743, 2309737967, 4275878552, 1985229328), H.Gf128.of_words(1726565332, 4018809915, 2286746201, 3392416558)) == H.Gf128.of_words(780021721, 1580971822, 2568813327, 4049188832) : H.Gf128}

# XTS: the top bit of byte 15 wraps round as 0x87 into byte 0
law v_xts_wrap:
  {H.Gf128.double_le(H.Gf128.of_words(0, 0, 0, 255)) == H.Gf128.of_words(2264924160, 0, 0, 254) : H.Gf128}

law v_xts_double:
  {H.Gf128.double_le(H.Gf128.of_words(19088743, 2309737967, 4275878552, 1985229328)) == H.Gf128.of_words(38177486, 307731423, 4256789809, 3987235872) : H.Gf128}

law v_gf128_octets:
  {H.Gf128.of_octets(H.Gf128.to_octets(H.Gf128.of_words(1726565332, 4018809915, 2286746201, 3392416558))) == Done{H.Gf128.of_words(1726565332, 4018809915, 2286746201, 3392416558)} : Result<&2, &2, H.Gf128Error, H.Gf128>}

law v_gf128_short:
  {H.Gf128.of_octets(B.Octets.zeros(15n)) == Fail{H.Gf128BadLength{15n}} : Result<&2, &2, H.Gf128Error, H.Gf128>}

# GF(2^m) (gfm.bend). For every field and input: addition commutes. For
# GF(2^4): multiplication commutes (all 256 pairs) and every nonzero element
# has an inverse; for GF(2^5), inverses too. Vectors for the BCH fields: x^13
# = x^4 + x^3 + x + 1, x has order 8191 (so generates GF(2^13)), a product,
# an inverse and a logarithm (x^100 = 1664), from an independent model
# (ref/gen.py).

law gfm_add_comm:
  for +f: M.GfmField
  for +a: U32
  for +b: U32
  {M.Gfm.add(f, a, b) == M.Gfm.add(f, b, a) : U32}

law gfm_mul_comm_gf16:
  for +a: U32
  for +b: U32
  {M.Gfm.mul(M.Gfm.gf16(), a, b) == M.Gfm.mul(M.Gfm.gf16(), b, a) : U32}

law gfm_mul_inv_gf16:
  for +a: U32
  for nz: {U32.is_eq(M.Gfm.elt(M.Gfm.gf16(), a), 0) == False{} : Bool}
  {M.Gfm.mul(M.Gfm.gf16(), a, M.Gfm.inv(M.Gfm.gf16(), a)) == 1 : U32}

law gfm_mul_inv_gf32:
  for +a: U32
  for nz: {U32.is_eq(M.Gfm.elt(M.Gfm.gf32(), a), 0) == False{} : Bool}
  {M.Gfm.mul(M.Gfm.gf32(), a, M.Gfm.inv(M.Gfm.gf32(), a)) == 1 : U32}

law v_bch13_x13:
  {M.Gfm.exp(M.Gfm.bch13(), 13) == 27 : U32}

law v_bch13_order:
  {M.Gfm.exp(M.Gfm.bch13(), 8191) == 1 : U32}

law v_bch13_mul:
  {M.Gfm.mul(M.Gfm.bch13(), 1234, 5678) == 4994 : U32}

law v_bch13_inv:
  {M.Gfm.inv(M.Gfm.bch13(), 1234) == 2297 : U32}

law v_bch13_log:
  {M.Gfm.log(M.Gfm.bch13(), 1664) == 100 : U32}

law v_bch14_mul:
  {M.Gfm.mul(M.Gfm.bch14(), 12345, 6789) == 6882 : U32}
