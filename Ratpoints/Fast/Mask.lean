/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# Bit masks in byte arrays

A mask is a `ByteArray`; bit `j` is bit `j % 8` of byte `j / 8`. Two operations are primitives
implemented in C (`@[extern c inline]`), each with a reference definition in Lean that the proofs
use: `Ratpoints.Mask.andRows`, the AND with a list of rows shifted to the right, one after the other
until nothing is left, in place when the mask is not shared, whose reference
`Ratpoints.Mask.andRowsFrom` is the loop of `Ratpoints.Mask.andShr` and whose C code, for at most
`64` rows with shifts that are multiples of `8` and rows long enough for the mask, works through the
mask in blocks of 128 bytes held in registers, every row ANDed into a block before the block is
written back, and otherwise goes row by row, byte by byte; and `Ratpoints.Mask.nextSet`, the first
set bit from a position on. The C code reads and writes words of 64 bits (16-byte vectors in
`Ratpoints.Mask.andRows`) and bytes; it does not depend on the byte order. It assumes that `size_t`
has 64 bits: a shift or a position that is not a scalar becomes `SIZE_MAX`, which lies beyond every
array only then, and eight times the size of a mask must not wrap. On a platform with 32 bits, rows
of more than 256 MiB with shifts from `2 ^ 31` on, and masks of 512 MiB or more, could give other
results than the reference definitions.

The compiled program runs the C code, the proofs are about the reference definitions: that the
two agree is not proved, it is what one has to trust beyond Lean's runtime.
-/

@[expose] public section

namespace Ratpoints

namespace Mask

/-- Byte `i` of `a` as a natural number, `0` past the end. -/
def byte (a : ByteArray) (i : Nat) : Nat := if h : i < a.size then a[i].toNat else 0

/-- Bit `j` of the mask `a`. -/
def bit (a : ByteArray) (j : Nat) : Bool := (byte a (j / 8)).testBit (j % 8)

/-- Byte `i` of the mask `row` shifted to the right by `s` bits. -/
def shrByte (row : ByteArray) (s i : Nat) : UInt8 :=
  ((byte row (s / 8 + i) + 256 * byte row (s / 8 + i + 1)) >>> (s % 8)).toUInt8

/-- The mask `acc` ANDed with the mask `row` shifted to the right by `s` bits: byte `i` of the
result is byte `i` of `acc` ANDed with byte `i` of `row` shifted to the right by `s` bits, so that
bit `j < 8 n` of the result (`n` the size of `acc`) is bit `j` of `acc` and bit `j + s` of `row`;
the result is the empty array when every byte is `0`. -/
def andShr (acc row : ByteArray) (s : Nat) : ByteArray :=
  let r : ByteArray := ⟨acc.data.mapIdx fun i x ↦ x &&& shrByte row s i⟩
  if r.data.all (· == 0) then .empty else r

/-- The reference definition of `Ratpoints.Mask.andRows`: `acc` ANDed with the rows `rs[i]`
shifted to the right by `sh[i] + o` bits (`Ratpoints.Mask.andShr`), from position `i` on, one after
the other until nothing is left. -/
def andRowsFrom (rs : Array ByteArray) (sh : Array Nat) (o : Nat) (acc : ByteArray) (i : Nat) :
    ByteArray :=
  if h : i < rs.size then
    let acc := andShr acc rs[i] (sh[i]! + o)
    if acc.size == 0 then acc else andRowsFrom rs sh o acc (i + 1)
  else acc
termination_by rs.size - i

/-- The mask `acc` ANDed with the rows `rs[i]` shifted to the right by `sh[i] + o` bits, all of
them: bit `j < 8 n` of the result (`n` the size of `acc`) is bit `j` of `acc` and bit
`j + sh[i] + o` of every `rs[i]`, and the result is the empty array when no bit is left (when there
is a row). The C code works in place when `acc` is not shared. -/
@[extern c inline "({ typedef uint64_t rp_v2 __attribute__((vector_size(16))); \
  lean_object * rp_r = #1; size_t rp_f = lean_array_size(#2); \
  if (rp_f > 0) { \
    rp_r = lean_sarray_ensure_exclusive(rp_r); \
    size_t rp_n = lean_sarray_size(rp_r), rp_nw = rp_n / 8, rp_ns = lean_array_size(#3); \
    uint8_t * rp_a = lean_sarray_cptr(rp_r); \
    size_t rp_o = lean_is_scalar(#4) ? lean_unbox(#4) : SIZE_MAX; \
    /* the fast path: at most 64 rows, every shift a multiple of 8, every row long enough */ \
    uint8_t const * rp_p[64]; int rp_fast = rp_f <= 64; \
    for (size_t rp_j = 0; rp_fast && rp_j < rp_f; rp_j++) { \
      lean_object * rp_row = lean_array_get_core(#2, rp_j); \
      lean_object * rp_so = rp_j < rp_ns ? lean_array_get_core(#3, rp_j) : lean_box(0); \
      size_t rp_m = lean_sarray_size(rp_row); \
      size_t rp_s = lean_is_scalar(rp_so) && rp_o != SIZE_MAX \
        ? lean_unbox(rp_so) + rp_o : SIZE_MAX; \
      size_t rp_q = rp_s >> 3; \
      if ((rp_s & 7) != 0 || rp_q > rp_m || rp_m - rp_q < rp_n) rp_fast = 0; \
      else rp_p[rp_j] = lean_sarray_cptr(rp_row) + rp_q; } \
    uint64_t rp_any = 0; \
    if (rp_fast) { \
      size_t rp_w = 0; \
      /* blocks of 16 words in eight vector registers; a block is left once it is zero, \
         which is tested after every fourth row */ \
      for (; rp_w + 16 <= rp_nw; rp_w += 16) { \
        uint8_t * rp_b = rp_a + 8 * rp_w; \
        rp_v2 rp_x0, rp_x1, rp_x2, rp_x3, rp_x4, rp_x5, rp_x6, rp_x7; \
        __builtin_memcpy(&rp_x0, rp_b, 16); __builtin_memcpy(&rp_x1, rp_b + 16, 16); \
        __builtin_memcpy(&rp_x2, rp_b + 32, 16); __builtin_memcpy(&rp_x3, rp_b + 48, 16); \
        __builtin_memcpy(&rp_x4, rp_b + 64, 16); __builtin_memcpy(&rp_x5, rp_b + 80, 16); \
        __builtin_memcpy(&rp_x6, rp_b + 96, 16); __builtin_memcpy(&rp_x7, rp_b + 112, 16); \
        for (size_t rp_j = 0; rp_j < rp_f; rp_j++) { \
          uint8_t const * rp_c = rp_p[rp_j] + 8 * rp_w; rp_v2 rp_y; \
          __builtin_memcpy(&rp_y, rp_c, 16); rp_x0 &= rp_y; \
          __builtin_memcpy(&rp_y, rp_c + 16, 16); rp_x1 &= rp_y; \
          __builtin_memcpy(&rp_y, rp_c + 32, 16); rp_x2 &= rp_y; \
          __builtin_memcpy(&rp_y, rp_c + 48, 16); rp_x3 &= rp_y; \
          __builtin_memcpy(&rp_y, rp_c + 64, 16); rp_x4 &= rp_y; \
          __builtin_memcpy(&rp_y, rp_c + 80, 16); rp_x5 &= rp_y; \
          __builtin_memcpy(&rp_y, rp_c + 96, 16); rp_x6 &= rp_y; \
          __builtin_memcpy(&rp_y, rp_c + 112, 16); rp_x7 &= rp_y; \
          if ((rp_j & 3) == 3) { \
            rp_v2 rp_t = rp_x0 | rp_x1 | rp_x2 | rp_x3 | rp_x4 | rp_x5 | rp_x6 | rp_x7; \
            if ((rp_t[0] | rp_t[1]) == 0) break; } } \
        __builtin_memcpy(rp_b, &rp_x0, 16); __builtin_memcpy(rp_b + 16, &rp_x1, 16); \
        __builtin_memcpy(rp_b + 32, &rp_x2, 16); __builtin_memcpy(rp_b + 48, &rp_x3, 16); \
        __builtin_memcpy(rp_b + 64, &rp_x4, 16); __builtin_memcpy(rp_b + 80, &rp_x5, 16); \
        __builtin_memcpy(rp_b + 96, &rp_x6, 16); __builtin_memcpy(rp_b + 112, &rp_x7, 16); \
        rp_v2 rp_t = rp_x0 | rp_x1 | rp_x2 | rp_x3 | rp_x4 | rp_x5 | rp_x6 | rp_x7; \
        rp_any |= rp_t[0] | rp_t[1]; } \
      /* the remaining words one at a time, then the remaining bytes */ \
      for (; rp_w < rp_nw; rp_w++) { \
        uint64_t rp_v; __builtin_memcpy(&rp_v, rp_a + 8 * rp_w, 8); \
        for (size_t rp_j = 0; rp_v && rp_j < rp_f; rp_j++) { \
          uint64_t rp_y; __builtin_memcpy(&rp_y, rp_p[rp_j] + 8 * rp_w, 8); rp_v &= rp_y; } \
        __builtin_memcpy(rp_a + 8 * rp_w, &rp_v, 8); rp_any |= rp_v; } \
      for (size_t rp_i = 8 * rp_nw; rp_i < rp_n; rp_i++) { \
        for (size_t rp_j = 0; rp_j < rp_f; rp_j++) rp_a[rp_i] &= rp_p[rp_j][rp_i]; \
        rp_any |= rp_a[rp_i]; } \
    } else { \
      /* otherwise row by row, byte by byte */ \
      for (size_t rp_j = 0; rp_j < rp_f; rp_j++) { \
        lean_object * rp_row = lean_array_get_core(#2, rp_j); \
        lean_object * rp_so = rp_j < rp_ns ? lean_array_get_core(#3, rp_j) : lean_box(0); \
        size_t rp_m = lean_sarray_size(rp_row); uint8_t const * rp_c = lean_sarray_cptr(rp_row); \
        size_t rp_s = lean_is_scalar(rp_so) && rp_o != SIZE_MAX \
          ? lean_unbox(rp_so) + rp_o : SIZE_MAX; \
        size_t rp_q = rp_s >> 3; unsigned rp_k = (unsigned)(rp_s & 7); \
        rp_any = 0; \
        for (size_t rp_i = 0; rp_i < rp_n; rp_i++) { \
          size_t rp_t = rp_q + rp_i; \
          unsigned rp_v = rp_t < rp_m ? rp_c[rp_t] : 0; \
          if (rp_t + 1 < rp_m) rp_v |= (unsigned)rp_c[rp_t + 1] << 8; \
          rp_a[rp_i] &= (uint8_t)(rp_v >> rp_k); rp_any |= rp_a[rp_i]; } \
        if (rp_any == 0) break; } } \
    if (rp_any == 0) lean_sarray_set_size(rp_r, 0); } \
  rp_r; })"]
def andRows (acc : ByteArray) (rs : @& Array ByteArray) (sh : @& Array Nat) (o : @& Nat) :
    ByteArray :=
  andRowsFrom rs sh o acc 0

/-- The reference definition of `Ratpoints.Mask.nextSet`: the first `k` from `j` to `8 n - 1`
with bit `k` of `a` set (`n` the size of `a`), or `8 n`. -/
def nextSetSpec (a : ByteArray) (j : Nat) : Nat :=
  ((List.range' j (8 * a.size - j)).find? (bit a)).getD (8 * a.size)

/-- The first set bit of the mask `a` at or after `j`, or `8 n` (`n` the size of `a`) when there
is none. -/
@[extern c inline "({ size_t rp_n = lean_sarray_size(#1); \
  uint8_t const * rp_a = lean_sarray_cptr(#1); \
  size_t rp_j = lean_is_scalar(#2) ? lean_unbox(#2) : SIZE_MAX; size_t rp_res = 8 * rp_n; \
  if (rp_j < 8 * rp_n) { \
    size_t rp_i = rp_j >> 3; unsigned rp_c = (unsigned)rp_a[rp_i] >> (rp_j & 7); \
    if (rp_c) rp_res = rp_j + (size_t)__builtin_ctz(rp_c); \
    else { \
      rp_i++; \
      for (;;) { uint64_t rp_w; if (rp_i + 8 > rp_n) break; \
        __builtin_memcpy(&rp_w, rp_a + rp_i, 8); if (rp_w) break; rp_i += 8; } \
      while (rp_i < rp_n && rp_a[rp_i] == 0) rp_i++; \
      if (rp_i < rp_n) rp_res = 8 * rp_i + (size_t)__builtin_ctz(rp_a[rp_i]); } } \
  lean_usize_to_nat(rp_res); })"]
def nextSet (a : @& ByteArray) (j : @& Nat) : Nat :=
  nextSetSpec a j

/-- Whether no bit of the mask `a` is set. -/
def isZero (a : ByteArray) : Bool := a.size == 0 || nextSet a 0 == 8 * a.size

/-- The set bits of the mask `a` from `j` on, in ascending order (with `fuel` at least the
number of them). -/
def setBitsFrom (a : ByteArray) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, j =>
    let k := nextSet a j
    if k < 8 * a.size then k :: setBitsFrom a fuel (k + 1) else []

/-- The set bits of the mask `a`, in ascending order. -/
def setBits (a : ByteArray) : List Nat := setBitsFrom a (8 * a.size) 0

end Mask

end Ratpoints
